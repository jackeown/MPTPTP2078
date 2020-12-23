%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:13 EST 2020

% Result     : Theorem 1.77s
% Output     : Refutation 1.77s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 159 expanded)
%              Number of leaves         :   14 (  44 expanded)
%              Depth                    :   15
%              Number of atoms          :  119 ( 467 expanded)
%              Number of equality atoms :   83 ( 404 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f536,plain,(
    $false ),
    inference(subsumption_resolution,[],[f535,f39])).

fof(f39,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & sK1 != sK2
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f32])).

fof(f32,plain,
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

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & X1 != X2
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & X1 != X2
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

fof(f535,plain,(
    k1_xboole_0 = sK2 ),
    inference(backward_demodulation,[],[f197,f534])).

fof(f534,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,sK2) ),
    inference(subsumption_resolution,[],[f524,f37])).

fof(f37,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f33])).

fof(f524,plain,
    ( sK1 = sK2
    | k1_xboole_0 = k3_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f329,f141])).

fof(f141,plain,(
    sK1 = k2_xboole_0(sK1,sK2) ),
    inference(backward_demodulation,[],[f36,f140])).

fof(f140,plain,(
    sK1 = k1_tarski(sK0) ),
    inference(subsumption_resolution,[],[f139,f38])).

fof(f38,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f33])).

fof(f139,plain,
    ( k1_xboole_0 = sK1
    | sK1 = k1_tarski(sK0) ),
    inference(resolution,[],[f52,f65])).

fof(f65,plain,(
    r1_tarski(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f44,f36])).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f36,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f329,plain,(
    ! [X0] :
      ( k2_xboole_0(sK1,X0) = X0
      | k1_xboole_0 = k3_xboole_0(sK1,X0) ) ),
    inference(resolution,[],[f171,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f171,plain,(
    ! [X0] :
      ( r1_xboole_0(sK1,X0)
      | k2_xboole_0(sK1,X0) = X0 ) ),
    inference(forward_demodulation,[],[f170,f140])).

fof(f170,plain,(
    ! [X0] :
      ( r1_xboole_0(sK1,X0)
      | k2_xboole_0(k1_tarski(sK0),X0) = X0 ) ),
    inference(resolution,[],[f151,f71])).

fof(f71,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,X5)
      | k2_xboole_0(k1_tarski(X4),X5) = X5 ) ),
    inference(resolution,[],[f50,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_tarski(X0),X1) ) ),
    inference(unused_predicate_definition_removal,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f151,plain,(
    ! [X0] :
      ( r2_hidden(sK0,X0)
      | r1_xboole_0(sK1,X0) ) ),
    inference(superposition,[],[f49,f140])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f197,plain,(
    sK2 = k3_xboole_0(sK1,sK2) ),
    inference(backward_demodulation,[],[f146,f196])).

fof(f196,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f172,f93])).

fof(f93,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f92,f42])).

fof(f42,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f92,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f83,f43])).

fof(f43,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f83,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(X0,X0)) ),
    inference(superposition,[],[f48,f40])).

fof(f40,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f172,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f57,f40])).

fof(f57,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

% (21213)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
fof(f7,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f146,plain,(
    k3_xboole_0(sK1,sK2) = k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) ),
    inference(backward_demodulation,[],[f130,f140])).

fof(f130,plain,(
    k3_xboole_0(sK1,sK2) = k5_xboole_0(k1_tarski(sK0),k5_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f89,f45])).

fof(f45,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f89,plain,(
    k3_xboole_0(sK1,sK2) = k5_xboole_0(k5_xboole_0(sK1,sK2),k1_tarski(sK0)) ),
    inference(superposition,[],[f48,f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:01:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.55  % (21192)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.56  % (21209)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.52/0.57  % (21208)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.52/0.57  % (21201)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.52/0.57  % (21201)Refutation not found, incomplete strategy% (21201)------------------------------
% 1.52/0.57  % (21201)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.57  % (21201)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.57  
% 1.52/0.57  % (21201)Memory used [KB]: 6140
% 1.52/0.57  % (21201)Time elapsed: 0.005 s
% 1.52/0.57  % (21201)------------------------------
% 1.52/0.57  % (21201)------------------------------
% 1.52/0.57  % (21200)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.52/0.58  % (21193)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.77/0.59  % (21188)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.77/0.59  % (21189)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.77/0.59  % (21191)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.77/0.59  % (21190)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.77/0.60  % (21186)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.77/0.61  % (21187)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.77/0.62  % (21193)Refutation found. Thanks to Tanya!
% 1.77/0.62  % SZS status Theorem for theBenchmark
% 1.77/0.62  % (21210)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.77/0.62  % SZS output start Proof for theBenchmark
% 1.77/0.62  fof(f536,plain,(
% 1.77/0.62    $false),
% 1.77/0.62    inference(subsumption_resolution,[],[f535,f39])).
% 1.77/0.62  fof(f39,plain,(
% 1.77/0.62    k1_xboole_0 != sK2),
% 1.77/0.62    inference(cnf_transformation,[],[f33])).
% 1.77/0.62  fof(f33,plain,(
% 1.77/0.62    k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & sK1 != sK2 & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.77/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f32])).
% 1.77/0.62  fof(f32,plain,(
% 1.77/0.62    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2)) => (k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & sK1 != sK2 & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 1.77/0.62    introduced(choice_axiom,[])).
% 1.77/0.62  fof(f27,plain,(
% 1.77/0.62    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.77/0.62    inference(ennf_transformation,[],[f22])).
% 1.77/0.62  fof(f22,negated_conjecture,(
% 1.77/0.62    ~! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.77/0.62    inference(negated_conjecture,[],[f21])).
% 1.77/0.62  fof(f21,conjecture,(
% 1.77/0.62    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.77/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).
% 1.77/0.62  fof(f535,plain,(
% 1.77/0.62    k1_xboole_0 = sK2),
% 1.77/0.62    inference(backward_demodulation,[],[f197,f534])).
% 1.77/0.62  fof(f534,plain,(
% 1.77/0.62    k1_xboole_0 = k3_xboole_0(sK1,sK2)),
% 1.77/0.62    inference(subsumption_resolution,[],[f524,f37])).
% 1.77/0.62  fof(f37,plain,(
% 1.77/0.62    sK1 != sK2),
% 1.77/0.62    inference(cnf_transformation,[],[f33])).
% 1.77/0.62  fof(f524,plain,(
% 1.77/0.62    sK1 = sK2 | k1_xboole_0 = k3_xboole_0(sK1,sK2)),
% 1.77/0.62    inference(superposition,[],[f329,f141])).
% 1.77/0.62  fof(f141,plain,(
% 1.77/0.62    sK1 = k2_xboole_0(sK1,sK2)),
% 1.77/0.62    inference(backward_demodulation,[],[f36,f140])).
% 1.77/0.62  fof(f140,plain,(
% 1.77/0.62    sK1 = k1_tarski(sK0)),
% 1.77/0.62    inference(subsumption_resolution,[],[f139,f38])).
% 1.77/0.62  fof(f38,plain,(
% 1.77/0.62    k1_xboole_0 != sK1),
% 1.77/0.62    inference(cnf_transformation,[],[f33])).
% 1.77/0.62  fof(f139,plain,(
% 1.77/0.62    k1_xboole_0 = sK1 | sK1 = k1_tarski(sK0)),
% 1.77/0.62    inference(resolution,[],[f52,f65])).
% 1.77/0.62  fof(f65,plain,(
% 1.77/0.62    r1_tarski(sK1,k1_tarski(sK0))),
% 1.77/0.62    inference(superposition,[],[f44,f36])).
% 1.77/0.62  fof(f44,plain,(
% 1.77/0.62    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.77/0.62    inference(cnf_transformation,[],[f6])).
% 1.77/0.62  fof(f6,axiom,(
% 1.77/0.62    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.77/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.77/0.62  fof(f52,plain,(
% 1.77/0.62    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 1.77/0.62    inference(cnf_transformation,[],[f35])).
% 1.77/0.62  fof(f35,plain,(
% 1.77/0.62    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.77/0.62    inference(flattening,[],[f34])).
% 1.77/0.62  fof(f34,plain,(
% 1.77/0.62    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.77/0.62    inference(nnf_transformation,[],[f19])).
% 1.77/0.62  fof(f19,axiom,(
% 1.77/0.62    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.77/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.77/0.62  fof(f36,plain,(
% 1.77/0.62    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.77/0.62    inference(cnf_transformation,[],[f33])).
% 1.77/0.62  fof(f329,plain,(
% 1.77/0.62    ( ! [X0] : (k2_xboole_0(sK1,X0) = X0 | k1_xboole_0 = k3_xboole_0(sK1,X0)) )),
% 1.77/0.62    inference(resolution,[],[f171,f51])).
% 1.77/0.62  fof(f51,plain,(
% 1.77/0.62    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.77/0.62    inference(cnf_transformation,[],[f30])).
% 1.77/0.62  fof(f30,plain,(
% 1.77/0.62    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 1.77/0.62    inference(ennf_transformation,[],[f26])).
% 1.77/0.62  fof(f26,plain,(
% 1.77/0.62    ! [X0,X1] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.77/0.62    inference(unused_predicate_definition_removal,[],[f2])).
% 1.77/0.62  fof(f2,axiom,(
% 1.77/0.62    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.77/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.77/0.62  fof(f171,plain,(
% 1.77/0.62    ( ! [X0] : (r1_xboole_0(sK1,X0) | k2_xboole_0(sK1,X0) = X0) )),
% 1.77/0.62    inference(forward_demodulation,[],[f170,f140])).
% 1.77/0.62  fof(f170,plain,(
% 1.77/0.62    ( ! [X0] : (r1_xboole_0(sK1,X0) | k2_xboole_0(k1_tarski(sK0),X0) = X0) )),
% 1.77/0.62    inference(resolution,[],[f151,f71])).
% 1.77/0.62  fof(f71,plain,(
% 1.77/0.62    ( ! [X4,X5] : (~r2_hidden(X4,X5) | k2_xboole_0(k1_tarski(X4),X5) = X5) )),
% 1.77/0.62    inference(resolution,[],[f50,f55])).
% 1.77/0.62  fof(f55,plain,(
% 1.77/0.62    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.77/0.62    inference(cnf_transformation,[],[f31])).
% 1.77/0.62  fof(f31,plain,(
% 1.77/0.62    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1))),
% 1.77/0.62    inference(ennf_transformation,[],[f25])).
% 1.77/0.62  fof(f25,plain,(
% 1.77/0.62    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_tarski(X0),X1))),
% 1.77/0.62    inference(unused_predicate_definition_removal,[],[f17])).
% 1.77/0.62  fof(f17,axiom,(
% 1.77/0.62    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.77/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.77/0.62  fof(f50,plain,(
% 1.77/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.77/0.62    inference(cnf_transformation,[],[f29])).
% 1.77/0.62  fof(f29,plain,(
% 1.77/0.62    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.77/0.62    inference(ennf_transformation,[],[f5])).
% 1.77/0.62  fof(f5,axiom,(
% 1.77/0.62    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.77/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.77/0.62  fof(f151,plain,(
% 1.77/0.62    ( ! [X0] : (r2_hidden(sK0,X0) | r1_xboole_0(sK1,X0)) )),
% 1.77/0.62    inference(superposition,[],[f49,f140])).
% 1.77/0.62  fof(f49,plain,(
% 1.77/0.62    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.77/0.62    inference(cnf_transformation,[],[f28])).
% 1.77/0.62  fof(f28,plain,(
% 1.77/0.62    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.77/0.62    inference(ennf_transformation,[],[f18])).
% 1.77/0.62  fof(f18,axiom,(
% 1.77/0.62    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.77/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.77/0.62  fof(f197,plain,(
% 1.77/0.62    sK2 = k3_xboole_0(sK1,sK2)),
% 1.77/0.62    inference(backward_demodulation,[],[f146,f196])).
% 1.77/0.62  fof(f196,plain,(
% 1.77/0.62    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 1.77/0.62    inference(forward_demodulation,[],[f172,f93])).
% 1.77/0.62  fof(f93,plain,(
% 1.77/0.62    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.77/0.62    inference(forward_demodulation,[],[f92,f42])).
% 1.77/0.62  fof(f42,plain,(
% 1.77/0.62    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.77/0.62    inference(cnf_transformation,[],[f23])).
% 1.77/0.62  fof(f23,plain,(
% 1.77/0.62    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.77/0.62    inference(rectify,[],[f4])).
% 1.77/0.62  fof(f4,axiom,(
% 1.77/0.62    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.77/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.77/0.62  fof(f92,plain,(
% 1.77/0.62    ( ! [X0] : (k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 1.77/0.62    inference(forward_demodulation,[],[f83,f43])).
% 1.77/0.62  fof(f43,plain,(
% 1.77/0.62    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 1.77/0.62    inference(cnf_transformation,[],[f24])).
% 1.77/0.62  fof(f24,plain,(
% 1.77/0.62    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 1.77/0.62    inference(rectify,[],[f3])).
% 1.77/0.62  fof(f3,axiom,(
% 1.77/0.62    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 1.77/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 1.77/0.62  fof(f83,plain,(
% 1.77/0.62    ( ! [X0] : (k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(X0,X0))) )),
% 1.77/0.62    inference(superposition,[],[f48,f40])).
% 1.77/0.62  fof(f40,plain,(
% 1.77/0.62    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.77/0.62    inference(cnf_transformation,[],[f8])).
% 1.77/0.62  fof(f8,axiom,(
% 1.77/0.62    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.77/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.77/0.62  fof(f48,plain,(
% 1.77/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 1.77/0.62    inference(cnf_transformation,[],[f9])).
% 1.77/0.62  fof(f9,axiom,(
% 1.77/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 1.77/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 1.77/0.62  fof(f172,plain,(
% 1.77/0.62    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 1.77/0.62    inference(superposition,[],[f57,f40])).
% 1.77/0.62  fof(f57,plain,(
% 1.77/0.62    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.77/0.62    inference(cnf_transformation,[],[f7])).
% 1.77/0.62  % (21213)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.77/0.62  fof(f7,axiom,(
% 1.77/0.62    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.77/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.77/0.62  fof(f146,plain,(
% 1.77/0.62    k3_xboole_0(sK1,sK2) = k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))),
% 1.77/0.62    inference(backward_demodulation,[],[f130,f140])).
% 1.77/0.62  fof(f130,plain,(
% 1.77/0.62    k3_xboole_0(sK1,sK2) = k5_xboole_0(k1_tarski(sK0),k5_xboole_0(sK1,sK2))),
% 1.77/0.62    inference(superposition,[],[f89,f45])).
% 1.77/0.62  fof(f45,plain,(
% 1.77/0.62    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.77/0.62    inference(cnf_transformation,[],[f1])).
% 1.77/0.62  fof(f1,axiom,(
% 1.77/0.62    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.77/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.77/0.62  fof(f89,plain,(
% 1.77/0.62    k3_xboole_0(sK1,sK2) = k5_xboole_0(k5_xboole_0(sK1,sK2),k1_tarski(sK0))),
% 1.77/0.62    inference(superposition,[],[f48,f36])).
% 1.77/0.62  % SZS output end Proof for theBenchmark
% 1.77/0.62  % (21193)------------------------------
% 1.77/0.62  % (21193)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.77/0.62  % (21193)Termination reason: Refutation
% 1.77/0.62  
% 1.77/0.62  % (21193)Memory used [KB]: 6652
% 1.77/0.62  % (21193)Time elapsed: 0.127 s
% 1.77/0.62  % (21193)------------------------------
% 1.77/0.62  % (21193)------------------------------
% 1.77/0.62  % (21204)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.77/0.63  % (21215)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.77/0.63  % (21185)Success in time 0.268 s
%------------------------------------------------------------------------------
