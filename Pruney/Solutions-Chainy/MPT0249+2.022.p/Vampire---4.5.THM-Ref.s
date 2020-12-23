%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:13 EST 2020

% Result     : Theorem 1.53s
% Output     : Refutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 153 expanded)
%              Number of leaves         :   11 (  44 expanded)
%              Depth                    :   14
%              Number of atoms          :   87 ( 406 expanded)
%              Number of equality atoms :   74 ( 369 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f159,plain,(
    $false ),
    inference(subsumption_resolution,[],[f158,f30])).

fof(f30,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & sK1 != sK2
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f23])).

fof(f23,plain,
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

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & X1 != X2
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & X1 != X2
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

fof(f158,plain,(
    k1_xboole_0 = sK2 ),
    inference(backward_demodulation,[],[f141,f157])).

fof(f157,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,sK2) ),
    inference(subsumption_resolution,[],[f154,f28])).

fof(f28,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f24])).

fof(f154,plain,
    ( sK1 = sK2
    | k1_xboole_0 = k3_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f141,f109])).

fof(f109,plain,(
    ! [X0] :
      ( sK1 = k3_xboole_0(sK1,X0)
      | k1_xboole_0 = k3_xboole_0(sK1,X0) ) ),
    inference(resolution,[],[f98,f36])).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f98,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | k1_xboole_0 = X0
      | sK1 = X0 ) ),
    inference(superposition,[],[f41,f94])).

fof(f94,plain,(
    sK1 = k1_tarski(sK0) ),
    inference(subsumption_resolution,[],[f93,f29])).

fof(f29,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f24])).

fof(f93,plain,
    ( k1_xboole_0 = sK1
    | sK1 = k1_tarski(sK0) ),
    inference(resolution,[],[f41,f54])).

fof(f54,plain,(
    r1_tarski(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f35,f27])).

fof(f27,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
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
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f141,plain,(
    sK2 = k3_xboole_0(sK1,sK2) ),
    inference(backward_demodulation,[],[f102,f140])).

fof(f140,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f112,f64])).

fof(f64,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f63,f33])).

fof(f33,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f63,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f57,f34])).

fof(f34,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f57,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(X0,X0)) ),
    inference(superposition,[],[f40,f31])).

fof(f31,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f112,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f45,f31])).

fof(f45,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f102,plain,(
    k3_xboole_0(sK1,sK2) = k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f95,f37])).

fof(f37,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f95,plain,(
    k3_xboole_0(sK1,sK2) = k5_xboole_0(k5_xboole_0(sK1,sK2),sK1) ),
    inference(backward_demodulation,[],[f62,f94])).

fof(f62,plain,(
    k3_xboole_0(sK1,sK2) = k5_xboole_0(k5_xboole_0(sK1,sK2),k1_tarski(sK0)) ),
    inference(superposition,[],[f40,f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:40:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (19917)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.50  % (19909)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.51  % (19901)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (19915)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.52  % (19902)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (19906)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (19904)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (19905)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (19908)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (19898)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (19899)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (19925)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (19896)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (19916)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (19897)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.41/0.54  % (19906)Refutation not found, incomplete strategy% (19906)------------------------------
% 1.41/0.54  % (19906)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.54  % (19906)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.54  
% 1.41/0.54  % (19906)Memory used [KB]: 10618
% 1.41/0.54  % (19906)Time elapsed: 0.137 s
% 1.41/0.54  % (19906)------------------------------
% 1.41/0.54  % (19906)------------------------------
% 1.41/0.54  % (19921)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.41/0.54  % (19918)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.41/0.55  % (19913)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.41/0.55  % (19919)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.41/0.55  % (19910)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.41/0.55  % (19900)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.41/0.55  % (19922)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.41/0.55  % (19920)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.41/0.55  % (19903)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.41/0.56  % (19913)Refutation not found, incomplete strategy% (19913)------------------------------
% 1.41/0.56  % (19913)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.56  % (19907)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.53/0.56  % (19913)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.56  
% 1.53/0.56  % (19913)Memory used [KB]: 10618
% 1.53/0.56  % (19913)Time elapsed: 0.154 s
% 1.53/0.56  % (19913)------------------------------
% 1.53/0.56  % (19913)------------------------------
% 1.53/0.56  % (19903)Refutation found. Thanks to Tanya!
% 1.53/0.56  % SZS status Theorem for theBenchmark
% 1.53/0.56  % SZS output start Proof for theBenchmark
% 1.53/0.56  fof(f159,plain,(
% 1.53/0.56    $false),
% 1.53/0.56    inference(subsumption_resolution,[],[f158,f30])).
% 1.53/0.56  fof(f30,plain,(
% 1.53/0.56    k1_xboole_0 != sK2),
% 1.53/0.56    inference(cnf_transformation,[],[f24])).
% 1.53/0.56  fof(f24,plain,(
% 1.53/0.56    k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & sK1 != sK2 & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.53/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f23])).
% 1.53/0.56  fof(f23,plain,(
% 1.53/0.56    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2)) => (k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & sK1 != sK2 & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 1.53/0.56    introduced(choice_axiom,[])).
% 1.53/0.56  fof(f22,plain,(
% 1.53/0.56    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.53/0.56    inference(ennf_transformation,[],[f19])).
% 1.53/0.56  fof(f19,negated_conjecture,(
% 1.53/0.56    ~! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.53/0.56    inference(negated_conjecture,[],[f18])).
% 1.53/0.56  fof(f18,conjecture,(
% 1.53/0.56    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.53/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).
% 1.53/0.56  fof(f158,plain,(
% 1.53/0.56    k1_xboole_0 = sK2),
% 1.53/0.56    inference(backward_demodulation,[],[f141,f157])).
% 1.53/0.56  fof(f157,plain,(
% 1.53/0.56    k1_xboole_0 = k3_xboole_0(sK1,sK2)),
% 1.53/0.56    inference(subsumption_resolution,[],[f154,f28])).
% 1.53/0.56  fof(f28,plain,(
% 1.53/0.56    sK1 != sK2),
% 1.53/0.56    inference(cnf_transformation,[],[f24])).
% 1.53/0.56  fof(f154,plain,(
% 1.53/0.56    sK1 = sK2 | k1_xboole_0 = k3_xboole_0(sK1,sK2)),
% 1.53/0.56    inference(superposition,[],[f141,f109])).
% 1.53/0.56  fof(f109,plain,(
% 1.53/0.56    ( ! [X0] : (sK1 = k3_xboole_0(sK1,X0) | k1_xboole_0 = k3_xboole_0(sK1,X0)) )),
% 1.53/0.56    inference(resolution,[],[f98,f36])).
% 1.53/0.56  fof(f36,plain,(
% 1.53/0.56    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.53/0.56    inference(cnf_transformation,[],[f4])).
% 1.53/0.56  fof(f4,axiom,(
% 1.53/0.56    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.53/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.53/0.56  fof(f98,plain,(
% 1.53/0.56    ( ! [X0] : (~r1_tarski(X0,sK1) | k1_xboole_0 = X0 | sK1 = X0) )),
% 1.53/0.56    inference(superposition,[],[f41,f94])).
% 1.53/0.56  fof(f94,plain,(
% 1.53/0.56    sK1 = k1_tarski(sK0)),
% 1.53/0.56    inference(subsumption_resolution,[],[f93,f29])).
% 1.53/0.56  fof(f29,plain,(
% 1.53/0.56    k1_xboole_0 != sK1),
% 1.53/0.56    inference(cnf_transformation,[],[f24])).
% 1.53/0.56  fof(f93,plain,(
% 1.53/0.56    k1_xboole_0 = sK1 | sK1 = k1_tarski(sK0)),
% 1.53/0.56    inference(resolution,[],[f41,f54])).
% 1.53/0.56  fof(f54,plain,(
% 1.53/0.56    r1_tarski(sK1,k1_tarski(sK0))),
% 1.53/0.56    inference(superposition,[],[f35,f27])).
% 1.53/0.56  fof(f27,plain,(
% 1.53/0.56    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.53/0.56    inference(cnf_transformation,[],[f24])).
% 1.53/0.56  fof(f35,plain,(
% 1.53/0.56    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.53/0.56    inference(cnf_transformation,[],[f5])).
% 1.53/0.56  fof(f5,axiom,(
% 1.53/0.56    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.53/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.53/0.56  fof(f41,plain,(
% 1.53/0.56    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 1.53/0.56    inference(cnf_transformation,[],[f26])).
% 1.53/0.56  fof(f26,plain,(
% 1.53/0.56    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.53/0.56    inference(flattening,[],[f25])).
% 1.53/0.56  fof(f25,plain,(
% 1.53/0.56    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.53/0.56    inference(nnf_transformation,[],[f16])).
% 1.53/0.56  fof(f16,axiom,(
% 1.53/0.56    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.53/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.53/0.56  fof(f141,plain,(
% 1.53/0.56    sK2 = k3_xboole_0(sK1,sK2)),
% 1.53/0.56    inference(backward_demodulation,[],[f102,f140])).
% 1.53/0.56  fof(f140,plain,(
% 1.53/0.56    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 1.53/0.56    inference(forward_demodulation,[],[f112,f64])).
% 1.53/0.56  fof(f64,plain,(
% 1.53/0.56    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.53/0.56    inference(forward_demodulation,[],[f63,f33])).
% 1.53/0.56  fof(f33,plain,(
% 1.53/0.56    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.53/0.56    inference(cnf_transformation,[],[f20])).
% 1.53/0.56  fof(f20,plain,(
% 1.53/0.56    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.53/0.56    inference(rectify,[],[f3])).
% 1.53/0.56  fof(f3,axiom,(
% 1.53/0.56    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.53/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.53/0.56  fof(f63,plain,(
% 1.53/0.56    ( ! [X0] : (k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 1.53/0.56    inference(forward_demodulation,[],[f57,f34])).
% 1.53/0.56  fof(f34,plain,(
% 1.53/0.56    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 1.53/0.56    inference(cnf_transformation,[],[f21])).
% 1.53/0.56  fof(f21,plain,(
% 1.53/0.56    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 1.53/0.56    inference(rectify,[],[f2])).
% 1.53/0.56  fof(f2,axiom,(
% 1.53/0.56    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 1.53/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 1.53/0.56  fof(f57,plain,(
% 1.53/0.56    ( ! [X0] : (k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(X0,X0))) )),
% 1.53/0.56    inference(superposition,[],[f40,f31])).
% 1.53/0.56  fof(f31,plain,(
% 1.53/0.56    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 1.53/0.56    inference(cnf_transformation,[],[f7])).
% 1.53/0.56  fof(f7,axiom,(
% 1.53/0.56    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 1.53/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.53/0.56  fof(f40,plain,(
% 1.53/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 1.53/0.56    inference(cnf_transformation,[],[f8])).
% 1.53/0.56  fof(f8,axiom,(
% 1.53/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 1.53/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 1.53/0.56  fof(f112,plain,(
% 1.53/0.56    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 1.53/0.56    inference(superposition,[],[f45,f31])).
% 1.53/0.56  fof(f45,plain,(
% 1.53/0.56    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.53/0.56    inference(cnf_transformation,[],[f6])).
% 1.53/0.56  fof(f6,axiom,(
% 1.53/0.56    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.53/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.53/0.56  fof(f102,plain,(
% 1.53/0.56    k3_xboole_0(sK1,sK2) = k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))),
% 1.53/0.56    inference(superposition,[],[f95,f37])).
% 1.53/0.56  fof(f37,plain,(
% 1.53/0.56    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.53/0.56    inference(cnf_transformation,[],[f1])).
% 1.53/0.56  fof(f1,axiom,(
% 1.53/0.56    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.53/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.53/0.56  fof(f95,plain,(
% 1.53/0.56    k3_xboole_0(sK1,sK2) = k5_xboole_0(k5_xboole_0(sK1,sK2),sK1)),
% 1.53/0.56    inference(backward_demodulation,[],[f62,f94])).
% 1.53/0.56  fof(f62,plain,(
% 1.53/0.56    k3_xboole_0(sK1,sK2) = k5_xboole_0(k5_xboole_0(sK1,sK2),k1_tarski(sK0))),
% 1.53/0.56    inference(superposition,[],[f40,f27])).
% 1.53/0.56  % SZS output end Proof for theBenchmark
% 1.53/0.56  % (19903)------------------------------
% 1.53/0.56  % (19903)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.56  % (19903)Termination reason: Refutation
% 1.53/0.56  
% 1.53/0.56  % (19903)Memory used [KB]: 6396
% 1.53/0.56  % (19903)Time elapsed: 0.152 s
% 1.53/0.56  % (19903)------------------------------
% 1.53/0.56  % (19903)------------------------------
% 1.53/0.56  % (19895)Success in time 0.199 s
%------------------------------------------------------------------------------
