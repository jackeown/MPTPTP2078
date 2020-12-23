%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:37 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 143 expanded)
%              Number of leaves         :   16 (  43 expanded)
%              Depth                    :   11
%              Number of atoms          :   85 ( 217 expanded)
%              Number of equality atoms :   61 ( 146 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f782,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f781])).

fof(f781,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK1) != k3_enumset1(sK0,sK0,sK0,sK0,sK1) ),
    inference(superposition,[],[f740,f501])).

fof(f501,plain,(
    ! [X10,X11] : k5_xboole_0(X10,k5_xboole_0(X10,X11)) = X11 ),
    inference(backward_demodulation,[],[f78,f484])).

fof(f484,plain,(
    ! [X9] : k5_xboole_0(k1_xboole_0,X9) = X9 ),
    inference(superposition,[],[f78,f345])).

fof(f345,plain,(
    ! [X9] : k5_xboole_0(k1_xboole_0,k5_xboole_0(X9,k3_xboole_0(k1_xboole_0,X9))) = X9 ),
    inference(forward_demodulation,[],[f289,f35])).

fof(f35,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f289,plain,(
    ! [X9] : k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,X9),X9)) = X9 ),
    inference(superposition,[],[f80,f50])).

fof(f50,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(definition_unfolding,[],[f29,f45])).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f28,f34])).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f29,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f80,plain,(
    ! [X4,X5,X3] : k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X5,k5_xboole_0(X3,X4)) ),
    inference(superposition,[],[f33,f35])).

fof(f33,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f78,plain,(
    ! [X10,X11] : k5_xboole_0(X10,k5_xboole_0(X10,X11)) = k5_xboole_0(k1_xboole_0,X11) ),
    inference(superposition,[],[f33,f64])).

fof(f64,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f63,f56])).

fof(f56,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(resolution,[],[f41,f54])).

fof(f54,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f63,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0)) ),
    inference(resolution,[],[f52,f54])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f37,f34])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f740,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK1))) ),
    inference(forward_demodulation,[],[f733,f35])).

fof(f733,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    inference(backward_demodulation,[],[f120,f197])).

fof(f197,plain,(
    ! [X6,X7] : k3_enumset1(X6,X6,X6,X6,X6) = k3_xboole_0(k3_enumset1(X6,X6,X6,X6,X6),k3_enumset1(X6,X6,X6,X6,X7)) ),
    inference(resolution,[],[f51,f41])).

fof(f51,plain,(
    ! [X0,X1] : r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f30,f48,f47])).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f32,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f42,f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f42,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f32,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f48,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f31,f47])).

fof(f31,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

fof(f120,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK1)))) ),
    inference(forward_demodulation,[],[f49,f43])).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f49,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) ),
    inference(definition_unfolding,[],[f27,f47,f45,f48,f47])).

fof(f27,plain,(
    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f22])).

fof(f22,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))
   => k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:35:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (31053)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.49  % (31061)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.50  % (31041)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.51  % (31043)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.51  % (31045)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.51  % (31051)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.51  % (31042)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.51  % (31051)Refutation not found, incomplete strategy% (31051)------------------------------
% 0.20/0.51  % (31051)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (31051)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (31051)Memory used [KB]: 6140
% 0.20/0.51  % (31051)Time elapsed: 0.110 s
% 0.20/0.51  % (31051)------------------------------
% 0.20/0.51  % (31051)------------------------------
% 0.20/0.51  % (31047)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.51  % (31052)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.51  % (31052)Refutation not found, incomplete strategy% (31052)------------------------------
% 0.20/0.51  % (31052)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (31046)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (31052)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (31052)Memory used [KB]: 10618
% 0.20/0.51  % (31052)Time elapsed: 0.117 s
% 0.20/0.51  % (31052)------------------------------
% 0.20/0.51  % (31052)------------------------------
% 0.20/0.52  % (31057)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.52  % (31069)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.52  % (31069)Refutation not found, incomplete strategy% (31069)------------------------------
% 0.20/0.52  % (31069)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (31069)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (31069)Memory used [KB]: 1663
% 0.20/0.52  % (31069)Time elapsed: 0.120 s
% 0.20/0.52  % (31069)------------------------------
% 0.20/0.52  % (31069)------------------------------
% 0.20/0.52  % (31040)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.52  % (31059)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.52  % (31063)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.52  % (31049)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.52  % (31067)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.52  % (31041)Refutation not found, incomplete strategy% (31041)------------------------------
% 0.20/0.52  % (31041)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (31041)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (31041)Memory used [KB]: 1663
% 0.20/0.52  % (31041)Time elapsed: 0.127 s
% 0.20/0.52  % (31041)------------------------------
% 0.20/0.52  % (31041)------------------------------
% 0.20/0.52  % (31067)Refutation not found, incomplete strategy% (31067)------------------------------
% 0.20/0.52  % (31067)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (31062)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.53  % (31055)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.53  % (31067)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (31067)Memory used [KB]: 6140
% 0.20/0.53  % (31067)Time elapsed: 0.132 s
% 0.20/0.53  % (31067)------------------------------
% 0.20/0.53  % (31067)------------------------------
% 0.20/0.53  % (31050)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.53  % (31064)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.53  % (31060)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.53  % (31064)Refutation not found, incomplete strategy% (31064)------------------------------
% 0.20/0.53  % (31064)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (31064)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (31064)Memory used [KB]: 10618
% 0.20/0.53  % (31064)Time elapsed: 0.130 s
% 0.20/0.53  % (31064)------------------------------
% 0.20/0.53  % (31064)------------------------------
% 0.20/0.53  % (31044)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.53  % (31056)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.53  % (31048)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.53  % (31054)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.53  % (31065)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.53  % (31054)Refutation not found, incomplete strategy% (31054)------------------------------
% 0.20/0.53  % (31054)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (31054)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (31054)Memory used [KB]: 1663
% 0.20/0.53  % (31054)Time elapsed: 0.105 s
% 0.20/0.53  % (31054)------------------------------
% 0.20/0.53  % (31054)------------------------------
% 0.20/0.53  % (31056)Refutation not found, incomplete strategy% (31056)------------------------------
% 0.20/0.53  % (31056)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (31065)Refutation not found, incomplete strategy% (31065)------------------------------
% 0.20/0.53  % (31065)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (31065)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (31065)Memory used [KB]: 6140
% 0.20/0.53  % (31065)Time elapsed: 0.141 s
% 0.20/0.53  % (31065)------------------------------
% 0.20/0.53  % (31065)------------------------------
% 0.20/0.53  % (31056)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (31056)Memory used [KB]: 10618
% 0.20/0.53  % (31056)Time elapsed: 0.140 s
% 0.20/0.53  % (31056)------------------------------
% 0.20/0.53  % (31056)------------------------------
% 0.20/0.53  % (31057)Refutation not found, incomplete strategy% (31057)------------------------------
% 0.20/0.53  % (31057)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (31057)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (31057)Memory used [KB]: 1663
% 0.20/0.53  % (31057)Time elapsed: 0.142 s
% 0.20/0.53  % (31057)------------------------------
% 0.20/0.53  % (31057)------------------------------
% 0.20/0.54  % (31066)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (31068)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.54  % (31066)Refutation not found, incomplete strategy% (31066)------------------------------
% 0.20/0.54  % (31066)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (31066)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (31066)Memory used [KB]: 6140
% 0.20/0.54  % (31066)Time elapsed: 0.140 s
% 0.20/0.54  % (31066)------------------------------
% 0.20/0.54  % (31066)------------------------------
% 0.20/0.54  % (31068)Refutation not found, incomplete strategy% (31068)------------------------------
% 0.20/0.54  % (31068)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (31068)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (31068)Memory used [KB]: 10746
% 0.20/0.54  % (31068)Time elapsed: 0.143 s
% 0.20/0.54  % (31068)------------------------------
% 0.20/0.54  % (31068)------------------------------
% 0.20/0.54  % (31058)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.54  % (31058)Refutation not found, incomplete strategy% (31058)------------------------------
% 0.20/0.54  % (31058)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (31058)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (31058)Memory used [KB]: 1663
% 0.20/0.54  % (31058)Time elapsed: 0.141 s
% 0.20/0.54  % (31058)------------------------------
% 0.20/0.54  % (31058)------------------------------
% 0.20/0.54  % (31050)Refutation not found, incomplete strategy% (31050)------------------------------
% 0.20/0.54  % (31050)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (31050)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (31050)Memory used [KB]: 10746
% 0.20/0.54  % (31050)Time elapsed: 0.143 s
% 0.20/0.54  % (31050)------------------------------
% 0.20/0.54  % (31050)------------------------------
% 0.20/0.54  % (31045)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  fof(f782,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(trivial_inequality_removal,[],[f781])).
% 0.20/0.54  fof(f781,plain,(
% 0.20/0.54    k3_enumset1(sK0,sK0,sK0,sK0,sK1) != k3_enumset1(sK0,sK0,sK0,sK0,sK1)),
% 0.20/0.54    inference(superposition,[],[f740,f501])).
% 0.20/0.55  fof(f501,plain,(
% 0.20/0.55    ( ! [X10,X11] : (k5_xboole_0(X10,k5_xboole_0(X10,X11)) = X11) )),
% 0.20/0.55    inference(backward_demodulation,[],[f78,f484])).
% 0.20/0.55  fof(f484,plain,(
% 0.20/0.55    ( ! [X9] : (k5_xboole_0(k1_xboole_0,X9) = X9) )),
% 0.20/0.55    inference(superposition,[],[f78,f345])).
% 0.20/0.55  fof(f345,plain,(
% 0.20/0.55    ( ! [X9] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(X9,k3_xboole_0(k1_xboole_0,X9))) = X9) )),
% 0.20/0.55    inference(forward_demodulation,[],[f289,f35])).
% 0.20/0.55  fof(f35,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f2])).
% 0.20/0.55  fof(f2,axiom,(
% 0.20/0.55    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 0.20/0.56  fof(f289,plain,(
% 0.20/0.56    ( ! [X9] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,X9),X9)) = X9) )),
% 0.20/0.56    inference(superposition,[],[f80,f50])).
% 0.20/0.56  fof(f50,plain,(
% 0.20/0.56    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0) )),
% 0.20/0.56    inference(definition_unfolding,[],[f29,f45])).
% 0.20/0.56  fof(f45,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 0.20/0.56    inference(definition_unfolding,[],[f28,f34])).
% 0.20/0.56  fof(f34,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.56    inference(cnf_transformation,[],[f5])).
% 0.20/0.56  fof(f5,axiom,(
% 0.20/0.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.56  fof(f28,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.56    inference(cnf_transformation,[],[f9])).
% 0.20/0.56  fof(f9,axiom,(
% 0.20/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.20/0.56  fof(f29,plain,(
% 0.20/0.56    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.56    inference(cnf_transformation,[],[f6])).
% 0.20/0.56  fof(f6,axiom,(
% 0.20/0.56    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.20/0.56  fof(f80,plain,(
% 0.20/0.56    ( ! [X4,X5,X3] : (k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X5,k5_xboole_0(X3,X4))) )),
% 0.20/0.56    inference(superposition,[],[f33,f35])).
% 0.20/0.56  fof(f33,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.20/0.56    inference(cnf_transformation,[],[f8])).
% 0.20/0.56  fof(f8,axiom,(
% 0.20/0.56    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.20/0.56  fof(f78,plain,(
% 0.20/0.56    ( ! [X10,X11] : (k5_xboole_0(X10,k5_xboole_0(X10,X11)) = k5_xboole_0(k1_xboole_0,X11)) )),
% 0.20/0.56    inference(superposition,[],[f33,f64])).
% 0.20/0.56  fof(f64,plain,(
% 0.20/0.56    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.20/0.56    inference(forward_demodulation,[],[f63,f56])).
% 0.20/0.56  fof(f56,plain,(
% 0.20/0.56    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.20/0.56    inference(resolution,[],[f41,f54])).
% 0.20/0.56  fof(f54,plain,(
% 0.20/0.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.56    inference(equality_resolution,[],[f39])).
% 0.20/0.56  fof(f39,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.56    inference(cnf_transformation,[],[f26])).
% 0.20/0.56  fof(f26,plain,(
% 0.20/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.56    inference(flattening,[],[f25])).
% 0.20/0.56  fof(f25,plain,(
% 0.20/0.56    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.56    inference(nnf_transformation,[],[f3])).
% 0.20/0.56  fof(f3,axiom,(
% 0.20/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.56  fof(f41,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.20/0.56    inference(cnf_transformation,[],[f21])).
% 0.20/0.56  fof(f21,plain,(
% 0.20/0.56    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.56    inference(ennf_transformation,[],[f7])).
% 0.20/0.56  fof(f7,axiom,(
% 0.20/0.56    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.56  fof(f63,plain,(
% 0.20/0.56    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0))) )),
% 0.20/0.56    inference(resolution,[],[f52,f54])).
% 0.20/0.56  fof(f52,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.56    inference(definition_unfolding,[],[f37,f34])).
% 0.20/0.56  fof(f37,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f24])).
% 0.20/0.56  fof(f24,plain,(
% 0.20/0.56    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.20/0.56    inference(nnf_transformation,[],[f4])).
% 0.20/0.56  fof(f4,axiom,(
% 0.20/0.56    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.56  fof(f740,plain,(
% 0.20/0.56    k3_enumset1(sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK1)))),
% 0.20/0.56    inference(forward_demodulation,[],[f733,f35])).
% 0.20/0.56  fof(f733,plain,(
% 0.20/0.56    k3_enumset1(sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),
% 0.20/0.56    inference(backward_demodulation,[],[f120,f197])).
% 0.20/0.56  fof(f197,plain,(
% 0.20/0.56    ( ! [X6,X7] : (k3_enumset1(X6,X6,X6,X6,X6) = k3_xboole_0(k3_enumset1(X6,X6,X6,X6,X6),k3_enumset1(X6,X6,X6,X6,X7))) )),
% 0.20/0.56    inference(resolution,[],[f51,f41])).
% 0.20/0.56  fof(f51,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X1))) )),
% 0.20/0.56    inference(definition_unfolding,[],[f30,f48,f47])).
% 0.20/0.56  fof(f47,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.20/0.56    inference(definition_unfolding,[],[f32,f46])).
% 0.20/0.56  fof(f46,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.20/0.56    inference(definition_unfolding,[],[f42,f44])).
% 0.20/0.56  fof(f44,plain,(
% 0.20/0.56    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f13])).
% 0.20/0.56  fof(f13,axiom,(
% 0.20/0.56    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.56  fof(f42,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f12])).
% 0.20/0.56  fof(f12,axiom,(
% 0.20/0.56    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.56  fof(f32,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f11])).
% 0.20/0.56  fof(f11,axiom,(
% 0.20/0.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.56  fof(f48,plain,(
% 0.20/0.56    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.20/0.56    inference(definition_unfolding,[],[f31,f47])).
% 0.20/0.56  fof(f31,plain,(
% 0.20/0.56    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f10])).
% 0.20/0.56  fof(f10,axiom,(
% 0.20/0.56    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.56  fof(f30,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 0.20/0.56    inference(cnf_transformation,[],[f17])).
% 0.20/0.56  fof(f17,axiom,(
% 0.20/0.56    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).
% 0.20/0.56  fof(f120,plain,(
% 0.20/0.56    k3_enumset1(sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK1))))),
% 0.20/0.56    inference(forward_demodulation,[],[f49,f43])).
% 0.20/0.56  fof(f43,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f1])).
% 0.20/0.56  fof(f1,axiom,(
% 0.20/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.56  fof(f49,plain,(
% 0.20/0.56    k3_enumset1(sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),
% 0.20/0.56    inference(definition_unfolding,[],[f27,f47,f45,f48,f47])).
% 0.20/0.56  fof(f27,plain,(
% 0.20/0.56    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 0.20/0.56    inference(cnf_transformation,[],[f23])).
% 0.20/0.56  fof(f23,plain,(
% 0.20/0.56    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 0.20/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f22])).
% 0.20/0.56  fof(f22,plain,(
% 0.20/0.56    ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) => k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f20,plain,(
% 0.20/0.56    ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.20/0.56    inference(ennf_transformation,[],[f19])).
% 0.20/0.56  fof(f19,negated_conjecture,(
% 0.20/0.56    ~! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.20/0.56    inference(negated_conjecture,[],[f18])).
% 0.20/0.56  fof(f18,conjecture,(
% 0.20/0.56    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_zfmisc_1)).
% 0.20/0.56  % SZS output end Proof for theBenchmark
% 0.20/0.56  % (31045)------------------------------
% 0.20/0.56  % (31045)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (31045)Termination reason: Refutation
% 0.20/0.56  
% 0.20/0.56  % (31045)Memory used [KB]: 2174
% 0.20/0.56  % (31045)Time elapsed: 0.156 s
% 0.20/0.56  % (31045)------------------------------
% 0.20/0.56  % (31045)------------------------------
% 0.20/0.56  % (31039)Success in time 0.196 s
%------------------------------------------------------------------------------
