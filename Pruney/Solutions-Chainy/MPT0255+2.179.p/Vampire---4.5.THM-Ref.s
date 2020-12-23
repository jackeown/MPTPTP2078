%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 143 expanded)
%              Number of leaves         :   14 (  41 expanded)
%              Depth                    :   18
%              Number of atoms          :   70 ( 176 expanded)
%              Number of equality atoms :   69 ( 175 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f109,plain,(
    $false ),
    inference(subsumption_resolution,[],[f106,f76])).

fof(f76,plain,(
    ! [X1] : k1_xboole_0 != k1_tarski(X1) ),
    inference(backward_demodulation,[],[f57,f75])).

fof(f75,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f74,f35])).

fof(f35,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f74,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f42,f39])).

fof(f39,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f42,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f57,plain,(
    ! [X1] : k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f106,plain,(
    k1_xboole_0 = k1_tarski(k1_xboole_0) ),
    inference(superposition,[],[f102,f38])).

fof(f38,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f102,plain,(
    k1_xboole_0 = k2_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f70,f99])).

fof(f99,plain,(
    k1_xboole_0 = sK1 ),
    inference(backward_demodulation,[],[f91,f97])).

fof(f97,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1) ),
    inference(forward_demodulation,[],[f94,f34])).

fof(f34,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f94,plain,(
    ! [X1] : k3_xboole_0(k1_xboole_0,X1) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f85,f42])).

fof(f85,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f84,f39])).

fof(f84,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f77,f59])).

fof(f59,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(forward_demodulation,[],[f58,f36])).

fof(f36,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

fof(f58,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = k2_xboole_0(X0,X0) ),
    inference(superposition,[],[f40,f38])).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f77,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(X0,X0)) ),
    inference(superposition,[],[f43,f35])).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f91,plain,(
    sK1 = k3_xboole_0(k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f90,f37])).

fof(f37,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f90,plain,(
    k3_xboole_0(k1_xboole_0,sK1) = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f83,f85])).

fof(f83,plain,(
    k3_xboole_0(k1_xboole_0,sK1) = k5_xboole_0(k5_xboole_0(k1_xboole_0,sK1),k1_xboole_0) ),
    inference(superposition,[],[f43,f69])).

fof(f69,plain,(
    k1_xboole_0 = k2_xboole_0(k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f66,f68])).

fof(f68,plain,(
    k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f67])).

fof(f67,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f44,f66])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) != k1_xboole_0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k2_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = k1_xboole_0
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_xboole_1)).

fof(f66,plain,(
    k1_xboole_0 = k2_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f65,f33])).

fof(f33,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(f65,plain,(
    k3_tarski(k1_xboole_0) = k2_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f40,f62])).

fof(f62,plain,(
    k1_xboole_0 = k2_tarski(sK0,sK1) ),
    inference(trivial_inequality_removal,[],[f60])).

fof(f60,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_tarski(sK0,sK1) ),
    inference(superposition,[],[f44,f32])).

fof(f32,plain,(
    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f29])).

fof(f29,plain,
    ( ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2)
   => k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

fof(f70,plain,(
    k1_xboole_0 = k2_tarski(k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f62,f68])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:56:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (4254)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.51  % (4246)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.52  % (4246)Refutation not found, incomplete strategy% (4246)------------------------------
% 0.21/0.52  % (4246)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (4230)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (4225)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (4237)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (4246)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (4246)Memory used [KB]: 1791
% 0.21/0.53  % (4246)Time elapsed: 0.098 s
% 0.21/0.53  % (4246)------------------------------
% 0.21/0.53  % (4246)------------------------------
% 0.21/0.54  % (4229)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (4226)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (4228)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (4224)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (4227)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (4226)Refutation not found, incomplete strategy% (4226)------------------------------
% 0.21/0.54  % (4226)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (4226)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (4226)Memory used [KB]: 10746
% 0.21/0.54  % (4226)Time elapsed: 0.125 s
% 0.21/0.54  % (4226)------------------------------
% 0.21/0.54  % (4226)------------------------------
% 0.21/0.55  % (4224)Refutation not found, incomplete strategy% (4224)------------------------------
% 0.21/0.55  % (4224)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (4224)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (4224)Memory used [KB]: 1663
% 0.21/0.55  % (4224)Time elapsed: 0.120 s
% 0.21/0.55  % (4224)------------------------------
% 0.21/0.55  % (4224)------------------------------
% 0.21/0.55  % (4253)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (4245)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (4242)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (4232)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (4235)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.55  % (4235)Refutation not found, incomplete strategy% (4235)------------------------------
% 0.21/0.55  % (4235)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (4235)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (4235)Memory used [KB]: 10618
% 0.21/0.55  % (4235)Time elapsed: 0.138 s
% 0.21/0.55  % (4235)------------------------------
% 0.21/0.55  % (4235)------------------------------
% 0.21/0.55  % (4249)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (4250)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.56  % (4250)Refutation not found, incomplete strategy% (4250)------------------------------
% 0.21/0.56  % (4250)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (4250)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (4250)Memory used [KB]: 6396
% 0.21/0.56  % (4250)Time elapsed: 0.137 s
% 0.21/0.56  % (4250)------------------------------
% 0.21/0.56  % (4250)------------------------------
% 0.21/0.56  % (4251)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.56  % (4238)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.56  % (4252)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.56  % (4242)Refutation not found, incomplete strategy% (4242)------------------------------
% 0.21/0.56  % (4242)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (4242)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (4242)Memory used [KB]: 10618
% 0.21/0.56  % (4242)Time elapsed: 0.138 s
% 0.21/0.56  % (4242)------------------------------
% 0.21/0.56  % (4242)------------------------------
% 0.21/0.56  % (4234)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.56  % (4239)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.56  % (4241)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.56  % (4248)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.56  % (4244)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.56  % (4231)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.57  % (4247)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.57  % (4232)Refutation not found, incomplete strategy% (4232)------------------------------
% 0.21/0.57  % (4232)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (4232)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (4232)Memory used [KB]: 10746
% 0.21/0.57  % (4232)Time elapsed: 0.147 s
% 0.21/0.57  % (4232)------------------------------
% 0.21/0.57  % (4232)------------------------------
% 0.21/0.57  % (4234)Refutation not found, incomplete strategy% (4234)------------------------------
% 0.21/0.57  % (4234)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (4234)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (4234)Memory used [KB]: 10618
% 0.21/0.57  % (4234)Time elapsed: 0.147 s
% 0.21/0.57  % (4234)------------------------------
% 0.21/0.57  % (4234)------------------------------
% 0.21/0.57  % (4240)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.57  % (4240)Refutation not found, incomplete strategy% (4240)------------------------------
% 0.21/0.57  % (4240)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (4240)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (4240)Memory used [KB]: 6140
% 0.21/0.57  % (4240)Time elapsed: 0.003 s
% 0.21/0.57  % (4240)------------------------------
% 0.21/0.57  % (4240)------------------------------
% 0.21/0.57  % (4231)Refutation found. Thanks to Tanya!
% 0.21/0.57  % SZS status Theorem for theBenchmark
% 0.21/0.57  % (4243)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f109,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(subsumption_resolution,[],[f106,f76])).
% 0.21/0.57  fof(f76,plain,(
% 0.21/0.57    ( ! [X1] : (k1_xboole_0 != k1_tarski(X1)) )),
% 0.21/0.57    inference(backward_demodulation,[],[f57,f75])).
% 0.21/0.57  fof(f75,plain,(
% 0.21/0.57    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.21/0.57    inference(forward_demodulation,[],[f74,f35])).
% 0.21/0.57  fof(f35,plain,(
% 0.21/0.57    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f7])).
% 0.21/0.57  fof(f7,axiom,(
% 0.21/0.57    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.21/0.57  fof(f74,plain,(
% 0.21/0.57    ( ! [X0] : (k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0)) )),
% 0.21/0.57    inference(superposition,[],[f42,f39])).
% 0.21/0.57  fof(f39,plain,(
% 0.21/0.57    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f26])).
% 0.21/0.57  fof(f26,plain,(
% 0.21/0.57    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.21/0.57    inference(rectify,[],[f1])).
% 0.21/0.57  fof(f1,axiom,(
% 0.21/0.57    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.21/0.57  fof(f42,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f2])).
% 0.21/0.57  fof(f2,axiom,(
% 0.21/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.57  fof(f57,plain,(
% 0.21/0.57    ( ! [X1] : (k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1))) )),
% 0.21/0.57    inference(equality_resolution,[],[f45])).
% 0.21/0.57  fof(f45,plain,(
% 0.21/0.57    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f31])).
% 0.21/0.57  fof(f31,plain,(
% 0.21/0.57    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 0.21/0.57    inference(nnf_transformation,[],[f21])).
% 0.21/0.57  fof(f21,axiom,(
% 0.21/0.57    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.21/0.57  fof(f106,plain,(
% 0.21/0.57    k1_xboole_0 = k1_tarski(k1_xboole_0)),
% 0.21/0.57    inference(superposition,[],[f102,f38])).
% 0.21/0.57  fof(f38,plain,(
% 0.21/0.57    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f13])).
% 0.21/0.57  fof(f13,axiom,(
% 0.21/0.57    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.57  fof(f102,plain,(
% 0.21/0.57    k1_xboole_0 = k2_tarski(k1_xboole_0,k1_xboole_0)),
% 0.21/0.57    inference(backward_demodulation,[],[f70,f99])).
% 0.21/0.57  fof(f99,plain,(
% 0.21/0.57    k1_xboole_0 = sK1),
% 0.21/0.57    inference(backward_demodulation,[],[f91,f97])).
% 0.21/0.57  fof(f97,plain,(
% 0.21/0.57    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1)) )),
% 0.21/0.57    inference(forward_demodulation,[],[f94,f34])).
% 0.21/0.57  fof(f34,plain,(
% 0.21/0.57    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f4])).
% 0.21/0.57  fof(f4,axiom,(
% 0.21/0.57    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 0.21/0.57  fof(f94,plain,(
% 0.21/0.57    ( ! [X1] : (k3_xboole_0(k1_xboole_0,X1) = k4_xboole_0(k1_xboole_0,X1)) )),
% 0.21/0.57    inference(superposition,[],[f85,f42])).
% 0.21/0.57  fof(f85,plain,(
% 0.21/0.57    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.21/0.57    inference(forward_demodulation,[],[f84,f39])).
% 0.21/0.57  fof(f84,plain,(
% 0.21/0.57    ( ! [X0] : (k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.57    inference(forward_demodulation,[],[f77,f59])).
% 0.21/0.57  fof(f59,plain,(
% 0.21/0.57    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.21/0.57    inference(forward_demodulation,[],[f58,f36])).
% 0.21/0.57  fof(f36,plain,(
% 0.21/0.57    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f23])).
% 0.21/0.57  fof(f23,axiom,(
% 0.21/0.57    ! [X0] : k3_tarski(k1_tarski(X0)) = X0),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).
% 0.21/0.57  fof(f58,plain,(
% 0.21/0.57    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = k2_xboole_0(X0,X0)) )),
% 0.21/0.57    inference(superposition,[],[f40,f38])).
% 0.21/0.57  fof(f40,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f20])).
% 0.21/0.57  fof(f20,axiom,(
% 0.21/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.57  fof(f77,plain,(
% 0.21/0.57    ( ! [X0] : (k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(X0,X0))) )),
% 0.21/0.57    inference(superposition,[],[f43,f35])).
% 0.21/0.57  fof(f43,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f8])).
% 0.21/0.57  fof(f8,axiom,(
% 0.21/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 0.21/0.57  fof(f91,plain,(
% 0.21/0.57    sK1 = k3_xboole_0(k1_xboole_0,sK1)),
% 0.21/0.57    inference(forward_demodulation,[],[f90,f37])).
% 0.21/0.57  fof(f37,plain,(
% 0.21/0.57    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f5])).
% 0.21/0.57  fof(f5,axiom,(
% 0.21/0.57    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.21/0.57  fof(f90,plain,(
% 0.21/0.57    k3_xboole_0(k1_xboole_0,sK1) = k5_xboole_0(sK1,k1_xboole_0)),
% 0.21/0.57    inference(forward_demodulation,[],[f83,f85])).
% 0.21/0.57  fof(f83,plain,(
% 0.21/0.57    k3_xboole_0(k1_xboole_0,sK1) = k5_xboole_0(k5_xboole_0(k1_xboole_0,sK1),k1_xboole_0)),
% 0.21/0.57    inference(superposition,[],[f43,f69])).
% 0.21/0.57  fof(f69,plain,(
% 0.21/0.57    k1_xboole_0 = k2_xboole_0(k1_xboole_0,sK1)),
% 0.21/0.57    inference(backward_demodulation,[],[f66,f68])).
% 0.21/0.57  fof(f68,plain,(
% 0.21/0.57    k1_xboole_0 = sK0),
% 0.21/0.57    inference(trivial_inequality_removal,[],[f67])).
% 0.21/0.57  fof(f67,plain,(
% 0.21/0.57    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0),
% 0.21/0.57    inference(superposition,[],[f44,f66])).
% 0.21/0.57  fof(f44,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) != k1_xboole_0 | k1_xboole_0 = X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f28])).
% 0.21/0.57  fof(f28,plain,(
% 0.21/0.57    ! [X0,X1] : (k1_xboole_0 = X0 | k2_xboole_0(X0,X1) != k1_xboole_0)),
% 0.21/0.57    inference(ennf_transformation,[],[f3])).
% 0.21/0.57  fof(f3,axiom,(
% 0.21/0.57    ! [X0,X1] : (k2_xboole_0(X0,X1) = k1_xboole_0 => k1_xboole_0 = X0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_xboole_1)).
% 0.21/0.57  fof(f66,plain,(
% 0.21/0.57    k1_xboole_0 = k2_xboole_0(sK0,sK1)),
% 0.21/0.57    inference(forward_demodulation,[],[f65,f33])).
% 0.21/0.57  fof(f33,plain,(
% 0.21/0.57    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.21/0.57    inference(cnf_transformation,[],[f22])).
% 0.21/0.58  fof(f22,axiom,(
% 0.21/0.58    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).
% 0.21/0.58  fof(f65,plain,(
% 0.21/0.58    k3_tarski(k1_xboole_0) = k2_xboole_0(sK0,sK1)),
% 0.21/0.58    inference(superposition,[],[f40,f62])).
% 0.21/0.58  fof(f62,plain,(
% 0.21/0.58    k1_xboole_0 = k2_tarski(sK0,sK1)),
% 0.21/0.58    inference(trivial_inequality_removal,[],[f60])).
% 0.21/0.58  fof(f60,plain,(
% 0.21/0.58    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_tarski(sK0,sK1)),
% 0.21/0.58    inference(superposition,[],[f44,f32])).
% 0.21/0.58  fof(f32,plain,(
% 0.21/0.58    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.21/0.58    inference(cnf_transformation,[],[f30])).
% 0.21/0.58  fof(f30,plain,(
% 0.21/0.58    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.21/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f29])).
% 0.21/0.58  fof(f29,plain,(
% 0.21/0.58    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2) => k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.21/0.58    introduced(choice_axiom,[])).
% 0.21/0.58  fof(f27,plain,(
% 0.21/0.58    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2)),
% 0.21/0.58    inference(ennf_transformation,[],[f25])).
% 0.21/0.58  fof(f25,negated_conjecture,(
% 0.21/0.58    ~! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 0.21/0.58    inference(negated_conjecture,[],[f24])).
% 0.21/0.58  fof(f24,conjecture,(
% 0.21/0.58    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).
% 0.21/0.58  fof(f70,plain,(
% 0.21/0.58    k1_xboole_0 = k2_tarski(k1_xboole_0,sK1)),
% 0.21/0.58    inference(backward_demodulation,[],[f62,f68])).
% 0.21/0.58  % SZS output end Proof for theBenchmark
% 0.21/0.58  % (4231)------------------------------
% 0.21/0.58  % (4231)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (4231)Termination reason: Refutation
% 0.21/0.58  
% 0.21/0.58  % (4231)Memory used [KB]: 6268
% 0.21/0.58  % (4231)Time elapsed: 0.068 s
% 0.21/0.58  % (4231)------------------------------
% 0.21/0.58  % (4231)------------------------------
% 0.21/0.58  % (4222)Success in time 0.205 s
%------------------------------------------------------------------------------
