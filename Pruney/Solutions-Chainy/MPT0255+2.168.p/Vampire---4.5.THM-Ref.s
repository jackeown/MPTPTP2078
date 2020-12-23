%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:55 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 145 expanded)
%              Number of leaves         :   15 (  43 expanded)
%              Depth                    :   18
%              Number of atoms          :   69 ( 172 expanded)
%              Number of equality atoms :   61 ( 135 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f115,plain,(
    $false ),
    inference(subsumption_resolution,[],[f112,f82])).

fof(f82,plain,(
    ! [X1] : k1_xboole_0 != k1_tarski(X1) ),
    inference(backward_demodulation,[],[f60,f81])).

fof(f81,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f80,f37])).

fof(f37,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f80,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f46,f41])).

fof(f41,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f60,plain,(
    ! [X1] : k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f112,plain,(
    k1_xboole_0 = k1_tarski(k1_xboole_0) ),
    inference(superposition,[],[f108,f39])).

fof(f39,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f108,plain,(
    k1_xboole_0 = k2_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f76,f105])).

fof(f105,plain,(
    k1_xboole_0 = sK1 ),
    inference(backward_demodulation,[],[f97,f103])).

fof(f103,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1) ),
    inference(forward_demodulation,[],[f100,f36])).

fof(f36,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f100,plain,(
    ! [X1] : k3_xboole_0(k1_xboole_0,X1) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f91,f46])).

fof(f91,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f90,f41])).

fof(f90,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f83,f42])).

fof(f42,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f83,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(X0,X0)) ),
    inference(superposition,[],[f47,f37])).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f97,plain,(
    sK1 = k3_xboole_0(k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f96,f38])).

fof(f38,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f96,plain,(
    k3_xboole_0(k1_xboole_0,sK1) = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f89,f91])).

fof(f89,plain,(
    k3_xboole_0(k1_xboole_0,sK1) = k5_xboole_0(k5_xboole_0(k1_xboole_0,sK1),k1_xboole_0) ),
    inference(superposition,[],[f47,f75])).

fof(f75,plain,(
    k1_xboole_0 = k2_xboole_0(k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f71,f73])).

fof(f73,plain,(
    k1_xboole_0 = sK0 ),
    inference(resolution,[],[f72,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f4])).

% (2557)Refutation not found, incomplete strategy% (2557)------------------------------
% (2557)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (2586)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% (2572)Refutation not found, incomplete strategy% (2572)------------------------------
% (2572)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (2557)Termination reason: Refutation not found, incomplete strategy

% (2557)Memory used [KB]: 1663
% (2557)Time elapsed: 0.109 s
% (2557)------------------------------
% (2557)------------------------------
% (2572)Termination reason: Refutation not found, incomplete strategy

% (2572)Memory used [KB]: 6140
% (2572)Time elapsed: 0.003 s
% (2572)------------------------------
% (2572)------------------------------
% (2578)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% (2577)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% (2587)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% (2576)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% (2567)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% (2571)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% (2567)Refutation not found, incomplete strategy% (2567)------------------------------
% (2567)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (2567)Termination reason: Refutation not found, incomplete strategy

% (2567)Memory used [KB]: 10618
% (2579)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% (2567)Time elapsed: 0.133 s
% (2567)------------------------------
% (2567)------------------------------
% (2559)Refutation not found, incomplete strategy% (2559)------------------------------
% (2559)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (2559)Termination reason: Refutation not found, incomplete strategy

% (2559)Memory used [KB]: 10746
% (2559)Time elapsed: 0.132 s
% (2559)------------------------------
% (2559)------------------------------
fof(f4,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f72,plain,(
    r1_tarski(sK0,k1_xboole_0) ),
    inference(superposition,[],[f43,f71])).

fof(f43,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f71,plain,(
    k1_xboole_0 = k2_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f69,f35])).

fof(f35,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(f69,plain,(
    k3_tarski(k1_xboole_0) = k2_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f44,f64])).

fof(f64,plain,(
    k1_xboole_0 = k2_tarski(sK0,sK1) ),
    inference(resolution,[],[f63,f40])).

fof(f63,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k1_xboole_0) ),
    inference(superposition,[],[f43,f34])).

fof(f34,plain,(
    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f31])).

fof(f31,plain,
    ( ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2)
   => k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f76,plain,(
    k1_xboole_0 = k2_tarski(k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f64,f73])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:02:35 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.51  % (2558)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (2559)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (2568)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (2568)Refutation not found, incomplete strategy% (2568)------------------------------
% 0.20/0.52  % (2568)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (2568)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (2568)Memory used [KB]: 10618
% 0.20/0.52  % (2568)Time elapsed: 0.105 s
% 0.20/0.52  % (2568)------------------------------
% 0.20/0.52  % (2568)------------------------------
% 0.20/0.52  % (2566)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.53  % (2566)Refutation not found, incomplete strategy% (2566)------------------------------
% 0.20/0.53  % (2566)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (2566)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (2566)Memory used [KB]: 10618
% 0.20/0.53  % (2566)Time elapsed: 0.110 s
% 0.20/0.53  % (2566)------------------------------
% 0.20/0.53  % (2566)------------------------------
% 0.20/0.53  % (2580)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.53  % (2560)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (2563)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (2557)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.54  % (2562)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.54  % (2572)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.54  % (2561)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.54  % (2561)Refutation not found, incomplete strategy% (2561)------------------------------
% 0.20/0.54  % (2561)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (2561)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (2561)Memory used [KB]: 6140
% 0.20/0.54  % (2561)Time elapsed: 0.124 s
% 0.20/0.54  % (2561)------------------------------
% 0.20/0.54  % (2561)------------------------------
% 0.20/0.54  % (2565)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.54  % (2564)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.54  % (2573)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.54  % (2565)Refutation not found, incomplete strategy% (2565)------------------------------
% 0.20/0.54  % (2565)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (2565)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (2565)Memory used [KB]: 10746
% 0.20/0.54  % (2565)Time elapsed: 0.122 s
% 0.20/0.54  % (2565)------------------------------
% 0.20/0.54  % (2565)------------------------------
% 0.20/0.54  % (2564)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  fof(f115,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(subsumption_resolution,[],[f112,f82])).
% 0.20/0.54  fof(f82,plain,(
% 0.20/0.54    ( ! [X1] : (k1_xboole_0 != k1_tarski(X1)) )),
% 0.20/0.54    inference(backward_demodulation,[],[f60,f81])).
% 0.20/0.54  fof(f81,plain,(
% 0.20/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.20/0.54    inference(forward_demodulation,[],[f80,f37])).
% 0.20/0.54  fof(f37,plain,(
% 0.20/0.54    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f9])).
% 0.20/0.54  fof(f9,axiom,(
% 0.20/0.54    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.20/0.54  fof(f80,plain,(
% 0.20/0.54    ( ! [X0] : (k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0)) )),
% 0.20/0.54    inference(superposition,[],[f46,f41])).
% 0.20/0.54  fof(f41,plain,(
% 0.20/0.54    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.20/0.54    inference(cnf_transformation,[],[f27])).
% 0.20/0.54  fof(f27,plain,(
% 0.20/0.54    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.20/0.54    inference(rectify,[],[f2])).
% 0.20/0.54  fof(f2,axiom,(
% 0.20/0.54    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.20/0.54  fof(f46,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f3])).
% 0.20/0.54  fof(f3,axiom,(
% 0.20/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.54  fof(f60,plain,(
% 0.20/0.54    ( ! [X1] : (k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1))) )),
% 0.20/0.54    inference(equality_resolution,[],[f48])).
% 0.20/0.54  fof(f48,plain,(
% 0.20/0.54    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f33])).
% 0.20/0.54  fof(f33,plain,(
% 0.20/0.54    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 0.20/0.54    inference(nnf_transformation,[],[f23])).
% 0.20/0.54  fof(f23,axiom,(
% 0.20/0.54    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.20/0.54  fof(f112,plain,(
% 0.20/0.54    k1_xboole_0 = k1_tarski(k1_xboole_0)),
% 0.20/0.54    inference(superposition,[],[f108,f39])).
% 0.20/0.54  fof(f39,plain,(
% 0.20/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f15])).
% 0.20/0.54  fof(f15,axiom,(
% 0.20/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.54  fof(f108,plain,(
% 0.20/0.54    k1_xboole_0 = k2_tarski(k1_xboole_0,k1_xboole_0)),
% 0.20/0.54    inference(backward_demodulation,[],[f76,f105])).
% 0.20/0.54  fof(f105,plain,(
% 0.20/0.54    k1_xboole_0 = sK1),
% 0.20/0.54    inference(backward_demodulation,[],[f97,f103])).
% 0.20/0.54  fof(f103,plain,(
% 0.20/0.54    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1)) )),
% 0.20/0.54    inference(forward_demodulation,[],[f100,f36])).
% 0.20/0.54  fof(f36,plain,(
% 0.20/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f5])).
% 0.20/0.54  fof(f5,axiom,(
% 0.20/0.54    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 0.20/0.54  fof(f100,plain,(
% 0.20/0.54    ( ! [X1] : (k3_xboole_0(k1_xboole_0,X1) = k4_xboole_0(k1_xboole_0,X1)) )),
% 0.20/0.54    inference(superposition,[],[f91,f46])).
% 0.20/0.54  fof(f91,plain,(
% 0.20/0.54    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.20/0.54    inference(forward_demodulation,[],[f90,f41])).
% 0.20/0.54  fof(f90,plain,(
% 0.20/0.54    ( ! [X0] : (k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 0.20/0.54    inference(forward_demodulation,[],[f83,f42])).
% 0.20/0.54  fof(f42,plain,(
% 0.20/0.54    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.20/0.54    inference(cnf_transformation,[],[f28])).
% 0.20/0.54  fof(f28,plain,(
% 0.20/0.54    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.20/0.54    inference(rectify,[],[f1])).
% 0.20/0.54  fof(f1,axiom,(
% 0.20/0.54    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.20/0.54  fof(f83,plain,(
% 0.20/0.54    ( ! [X0] : (k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(X0,X0))) )),
% 0.20/0.54    inference(superposition,[],[f47,f37])).
% 0.20/0.54  fof(f47,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f10])).
% 0.20/0.54  fof(f10,axiom,(
% 0.20/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 0.20/0.54  fof(f97,plain,(
% 0.20/0.54    sK1 = k3_xboole_0(k1_xboole_0,sK1)),
% 0.20/0.54    inference(forward_demodulation,[],[f96,f38])).
% 0.20/0.54  fof(f38,plain,(
% 0.20/0.54    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.54    inference(cnf_transformation,[],[f6])).
% 0.20/0.54  fof(f6,axiom,(
% 0.20/0.54    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.20/0.54  fof(f96,plain,(
% 0.20/0.54    k3_xboole_0(k1_xboole_0,sK1) = k5_xboole_0(sK1,k1_xboole_0)),
% 0.20/0.54    inference(forward_demodulation,[],[f89,f91])).
% 0.20/0.54  fof(f89,plain,(
% 0.20/0.54    k3_xboole_0(k1_xboole_0,sK1) = k5_xboole_0(k5_xboole_0(k1_xboole_0,sK1),k1_xboole_0)),
% 0.20/0.54    inference(superposition,[],[f47,f75])).
% 0.20/0.54  fof(f75,plain,(
% 0.20/0.54    k1_xboole_0 = k2_xboole_0(k1_xboole_0,sK1)),
% 0.20/0.54    inference(backward_demodulation,[],[f71,f73])).
% 0.20/0.54  fof(f73,plain,(
% 0.20/0.54    k1_xboole_0 = sK0),
% 0.20/0.54    inference(resolution,[],[f72,f40])).
% 0.20/0.54  fof(f40,plain,(
% 0.20/0.54    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.20/0.54    inference(cnf_transformation,[],[f30])).
% 0.20/0.54  fof(f30,plain,(
% 0.20/0.54    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.20/0.54    inference(ennf_transformation,[],[f4])).
% 0.20/0.54  % (2557)Refutation not found, incomplete strategy% (2557)------------------------------
% 0.20/0.54  % (2557)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (2586)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (2572)Refutation not found, incomplete strategy% (2572)------------------------------
% 0.20/0.54  % (2572)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (2557)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (2557)Memory used [KB]: 1663
% 0.20/0.54  % (2557)Time elapsed: 0.109 s
% 0.20/0.54  % (2557)------------------------------
% 0.20/0.54  % (2557)------------------------------
% 0.20/0.54  % (2572)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (2572)Memory used [KB]: 6140
% 0.20/0.54  % (2572)Time elapsed: 0.003 s
% 0.20/0.55  % (2572)------------------------------
% 0.20/0.55  % (2572)------------------------------
% 0.20/0.55  % (2578)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.55  % (2577)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.44/0.55  % (2587)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.44/0.55  % (2576)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.44/0.55  % (2567)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.44/0.55  % (2571)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.44/0.55  % (2567)Refutation not found, incomplete strategy% (2567)------------------------------
% 1.44/0.55  % (2567)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.55  % (2567)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.55  
% 1.44/0.55  % (2567)Memory used [KB]: 10618
% 1.44/0.55  % (2579)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.44/0.55  % (2567)Time elapsed: 0.133 s
% 1.44/0.55  % (2567)------------------------------
% 1.44/0.55  % (2567)------------------------------
% 1.44/0.55  % (2559)Refutation not found, incomplete strategy% (2559)------------------------------
% 1.44/0.55  % (2559)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.55  % (2559)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.55  
% 1.44/0.55  % (2559)Memory used [KB]: 10746
% 1.44/0.55  % (2559)Time elapsed: 0.132 s
% 1.44/0.55  % (2559)------------------------------
% 1.44/0.55  % (2559)------------------------------
% 1.44/0.55  fof(f4,axiom,(
% 1.44/0.55    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 1.44/0.55  fof(f72,plain,(
% 1.44/0.55    r1_tarski(sK0,k1_xboole_0)),
% 1.44/0.55    inference(superposition,[],[f43,f71])).
% 1.44/0.55  fof(f43,plain,(
% 1.44/0.55    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.44/0.55    inference(cnf_transformation,[],[f7])).
% 1.44/0.55  fof(f7,axiom,(
% 1.44/0.55    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.44/0.55  fof(f71,plain,(
% 1.44/0.55    k1_xboole_0 = k2_xboole_0(sK0,sK1)),
% 1.44/0.55    inference(forward_demodulation,[],[f69,f35])).
% 1.44/0.55  fof(f35,plain,(
% 1.44/0.55    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 1.44/0.55    inference(cnf_transformation,[],[f24])).
% 1.44/0.55  fof(f24,axiom,(
% 1.44/0.55    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).
% 1.44/0.55  fof(f69,plain,(
% 1.44/0.55    k3_tarski(k1_xboole_0) = k2_xboole_0(sK0,sK1)),
% 1.44/0.55    inference(superposition,[],[f44,f64])).
% 1.44/0.55  fof(f64,plain,(
% 1.44/0.55    k1_xboole_0 = k2_tarski(sK0,sK1)),
% 1.44/0.55    inference(resolution,[],[f63,f40])).
% 1.44/0.55  fof(f63,plain,(
% 1.44/0.55    r1_tarski(k2_tarski(sK0,sK1),k1_xboole_0)),
% 1.44/0.55    inference(superposition,[],[f43,f34])).
% 1.44/0.55  fof(f34,plain,(
% 1.44/0.55    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.44/0.55    inference(cnf_transformation,[],[f32])).
% 1.44/0.55  fof(f32,plain,(
% 1.44/0.55    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.44/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f31])).
% 1.44/0.55  fof(f31,plain,(
% 1.44/0.55    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2) => k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.44/0.55    introduced(choice_axiom,[])).
% 1.44/0.55  fof(f29,plain,(
% 1.44/0.55    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2)),
% 1.44/0.55    inference(ennf_transformation,[],[f26])).
% 1.44/0.55  fof(f26,negated_conjecture,(
% 1.44/0.55    ~! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 1.44/0.55    inference(negated_conjecture,[],[f25])).
% 1.44/0.55  fof(f25,conjecture,(
% 1.44/0.55    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).
% 1.44/0.55  fof(f44,plain,(
% 1.44/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.44/0.55    inference(cnf_transformation,[],[f22])).
% 1.44/0.55  fof(f22,axiom,(
% 1.44/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.44/0.55  fof(f76,plain,(
% 1.44/0.55    k1_xboole_0 = k2_tarski(k1_xboole_0,sK1)),
% 1.44/0.55    inference(backward_demodulation,[],[f64,f73])).
% 1.44/0.55  % SZS output end Proof for theBenchmark
% 1.44/0.55  % (2564)------------------------------
% 1.44/0.55  % (2564)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.55  % (2564)Termination reason: Refutation
% 1.44/0.55  
% 1.44/0.55  % (2564)Memory used [KB]: 6268
% 1.44/0.55  % (2564)Time elapsed: 0.091 s
% 1.44/0.55  % (2564)------------------------------
% 1.44/0.55  % (2564)------------------------------
% 1.44/0.55  % (2555)Success in time 0.183 s
%------------------------------------------------------------------------------
