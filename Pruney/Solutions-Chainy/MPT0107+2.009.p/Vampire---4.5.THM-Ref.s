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
% DateTime   : Thu Dec  3 12:32:10 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   47 (  85 expanded)
%              Number of leaves         :   12 (  28 expanded)
%              Depth                    :   14
%              Number of atoms          :   48 (  86 expanded)
%              Number of equality atoms :   47 (  85 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f593,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f592])).

fof(f592,plain,(
    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f589,f83])).

fof(f83,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f66,f52])).

fof(f52,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f29,f26])).

fof(f26,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f29,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f66,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f38,f25])).

fof(f25,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f38,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f589,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(backward_demodulation,[],[f41,f577])).

fof(f577,plain,(
    ! [X10,X9] : k4_xboole_0(X9,k4_xboole_0(X9,X10)) = k5_xboole_0(X9,k4_xboole_0(X9,X10)) ),
    inference(forward_demodulation,[],[f567,f29])).

fof(f567,plain,(
    ! [X10,X9] : k5_xboole_0(k4_xboole_0(X9,X10),X9) = k4_xboole_0(X9,k4_xboole_0(X9,X10)) ),
    inference(superposition,[],[f97,f544])).

fof(f544,plain,(
    ! [X0,X1] : k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(backward_demodulation,[],[f46,f526])).

fof(f526,plain,(
    ! [X4,X5] : k4_xboole_0(X4,X5) = k4_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X4,k4_xboole_0(X4,X5))) ),
    inference(superposition,[],[f377,f44])).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f32,f30])).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f377,plain,(
    ! [X4,X3] : k4_xboole_0(X4,X3) = k4_xboole_0(k4_xboole_0(X4,X3),X3) ),
    inference(forward_demodulation,[],[f350,f26])).

fof(f350,plain,(
    ! [X4,X3] : k4_xboole_0(k4_xboole_0(X4,X3),X3) = k4_xboole_0(X4,k5_xboole_0(X3,k1_xboole_0)) ),
    inference(superposition,[],[f49,f111])).

fof(f111,plain,(
    ! [X7] : k1_xboole_0 = k4_xboole_0(X7,X7) ),
    inference(forward_demodulation,[],[f99,f25])).

fof(f99,plain,(
    ! [X7] : k4_xboole_0(X7,X7) = k5_xboole_0(X7,X7) ),
    inference(superposition,[],[f83,f42])).

fof(f42,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f27,f31])).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f27,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f49,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(definition_unfolding,[],[f39,f31])).

fof(f39,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f46,plain,(
    ! [X0,X1] : k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = X0 ),
    inference(definition_unfolding,[],[f34,f31,f30])).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f97,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f83,f29])).

fof(f41,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f24,f30])).

fof(f24,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f22])).

fof(f22,plain,
    ( ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1))
   => k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:35:05 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.50  % (4375)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.50  % (4365)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.50  % (4368)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.51  % (4362)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (4375)Refutation not found, incomplete strategy% (4375)------------------------------
% 0.20/0.51  % (4375)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (4375)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (4375)Memory used [KB]: 10618
% 0.20/0.51  % (4375)Time elapsed: 0.102 s
% 0.20/0.51  % (4375)------------------------------
% 0.20/0.51  % (4375)------------------------------
% 0.20/0.51  % (4366)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.52  % (4361)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % (4364)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (4358)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (4358)Refutation not found, incomplete strategy% (4358)------------------------------
% 0.20/0.52  % (4358)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (4358)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (4358)Memory used [KB]: 1663
% 0.20/0.52  % (4358)Time elapsed: 0.113 s
% 0.20/0.52  % (4358)------------------------------
% 0.20/0.52  % (4358)------------------------------
% 0.20/0.52  % (4383)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.52  % (4369)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (4376)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.53  % (4378)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.53  % (4370)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (4380)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (4382)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.53  % (4378)Refutation not found, incomplete strategy% (4378)------------------------------
% 0.20/0.53  % (4378)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (4378)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (4378)Memory used [KB]: 10618
% 0.20/0.53  % (4378)Time elapsed: 0.128 s
% 0.20/0.53  % (4378)------------------------------
% 0.20/0.53  % (4378)------------------------------
% 0.20/0.53  % (4385)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.53  % (4380)Refutation not found, incomplete strategy% (4380)------------------------------
% 0.20/0.53  % (4380)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (4380)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (4380)Memory used [KB]: 10618
% 0.20/0.53  % (4380)Time elapsed: 0.091 s
% 0.20/0.53  % (4380)------------------------------
% 0.20/0.53  % (4380)------------------------------
% 0.20/0.53  % (4363)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  % (4372)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (4360)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (4360)Refutation not found, incomplete strategy% (4360)------------------------------
% 0.20/0.53  % (4360)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (4360)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (4360)Memory used [KB]: 10618
% 0.20/0.53  % (4360)Time elapsed: 0.125 s
% 0.20/0.53  % (4360)------------------------------
% 0.20/0.53  % (4360)------------------------------
% 0.20/0.53  % (4384)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.53  % (4359)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.54  % (4374)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.54  % (4366)Refutation not found, incomplete strategy% (4366)------------------------------
% 0.20/0.54  % (4366)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (4366)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (4366)Memory used [KB]: 10618
% 0.20/0.54  % (4366)Time elapsed: 0.124 s
% 0.20/0.54  % (4366)------------------------------
% 0.20/0.54  % (4366)------------------------------
% 0.20/0.54  % (4371)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.54  % (4381)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.54  % (4381)Refutation not found, incomplete strategy% (4381)------------------------------
% 0.20/0.54  % (4381)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (4381)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (4381)Memory used [KB]: 1663
% 0.20/0.54  % (4381)Time elapsed: 0.140 s
% 0.20/0.54  % (4381)------------------------------
% 0.20/0.54  % (4381)------------------------------
% 0.20/0.54  % (4367)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.54  % (4379)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.54  % (4387)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  % (4373)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.54  % (4379)Refutation not found, incomplete strategy% (4379)------------------------------
% 0.20/0.54  % (4379)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (4379)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (4379)Memory used [KB]: 1663
% 0.20/0.54  % (4379)Time elapsed: 0.140 s
% 0.20/0.54  % (4379)------------------------------
% 0.20/0.54  % (4379)------------------------------
% 0.20/0.54  % (4377)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.55  % (4386)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.57  % (4370)Refutation found. Thanks to Tanya!
% 0.20/0.57  % SZS status Theorem for theBenchmark
% 0.20/0.57  % SZS output start Proof for theBenchmark
% 0.20/0.57  fof(f593,plain,(
% 0.20/0.57    $false),
% 0.20/0.57    inference(trivial_inequality_removal,[],[f592])).
% 0.20/0.57  fof(f592,plain,(
% 0.20/0.57    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,sK1)),
% 0.20/0.57    inference(superposition,[],[f589,f83])).
% 0.20/0.57  fof(f83,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 0.20/0.57    inference(forward_demodulation,[],[f66,f52])).
% 0.20/0.57  fof(f52,plain,(
% 0.20/0.57    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 0.20/0.57    inference(superposition,[],[f29,f26])).
% 0.20/0.57  fof(f26,plain,(
% 0.20/0.57    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.57    inference(cnf_transformation,[],[f12])).
% 0.20/0.57  fof(f12,axiom,(
% 0.20/0.57    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.20/0.57  fof(f29,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f2])).
% 0.20/0.57  fof(f2,axiom,(
% 0.20/0.57    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 0.20/0.57  fof(f66,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 0.20/0.57    inference(superposition,[],[f38,f25])).
% 0.20/0.57  fof(f25,plain,(
% 0.20/0.57    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f14])).
% 0.20/0.57  fof(f14,axiom,(
% 0.20/0.57    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.20/0.57  fof(f38,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f13])).
% 0.20/0.57  fof(f13,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.20/0.57  fof(f589,plain,(
% 0.20/0.57    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 0.20/0.57    inference(backward_demodulation,[],[f41,f577])).
% 0.20/0.57  fof(f577,plain,(
% 0.20/0.57    ( ! [X10,X9] : (k4_xboole_0(X9,k4_xboole_0(X9,X10)) = k5_xboole_0(X9,k4_xboole_0(X9,X10))) )),
% 0.20/0.57    inference(forward_demodulation,[],[f567,f29])).
% 0.20/0.57  fof(f567,plain,(
% 0.20/0.57    ( ! [X10,X9] : (k5_xboole_0(k4_xboole_0(X9,X10),X9) = k4_xboole_0(X9,k4_xboole_0(X9,X10))) )),
% 0.20/0.57    inference(superposition,[],[f97,f544])).
% 0.20/0.57  fof(f544,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 0.20/0.57    inference(backward_demodulation,[],[f46,f526])).
% 0.20/0.57  fof(f526,plain,(
% 0.20/0.57    ( ! [X4,X5] : (k4_xboole_0(X4,X5) = k4_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X4,k4_xboole_0(X4,X5)))) )),
% 0.20/0.57    inference(superposition,[],[f377,f44])).
% 0.20/0.57  fof(f44,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.20/0.57    inference(definition_unfolding,[],[f32,f30])).
% 0.20/0.57  fof(f30,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f8])).
% 0.20/0.57  fof(f8,axiom,(
% 0.20/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.57  fof(f32,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f7])).
% 0.20/0.57  fof(f7,axiom,(
% 0.20/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.20/0.57  fof(f377,plain,(
% 0.20/0.57    ( ! [X4,X3] : (k4_xboole_0(X4,X3) = k4_xboole_0(k4_xboole_0(X4,X3),X3)) )),
% 0.20/0.57    inference(forward_demodulation,[],[f350,f26])).
% 0.20/0.57  fof(f350,plain,(
% 0.20/0.57    ( ! [X4,X3] : (k4_xboole_0(k4_xboole_0(X4,X3),X3) = k4_xboole_0(X4,k5_xboole_0(X3,k1_xboole_0))) )),
% 0.20/0.57    inference(superposition,[],[f49,f111])).
% 0.20/0.57  fof(f111,plain,(
% 0.20/0.57    ( ! [X7] : (k1_xboole_0 = k4_xboole_0(X7,X7)) )),
% 0.20/0.57    inference(forward_demodulation,[],[f99,f25])).
% 0.20/0.57  fof(f99,plain,(
% 0.20/0.57    ( ! [X7] : (k4_xboole_0(X7,X7) = k5_xboole_0(X7,X7)) )),
% 0.20/0.57    inference(superposition,[],[f83,f42])).
% 0.20/0.57  fof(f42,plain,(
% 0.20/0.57    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 0.20/0.57    inference(definition_unfolding,[],[f27,f31])).
% 0.20/0.57  fof(f31,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f16])).
% 0.20/0.57  fof(f16,axiom,(
% 0.20/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.20/0.57  fof(f27,plain,(
% 0.20/0.57    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.20/0.57    inference(cnf_transformation,[],[f19])).
% 0.20/0.57  fof(f19,plain,(
% 0.20/0.57    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.20/0.57    inference(rectify,[],[f3])).
% 0.20/0.57  fof(f3,axiom,(
% 0.20/0.57    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.20/0.57  fof(f49,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) )),
% 0.20/0.57    inference(definition_unfolding,[],[f39,f31])).
% 0.20/0.57  fof(f39,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f6])).
% 0.20/0.57  fof(f6,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.20/0.57  fof(f46,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = X0) )),
% 0.20/0.57    inference(definition_unfolding,[],[f34,f31,f30])).
% 0.20/0.57  fof(f34,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.20/0.57    inference(cnf_transformation,[],[f10])).
% 0.20/0.57  fof(f10,axiom,(
% 0.20/0.57    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.20/0.57  fof(f97,plain,(
% 0.20/0.57    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 0.20/0.57    inference(superposition,[],[f83,f29])).
% 0.20/0.57  fof(f41,plain,(
% 0.20/0.57    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 0.20/0.57    inference(definition_unfolding,[],[f24,f30])).
% 0.20/0.57  fof(f24,plain,(
% 0.20/0.57    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.20/0.57    inference(cnf_transformation,[],[f23])).
% 0.20/0.57  fof(f23,plain,(
% 0.20/0.57    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.20/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f22])).
% 0.20/0.57  fof(f22,plain,(
% 0.20/0.57    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1)) => k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f20,plain,(
% 0.20/0.57    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.57    inference(ennf_transformation,[],[f18])).
% 0.20/0.57  fof(f18,negated_conjecture,(
% 0.20/0.57    ~! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.57    inference(negated_conjecture,[],[f17])).
% 0.20/0.57  fof(f17,conjecture,(
% 0.20/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.57  % SZS output end Proof for theBenchmark
% 0.20/0.57  % (4370)------------------------------
% 0.20/0.57  % (4370)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (4370)Termination reason: Refutation
% 0.20/0.57  
% 0.20/0.57  % (4370)Memory used [KB]: 6652
% 0.20/0.57  % (4370)Time elapsed: 0.175 s
% 0.20/0.57  % (4370)------------------------------
% 0.20/0.57  % (4370)------------------------------
% 1.69/0.58  % (4357)Success in time 0.218 s
%------------------------------------------------------------------------------
