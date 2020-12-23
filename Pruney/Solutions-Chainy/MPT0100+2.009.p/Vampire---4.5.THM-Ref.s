%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:50 EST 2020

% Result     : Theorem 1.37s
% Output     : Refutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 103 expanded)
%              Number of leaves         :   14 (  34 expanded)
%              Depth                    :   13
%              Number of atoms          :   68 ( 115 expanded)
%              Number of equality atoms :   54 (  96 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f736,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f733])).

fof(f733,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f683,f23])).

fof(f23,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f683,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(sK0,sK1),k1_xboole_0) ),
    inference(forward_demodulation,[],[f682,f31])).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f682,plain,(
    k2_xboole_0(k2_xboole_0(sK0,sK1),k1_xboole_0) != k2_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(forward_demodulation,[],[f681,f23])).

fof(f681,plain,(
    k2_xboole_0(k2_xboole_0(sK0,sK1),k1_xboole_0) != k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f680,f361])).

fof(f361,plain,(
    ! [X10,X11,X9] : k2_xboole_0(X9,k2_xboole_0(k4_xboole_0(X9,X10),X11)) = k2_xboole_0(X9,X11) ),
    inference(superposition,[],[f34,f320])).

fof(f320,plain,(
    ! [X2,X3] : k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2 ),
    inference(superposition,[],[f40,f42])).

fof(f42,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f30,f29])).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f27,f29])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f34,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f680,plain,(
    k2_xboole_0(k2_xboole_0(sK0,sK1),k1_xboole_0) != k2_xboole_0(k2_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k1_xboole_0) ),
    inference(forward_demodulation,[],[f679,f217])).

fof(f217,plain,(
    ! [X8,X7,X9] : k2_xboole_0(X9,k2_xboole_0(X7,X8)) = k2_xboole_0(X7,k2_xboole_0(X8,X9)) ),
    inference(superposition,[],[f34,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f679,plain,(
    k2_xboole_0(k2_xboole_0(sK0,sK1),k1_xboole_0) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK1,sK0),sK0)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f620,f243])).

fof(f243,plain,(
    ! [X14,X15,X13] : k2_xboole_0(X13,k2_xboole_0(X14,X15)) = k2_xboole_0(X13,k2_xboole_0(X14,k4_xboole_0(X15,X13))) ),
    inference(forward_demodulation,[],[f242,f34])).

fof(f242,plain,(
    ! [X14,X15,X13] : k2_xboole_0(k2_xboole_0(X13,X14),X15) = k2_xboole_0(X13,k2_xboole_0(X14,k4_xboole_0(X15,X13))) ),
    inference(forward_demodulation,[],[f219,f125])).

fof(f125,plain,(
    ! [X6,X7,X5] : k2_xboole_0(X7,k4_xboole_0(X5,X6)) = k2_xboole_0(X7,k4_xboole_0(X5,k2_xboole_0(X6,X7))) ),
    inference(superposition,[],[f31,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f219,plain,(
    ! [X14,X15,X13] : k2_xboole_0(k2_xboole_0(X13,X14),X15) = k2_xboole_0(X13,k2_xboole_0(X14,k4_xboole_0(X15,k2_xboole_0(X13,X14)))) ),
    inference(superposition,[],[f34,f31])).

fof(f620,plain,(
    k2_xboole_0(k2_xboole_0(sK0,sK1),k1_xboole_0) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f222,f47,f47,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) != k2_xboole_0(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X2,X1)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( X0 = X2
      | ~ r1_xboole_0(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( X0 = X2
      | ~ r1_xboole_0(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X2,X1)
        & r1_xboole_0(X0,X1)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
     => X0 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_xboole_1)).

fof(f47,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f46,f44])).

fof(f44,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f39,f24])).

fof(f24,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f26,f29])).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f46,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(backward_demodulation,[],[f41,f42])).

fof(f41,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),X1) ),
    inference(definition_unfolding,[],[f28,f29])).

fof(f28,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_xboole_1)).

fof(f222,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) ),
    inference(superposition,[],[f37,f34])).

fof(f37,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f21,f32,f29])).

fof(f32,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f21,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:27:24 EST 2020
% 0.14/0.34  % CPUTime    : 
% 1.27/0.52  % (18401)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.27/0.53  % (18405)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.27/0.53  % (18421)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.27/0.53  % (18421)Refutation not found, incomplete strategy% (18421)------------------------------
% 1.27/0.53  % (18421)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.53  % (18417)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.27/0.54  % (18413)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.27/0.54  % (18421)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.54  
% 1.27/0.54  % (18421)Memory used [KB]: 10618
% 1.27/0.54  % (18421)Time elapsed: 0.114 s
% 1.27/0.54  % (18421)------------------------------
% 1.27/0.54  % (18421)------------------------------
% 1.27/0.54  % (18409)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.27/0.54  % (18405)Refutation not found, incomplete strategy% (18405)------------------------------
% 1.27/0.54  % (18405)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.54  % (18405)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.54  
% 1.27/0.54  % (18405)Memory used [KB]: 10618
% 1.27/0.54  % (18405)Time elapsed: 0.124 s
% 1.27/0.54  % (18405)------------------------------
% 1.27/0.54  % (18405)------------------------------
% 1.27/0.54  % (18420)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.27/0.54  % (18398)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.37/0.54  % (18410)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.37/0.54  % (18402)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.37/0.55  % (18412)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.37/0.55  % (18412)Refutation not found, incomplete strategy% (18412)------------------------------
% 1.37/0.55  % (18412)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.55  % (18412)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.55  
% 1.37/0.55  % (18412)Memory used [KB]: 10618
% 1.37/0.55  % (18412)Time elapsed: 0.121 s
% 1.37/0.55  % (18412)------------------------------
% 1.37/0.55  % (18412)------------------------------
% 1.37/0.55  % (18404)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.37/0.55  % (18396)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.37/0.55  % (18417)Refutation not found, incomplete strategy% (18417)------------------------------
% 1.37/0.55  % (18417)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.55  % (18417)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.55  
% 1.37/0.55  % (18417)Memory used [KB]: 10746
% 1.37/0.55  % (18417)Time elapsed: 0.127 s
% 1.37/0.55  % (18417)------------------------------
% 1.37/0.55  % (18417)------------------------------
% 1.37/0.55  % (18410)Refutation not found, incomplete strategy% (18410)------------------------------
% 1.37/0.55  % (18410)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.55  % (18410)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.55  
% 1.37/0.55  % (18410)Memory used [KB]: 6140
% 1.37/0.55  % (18410)Time elapsed: 0.125 s
% 1.37/0.55  % (18410)------------------------------
% 1.37/0.55  % (18410)------------------------------
% 1.37/0.55  % (18404)Refutation not found, incomplete strategy% (18404)------------------------------
% 1.37/0.55  % (18404)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.55  % (18404)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.55  
% 1.37/0.55  % (18404)Memory used [KB]: 10618
% 1.37/0.55  % (18404)Time elapsed: 0.121 s
% 1.37/0.55  % (18404)------------------------------
% 1.37/0.55  % (18404)------------------------------
% 1.37/0.55  % (18424)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.37/0.55  % (18414)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.37/0.55  % (18420)Refutation not found, incomplete strategy% (18420)------------------------------
% 1.37/0.55  % (18420)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.55  % (18420)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.55  
% 1.37/0.55  % (18420)Memory used [KB]: 6268
% 1.37/0.55  % (18420)Time elapsed: 0.120 s
% 1.37/0.55  % (18420)------------------------------
% 1.37/0.55  % (18420)------------------------------
% 1.37/0.56  % (18397)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.37/0.56  % (18406)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.37/0.56  % (18397)Refutation not found, incomplete strategy% (18397)------------------------------
% 1.37/0.56  % (18397)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.56  % (18397)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.56  
% 1.37/0.56  % (18397)Memory used [KB]: 10618
% 1.37/0.56  % (18397)Time elapsed: 0.140 s
% 1.37/0.56  % (18397)------------------------------
% 1.37/0.56  % (18397)------------------------------
% 1.37/0.56  % (18399)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.37/0.56  % (18399)Refutation not found, incomplete strategy% (18399)------------------------------
% 1.37/0.56  % (18399)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.56  % (18399)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.56  
% 1.37/0.56  % (18399)Memory used [KB]: 6140
% 1.37/0.56  % (18399)Time elapsed: 0.145 s
% 1.37/0.56  % (18399)------------------------------
% 1.37/0.56  % (18399)------------------------------
% 1.37/0.56  % (18416)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.37/0.56  % (18395)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.37/0.56  % (18419)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.37/0.56  % (18395)Refutation not found, incomplete strategy% (18395)------------------------------
% 1.37/0.56  % (18395)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.56  % (18395)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.56  
% 1.37/0.56  % (18395)Memory used [KB]: 1663
% 1.37/0.56  % (18395)Time elapsed: 0.129 s
% 1.37/0.56  % (18395)------------------------------
% 1.37/0.56  % (18395)------------------------------
% 1.37/0.57  % (18411)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.37/0.57  % (18415)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.37/0.57  % (18422)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.37/0.57  % (18415)Refutation not found, incomplete strategy% (18415)------------------------------
% 1.37/0.57  % (18415)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.57  % (18415)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.57  
% 1.37/0.57  % (18415)Memory used [KB]: 10618
% 1.37/0.57  % (18415)Time elapsed: 0.155 s
% 1.37/0.57  % (18415)------------------------------
% 1.37/0.57  % (18415)------------------------------
% 1.37/0.57  % (18423)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.37/0.57  % (18400)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.37/0.58  % (18408)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.37/0.58  % (18407)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.37/0.58  % (18403)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.37/0.58  % (18416)Refutation not found, incomplete strategy% (18416)------------------------------
% 1.37/0.58  % (18416)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.58  % (18416)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.58  
% 1.37/0.58  % (18416)Memory used [KB]: 1663
% 1.37/0.58  % (18416)Time elapsed: 0.132 s
% 1.37/0.58  % (18416)------------------------------
% 1.37/0.58  % (18416)------------------------------
% 1.37/0.58  % (18403)Refutation not found, incomplete strategy% (18403)------------------------------
% 1.37/0.58  % (18403)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.58  % (18403)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.58  
% 1.37/0.58  % (18403)Memory used [KB]: 10618
% 1.37/0.58  % (18403)Time elapsed: 0.166 s
% 1.37/0.58  % (18403)------------------------------
% 1.37/0.58  % (18403)------------------------------
% 1.37/0.59  % (18418)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.37/0.61  % (18418)Refutation not found, incomplete strategy% (18418)------------------------------
% 1.37/0.61  % (18418)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.61  % (18418)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.61  
% 1.37/0.61  % (18418)Memory used [KB]: 1663
% 1.37/0.61  % (18418)Time elapsed: 0.184 s
% 1.37/0.61  % (18418)------------------------------
% 1.37/0.61  % (18418)------------------------------
% 1.37/0.61  % (18419)Refutation found. Thanks to Tanya!
% 1.37/0.61  % SZS status Theorem for theBenchmark
% 1.37/0.62  % SZS output start Proof for theBenchmark
% 1.37/0.62  fof(f736,plain,(
% 1.37/0.62    $false),
% 1.37/0.62    inference(trivial_inequality_removal,[],[f733])).
% 1.37/0.63  fof(f733,plain,(
% 1.37/0.63    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,sK1)),
% 1.37/0.63    inference(superposition,[],[f683,f23])).
% 1.37/0.63  fof(f23,plain,(
% 1.37/0.63    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.37/0.63    inference(cnf_transformation,[],[f4])).
% 1.37/0.63  fof(f4,axiom,(
% 1.37/0.63    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.37/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.37/0.63  fof(f683,plain,(
% 1.37/0.63    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(sK0,sK1),k1_xboole_0)),
% 1.37/0.63    inference(forward_demodulation,[],[f682,f31])).
% 1.37/0.63  fof(f31,plain,(
% 1.37/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.37/0.63    inference(cnf_transformation,[],[f8])).
% 1.37/0.63  fof(f8,axiom,(
% 1.37/0.63    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.37/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.37/0.63  fof(f682,plain,(
% 1.37/0.63    k2_xboole_0(k2_xboole_0(sK0,sK1),k1_xboole_0) != k2_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 1.37/0.63    inference(forward_demodulation,[],[f681,f23])).
% 1.37/0.63  fof(f681,plain,(
% 1.37/0.63    k2_xboole_0(k2_xboole_0(sK0,sK1),k1_xboole_0) != k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k1_xboole_0)),
% 1.37/0.63    inference(forward_demodulation,[],[f680,f361])).
% 1.37/0.63  fof(f361,plain,(
% 1.37/0.63    ( ! [X10,X11,X9] : (k2_xboole_0(X9,k2_xboole_0(k4_xboole_0(X9,X10),X11)) = k2_xboole_0(X9,X11)) )),
% 1.37/0.63    inference(superposition,[],[f34,f320])).
% 1.37/0.63  fof(f320,plain,(
% 1.37/0.63    ( ! [X2,X3] : (k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2) )),
% 1.37/0.63    inference(superposition,[],[f40,f42])).
% 1.37/0.63  fof(f42,plain,(
% 1.37/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.37/0.63    inference(definition_unfolding,[],[f30,f29])).
% 1.37/0.63  fof(f29,plain,(
% 1.37/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.37/0.63    inference(cnf_transformation,[],[f12])).
% 1.37/0.63  fof(f12,axiom,(
% 1.37/0.63    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.37/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.37/0.63  fof(f30,plain,(
% 1.37/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.37/0.63    inference(cnf_transformation,[],[f11])).
% 1.37/0.63  fof(f11,axiom,(
% 1.37/0.63    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.37/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 1.37/0.63  fof(f40,plain,(
% 1.37/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0) )),
% 1.37/0.63    inference(definition_unfolding,[],[f27,f29])).
% 1.37/0.63  fof(f27,plain,(
% 1.37/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 1.37/0.63    inference(cnf_transformation,[],[f6])).
% 1.37/0.63  fof(f6,axiom,(
% 1.37/0.63    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 1.37/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 1.37/0.63  fof(f34,plain,(
% 1.37/0.63    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.37/0.63    inference(cnf_transformation,[],[f13])).
% 1.37/0.63  fof(f13,axiom,(
% 1.37/0.63    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.37/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 1.37/0.63  fof(f680,plain,(
% 1.37/0.63    k2_xboole_0(k2_xboole_0(sK0,sK1),k1_xboole_0) != k2_xboole_0(k2_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k1_xboole_0)),
% 1.37/0.63    inference(forward_demodulation,[],[f679,f217])).
% 1.37/0.63  fof(f217,plain,(
% 1.37/0.63    ( ! [X8,X7,X9] : (k2_xboole_0(X9,k2_xboole_0(X7,X8)) = k2_xboole_0(X7,k2_xboole_0(X8,X9))) )),
% 1.37/0.63    inference(superposition,[],[f34,f25])).
% 1.37/0.63  fof(f25,plain,(
% 1.37/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.37/0.63    inference(cnf_transformation,[],[f1])).
% 1.37/0.63  fof(f1,axiom,(
% 1.37/0.63    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.37/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.37/0.63  fof(f679,plain,(
% 1.37/0.63    k2_xboole_0(k2_xboole_0(sK0,sK1),k1_xboole_0) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK1,sK0),sK0)),k1_xboole_0)),
% 1.37/0.63    inference(forward_demodulation,[],[f620,f243])).
% 1.37/0.63  fof(f243,plain,(
% 1.37/0.63    ( ! [X14,X15,X13] : (k2_xboole_0(X13,k2_xboole_0(X14,X15)) = k2_xboole_0(X13,k2_xboole_0(X14,k4_xboole_0(X15,X13)))) )),
% 1.37/0.63    inference(forward_demodulation,[],[f242,f34])).
% 1.37/0.63  fof(f242,plain,(
% 1.37/0.63    ( ! [X14,X15,X13] : (k2_xboole_0(k2_xboole_0(X13,X14),X15) = k2_xboole_0(X13,k2_xboole_0(X14,k4_xboole_0(X15,X13)))) )),
% 1.37/0.63    inference(forward_demodulation,[],[f219,f125])).
% 1.37/0.63  fof(f125,plain,(
% 1.37/0.63    ( ! [X6,X7,X5] : (k2_xboole_0(X7,k4_xboole_0(X5,X6)) = k2_xboole_0(X7,k4_xboole_0(X5,k2_xboole_0(X6,X7)))) )),
% 1.37/0.63    inference(superposition,[],[f31,f33])).
% 1.37/0.63  fof(f33,plain,(
% 1.37/0.63    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.37/0.63    inference(cnf_transformation,[],[f9])).
% 1.37/0.63  fof(f9,axiom,(
% 1.37/0.63    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.37/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.37/0.63  fof(f219,plain,(
% 1.37/0.63    ( ! [X14,X15,X13] : (k2_xboole_0(k2_xboole_0(X13,X14),X15) = k2_xboole_0(X13,k2_xboole_0(X14,k4_xboole_0(X15,k2_xboole_0(X13,X14))))) )),
% 1.37/0.63    inference(superposition,[],[f34,f31])).
% 1.37/0.63  fof(f620,plain,(
% 1.37/0.63    k2_xboole_0(k2_xboole_0(sK0,sK1),k1_xboole_0) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),k1_xboole_0)),
% 1.37/0.63    inference(unit_resulting_resolution,[],[f222,f47,f47,f36])).
% 1.37/0.63  fof(f36,plain,(
% 1.37/0.63    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) != k2_xboole_0(X2,X1) | ~r1_xboole_0(X0,X1) | ~r1_xboole_0(X2,X1) | X0 = X2) )),
% 1.37/0.63    inference(cnf_transformation,[],[f20])).
% 1.37/0.63  fof(f20,plain,(
% 1.37/0.63    ! [X0,X1,X2] : (X0 = X2 | ~r1_xboole_0(X2,X1) | ~r1_xboole_0(X0,X1) | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X1))),
% 1.37/0.63    inference(flattening,[],[f19])).
% 1.37/0.63  fof(f19,plain,(
% 1.37/0.63    ! [X0,X1,X2] : (X0 = X2 | (~r1_xboole_0(X2,X1) | ~r1_xboole_0(X0,X1) | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X1)))),
% 1.37/0.63    inference(ennf_transformation,[],[f14])).
% 1.37/0.63  fof(f14,axiom,(
% 1.37/0.63    ! [X0,X1,X2] : ((r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)) => X0 = X2)),
% 1.37/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_xboole_1)).
% 1.37/0.63  fof(f47,plain,(
% 1.37/0.63    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.37/0.63    inference(superposition,[],[f46,f44])).
% 1.37/0.63  fof(f44,plain,(
% 1.37/0.63    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.37/0.63    inference(forward_demodulation,[],[f39,f24])).
% 1.37/0.63  fof(f24,plain,(
% 1.37/0.63    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 1.37/0.63    inference(cnf_transformation,[],[f10])).
% 1.37/0.63  fof(f10,axiom,(
% 1.37/0.63    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 1.37/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 1.37/0.63  fof(f39,plain,(
% 1.37/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0) )),
% 1.37/0.63    inference(definition_unfolding,[],[f26,f29])).
% 1.37/0.63  fof(f26,plain,(
% 1.37/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 1.37/0.63    inference(cnf_transformation,[],[f5])).
% 1.37/0.63  fof(f5,axiom,(
% 1.37/0.63    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 1.37/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).
% 1.37/0.63  fof(f46,plain,(
% 1.37/0.63    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.37/0.63    inference(backward_demodulation,[],[f41,f42])).
% 1.37/0.63  fof(f41,plain,(
% 1.37/0.63    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),X1)) )),
% 1.37/0.63    inference(definition_unfolding,[],[f28,f29])).
% 1.37/0.63  fof(f28,plain,(
% 1.37/0.63    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 1.37/0.63    inference(cnf_transformation,[],[f15])).
% 1.37/0.63  fof(f15,axiom,(
% 1.37/0.63    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1)),
% 1.37/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_xboole_1)).
% 1.37/0.63  fof(f222,plain,(
% 1.37/0.63    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))),
% 1.37/0.63    inference(superposition,[],[f37,f34])).
% 1.37/0.63  fof(f37,plain,(
% 1.37/0.63    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 1.37/0.63    inference(definition_unfolding,[],[f21,f32,f29])).
% 1.37/0.63  fof(f32,plain,(
% 1.37/0.63    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 1.37/0.63    inference(cnf_transformation,[],[f2])).
% 1.37/0.63  fof(f2,axiom,(
% 1.37/0.63    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 1.37/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).
% 1.37/0.63  fof(f21,plain,(
% 1.37/0.63    k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 1.37/0.63    inference(cnf_transformation,[],[f18])).
% 1.37/0.63  fof(f18,plain,(
% 1.37/0.63    ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.37/0.63    inference(ennf_transformation,[],[f17])).
% 1.37/0.63  fof(f17,negated_conjecture,(
% 1.37/0.63    ~! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.37/0.63    inference(negated_conjecture,[],[f16])).
% 1.37/0.63  fof(f16,conjecture,(
% 1.37/0.63    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.37/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).
% 1.37/0.63  % SZS output end Proof for theBenchmark
% 1.37/0.63  % (18419)------------------------------
% 1.37/0.63  % (18419)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.63  % (18419)Termination reason: Refutation
% 1.37/0.63  
% 1.37/0.63  % (18419)Memory used [KB]: 6780
% 1.37/0.63  % (18419)Time elapsed: 0.184 s
% 1.37/0.63  % (18419)------------------------------
% 1.37/0.63  % (18419)------------------------------
% 1.37/0.63  % (18394)Success in time 0.262 s
%------------------------------------------------------------------------------
