%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:43 EST 2020

% Result     : Theorem 1.63s
% Output     : Refutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   41 (  48 expanded)
%              Number of leaves         :   11 (  14 expanded)
%              Depth                    :   10
%              Number of atoms          :   60 (  72 expanded)
%              Number of equality atoms :   41 (  49 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f196,plain,(
    $false ),
    inference(subsumption_resolution,[],[f38,f195])).

fof(f195,plain,(
    ! [X2,X1] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k2_tarski(X1,X2)) ),
    inference(forward_demodulation,[],[f194,f86])).

fof(f86,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f84,f42])).

fof(f42,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f84,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f82,f40])).

fof(f40,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f82,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f45,f72])).

fof(f72,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(resolution,[],[f54,f66])).

fof(f66,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f194,plain,(
    ! [X2,X1] : k5_xboole_0(k1_xboole_0,k2_tarski(X1,X2)) = k2_xboole_0(k1_tarski(X1),k2_tarski(X1,X2)) ),
    inference(forward_demodulation,[],[f181,f42])).

fof(f181,plain,(
    ! [X2,X1] : k5_xboole_0(k2_tarski(X1,X2),k1_xboole_0) = k2_xboole_0(k1_tarski(X1),k2_tarski(X1,X2)) ),
    inference(superposition,[],[f178,f73])).

fof(f73,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(k1_tarski(X1),k2_tarski(X1,X2)) ),
    inference(resolution,[],[f54,f41])).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

fof(f178,plain,(
    ! [X4,X3] : k2_xboole_0(X4,X3) = k5_xboole_0(X3,k4_xboole_0(X4,X3)) ),
    inference(forward_demodulation,[],[f169,f44])).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f169,plain,(
    ! [X4,X3] : k5_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X4,X3))) = k2_xboole_0(X4,X3) ),
    inference(superposition,[],[f111,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f111,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X1,X0),k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f46,f42])).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f38,plain,(
    k2_tarski(sK1,sK2) != k2_xboole_0(k1_tarski(sK1),k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    k2_tarski(sK1,sK2) != k2_xboole_0(k1_tarski(sK1),k2_tarski(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f19,f23])).

fof(f23,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))
   => k2_tarski(sK1,sK2) != k2_xboole_0(k1_tarski(sK1),k2_tarski(sK1,sK2)) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:51:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (27352)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.47  % (27352)Refutation not found, incomplete strategy% (27352)------------------------------
% 0.21/0.47  % (27352)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (27360)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.48  % (27352)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (27352)Memory used [KB]: 10618
% 0.21/0.48  % (27352)Time elapsed: 0.054 s
% 0.21/0.48  % (27352)------------------------------
% 0.21/0.48  % (27352)------------------------------
% 0.21/0.53  % (27363)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (27347)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (27349)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (27358)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (27344)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (27344)Refutation not found, incomplete strategy% (27344)------------------------------
% 0.21/0.54  % (27344)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (27344)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (27344)Memory used [KB]: 1663
% 0.21/0.54  % (27344)Time elapsed: 0.121 s
% 0.21/0.54  % (27344)------------------------------
% 0.21/0.54  % (27344)------------------------------
% 0.21/0.54  % (27345)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (27366)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (27354)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (27353)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (27371)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (27351)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.55  % (27359)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (27373)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.45/0.55  % (27354)Refutation not found, incomplete strategy% (27354)------------------------------
% 1.45/0.55  % (27354)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.55  % (27354)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.55  
% 1.45/0.55  % (27354)Memory used [KB]: 10618
% 1.45/0.55  % (27354)Time elapsed: 0.140 s
% 1.45/0.55  % (27354)------------------------------
% 1.45/0.55  % (27354)------------------------------
% 1.45/0.55  % (27353)Refutation not found, incomplete strategy% (27353)------------------------------
% 1.45/0.55  % (27353)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.55  % (27353)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.55  
% 1.45/0.55  % (27353)Memory used [KB]: 10618
% 1.45/0.55  % (27353)Time elapsed: 0.140 s
% 1.45/0.55  % (27353)------------------------------
% 1.45/0.55  % (27353)------------------------------
% 1.45/0.55  % (27357)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.45/0.55  % (27350)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.45/0.55  % (27346)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.45/0.55  % (27346)Refutation not found, incomplete strategy% (27346)------------------------------
% 1.45/0.55  % (27346)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.55  % (27346)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.55  
% 1.45/0.55  % (27346)Memory used [KB]: 10618
% 1.45/0.55  % (27346)Time elapsed: 0.141 s
% 1.45/0.55  % (27346)------------------------------
% 1.45/0.55  % (27346)------------------------------
% 1.45/0.55  % (27367)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.45/0.55  % (27348)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.45/0.55  % (27355)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.45/0.55  % (27367)Refutation not found, incomplete strategy% (27367)------------------------------
% 1.45/0.55  % (27367)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.55  % (27367)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.55  
% 1.45/0.55  % (27367)Memory used [KB]: 1663
% 1.45/0.55  % (27367)Time elapsed: 0.145 s
% 1.45/0.55  % (27348)Refutation not found, incomplete strategy% (27348)------------------------------
% 1.45/0.55  % (27348)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.55  % (27348)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.55  
% 1.45/0.55  % (27348)Memory used [KB]: 6140
% 1.45/0.55  % (27348)Time elapsed: 0.144 s
% 1.45/0.55  % (27348)------------------------------
% 1.45/0.55  % (27348)------------------------------
% 1.45/0.55  % (27367)------------------------------
% 1.45/0.55  % (27367)------------------------------
% 1.45/0.55  % (27355)Refutation not found, incomplete strategy% (27355)------------------------------
% 1.45/0.55  % (27355)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.55  % (27355)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.55  
% 1.45/0.55  % (27355)Memory used [KB]: 10618
% 1.45/0.55  % (27355)Time elapsed: 0.141 s
% 1.45/0.55  % (27355)------------------------------
% 1.45/0.55  % (27355)------------------------------
% 1.45/0.55  % (27368)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.45/0.56  % (27361)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.45/0.56  % (27362)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.45/0.56  % (27364)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.45/0.56  % (27372)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.45/0.56  % (27365)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.45/0.56  % (27356)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.45/0.56  % (27369)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.45/0.56  % (27365)Refutation not found, incomplete strategy% (27365)------------------------------
% 1.45/0.56  % (27365)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.56  % (27369)Refutation not found, incomplete strategy% (27369)------------------------------
% 1.45/0.56  % (27369)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.56  % (27370)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.63/0.57  % (27361)Refutation not found, incomplete strategy% (27361)------------------------------
% 1.63/0.57  % (27361)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.57  % (27351)Refutation found. Thanks to Tanya!
% 1.63/0.57  % SZS status Theorem for theBenchmark
% 1.63/0.57  % (27365)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.57  
% 1.63/0.57  % (27365)Memory used [KB]: 1663
% 1.63/0.57  % (27365)Time elapsed: 0.158 s
% 1.63/0.57  % (27365)------------------------------
% 1.63/0.57  % (27365)------------------------------
% 1.63/0.57  % (27364)Refutation not found, incomplete strategy% (27364)------------------------------
% 1.63/0.57  % (27364)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.57  % (27369)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.57  
% 1.63/0.57  % (27369)Memory used [KB]: 6268
% 1.63/0.57  % (27369)Time elapsed: 0.156 s
% 1.63/0.57  % (27369)------------------------------
% 1.63/0.57  % (27369)------------------------------
% 1.63/0.57  % (27361)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.57  
% 1.63/0.57  % (27361)Memory used [KB]: 10618
% 1.63/0.57  % (27361)Time elapsed: 0.158 s
% 1.63/0.57  % (27361)------------------------------
% 1.63/0.57  % (27361)------------------------------
% 1.63/0.58  % (27364)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.58  
% 1.63/0.58  % (27364)Memory used [KB]: 10746
% 1.63/0.58  % (27364)Time elapsed: 0.168 s
% 1.63/0.58  % (27364)------------------------------
% 1.63/0.58  % (27364)------------------------------
% 1.63/0.59  % SZS output start Proof for theBenchmark
% 1.63/0.59  fof(f196,plain,(
% 1.63/0.59    $false),
% 1.63/0.59    inference(subsumption_resolution,[],[f38,f195])).
% 1.63/0.59  fof(f195,plain,(
% 1.63/0.59    ( ! [X2,X1] : (k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k2_tarski(X1,X2))) )),
% 1.63/0.59    inference(forward_demodulation,[],[f194,f86])).
% 1.63/0.59  fof(f86,plain,(
% 1.63/0.59    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 1.63/0.59    inference(superposition,[],[f84,f42])).
% 1.63/0.59  fof(f42,plain,(
% 1.63/0.59    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f1])).
% 1.63/0.59  fof(f1,axiom,(
% 1.63/0.59    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.63/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.63/0.59  fof(f84,plain,(
% 1.63/0.59    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.63/0.59    inference(forward_demodulation,[],[f82,f40])).
% 1.63/0.59  fof(f40,plain,(
% 1.63/0.59    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 1.63/0.59    inference(cnf_transformation,[],[f18])).
% 1.63/0.59  fof(f18,plain,(
% 1.63/0.59    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 1.63/0.59    inference(rectify,[],[f4])).
% 1.63/0.59  fof(f4,axiom,(
% 1.63/0.59    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 1.63/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 1.63/0.59  fof(f82,plain,(
% 1.63/0.59    ( ! [X0] : (k2_xboole_0(X0,X0) = k5_xboole_0(X0,k1_xboole_0)) )),
% 1.63/0.59    inference(superposition,[],[f45,f72])).
% 1.63/0.59  fof(f72,plain,(
% 1.63/0.59    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.63/0.59    inference(resolution,[],[f54,f66])).
% 1.63/0.59  fof(f66,plain,(
% 1.63/0.59    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.63/0.59    inference(equality_resolution,[],[f48])).
% 1.63/0.59  fof(f48,plain,(
% 1.63/0.59    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.63/0.59    inference(cnf_transformation,[],[f26])).
% 1.63/0.59  fof(f26,plain,(
% 1.63/0.59    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.63/0.59    inference(flattening,[],[f25])).
% 1.63/0.59  fof(f25,plain,(
% 1.63/0.59    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.63/0.59    inference(nnf_transformation,[],[f5])).
% 1.63/0.59  fof(f5,axiom,(
% 1.63/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.63/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.63/0.59  fof(f54,plain,(
% 1.63/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.63/0.59    inference(cnf_transformation,[],[f31])).
% 1.63/0.59  fof(f31,plain,(
% 1.63/0.59    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.63/0.59    inference(nnf_transformation,[],[f6])).
% 1.63/0.59  fof(f6,axiom,(
% 1.63/0.59    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.63/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.63/0.59  fof(f45,plain,(
% 1.63/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.63/0.59    inference(cnf_transformation,[],[f10])).
% 1.63/0.59  fof(f10,axiom,(
% 1.63/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.63/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.63/0.59  fof(f194,plain,(
% 1.63/0.59    ( ! [X2,X1] : (k5_xboole_0(k1_xboole_0,k2_tarski(X1,X2)) = k2_xboole_0(k1_tarski(X1),k2_tarski(X1,X2))) )),
% 1.63/0.59    inference(forward_demodulation,[],[f181,f42])).
% 1.63/0.59  fof(f181,plain,(
% 1.63/0.59    ( ! [X2,X1] : (k5_xboole_0(k2_tarski(X1,X2),k1_xboole_0) = k2_xboole_0(k1_tarski(X1),k2_tarski(X1,X2))) )),
% 1.63/0.59    inference(superposition,[],[f178,f73])).
% 1.63/0.59  fof(f73,plain,(
% 1.63/0.59    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X1),k2_tarski(X1,X2))) )),
% 1.63/0.59    inference(resolution,[],[f54,f41])).
% 1.63/0.59  fof(f41,plain,(
% 1.63/0.59    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 1.63/0.59    inference(cnf_transformation,[],[f15])).
% 1.63/0.59  fof(f15,axiom,(
% 1.63/0.59    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.63/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).
% 1.63/0.59  fof(f178,plain,(
% 1.63/0.59    ( ! [X4,X3] : (k2_xboole_0(X4,X3) = k5_xboole_0(X3,k4_xboole_0(X4,X3))) )),
% 1.63/0.59    inference(forward_demodulation,[],[f169,f44])).
% 1.63/0.59  fof(f44,plain,(
% 1.63/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.63/0.59    inference(cnf_transformation,[],[f7])).
% 1.63/0.59  fof(f7,axiom,(
% 1.63/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.63/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.63/0.59  fof(f169,plain,(
% 1.63/0.59    ( ! [X4,X3] : (k5_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X4,X3))) = k2_xboole_0(X4,X3)) )),
% 1.63/0.59    inference(superposition,[],[f111,f56])).
% 1.63/0.59  fof(f56,plain,(
% 1.63/0.59    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.63/0.59    inference(cnf_transformation,[],[f8])).
% 1.63/0.59  fof(f8,axiom,(
% 1.63/0.59    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.63/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.63/0.59  fof(f111,plain,(
% 1.63/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X1,X0),k3_xboole_0(X0,X1))) )),
% 1.63/0.59    inference(superposition,[],[f46,f42])).
% 1.63/0.59  fof(f46,plain,(
% 1.63/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 1.63/0.59    inference(cnf_transformation,[],[f9])).
% 1.63/0.59  fof(f9,axiom,(
% 1.63/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.63/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 1.63/0.59  fof(f38,plain,(
% 1.63/0.59    k2_tarski(sK1,sK2) != k2_xboole_0(k1_tarski(sK1),k2_tarski(sK1,sK2))),
% 1.63/0.59    inference(cnf_transformation,[],[f24])).
% 1.63/0.59  fof(f24,plain,(
% 1.63/0.59    k2_tarski(sK1,sK2) != k2_xboole_0(k1_tarski(sK1),k2_tarski(sK1,sK2))),
% 1.63/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f19,f23])).
% 1.63/0.59  fof(f23,plain,(
% 1.63/0.59    ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) => k2_tarski(sK1,sK2) != k2_xboole_0(k1_tarski(sK1),k2_tarski(sK1,sK2))),
% 1.63/0.59    introduced(choice_axiom,[])).
% 1.63/0.59  fof(f19,plain,(
% 1.63/0.59    ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.63/0.59    inference(ennf_transformation,[],[f17])).
% 1.63/0.59  fof(f17,negated_conjecture,(
% 1.63/0.59    ~! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.63/0.59    inference(negated_conjecture,[],[f16])).
% 1.63/0.59  fof(f16,conjecture,(
% 1.63/0.59    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.63/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_zfmisc_1)).
% 1.63/0.59  % SZS output end Proof for theBenchmark
% 1.63/0.59  % (27351)------------------------------
% 1.63/0.59  % (27351)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.59  % (27351)Termination reason: Refutation
% 1.63/0.59  
% 1.63/0.59  % (27351)Memory used [KB]: 6396
% 1.63/0.59  % (27351)Time elapsed: 0.159 s
% 1.63/0.59  % (27351)------------------------------
% 1.63/0.59  % (27351)------------------------------
% 1.63/0.59  % (27343)Success in time 0.239 s
%------------------------------------------------------------------------------
