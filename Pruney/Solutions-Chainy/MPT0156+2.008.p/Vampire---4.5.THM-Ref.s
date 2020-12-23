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
% DateTime   : Thu Dec  3 12:33:42 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   15 (  15 expanded)
%              Number of leaves         :    5 (   5 expanded)
%              Depth                    :    5
%              Number of atoms          :   16 (  16 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,plain,(
    $false ),
    inference(subsumption_resolution,[],[f10,f16])).

fof(f16,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(forward_demodulation,[],[f15,f13])).

fof(f13,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

fof(f15,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(superposition,[],[f14,f11])).

fof(f11,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f14,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_enumset1)).

fof(f10,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f9])).

% (10986)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% (10982)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% (10980)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% (10981)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
fof(f9,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f8])).

fof(f8,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k3_enumset1(X0,X0,X1,X2,X3)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:33:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.37  ipcrm: permission denied for id (1219887105)
% 0.22/0.38  ipcrm: permission denied for id (1218281474)
% 0.22/0.38  ipcrm: permission denied for id (1219919875)
% 0.22/0.38  ipcrm: permission denied for id (1218314244)
% 0.22/0.38  ipcrm: permission denied for id (1219952645)
% 0.22/0.38  ipcrm: permission denied for id (1223491590)
% 0.22/0.38  ipcrm: permission denied for id (1223524359)
% 0.22/0.38  ipcrm: permission denied for id (1220050952)
% 0.22/0.39  ipcrm: permission denied for id (1220247565)
% 0.22/0.39  ipcrm: permission denied for id (1218412558)
% 0.22/0.39  ipcrm: permission denied for id (1218445327)
% 0.22/0.39  ipcrm: permission denied for id (1220280336)
% 0.22/0.39  ipcrm: permission denied for id (1220313105)
% 0.22/0.39  ipcrm: permission denied for id (1220345874)
% 0.22/0.40  ipcrm: permission denied for id (1220378643)
% 0.22/0.40  ipcrm: permission denied for id (1220411412)
% 0.22/0.40  ipcrm: permission denied for id (1223688213)
% 0.22/0.40  ipcrm: permission denied for id (1220476950)
% 0.22/0.40  ipcrm: permission denied for id (1220542488)
% 0.22/0.40  ipcrm: permission denied for id (1218543641)
% 0.22/0.40  ipcrm: permission denied for id (1218576410)
% 0.22/0.41  ipcrm: permission denied for id (1220575259)
% 0.22/0.41  ipcrm: permission denied for id (1218609181)
% 0.22/0.41  ipcrm: permission denied for id (1223786526)
% 0.22/0.41  ipcrm: permission denied for id (1223819295)
% 0.22/0.41  ipcrm: permission denied for id (1220706336)
% 0.22/0.41  ipcrm: permission denied for id (1223852065)
% 0.22/0.41  ipcrm: permission denied for id (1220771874)
% 0.22/0.42  ipcrm: permission denied for id (1223917604)
% 0.22/0.42  ipcrm: permission denied for id (1220902950)
% 0.22/0.42  ipcrm: permission denied for id (1220935719)
% 0.22/0.42  ipcrm: permission denied for id (1220968488)
% 0.22/0.42  ipcrm: permission denied for id (1223983145)
% 0.22/0.42  ipcrm: permission denied for id (1221034026)
% 0.22/0.43  ipcrm: permission denied for id (1221099563)
% 0.22/0.43  ipcrm: permission denied for id (1221132332)
% 0.22/0.43  ipcrm: permission denied for id (1224015917)
% 0.22/0.43  ipcrm: permission denied for id (1224048686)
% 0.22/0.43  ipcrm: permission denied for id (1224081455)
% 0.22/0.43  ipcrm: permission denied for id (1221263408)
% 0.22/0.43  ipcrm: permission denied for id (1218773041)
% 0.22/0.44  ipcrm: permission denied for id (1224179764)
% 0.22/0.44  ipcrm: permission denied for id (1218805813)
% 0.22/0.44  ipcrm: permission denied for id (1221394486)
% 0.22/0.44  ipcrm: permission denied for id (1218838583)
% 0.22/0.44  ipcrm: permission denied for id (1218871352)
% 0.22/0.44  ipcrm: permission denied for id (1218904121)
% 0.22/0.45  ipcrm: permission denied for id (1218969660)
% 0.22/0.45  ipcrm: permission denied for id (1219002429)
% 0.22/0.45  ipcrm: permission denied for id (1219035198)
% 0.22/0.45  ipcrm: permission denied for id (1221525568)
% 0.22/0.45  ipcrm: permission denied for id (1224343618)
% 0.22/0.45  ipcrm: permission denied for id (1221689411)
% 0.22/0.46  ipcrm: permission denied for id (1221722181)
% 0.22/0.46  ipcrm: permission denied for id (1219133510)
% 0.22/0.46  ipcrm: permission denied for id (1224409159)
% 0.22/0.46  ipcrm: permission denied for id (1221787720)
% 0.22/0.46  ipcrm: permission denied for id (1224441929)
% 0.22/0.46  ipcrm: permission denied for id (1221853258)
% 0.22/0.46  ipcrm: permission denied for id (1221886027)
% 0.22/0.47  ipcrm: permission denied for id (1224507469)
% 0.22/0.47  ipcrm: permission denied for id (1219231822)
% 0.22/0.47  ipcrm: permission denied for id (1222017104)
% 0.22/0.47  ipcrm: permission denied for id (1222049873)
% 0.22/0.47  ipcrm: permission denied for id (1222082642)
% 0.22/0.47  ipcrm: permission denied for id (1222115411)
% 0.22/0.48  ipcrm: permission denied for id (1222180949)
% 0.22/0.48  ipcrm: permission denied for id (1222246487)
% 0.22/0.48  ipcrm: permission denied for id (1222279256)
% 0.22/0.48  ipcrm: permission denied for id (1222312025)
% 0.22/0.48  ipcrm: permission denied for id (1222344794)
% 0.22/0.48  ipcrm: permission denied for id (1224638555)
% 0.22/0.48  ipcrm: permission denied for id (1224704093)
% 0.22/0.49  ipcrm: permission denied for id (1224769631)
% 0.22/0.49  ipcrm: permission denied for id (1219428449)
% 0.22/0.49  ipcrm: permission denied for id (1224835170)
% 0.22/0.49  ipcrm: permission denied for id (1224867939)
% 0.22/0.49  ipcrm: permission denied for id (1222639716)
% 0.22/0.49  ipcrm: permission denied for id (1219526757)
% 0.22/0.50  ipcrm: permission denied for id (1224900710)
% 0.22/0.50  ipcrm: permission denied for id (1222705255)
% 0.22/0.50  ipcrm: permission denied for id (1224966249)
% 0.22/0.50  ipcrm: permission denied for id (1222803562)
% 0.22/0.50  ipcrm: permission denied for id (1222869100)
% 0.22/0.50  ipcrm: permission denied for id (1225031789)
% 0.22/0.51  ipcrm: permission denied for id (1225097327)
% 0.22/0.51  ipcrm: permission denied for id (1219756146)
% 0.22/0.51  ipcrm: permission denied for id (1223131253)
% 0.22/0.51  ipcrm: permission denied for id (1223164022)
% 0.22/0.52  ipcrm: permission denied for id (1223229560)
% 0.22/0.52  ipcrm: permission denied for id (1225293945)
% 0.22/0.52  ipcrm: permission denied for id (1223295098)
% 0.22/0.52  ipcrm: permission denied for id (1219821691)
% 0.22/0.52  ipcrm: permission denied for id (1223327868)
% 0.22/0.52  ipcrm: permission denied for id (1223393406)
% 0.38/0.62  % (10984)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.38/0.62  % (10990)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.38/0.62  % (10990)Refutation found. Thanks to Tanya!
% 0.38/0.62  % SZS status Theorem for theBenchmark
% 0.38/0.62  % SZS output start Proof for theBenchmark
% 0.38/0.62  fof(f17,plain,(
% 0.38/0.62    $false),
% 0.38/0.62    inference(subsumption_resolution,[],[f10,f16])).
% 0.38/0.62  fof(f16,plain,(
% 0.38/0.62    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 0.38/0.62    inference(forward_demodulation,[],[f15,f13])).
% 0.38/0.62  fof(f13,plain,(
% 0.38/0.62    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 0.38/0.62    inference(cnf_transformation,[],[f1])).
% 0.38/0.62  fof(f1,axiom,(
% 0.38/0.62    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 0.38/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).
% 0.38/0.62  fof(f15,plain,(
% 0.38/0.62    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 0.38/0.62    inference(superposition,[],[f14,f11])).
% 0.38/0.62  fof(f11,plain,(
% 0.38/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.38/0.62    inference(cnf_transformation,[],[f3])).
% 0.38/0.62  fof(f3,axiom,(
% 0.38/0.62    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.38/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.38/0.62  fof(f14,plain,(
% 0.38/0.62    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))) )),
% 0.38/0.62    inference(cnf_transformation,[],[f2])).
% 0.38/0.62  fof(f2,axiom,(
% 0.38/0.62    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))),
% 0.38/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_enumset1)).
% 0.38/0.62  fof(f10,plain,(
% 0.38/0.62    k2_enumset1(sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3)),
% 0.38/0.62    inference(cnf_transformation,[],[f9])).
% 0.38/0.63  % (10986)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.38/0.64  % (10982)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.38/0.64  % (10980)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.38/0.64  % (10981)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.38/0.64  fof(f9,plain,(
% 0.38/0.64    k2_enumset1(sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3)),
% 0.38/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f8])).
% 0.38/0.64  fof(f8,plain,(
% 0.38/0.64    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k3_enumset1(X0,X0,X1,X2,X3) => k2_enumset1(sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3)),
% 0.38/0.64    introduced(choice_axiom,[])).
% 0.38/0.64  fof(f7,plain,(
% 0.38/0.64    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k3_enumset1(X0,X0,X1,X2,X3)),
% 0.38/0.64    inference(ennf_transformation,[],[f6])).
% 0.38/0.64  fof(f6,negated_conjecture,(
% 0.38/0.64    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.38/0.64    inference(negated_conjecture,[],[f5])).
% 0.38/0.64  fof(f5,conjecture,(
% 0.38/0.64    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.38/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.38/0.64  % SZS output end Proof for theBenchmark
% 0.38/0.64  % (10990)------------------------------
% 0.38/0.64  % (10990)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.38/0.64  % (10990)Termination reason: Refutation
% 0.38/0.64  
% 0.38/0.64  % (10990)Memory used [KB]: 6012
% 0.38/0.64  % (10990)Time elapsed: 0.060 s
% 0.38/0.64  % (10990)------------------------------
% 0.38/0.64  % (10990)------------------------------
% 0.38/0.64  % (10839)Success in time 0.272 s
%------------------------------------------------------------------------------
