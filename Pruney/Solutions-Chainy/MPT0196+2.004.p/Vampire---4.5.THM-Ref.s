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
% DateTime   : Thu Dec  3 12:34:29 EST 2020

% Result     : Theorem 1.27s
% Output     : Refutation 1.27s
% Verified   : 
% Statistics : Number of formulae       :   14 (  18 expanded)
%              Number of leaves         :    4 (   6 expanded)
%              Depth                    :    7
%              Number of atoms          :   15 (  19 expanded)
%              Number of equality atoms :   14 (  18 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f30,plain,(
    $false ),
    inference(subsumption_resolution,[],[f25,f19])).

fof(f19,plain,(
    ! [X14,X12,X15,X13] : k2_enumset1(X13,X14,X12,X15) = k2_enumset1(X12,X13,X15,X14) ),
    inference(superposition,[],[f12,f11])).

fof(f11,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l123_enumset1)).

fof(f12,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_enumset1)).

fof(f25,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK0,sK2) ),
    inference(superposition,[],[f17,f12])).

fof(f17,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK2,sK0) ),
    inference(superposition,[],[f10,f11])).

fof(f10,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK3,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK3,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f8])).

fof(f8,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X2,X1,X3,X0)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK3,sK0) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X2,X1,X3,X0) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X3,X0) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X3,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:01:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.37  ipcrm: permission denied for id (1212841984)
% 0.14/0.38  ipcrm: permission denied for id (1213005832)
% 0.14/0.38  ipcrm: permission denied for id (1213071372)
% 0.14/0.39  ipcrm: permission denied for id (1213235216)
% 0.14/0.39  ipcrm: permission denied for id (1213300756)
% 0.21/0.41  ipcrm: permission denied for id (1213464607)
% 0.21/0.41  ipcrm: permission denied for id (1213530145)
% 0.21/0.41  ipcrm: permission denied for id (1213562914)
% 0.21/0.41  ipcrm: permission denied for id (1213628453)
% 0.21/0.42  ipcrm: permission denied for id (1213661222)
% 0.21/0.42  ipcrm: permission denied for id (1213726760)
% 0.21/0.42  ipcrm: permission denied for id (1213792300)
% 0.21/0.43  ipcrm: permission denied for id (1213857843)
% 0.21/0.45  ipcrm: permission denied for id (1214087235)
% 0.21/0.45  ipcrm: permission denied for id (1214120005)
% 0.21/0.46  ipcrm: permission denied for id (1214185545)
% 0.21/0.47  ipcrm: permission denied for id (1214218320)
% 0.21/0.47  ipcrm: permission denied for id (1214251091)
% 0.21/0.47  ipcrm: permission denied for id (1214283860)
% 0.21/0.48  ipcrm: permission denied for id (1214349398)
% 0.21/0.48  ipcrm: permission denied for id (1214382169)
% 0.21/0.49  ipcrm: permission denied for id (1214414941)
% 0.21/0.49  ipcrm: permission denied for id (1214447710)
% 0.21/0.51  ipcrm: permission denied for id (1214546025)
% 0.21/0.51  ipcrm: permission denied for id (1214578794)
% 0.21/0.53  ipcrm: permission denied for id (1214677111)
% 0.21/0.53  ipcrm: permission denied for id (1214742649)
% 0.21/0.53  ipcrm: permission denied for id (1214775418)
% 0.98/0.67  % (22377)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 1.27/0.67  % (22377)Refutation found. Thanks to Tanya!
% 1.27/0.67  % SZS status Theorem for theBenchmark
% 1.27/0.67  % (22378)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 1.27/0.67  % (22380)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 1.27/0.67  % (22379)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 1.27/0.68  % (22382)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 1.27/0.68  % (22385)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 1.27/0.68  % SZS output start Proof for theBenchmark
% 1.27/0.68  fof(f30,plain,(
% 1.27/0.68    $false),
% 1.27/0.68    inference(subsumption_resolution,[],[f25,f19])).
% 1.27/0.68  fof(f19,plain,(
% 1.27/0.68    ( ! [X14,X12,X15,X13] : (k2_enumset1(X13,X14,X12,X15) = k2_enumset1(X12,X13,X15,X14)) )),
% 1.27/0.68    inference(superposition,[],[f12,f11])).
% 1.27/0.68  fof(f11,plain,(
% 1.27/0.68    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3)) )),
% 1.27/0.68    inference(cnf_transformation,[],[f1])).
% 1.27/0.68  fof(f1,axiom,(
% 1.27/0.68    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3)),
% 1.27/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l123_enumset1)).
% 1.27/0.68  fof(f12,plain,(
% 1.27/0.68    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)) )),
% 1.27/0.68    inference(cnf_transformation,[],[f2])).
% 1.27/0.68  fof(f2,axiom,(
% 1.27/0.68    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)),
% 1.27/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_enumset1)).
% 1.27/0.68  fof(f25,plain,(
% 1.27/0.68    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK0,sK2)),
% 1.27/0.68    inference(superposition,[],[f17,f12])).
% 1.27/0.68  fof(f17,plain,(
% 1.27/0.68    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK2,sK0)),
% 1.27/0.68    inference(superposition,[],[f10,f11])).
% 1.27/0.68  fof(f10,plain,(
% 1.27/0.68    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK3,sK0)),
% 1.27/0.68    inference(cnf_transformation,[],[f9])).
% 1.27/0.68  fof(f9,plain,(
% 1.27/0.68    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK3,sK0)),
% 1.27/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f8])).
% 1.27/0.68  fof(f8,plain,(
% 1.27/0.68    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X2,X1,X3,X0) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK3,sK0)),
% 1.27/0.68    introduced(choice_axiom,[])).
% 1.27/0.68  fof(f7,plain,(
% 1.27/0.68    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X2,X1,X3,X0)),
% 1.27/0.68    inference(ennf_transformation,[],[f6])).
% 1.27/0.68  fof(f6,negated_conjecture,(
% 1.27/0.68    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X3,X0)),
% 1.27/0.68    inference(negated_conjecture,[],[f5])).
% 1.27/0.68  fof(f5,conjecture,(
% 1.27/0.68    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X3,X0)),
% 1.27/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_enumset1)).
% 1.27/0.68  % SZS output end Proof for theBenchmark
% 1.27/0.68  % (22377)------------------------------
% 1.27/0.68  % (22377)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.68  % (22377)Termination reason: Refutation
% 1.27/0.68  
% 1.27/0.68  % (22377)Memory used [KB]: 1535
% 1.27/0.68  % (22377)Time elapsed: 0.060 s
% 1.27/0.68  % (22377)------------------------------
% 1.27/0.68  % (22377)------------------------------
% 1.27/0.68  % (22384)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 1.27/0.68  % (22376)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 1.27/0.68  % (22387)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 1.27/0.68  % (22202)Success in time 0.318 s
%------------------------------------------------------------------------------
