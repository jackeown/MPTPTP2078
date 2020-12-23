%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:47 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   10 (  10 expanded)
%              Number of leaves         :    3 (   3 expanded)
%              Depth                    :    5
%              Number of atoms          :   10 (  10 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,plain,(
    $false ),
    inference(subsumption_resolution,[],[f10,f7])).

fof(f7,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f10,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK0,sK1),sK1) ),
    inference(superposition,[],[f6,f8])).

fof(f8,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f6,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)),sK1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0,X1] : ~ r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:39:47 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.40  % (3684)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.20/0.41  % (3686)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.20/0.42  % (3681)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.20/0.42  % (3682)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.20/0.42  % (3681)Refutation found. Thanks to Tanya!
% 0.20/0.42  % SZS status Theorem for theBenchmark
% 0.20/0.42  % SZS output start Proof for theBenchmark
% 0.20/0.42  fof(f11,plain,(
% 0.20/0.42    $false),
% 0.20/0.42    inference(subsumption_resolution,[],[f10,f7])).
% 0.20/0.42  fof(f7,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f2])).
% 0.20/0.42  fof(f2,axiom,(
% 0.20/0.42    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.20/0.42  fof(f10,plain,(
% 0.20/0.42    ~r1_xboole_0(k4_xboole_0(sK0,sK1),sK1)),
% 0.20/0.42    inference(superposition,[],[f6,f8])).
% 0.20/0.42  fof(f8,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f1])).
% 0.20/0.42  fof(f1,axiom,(
% 0.20/0.42    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.20/0.42  fof(f6,plain,(
% 0.20/0.42    ~r1_xboole_0(k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)),sK1)),
% 0.20/0.42    inference(cnf_transformation,[],[f5])).
% 0.20/0.42  fof(f5,plain,(
% 0.20/0.42    ? [X0,X1] : ~r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1)),
% 0.20/0.42    inference(ennf_transformation,[],[f4])).
% 0.20/0.42  fof(f4,negated_conjecture,(
% 0.20/0.42    ~! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1)),
% 0.20/0.42    inference(negated_conjecture,[],[f3])).
% 0.20/0.42  fof(f3,conjecture,(
% 0.20/0.42    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1)),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_xboole_1)).
% 0.20/0.42  % SZS output end Proof for theBenchmark
% 0.20/0.42  % (3681)------------------------------
% 0.20/0.42  % (3681)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (3681)Termination reason: Refutation
% 0.20/0.42  
% 0.20/0.42  % (3681)Memory used [KB]: 10490
% 0.20/0.42  % (3681)Time elapsed: 0.004 s
% 0.20/0.42  % (3681)------------------------------
% 0.20/0.42  % (3681)------------------------------
% 0.20/0.42  % (3675)Success in time 0.073 s
%------------------------------------------------------------------------------
