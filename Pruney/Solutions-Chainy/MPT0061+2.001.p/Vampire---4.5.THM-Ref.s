%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:15 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   10 (  10 expanded)
%              Number of leaves         :    3 (   3 expanded)
%              Depth                    :    6
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f9])).

fof(f9,plain,(
    k4_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f7,f8])).

fof(f8,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l36_xboole_1)).

fof(f7,plain,(
    k4_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    k4_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f4,f5])).

fof(f5,plain,
    ( ? [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) != k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))
   => k4_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)) ),
    introduced(choice_axiom,[])).

fof(f4,plain,(
    ? [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) != k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:47:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (28891)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.20/0.44  % (28888)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.20/0.44  % (28888)Refutation found. Thanks to Tanya!
% 0.20/0.44  % SZS status Theorem for theBenchmark
% 0.20/0.44  % SZS output start Proof for theBenchmark
% 0.20/0.45  fof(f10,plain,(
% 0.20/0.45    $false),
% 0.20/0.45    inference(trivial_inequality_removal,[],[f9])).
% 0.20/0.45  fof(f9,plain,(
% 0.20/0.45    k4_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.20/0.45    inference(superposition,[],[f7,f8])).
% 0.20/0.45  fof(f8,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f1])).
% 0.20/0.45  fof(f1,axiom,(
% 0.20/0.45    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l36_xboole_1)).
% 0.20/0.45  fof(f7,plain,(
% 0.20/0.45    k4_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),
% 0.20/0.45    inference(cnf_transformation,[],[f6])).
% 0.20/0.45  fof(f6,plain,(
% 0.20/0.45    k4_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f4,f5])).
% 0.20/0.45  fof(f5,plain,(
% 0.20/0.45    ? [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) != k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) => k4_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f4,plain,(
% 0.20/0.45    ? [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) != k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 0.20/0.45    inference(ennf_transformation,[],[f3])).
% 0.20/0.45  fof(f3,negated_conjecture,(
% 0.20/0.45    ~! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 0.20/0.45    inference(negated_conjecture,[],[f2])).
% 0.20/0.45  fof(f2,conjecture,(
% 0.20/0.45    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_xboole_1)).
% 0.20/0.45  % SZS output end Proof for theBenchmark
% 0.20/0.45  % (28888)------------------------------
% 0.20/0.45  % (28888)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (28888)Termination reason: Refutation
% 0.20/0.45  
% 0.20/0.45  % (28888)Memory used [KB]: 6012
% 0.20/0.45  % (28888)Time elapsed: 0.003 s
% 0.20/0.45  % (28888)------------------------------
% 0.20/0.45  % (28888)------------------------------
% 0.20/0.45  % (28889)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.20/0.45  % (28883)Success in time 0.093 s
%------------------------------------------------------------------------------
