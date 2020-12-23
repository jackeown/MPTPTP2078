%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:55 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   13 (  13 expanded)
%              Number of leaves         :    4 (   4 expanded)
%              Depth                    :    7
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f16])).

fof(f16,plain,(
    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2) ),
    inference(superposition,[],[f15,f12])).

fof(f12,plain,(
    ! [X2,X0,X1] : k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_enumset1)).

fof(f15,plain,(
    k1_enumset1(sK0,sK1,sK2) != k3_enumset1(sK0,sK0,sK0,sK1,sK2) ),
    inference(superposition,[],[f10,f13])).

fof(f13,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f10,plain,(
    k1_enumset1(sK0,sK1,sK2) != k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    k1_enumset1(sK0,sK1,sK2) != k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f8])).

fof(f8,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k4_enumset1(X0,X0,X0,X0,X1,X2)
   => k1_enumset1(sK0,sK1,sK2) != k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:45:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.44  % (4256)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.44  % (4261)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.45  % (4261)Refutation found. Thanks to Tanya!
% 0.20/0.45  % SZS status Theorem for theBenchmark
% 0.20/0.45  % SZS output start Proof for theBenchmark
% 0.20/0.45  fof(f17,plain,(
% 0.20/0.45    $false),
% 0.20/0.45    inference(trivial_inequality_removal,[],[f16])).
% 0.20/0.45  fof(f16,plain,(
% 0.20/0.45    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2)),
% 0.20/0.45    inference(superposition,[],[f15,f12])).
% 0.20/0.45  fof(f12,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f4])).
% 0.20/0.45  fof(f4,axiom,(
% 0.20/0.45    ! [X0,X1,X2] : k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_enumset1)).
% 0.20/0.45  fof(f15,plain,(
% 0.20/0.45    k1_enumset1(sK0,sK1,sK2) != k3_enumset1(sK0,sK0,sK0,sK1,sK2)),
% 0.20/0.45    inference(superposition,[],[f10,f13])).
% 0.20/0.45  fof(f13,plain,(
% 0.20/0.45    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f2])).
% 0.20/0.45  fof(f2,axiom,(
% 0.20/0.45    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.20/0.45  fof(f10,plain,(
% 0.20/0.45    k1_enumset1(sK0,sK1,sK2) != k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2)),
% 0.20/0.45    inference(cnf_transformation,[],[f9])).
% 0.20/0.45  fof(f9,plain,(
% 0.20/0.45    k1_enumset1(sK0,sK1,sK2) != k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2)),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f8])).
% 0.20/0.45  fof(f8,plain,(
% 0.20/0.45    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k4_enumset1(X0,X0,X0,X0,X1,X2) => k1_enumset1(sK0,sK1,sK2) != k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2)),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f7,plain,(
% 0.20/0.45    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k4_enumset1(X0,X0,X0,X0,X1,X2)),
% 0.20/0.45    inference(ennf_transformation,[],[f6])).
% 0.20/0.45  fof(f6,negated_conjecture,(
% 0.20/0.45    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)),
% 0.20/0.45    inference(negated_conjecture,[],[f5])).
% 0.20/0.45  fof(f5,conjecture,(
% 0.20/0.45    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_enumset1)).
% 0.20/0.45  % SZS output end Proof for theBenchmark
% 0.20/0.45  % (4261)------------------------------
% 0.20/0.45  % (4261)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (4261)Termination reason: Refutation
% 0.20/0.45  
% 0.20/0.45  % (4261)Memory used [KB]: 6012
% 0.20/0.45  % (4261)Time elapsed: 0.047 s
% 0.20/0.45  % (4261)------------------------------
% 0.20/0.45  % (4261)------------------------------
% 0.20/0.45  % (4244)Success in time 0.094 s
%------------------------------------------------------------------------------
