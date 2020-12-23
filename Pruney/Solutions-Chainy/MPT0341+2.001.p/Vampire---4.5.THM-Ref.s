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
% DateTime   : Thu Dec  3 12:43:39 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   12 (  12 expanded)
%              Number of leaves         :    4 (   4 expanded)
%              Depth                    :    5
%              Number of atoms          :   13 (  13 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    4 (   2 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,plain,(
    $false ),
    inference(resolution,[],[f11,f8])).

fof(f8,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f5,f6])).

fof(f6,plain,
    ( ? [X0] : ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
   => ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0] : ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f11,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f10,f9])).

fof(f9,plain,(
    ! [X0] : k1_subset_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k1_subset_1(X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(f10,plain,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_subset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:19:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.23/0.42  % (25014)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.23/0.47  % (25017)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.23/0.47  % (25017)Refutation found. Thanks to Tanya!
% 0.23/0.47  % SZS status Theorem for theBenchmark
% 0.23/0.47  % SZS output start Proof for theBenchmark
% 0.23/0.47  fof(f12,plain,(
% 0.23/0.47    $false),
% 0.23/0.47    inference(resolution,[],[f11,f8])).
% 0.23/0.47  fof(f8,plain,(
% 0.23/0.47    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))),
% 0.23/0.47    inference(cnf_transformation,[],[f7])).
% 0.23/0.47  fof(f7,plain,(
% 0.23/0.47    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))),
% 0.23/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f5,f6])).
% 0.23/0.47  fof(f6,plain,(
% 0.23/0.47    ? [X0] : ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) => ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))),
% 0.23/0.47    introduced(choice_axiom,[])).
% 0.23/0.47  fof(f5,plain,(
% 0.23/0.47    ? [X0] : ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.23/0.47    inference(ennf_transformation,[],[f4])).
% 0.23/0.47  fof(f4,negated_conjecture,(
% 0.23/0.47    ~! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.23/0.47    inference(negated_conjecture,[],[f3])).
% 0.23/0.47  fof(f3,conjecture,(
% 0.23/0.47    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.23/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.23/0.47  fof(f11,plain,(
% 0.23/0.47    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.23/0.47    inference(forward_demodulation,[],[f10,f9])).
% 0.23/0.47  fof(f9,plain,(
% 0.23/0.47    ( ! [X0] : (k1_subset_1(X0) = k1_xboole_0) )),
% 0.23/0.47    inference(cnf_transformation,[],[f1])).
% 0.23/0.47  fof(f1,axiom,(
% 0.23/0.47    ! [X0] : k1_subset_1(X0) = k1_xboole_0),
% 0.23/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).
% 0.23/0.47  fof(f10,plain,(
% 0.23/0.47    ( ! [X0] : (m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.23/0.47    inference(cnf_transformation,[],[f2])).
% 0.23/0.47  fof(f2,axiom,(
% 0.23/0.47    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))),
% 0.23/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_subset_1)).
% 0.23/0.47  % SZS output end Proof for theBenchmark
% 0.23/0.47  % (25017)------------------------------
% 0.23/0.47  % (25017)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.47  % (25017)Termination reason: Refutation
% 0.23/0.47  
% 0.23/0.47  % (25017)Memory used [KB]: 1535
% 0.23/0.47  % (25017)Time elapsed: 0.056 s
% 0.23/0.47  % (25017)------------------------------
% 0.23/0.47  % (25017)------------------------------
% 0.23/0.47  % (25022)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.23/0.47  % (25019)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.23/0.48  % (25013)Success in time 0.108 s
%------------------------------------------------------------------------------
