%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:24 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   19 (  24 expanded)
%              Number of leaves         :    5 (   7 expanded)
%              Depth                    :    7
%              Number of atoms          :   35 (  47 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,plain,(
    $false ),
    inference(subsumption_resolution,[],[f18,f11])).

fof(f11,plain,(
    v1_finset_1(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( ~ v1_finset_1(k6_subset_1(sK0,sK1))
    & v1_finset_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f9])).

fof(f9,plain,
    ( ? [X0,X1] :
        ( ~ v1_finset_1(k6_subset_1(X0,X1))
        & v1_finset_1(X0) )
   => ( ~ v1_finset_1(k6_subset_1(sK0,sK1))
      & v1_finset_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ~ v1_finset_1(k6_subset_1(X0,X1))
      & v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_finset_1(X0)
       => v1_finset_1(k6_subset_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( v1_finset_1(X0)
     => v1_finset_1(k6_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_finset_1)).

fof(f18,plain,(
    ~ v1_finset_1(sK0) ),
    inference(resolution,[],[f17,f16])).

fof(f16,plain,(
    ~ v1_finset_1(k4_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f12,f14])).

fof(f14,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f12,plain,(
    ~ v1_finset_1(k6_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f17,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k4_xboole_0(X0,X1))
      | ~ v1_finset_1(X0) ) ),
    inference(resolution,[],[f15,f13])).

fof(f13,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v1_finset_1(X1)
      | v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( v1_finset_1(X0)
      | ~ v1_finset_1(X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( v1_finset_1(X0)
      | ~ v1_finset_1(X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_finset_1(X1)
        & r1_tarski(X0,X1) )
     => v1_finset_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_finset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:04:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.42  % (1243)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.19/0.45  % (1246)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.19/0.45  % (1246)Refutation not found, incomplete strategy% (1246)------------------------------
% 0.19/0.45  % (1246)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.45  % (1246)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.45  
% 0.19/0.45  % (1246)Memory used [KB]: 10490
% 0.19/0.45  % (1246)Time elapsed: 0.032 s
% 0.19/0.45  % (1246)------------------------------
% 0.19/0.45  % (1246)------------------------------
% 0.19/0.46  % (1238)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.19/0.46  % (1238)Refutation found. Thanks to Tanya!
% 0.19/0.46  % SZS status Theorem for theBenchmark
% 0.19/0.46  % SZS output start Proof for theBenchmark
% 0.19/0.46  fof(f19,plain,(
% 0.19/0.46    $false),
% 0.19/0.46    inference(subsumption_resolution,[],[f18,f11])).
% 0.19/0.46  fof(f11,plain,(
% 0.19/0.46    v1_finset_1(sK0)),
% 0.19/0.46    inference(cnf_transformation,[],[f10])).
% 0.19/0.46  fof(f10,plain,(
% 0.19/0.46    ~v1_finset_1(k6_subset_1(sK0,sK1)) & v1_finset_1(sK0)),
% 0.19/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f9])).
% 0.19/0.46  fof(f9,plain,(
% 0.19/0.46    ? [X0,X1] : (~v1_finset_1(k6_subset_1(X0,X1)) & v1_finset_1(X0)) => (~v1_finset_1(k6_subset_1(sK0,sK1)) & v1_finset_1(sK0))),
% 0.19/0.46    introduced(choice_axiom,[])).
% 0.19/0.46  fof(f6,plain,(
% 0.19/0.46    ? [X0,X1] : (~v1_finset_1(k6_subset_1(X0,X1)) & v1_finset_1(X0))),
% 0.19/0.46    inference(ennf_transformation,[],[f5])).
% 0.19/0.46  fof(f5,negated_conjecture,(
% 0.19/0.46    ~! [X0,X1] : (v1_finset_1(X0) => v1_finset_1(k6_subset_1(X0,X1)))),
% 0.19/0.46    inference(negated_conjecture,[],[f4])).
% 0.19/0.46  fof(f4,conjecture,(
% 0.19/0.46    ! [X0,X1] : (v1_finset_1(X0) => v1_finset_1(k6_subset_1(X0,X1)))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_finset_1)).
% 0.19/0.46  fof(f18,plain,(
% 0.19/0.46    ~v1_finset_1(sK0)),
% 0.19/0.46    inference(resolution,[],[f17,f16])).
% 0.19/0.46  fof(f16,plain,(
% 0.19/0.46    ~v1_finset_1(k4_xboole_0(sK0,sK1))),
% 0.19/0.46    inference(forward_demodulation,[],[f12,f14])).
% 0.19/0.46  fof(f14,plain,(
% 0.19/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f2])).
% 0.19/0.46  fof(f2,axiom,(
% 0.19/0.46    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.19/0.46  fof(f12,plain,(
% 0.19/0.46    ~v1_finset_1(k6_subset_1(sK0,sK1))),
% 0.19/0.46    inference(cnf_transformation,[],[f10])).
% 0.19/0.46  fof(f17,plain,(
% 0.19/0.46    ( ! [X0,X1] : (v1_finset_1(k4_xboole_0(X0,X1)) | ~v1_finset_1(X0)) )),
% 0.19/0.46    inference(resolution,[],[f15,f13])).
% 0.19/0.46  fof(f13,plain,(
% 0.19/0.46    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f1])).
% 0.19/0.46  fof(f1,axiom,(
% 0.19/0.46    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.19/0.46  fof(f15,plain,(
% 0.19/0.46    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v1_finset_1(X1) | v1_finset_1(X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f8])).
% 0.19/0.46  fof(f8,plain,(
% 0.19/0.46    ! [X0,X1] : (v1_finset_1(X0) | ~v1_finset_1(X1) | ~r1_tarski(X0,X1))),
% 0.19/0.46    inference(flattening,[],[f7])).
% 0.19/0.46  fof(f7,plain,(
% 0.19/0.46    ! [X0,X1] : (v1_finset_1(X0) | (~v1_finset_1(X1) | ~r1_tarski(X0,X1)))),
% 0.19/0.46    inference(ennf_transformation,[],[f3])).
% 0.19/0.46  fof(f3,axiom,(
% 0.19/0.46    ! [X0,X1] : ((v1_finset_1(X1) & r1_tarski(X0,X1)) => v1_finset_1(X0))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_finset_1)).
% 0.19/0.46  % SZS output end Proof for theBenchmark
% 0.19/0.46  % (1238)------------------------------
% 0.19/0.46  % (1238)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.46  % (1238)Termination reason: Refutation
% 0.19/0.46  
% 0.19/0.46  % (1238)Memory used [KB]: 1535
% 0.19/0.46  % (1238)Time elapsed: 0.051 s
% 0.19/0.46  % (1238)------------------------------
% 0.19/0.46  % (1238)------------------------------
% 0.19/0.46  % (1234)Success in time 0.107 s
%------------------------------------------------------------------------------
