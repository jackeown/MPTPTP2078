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
% DateTime   : Thu Dec  3 13:08:24 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   15 (  20 expanded)
%              Number of leaves         :    4 (   6 expanded)
%              Depth                    :    7
%              Number of atoms          :   25 (  37 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,plain,(
    $false ),
    inference(resolution,[],[f14,f9])).

fof(f9,plain,(
    v1_finset_1(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,
    ( ~ v1_finset_1(k6_subset_1(sK0,sK1))
    & v1_finset_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f5,f7])).

fof(f7,plain,
    ( ? [X0,X1] :
        ( ~ v1_finset_1(k6_subset_1(X0,X1))
        & v1_finset_1(X0) )
   => ( ~ v1_finset_1(k6_subset_1(sK0,sK1))
      & v1_finset_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1] :
      ( ~ v1_finset_1(k6_subset_1(X0,X1))
      & v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_finset_1(X0)
       => v1_finset_1(k6_subset_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( v1_finset_1(X0)
     => v1_finset_1(k6_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_finset_1)).

fof(f14,plain,(
    ~ v1_finset_1(sK0) ),
    inference(resolution,[],[f12,f13])).

fof(f13,plain,(
    ~ v1_finset_1(k4_xboole_0(sK0,sK1)) ),
    inference(definition_unfolding,[],[f10,f11])).

fof(f11,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f10,plain,(
    ~ v1_finset_1(k6_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f12,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k4_xboole_0(X0,X1))
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k4_xboole_0(X0,X1))
      | ~ v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_finset_1(X0)
     => v1_finset_1(k4_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_finset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:13:07 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.21/0.47  % (8079)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (8080)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (8078)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (8077)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (8078)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(resolution,[],[f14,f9])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    v1_finset_1(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ~v1_finset_1(k6_subset_1(sK0,sK1)) & v1_finset_1(sK0)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f5,f7])).
% 0.21/0.47  fof(f7,plain,(
% 0.21/0.47    ? [X0,X1] : (~v1_finset_1(k6_subset_1(X0,X1)) & v1_finset_1(X0)) => (~v1_finset_1(k6_subset_1(sK0,sK1)) & v1_finset_1(sK0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f5,plain,(
% 0.21/0.47    ? [X0,X1] : (~v1_finset_1(k6_subset_1(X0,X1)) & v1_finset_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1] : (v1_finset_1(X0) => v1_finset_1(k6_subset_1(X0,X1)))),
% 0.21/0.47    inference(negated_conjecture,[],[f3])).
% 0.21/0.47  fof(f3,conjecture,(
% 0.21/0.47    ! [X0,X1] : (v1_finset_1(X0) => v1_finset_1(k6_subset_1(X0,X1)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_finset_1)).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ~v1_finset_1(sK0)),
% 0.21/0.47    inference(resolution,[],[f12,f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ~v1_finset_1(k4_xboole_0(sK0,sK1))),
% 0.21/0.47    inference(definition_unfolding,[],[f10,f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k4_xboole_0(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ~v1_finset_1(k6_subset_1(sK0,sK1))),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v1_finset_1(k4_xboole_0(X0,X1)) | ~v1_finset_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,plain,(
% 0.21/0.47    ! [X0,X1] : (v1_finset_1(k4_xboole_0(X0,X1)) | ~v1_finset_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : (v1_finset_1(X0) => v1_finset_1(k4_xboole_0(X0,X1)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_finset_1)).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (8078)------------------------------
% 0.21/0.47  % (8078)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (8078)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (8078)Memory used [KB]: 6012
% 0.21/0.47  % (8078)Time elapsed: 0.051 s
% 0.21/0.47  % (8078)------------------------------
% 0.21/0.47  % (8078)------------------------------
% 0.21/0.47  % (8073)Success in time 0.111 s
%------------------------------------------------------------------------------
