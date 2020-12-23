%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:45 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   26 (  32 expanded)
%              Number of leaves         :    6 (   8 expanded)
%              Depth                    :   10
%              Number of atoms          :   45 (  55 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f37,plain,(
    $false ),
    inference(subsumption_resolution,[],[f36,f22])).

fof(f22,plain,(
    ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_zfmisc_1)).

fof(f36,plain,(
    ~ r1_tarski(k1_tarski(sK0),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f34,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f34,plain,(
    ~ m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(resolution,[],[f32,f18])).

fof(f18,plain,(
    ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f16])).

fof(f16,plain,
    ( ? [X0] : ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0)))
   => ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] : ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_setfam_1)).

fof(f32,plain,(
    ! [X0] :
      ( m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(superposition,[],[f21,f31])).

fof(f31,plain,(
    ! [X0] : k1_tarski(k1_xboole_0) = k7_setfam_1(X0,k1_tarski(X0)) ),
    inference(subsumption_resolution,[],[f29,f22])).

fof(f29,plain,(
    ! [X0] :
      ( k1_tarski(k1_xboole_0) = k7_setfam_1(X0,k1_tarski(X0))
      | ~ r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f24,f19])).

fof(f24,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_tarski(k1_xboole_0) = k7_setfam_1(X0,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f20])).

% (17233)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f20,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_xboole_0) = k7_setfam_1(X0,X1)
      | k1_tarski(X0) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_xboole_0) = k7_setfam_1(X0,X1)
      | k1_tarski(X0) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_xboole_0) = k7_setfam_1(X0,X1)
      | k1_tarski(X0) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( k1_tarski(X0) = X1
       => k1_tarski(k1_xboole_0) = k7_setfam_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_setfam_1)).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:30:14 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (17235)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.50  % (17252)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.50  % (17245)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (17245)Refutation not found, incomplete strategy% (17245)------------------------------
% 0.21/0.51  % (17245)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (17245)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (17245)Memory used [KB]: 6140
% 0.21/0.51  % (17245)Time elapsed: 0.055 s
% 0.21/0.51  % (17245)------------------------------
% 0.21/0.51  % (17245)------------------------------
% 0.21/0.51  % (17237)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (17255)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.51  % (17252)Refutation not found, incomplete strategy% (17252)------------------------------
% 0.21/0.51  % (17252)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (17252)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (17252)Memory used [KB]: 10618
% 0.21/0.51  % (17252)Time elapsed: 0.055 s
% 0.21/0.51  % (17252)------------------------------
% 0.21/0.51  % (17252)------------------------------
% 0.21/0.51  % (17235)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(subsumption_resolution,[],[f36,f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ( ! [X0] : (r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_zfmisc_1)).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ~r1_tarski(k1_tarski(sK0),k1_zfmisc_1(sK0))),
% 0.21/0.51    inference(resolution,[],[f34,f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.21/0.51    inference(unused_predicate_definition_removal,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ~m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.51    inference(resolution,[],[f32,f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ? [X0] : ~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) => ~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ? [X0] : ~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,negated_conjecture,(
% 0.21/0.51    ~! [X0] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0)))),
% 0.21/0.51    inference(negated_conjecture,[],[f8])).
% 0.21/0.51  fof(f8,conjecture,(
% 0.21/0.51    ! [X0] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_setfam_1)).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ( ! [X0] : (m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(k1_tarski(X0),k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.51    inference(superposition,[],[f21,f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ( ! [X0] : (k1_tarski(k1_xboole_0) = k7_setfam_1(X0,k1_tarski(X0))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f29,f22])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ( ! [X0] : (k1_tarski(k1_xboole_0) = k7_setfam_1(X0,k1_tarski(X0)) | ~r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.51    inference(resolution,[],[f24,f19])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(k1_tarski(X0),k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_tarski(k1_xboole_0) = k7_setfam_1(X0,k1_tarski(X0))) )),
% 0.21/0.51    inference(equality_resolution,[],[f20])).
% 0.21/0.51  % (17233)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_tarski(k1_xboole_0) = k7_setfam_1(X0,X1) | k1_tarski(X0) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0,X1] : (k1_tarski(k1_xboole_0) = k7_setfam_1(X0,X1) | k1_tarski(X0) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.51    inference(flattening,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0,X1] : ((k1_tarski(k1_xboole_0) = k7_setfam_1(X0,X1) | k1_tarski(X0) != X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k1_tarski(X0) = X1 => k1_tarski(k1_xboole_0) = k7_setfam_1(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_setfam_1)).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ( ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (17235)------------------------------
% 0.21/0.51  % (17235)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (17235)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (17235)Memory used [KB]: 6140
% 0.21/0.51  % (17235)Time elapsed: 0.094 s
% 0.21/0.51  % (17235)------------------------------
% 0.21/0.51  % (17235)------------------------------
% 0.21/0.51  % (17229)Success in time 0.15 s
%------------------------------------------------------------------------------
