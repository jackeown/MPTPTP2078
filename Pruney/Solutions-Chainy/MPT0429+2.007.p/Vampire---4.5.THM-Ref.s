%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   41 ( 308 expanded)
%              Number of leaves         :   10 (  97 expanded)
%              Depth                    :   13
%              Number of atoms          :   54 ( 360 expanded)
%              Number of equality atoms :   29 ( 264 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f99,plain,(
    $false ),
    inference(subsumption_resolution,[],[f87,f98])).

fof(f98,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f82,f91])).

fof(f91,plain,(
    k1_xboole_0 = k1_zfmisc_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f80,f88])).

fof(f88,plain,(
    k1_xboole_0 = sK0 ),
    inference(forward_demodulation,[],[f86,f26])).

fof(f26,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(f86,plain,(
    k3_tarski(k1_xboole_0) = sK0 ),
    inference(superposition,[],[f29,f80])).

fof(f29,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f80,plain,(
    k1_xboole_0 = k1_zfmisc_1(sK0) ),
    inference(resolution,[],[f79,f62])).

fof(f62,plain,(
    ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(backward_demodulation,[],[f48,f49])).

fof(f49,plain,(
    k1_zfmisc_1(k1_xboole_0) = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f27,f47])).

fof(f47,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f30,f46])).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f32,f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f42,f43])).

fof(f43,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f42,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f32,plain,(
    ! [X0,X1] : k4_enumset1(X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_enumset1(X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_enumset1)).

fof(f30,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f27,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).

fof(f48,plain,(
    ~ m1_subset_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(definition_unfolding,[],[f25,f47])).

fof(f25,plain,(
    ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] : ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_setfam_1)).

fof(f79,plain,(
    ! [X0] :
      ( m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 = k1_zfmisc_1(X0) ) ),
    inference(resolution,[],[f78,f28])).

fof(f28,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f78,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,X0)
      | k1_xboole_0 = X0
      | m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f50,f49])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(definition_unfolding,[],[f33,f47])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k1_xboole_0 = X0
      | m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ( k1_xboole_0 != X0
       => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).

fof(f82,plain,(
    ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f62,f80])).

fof(f87,plain,(
    m1_subset_1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f28,f80])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:35:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (32337)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.49  % (32329)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.49  % (32337)Refutation not found, incomplete strategy% (32337)------------------------------
% 0.21/0.49  % (32337)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (32321)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.50  % (32337)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (32337)Memory used [KB]: 10746
% 0.21/0.50  % (32337)Time elapsed: 0.062 s
% 0.21/0.50  % (32337)------------------------------
% 0.21/0.50  % (32337)------------------------------
% 0.21/0.50  % (32338)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.50  % (32321)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % (32323)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (32319)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f99,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(subsumption_resolution,[],[f87,f98])).
% 0.21/0.51  fof(f98,plain,(
% 0.21/0.51    ~m1_subset_1(k1_xboole_0,k1_xboole_0)),
% 0.21/0.51    inference(backward_demodulation,[],[f82,f91])).
% 0.21/0.51  fof(f91,plain,(
% 0.21/0.51    k1_xboole_0 = k1_zfmisc_1(k1_xboole_0)),
% 0.21/0.51    inference(backward_demodulation,[],[f80,f88])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    k1_xboole_0 = sK0),
% 0.21/0.51    inference(forward_demodulation,[],[f86,f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    k3_tarski(k1_xboole_0) = sK0),
% 0.21/0.51    inference(superposition,[],[f29,f80])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    k1_xboole_0 = k1_zfmisc_1(sK0)),
% 0.21/0.51    inference(resolution,[],[f79,f62])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    ~m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.51    inference(backward_demodulation,[],[f48,f49])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    k1_zfmisc_1(k1_xboole_0) = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.21/0.51    inference(definition_unfolding,[],[f27,f47])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f30,f46])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f32,f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f42,f43])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k4_enumset1(X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1] : k4_enumset1(X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_enumset1)).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 0.21/0.51    inference(cnf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ~m1_subset_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.51    inference(definition_unfolding,[],[f25,f47])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ? [X0] : ~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,negated_conjecture,(
% 0.21/0.51    ~! [X0] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0)))),
% 0.21/0.51    inference(negated_conjecture,[],[f15])).
% 0.21/0.51  fof(f15,conjecture,(
% 0.21/0.51    ! [X0] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_setfam_1)).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    ( ! [X0] : (m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 = k1_zfmisc_1(X0)) )),
% 0.21/0.51    inference(resolution,[],[f78,f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,axiom,(
% 0.21/0.51    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(k1_xboole_0,X0) | k1_xboole_0 = X0 | m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(X0))) )),
% 0.21/0.51    inference(superposition,[],[f50,f49])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ( ! [X0,X1] : (m1_subset_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f33,f47])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k1_xboole_0 = X0 | m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0))),
% 0.21/0.51    inference(flattening,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0) | ~m1_subset_1(X1,X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X1,X0) => (k1_xboole_0 != X0 => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    ~m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.51    inference(backward_demodulation,[],[f62,f80])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    m1_subset_1(k1_xboole_0,k1_xboole_0)),
% 0.21/0.51    inference(superposition,[],[f28,f80])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (32321)------------------------------
% 0.21/0.51  % (32321)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (32321)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (32321)Memory used [KB]: 6268
% 0.21/0.51  % (32321)Time elapsed: 0.066 s
% 0.21/0.51  % (32321)------------------------------
% 0.21/0.51  % (32321)------------------------------
% 0.21/0.51  % (32319)Refutation not found, incomplete strategy% (32319)------------------------------
% 0.21/0.51  % (32319)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (32319)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (32319)Memory used [KB]: 6140
% 0.21/0.51  % (32319)Time elapsed: 0.109 s
% 0.21/0.51  % (32319)------------------------------
% 0.21/0.51  % (32319)------------------------------
% 0.21/0.51  % (32314)Success in time 0.153 s
%------------------------------------------------------------------------------
