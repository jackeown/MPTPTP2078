%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:24 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   25 (  42 expanded)
%              Number of leaves         :    5 (  12 expanded)
%              Depth                    :   13
%              Number of atoms          :   52 (  85 expanded)
%              Number of equality atoms :   51 (  84 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f62,plain,(
    $false ),
    inference(subsumption_resolution,[],[f54,f14])).

fof(f14,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f54,plain,(
    k1_xboole_0 != k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f36,f47])).

fof(f47,plain,(
    k1_xboole_0 = k2_tarski(sK1,sK1) ),
    inference(subsumption_resolution,[],[f46,f13])).

fof(f13,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1))
        | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 != X0
       => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
          & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
     => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
        & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).

fof(f46,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = k2_tarski(sK1,sK1) ),
    inference(trivial_inequality_removal,[],[f45])).

fof(f45,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k2_tarski(sK1,sK1) ),
    inference(duplicate_literal_removal,[],[f44])).

fof(f44,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k2_tarski(sK1,sK1)
    | k1_xboole_0 = k2_tarski(sK1,sK1) ),
    inference(superposition,[],[f16,f43])).

fof(f43,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_tarski(sK1,sK1),sK0)
    | k1_xboole_0 = k2_tarski(sK1,sK1) ),
    inference(subsumption_resolution,[],[f42,f13])).

fof(f42,plain,
    ( k1_xboole_0 = k2_tarski(sK1,sK1)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k2_zfmisc_1(k2_tarski(sK1,sK1),sK0) ),
    inference(trivial_inequality_removal,[],[f41])).

fof(f41,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_tarski(sK1,sK1)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k2_zfmisc_1(k2_tarski(sK1,sK1),sK0) ),
    inference(superposition,[],[f16,f27])).

fof(f27,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,k2_tarski(sK1,sK1))
    | k1_xboole_0 = k2_zfmisc_1(k2_tarski(sK1,sK1),sK0) ),
    inference(definition_unfolding,[],[f12,f15,f15])).

fof(f15,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

% (28382)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f12,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0)
    | k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f36,plain,(
    ! [X1] : k2_tarski(X1,X1) != k4_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X1)) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k2_tarski(X0,X0) != k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1)) ) ),
    inference(definition_unfolding,[],[f20,f15,f15,f15])).

fof(f20,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:35:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.57  % (28384)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.57  % (28368)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.57  % (28372)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.58  % (28376)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.58  % (28359)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.58  % (28371)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.59  % (28370)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.59  % (28388)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.59  % (28380)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.59  % (28380)Refutation found. Thanks to Tanya!
% 0.21/0.59  % SZS status Theorem for theBenchmark
% 0.21/0.59  % (28376)Refutation not found, incomplete strategy% (28376)------------------------------
% 0.21/0.59  % (28376)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (28376)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.59  
% 0.21/0.59  % (28376)Memory used [KB]: 10618
% 0.21/0.59  % (28376)Time elapsed: 0.157 s
% 0.21/0.59  % (28376)------------------------------
% 0.21/0.59  % (28376)------------------------------
% 0.21/0.59  % SZS output start Proof for theBenchmark
% 0.21/0.59  fof(f62,plain,(
% 0.21/0.59    $false),
% 0.21/0.59    inference(subsumption_resolution,[],[f54,f14])).
% 0.21/0.59  fof(f14,plain,(
% 0.21/0.59    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f1])).
% 0.21/0.59  fof(f1,axiom,(
% 0.21/0.59    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 0.21/0.59  fof(f54,plain,(
% 0.21/0.59    k1_xboole_0 != k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.21/0.59    inference(superposition,[],[f36,f47])).
% 0.21/0.59  fof(f47,plain,(
% 0.21/0.59    k1_xboole_0 = k2_tarski(sK1,sK1)),
% 0.21/0.59    inference(subsumption_resolution,[],[f46,f13])).
% 0.21/0.59  fof(f13,plain,(
% 0.21/0.59    k1_xboole_0 != sK0),
% 0.21/0.59    inference(cnf_transformation,[],[f9])).
% 0.21/0.59  fof(f9,plain,(
% 0.21/0.59    ? [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0)) & k1_xboole_0 != X0)),
% 0.21/0.59    inference(ennf_transformation,[],[f8])).
% 0.21/0.59  fof(f8,negated_conjecture,(
% 0.21/0.59    ~! [X0,X1] : (k1_xboole_0 != X0 => (k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)))),
% 0.21/0.59    inference(negated_conjecture,[],[f7])).
% 0.21/0.59  fof(f7,conjecture,(
% 0.21/0.59    ! [X0,X1] : (k1_xboole_0 != X0 => (k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).
% 0.21/0.59  fof(f46,plain,(
% 0.21/0.59    k1_xboole_0 = sK0 | k1_xboole_0 = k2_tarski(sK1,sK1)),
% 0.21/0.59    inference(trivial_inequality_removal,[],[f45])).
% 0.21/0.59  fof(f45,plain,(
% 0.21/0.59    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_tarski(sK1,sK1)),
% 0.21/0.59    inference(duplicate_literal_removal,[],[f44])).
% 0.21/0.59  fof(f44,plain,(
% 0.21/0.59    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_tarski(sK1,sK1) | k1_xboole_0 = k2_tarski(sK1,sK1)),
% 0.21/0.59    inference(superposition,[],[f16,f43])).
% 0.21/0.59  fof(f43,plain,(
% 0.21/0.59    k1_xboole_0 = k2_zfmisc_1(k2_tarski(sK1,sK1),sK0) | k1_xboole_0 = k2_tarski(sK1,sK1)),
% 0.21/0.59    inference(subsumption_resolution,[],[f42,f13])).
% 0.21/0.59  fof(f42,plain,(
% 0.21/0.59    k1_xboole_0 = k2_tarski(sK1,sK1) | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(k2_tarski(sK1,sK1),sK0)),
% 0.21/0.59    inference(trivial_inequality_removal,[],[f41])).
% 0.21/0.59  fof(f41,plain,(
% 0.21/0.59    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_tarski(sK1,sK1) | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(k2_tarski(sK1,sK1),sK0)),
% 0.21/0.59    inference(superposition,[],[f16,f27])).
% 0.21/0.59  fof(f27,plain,(
% 0.21/0.59    k1_xboole_0 = k2_zfmisc_1(sK0,k2_tarski(sK1,sK1)) | k1_xboole_0 = k2_zfmisc_1(k2_tarski(sK1,sK1),sK0)),
% 0.21/0.59    inference(definition_unfolding,[],[f12,f15,f15])).
% 0.21/0.59  fof(f15,plain,(
% 0.21/0.59    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f2])).
% 0.21/0.59  % (28382)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.59  fof(f2,axiom,(
% 0.21/0.59    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.59  fof(f12,plain,(
% 0.21/0.59    k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0) | k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1))),
% 0.21/0.59    inference(cnf_transformation,[],[f9])).
% 0.21/0.59  fof(f16,plain,(
% 0.21/0.59    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.59    inference(cnf_transformation,[],[f3])).
% 0.21/0.59  fof(f3,axiom,(
% 0.21/0.59    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.59  fof(f36,plain,(
% 0.21/0.59    ( ! [X1] : (k2_tarski(X1,X1) != k4_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X1))) )),
% 0.21/0.59    inference(equality_resolution,[],[f28])).
% 0.21/0.59  fof(f28,plain,(
% 0.21/0.59    ( ! [X0,X1] : (X0 != X1 | k2_tarski(X0,X0) != k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1))) )),
% 0.21/0.59    inference(definition_unfolding,[],[f20,f15,f15,f15])).
% 0.21/0.59  fof(f20,plain,(
% 0.21/0.59    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.21/0.59    inference(cnf_transformation,[],[f4])).
% 0.21/0.59  fof(f4,axiom,(
% 0.21/0.59    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.21/0.59  % SZS output end Proof for theBenchmark
% 0.21/0.59  % (28380)------------------------------
% 0.21/0.59  % (28380)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (28380)Termination reason: Refutation
% 0.21/0.59  
% 0.21/0.59  % (28380)Memory used [KB]: 1663
% 0.21/0.59  % (28380)Time elapsed: 0.147 s
% 0.21/0.59  % (28380)------------------------------
% 0.21/0.59  % (28380)------------------------------
% 0.21/0.60  % (28358)Success in time 0.228 s
%------------------------------------------------------------------------------
