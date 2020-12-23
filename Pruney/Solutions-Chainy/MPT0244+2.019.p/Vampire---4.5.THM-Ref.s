%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:44 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   32 ( 115 expanded)
%              Number of leaves         :    4 (  36 expanded)
%              Depth                    :   11
%              Number of atoms          :   64 ( 183 expanded)
%              Number of equality atoms :   40 ( 143 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f65,plain,(
    $false ),
    inference(subsumption_resolution,[],[f63,f35])).

fof(f35,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k1_enumset1(X1,X1,X1)) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | r1_tarski(X0,k1_enumset1(X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f15,f22])).

fof(f22,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f12,f13])).

fof(f13,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f12,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f63,plain,(
    ~ r1_tarski(k1_xboole_0,k1_enumset1(sK1,sK1,sK1)) ),
    inference(trivial_inequality_removal,[],[f62])).

fof(f62,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k1_enumset1(sK1,sK1,sK1)) ),
    inference(backward_demodulation,[],[f41,f60])).

fof(f60,plain,(
    k1_xboole_0 = sK0 ),
    inference(global_subsumption,[],[f40,f49,f54])).

fof(f54,plain,
    ( r1_tarski(sK0,sK0)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f34,f49])).

fof(f34,plain,(
    ! [X1] : r1_tarski(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1)) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_enumset1(X1,X1,X1) != X0
      | r1_tarski(X0,k1_enumset1(X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f16,f22,f22])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) != X0
      | r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f49,plain,
    ( sK0 = k1_enumset1(sK1,sK1,sK1)
    | k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f48])).

fof(f48,plain,
    ( sK0 = k1_enumset1(sK1,sK1,sK1)
    | k1_xboole_0 = sK0
    | sK0 = k1_enumset1(sK1,sK1,sK1)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f28,f23])).

fof(f23,plain,
    ( r1_tarski(sK0,k1_enumset1(sK1,sK1,sK1))
    | sK0 = k1_enumset1(sK1,sK1,sK1)
    | k1_xboole_0 = sK0 ),
    inference(definition_unfolding,[],[f11,f22,f22])).

fof(f11,plain,
    ( k1_xboole_0 = sK0
    | sK0 = k1_tarski(sK1)
    | r1_tarski(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <~> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,k1_tarski(X1))
      <=> ( k1_tarski(X1) = X0
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_zfmisc_1)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_enumset1(X1,X1,X1))
      | k1_enumset1(X1,X1,X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f14,f22,f22])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f40,plain,
    ( ~ r1_tarski(sK0,sK0)
    | sK0 != k1_enumset1(sK1,sK1,sK1) ),
    inference(inner_rewriting,[],[f24])).

fof(f24,plain,
    ( sK0 != k1_enumset1(sK1,sK1,sK1)
    | ~ r1_tarski(sK0,k1_enumset1(sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f10,f22,f22])).

fof(f10,plain,
    ( sK0 != k1_tarski(sK1)
    | ~ r1_tarski(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f41,plain,
    ( k1_xboole_0 != sK0
    | ~ r1_tarski(k1_xboole_0,k1_enumset1(sK1,sK1,sK1)) ),
    inference(inner_rewriting,[],[f25])).

fof(f25,plain,
    ( k1_xboole_0 != sK0
    | ~ r1_tarski(sK0,k1_enumset1(sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f9,f22])).

fof(f9,plain,
    ( k1_xboole_0 != sK0
    | ~ r1_tarski(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f7])).

% (13872)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% (13865)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% (13864)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% (13883)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% (13884)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% (13878)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% (13862)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% (13874)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% (13876)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% (13866)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% (13888)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% (13885)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n013.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:17:54 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (13890)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.51  % (13882)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.51  % (13863)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (13867)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.51  % (13867)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f65,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(subsumption_resolution,[],[f63,f35])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ( ! [X1] : (r1_tarski(k1_xboole_0,k1_enumset1(X1,X1,X1))) )),
% 0.22/0.51    inference(equality_resolution,[],[f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k1_xboole_0 != X0 | r1_tarski(X0,k1_enumset1(X1,X1,X1))) )),
% 0.22/0.51    inference(definition_unfolding,[],[f15,f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.22/0.51    inference(definition_unfolding,[],[f12,f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k1_xboole_0 != X0 | r1_tarski(X0,k1_tarski(X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.22/0.51  fof(f63,plain,(
% 0.22/0.51    ~r1_tarski(k1_xboole_0,k1_enumset1(sK1,sK1,sK1))),
% 0.22/0.51    inference(trivial_inequality_removal,[],[f62])).
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    k1_xboole_0 != k1_xboole_0 | ~r1_tarski(k1_xboole_0,k1_enumset1(sK1,sK1,sK1))),
% 0.22/0.51    inference(backward_demodulation,[],[f41,f60])).
% 0.22/0.51  fof(f60,plain,(
% 0.22/0.51    k1_xboole_0 = sK0),
% 0.22/0.51    inference(global_subsumption,[],[f40,f49,f54])).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    r1_tarski(sK0,sK0) | k1_xboole_0 = sK0),
% 0.22/0.51    inference(superposition,[],[f34,f49])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ( ! [X1] : (r1_tarski(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1))) )),
% 0.22/0.51    inference(equality_resolution,[],[f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k1_enumset1(X1,X1,X1) != X0 | r1_tarski(X0,k1_enumset1(X1,X1,X1))) )),
% 0.22/0.51    inference(definition_unfolding,[],[f16,f22,f22])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k1_tarski(X1) != X0 | r1_tarski(X0,k1_tarski(X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f3])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    sK0 = k1_enumset1(sK1,sK1,sK1) | k1_xboole_0 = sK0),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f48])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    sK0 = k1_enumset1(sK1,sK1,sK1) | k1_xboole_0 = sK0 | sK0 = k1_enumset1(sK1,sK1,sK1) | k1_xboole_0 = sK0),
% 0.22/0.51    inference(resolution,[],[f28,f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    r1_tarski(sK0,k1_enumset1(sK1,sK1,sK1)) | sK0 = k1_enumset1(sK1,sK1,sK1) | k1_xboole_0 = sK0),
% 0.22/0.51    inference(definition_unfolding,[],[f11,f22,f22])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    k1_xboole_0 = sK0 | sK0 = k1_tarski(sK1) | r1_tarski(sK0,k1_tarski(sK1))),
% 0.22/0.51    inference(cnf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,plain,(
% 0.22/0.51    ? [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <~> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.22/0.51    inference(negated_conjecture,[],[f5])).
% 0.22/0.51  fof(f5,conjecture,(
% 0.22/0.51    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_zfmisc_1)).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_tarski(X0,k1_enumset1(X1,X1,X1)) | k1_enumset1(X1,X1,X1) = X0 | k1_xboole_0 = X0) )),
% 0.22/0.51    inference(definition_unfolding,[],[f14,f22,f22])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f3])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ~r1_tarski(sK0,sK0) | sK0 != k1_enumset1(sK1,sK1,sK1)),
% 0.22/0.51    inference(inner_rewriting,[],[f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    sK0 != k1_enumset1(sK1,sK1,sK1) | ~r1_tarski(sK0,k1_enumset1(sK1,sK1,sK1))),
% 0.22/0.51    inference(definition_unfolding,[],[f10,f22,f22])).
% 0.22/0.51  fof(f10,plain,(
% 0.22/0.51    sK0 != k1_tarski(sK1) | ~r1_tarski(sK0,k1_tarski(sK1))),
% 0.22/0.51    inference(cnf_transformation,[],[f7])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    k1_xboole_0 != sK0 | ~r1_tarski(k1_xboole_0,k1_enumset1(sK1,sK1,sK1))),
% 0.22/0.51    inference(inner_rewriting,[],[f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    k1_xboole_0 != sK0 | ~r1_tarski(sK0,k1_enumset1(sK1,sK1,sK1))),
% 0.22/0.51    inference(definition_unfolding,[],[f9,f22])).
% 0.22/0.51  fof(f9,plain,(
% 0.22/0.51    k1_xboole_0 != sK0 | ~r1_tarski(sK0,k1_tarski(sK1))),
% 0.22/0.51    inference(cnf_transformation,[],[f7])).
% 0.22/0.52  % (13872)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.52  % (13865)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (13864)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (13883)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.53  % (13884)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.53  % (13878)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.53  % (13862)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (13874)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.53  % (13876)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.53  % (13866)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (13888)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.53  % (13885)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (13867)------------------------------
% 0.22/0.53  % (13867)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (13867)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (13867)Memory used [KB]: 6140
% 0.22/0.53  % (13867)Time elapsed: 0.109 s
% 0.22/0.53  % (13867)------------------------------
% 0.22/0.53  % (13867)------------------------------
% 0.22/0.53  % (13876)Refutation not found, incomplete strategy% (13876)------------------------------
% 0.22/0.53  % (13876)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (13876)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (13876)Memory used [KB]: 6140
% 0.22/0.53  % (13876)Time elapsed: 0.003 s
% 0.22/0.53  % (13876)------------------------------
% 0.22/0.53  % (13876)------------------------------
% 0.22/0.54  % (13886)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.54  % (13861)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (13860)Success in time 0.175 s
%------------------------------------------------------------------------------
