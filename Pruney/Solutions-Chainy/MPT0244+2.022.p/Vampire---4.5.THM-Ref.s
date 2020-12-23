%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:44 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   35 (  77 expanded)
%              Number of leaves         :    6 (  23 expanded)
%              Depth                    :   12
%              Number of atoms          :   67 ( 123 expanded)
%              Number of equality atoms :   42 (  91 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f47,plain,(
    $false ),
    inference(subsumption_resolution,[],[f45,f27])).

fof(f27,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k1_enumset1(X1,X1,X1)) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | r1_tarski(X0,k1_enumset1(X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f17,f19])).

fof(f19,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f13,f15])).

fof(f15,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f13,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

% (18389)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
fof(f45,plain,(
    ~ r1_tarski(k1_xboole_0,k1_enumset1(sK1,sK1,sK1)) ),
    inference(trivial_inequality_removal,[],[f44])).

fof(f44,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k1_enumset1(sK1,sK1,sK1)) ),
    inference(backward_demodulation,[],[f29,f42])).

fof(f42,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f41,f30])).

fof(f30,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f14,f12])).

fof(f12,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f14,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f41,plain,
    ( ~ r1_tarski(sK0,sK0)
    | k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f37])).

fof(f37,plain,
    ( sK0 != sK0
    | ~ r1_tarski(sK0,sK0)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f28,f35])).

fof(f35,plain,
    ( sK0 = k1_enumset1(sK1,sK1,sK1)
    | k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f34])).

fof(f34,plain,
    ( sK0 = k1_enumset1(sK1,sK1,sK1)
    | k1_xboole_0 = sK0
    | sK0 = k1_enumset1(sK1,sK1,sK1)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f25,f20])).

fof(f20,plain,
    ( r1_tarski(sK0,k1_enumset1(sK1,sK1,sK1))
    | sK0 = k1_enumset1(sK1,sK1,sK1)
    | k1_xboole_0 = sK0 ),
    inference(definition_unfolding,[],[f11,f19,f19])).

fof(f11,plain,
    ( k1_xboole_0 = sK0
    | sK0 = k1_tarski(sK1)
    | r1_tarski(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <~> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,k1_tarski(X1))
      <=> ( k1_tarski(X1) = X0
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_zfmisc_1)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_enumset1(X1,X1,X1))
      | k1_enumset1(X1,X1,X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f16,f19,f19])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f28,plain,
    ( sK0 != k1_enumset1(sK1,sK1,sK1)
    | ~ r1_tarski(sK0,sK0) ),
    inference(inner_rewriting,[],[f21])).

fof(f21,plain,
    ( sK0 != k1_enumset1(sK1,sK1,sK1)
    | ~ r1_tarski(sK0,k1_enumset1(sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f10,f19,f19])).

fof(f10,plain,
    ( sK0 != k1_tarski(sK1)
    | ~ r1_tarski(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f29,plain,
    ( k1_xboole_0 != sK0
    | ~ r1_tarski(k1_xboole_0,k1_enumset1(sK1,sK1,sK1)) ),
    inference(inner_rewriting,[],[f22])).

fof(f22,plain,
    ( k1_xboole_0 != sK0
    | ~ r1_tarski(sK0,k1_enumset1(sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f9,f19])).

fof(f9,plain,
    ( k1_xboole_0 != sK0
    | ~ r1_tarski(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.11  % Command    : run_vampire %s %d
% 0.12/0.31  % Computer   : n021.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % WCLimit    : 600
% 0.12/0.31  % DateTime   : Tue Dec  1 15:44:04 EST 2020
% 0.12/0.31  % CPUTime    : 
% 0.18/0.47  % (18400)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.18/0.47  % (18392)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.18/0.48  % (18384)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.18/0.48  % (18384)Refutation found. Thanks to Tanya!
% 0.18/0.48  % SZS status Theorem for theBenchmark
% 0.18/0.48  % SZS output start Proof for theBenchmark
% 0.18/0.48  fof(f47,plain,(
% 0.18/0.48    $false),
% 0.18/0.48    inference(subsumption_resolution,[],[f45,f27])).
% 0.18/0.48  fof(f27,plain,(
% 0.18/0.48    ( ! [X1] : (r1_tarski(k1_xboole_0,k1_enumset1(X1,X1,X1))) )),
% 0.18/0.48    inference(equality_resolution,[],[f24])).
% 0.18/0.48  fof(f24,plain,(
% 0.18/0.48    ( ! [X0,X1] : (k1_xboole_0 != X0 | r1_tarski(X0,k1_enumset1(X1,X1,X1))) )),
% 0.18/0.48    inference(definition_unfolding,[],[f17,f19])).
% 0.18/0.48  fof(f19,plain,(
% 0.18/0.48    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.18/0.48    inference(definition_unfolding,[],[f13,f15])).
% 0.18/0.48  fof(f15,plain,(
% 0.18/0.48    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.18/0.48    inference(cnf_transformation,[],[f4])).
% 0.18/0.48  fof(f4,axiom,(
% 0.18/0.48    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.18/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.18/0.48  fof(f13,plain,(
% 0.18/0.48    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.18/0.48    inference(cnf_transformation,[],[f3])).
% 0.18/0.48  fof(f3,axiom,(
% 0.18/0.48    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.18/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.18/0.48  fof(f17,plain,(
% 0.18/0.48    ( ! [X0,X1] : (k1_xboole_0 != X0 | r1_tarski(X0,k1_tarski(X1))) )),
% 0.18/0.48    inference(cnf_transformation,[],[f5])).
% 0.18/0.48  fof(f5,axiom,(
% 0.18/0.48    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.18/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.18/0.48  % (18389)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.18/0.48  fof(f45,plain,(
% 0.18/0.48    ~r1_tarski(k1_xboole_0,k1_enumset1(sK1,sK1,sK1))),
% 0.18/0.48    inference(trivial_inequality_removal,[],[f44])).
% 0.18/0.48  fof(f44,plain,(
% 0.18/0.48    k1_xboole_0 != k1_xboole_0 | ~r1_tarski(k1_xboole_0,k1_enumset1(sK1,sK1,sK1))),
% 0.18/0.48    inference(backward_demodulation,[],[f29,f42])).
% 0.18/0.48  fof(f42,plain,(
% 0.18/0.48    k1_xboole_0 = sK0),
% 0.18/0.48    inference(subsumption_resolution,[],[f41,f30])).
% 0.18/0.48  fof(f30,plain,(
% 0.18/0.48    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.18/0.48    inference(superposition,[],[f14,f12])).
% 0.18/0.48  fof(f12,plain,(
% 0.18/0.48    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.18/0.48    inference(cnf_transformation,[],[f1])).
% 0.18/0.48  fof(f1,axiom,(
% 0.18/0.48    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.18/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.18/0.48  fof(f14,plain,(
% 0.18/0.48    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.18/0.48    inference(cnf_transformation,[],[f2])).
% 0.18/0.48  fof(f2,axiom,(
% 0.18/0.48    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.18/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.18/0.48  fof(f41,plain,(
% 0.18/0.48    ~r1_tarski(sK0,sK0) | k1_xboole_0 = sK0),
% 0.18/0.48    inference(trivial_inequality_removal,[],[f37])).
% 0.18/0.48  fof(f37,plain,(
% 0.18/0.48    sK0 != sK0 | ~r1_tarski(sK0,sK0) | k1_xboole_0 = sK0),
% 0.18/0.48    inference(superposition,[],[f28,f35])).
% 0.18/0.48  fof(f35,plain,(
% 0.18/0.48    sK0 = k1_enumset1(sK1,sK1,sK1) | k1_xboole_0 = sK0),
% 0.18/0.48    inference(duplicate_literal_removal,[],[f34])).
% 0.18/0.48  fof(f34,plain,(
% 0.18/0.48    sK0 = k1_enumset1(sK1,sK1,sK1) | k1_xboole_0 = sK0 | sK0 = k1_enumset1(sK1,sK1,sK1) | k1_xboole_0 = sK0),
% 0.18/0.48    inference(resolution,[],[f25,f20])).
% 0.18/0.48  fof(f20,plain,(
% 0.18/0.48    r1_tarski(sK0,k1_enumset1(sK1,sK1,sK1)) | sK0 = k1_enumset1(sK1,sK1,sK1) | k1_xboole_0 = sK0),
% 0.18/0.48    inference(definition_unfolding,[],[f11,f19,f19])).
% 0.18/0.48  fof(f11,plain,(
% 0.18/0.48    k1_xboole_0 = sK0 | sK0 = k1_tarski(sK1) | r1_tarski(sK0,k1_tarski(sK1))),
% 0.18/0.48    inference(cnf_transformation,[],[f8])).
% 0.18/0.48  fof(f8,plain,(
% 0.18/0.48    ? [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <~> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.18/0.48    inference(ennf_transformation,[],[f7])).
% 0.18/0.48  fof(f7,negated_conjecture,(
% 0.18/0.48    ~! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.18/0.48    inference(negated_conjecture,[],[f6])).
% 0.18/0.48  fof(f6,conjecture,(
% 0.18/0.48    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.18/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_zfmisc_1)).
% 0.18/0.48  fof(f25,plain,(
% 0.18/0.48    ( ! [X0,X1] : (~r1_tarski(X0,k1_enumset1(X1,X1,X1)) | k1_enumset1(X1,X1,X1) = X0 | k1_xboole_0 = X0) )),
% 0.18/0.48    inference(definition_unfolding,[],[f16,f19,f19])).
% 0.18/0.48  fof(f16,plain,(
% 0.18/0.48    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 0.18/0.48    inference(cnf_transformation,[],[f5])).
% 0.18/0.48  fof(f28,plain,(
% 0.18/0.48    sK0 != k1_enumset1(sK1,sK1,sK1) | ~r1_tarski(sK0,sK0)),
% 0.18/0.48    inference(inner_rewriting,[],[f21])).
% 0.18/0.48  fof(f21,plain,(
% 0.18/0.48    sK0 != k1_enumset1(sK1,sK1,sK1) | ~r1_tarski(sK0,k1_enumset1(sK1,sK1,sK1))),
% 0.18/0.48    inference(definition_unfolding,[],[f10,f19,f19])).
% 0.18/0.48  fof(f10,plain,(
% 0.18/0.48    sK0 != k1_tarski(sK1) | ~r1_tarski(sK0,k1_tarski(sK1))),
% 0.18/0.48    inference(cnf_transformation,[],[f8])).
% 0.18/0.48  fof(f29,plain,(
% 0.18/0.48    k1_xboole_0 != sK0 | ~r1_tarski(k1_xboole_0,k1_enumset1(sK1,sK1,sK1))),
% 0.18/0.48    inference(inner_rewriting,[],[f22])).
% 0.18/0.48  fof(f22,plain,(
% 0.18/0.48    k1_xboole_0 != sK0 | ~r1_tarski(sK0,k1_enumset1(sK1,sK1,sK1))),
% 0.18/0.48    inference(definition_unfolding,[],[f9,f19])).
% 0.18/0.48  fof(f9,plain,(
% 0.18/0.48    k1_xboole_0 != sK0 | ~r1_tarski(sK0,k1_tarski(sK1))),
% 0.18/0.48    inference(cnf_transformation,[],[f8])).
% 0.18/0.48  % SZS output end Proof for theBenchmark
% 0.18/0.48  % (18384)------------------------------
% 0.18/0.48  % (18384)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.48  % (18384)Termination reason: Refutation
% 0.18/0.48  
% 0.18/0.48  % (18384)Memory used [KB]: 6140
% 0.18/0.48  % (18384)Time elapsed: 0.067 s
% 0.18/0.48  % (18384)------------------------------
% 0.18/0.48  % (18384)------------------------------
% 0.18/0.48  % (18388)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.18/0.48  % (18390)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.18/0.48  % (18377)Success in time 0.16 s
%------------------------------------------------------------------------------
