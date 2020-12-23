%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:42 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 300 expanded)
%              Number of leaves         :   10 (  88 expanded)
%              Depth                    :   18
%              Number of atoms          :  123 ( 474 expanded)
%              Number of equality atoms :   75 ( 340 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f146,plain,(
    $false ),
    inference(subsumption_resolution,[],[f145,f55])).

fof(f55,plain,(
    sK0 != k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(subsumption_resolution,[],[f54,f47])).

fof(f47,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f54,plain,
    ( sK0 != k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ r1_tarski(sK0,sK0) ),
    inference(inner_rewriting,[],[f40])).

fof(f40,plain,
    ( sK0 != k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f16,f38,f38])).

fof(f38,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f19,f37])).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f21,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f21,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f19,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f16,plain,
    ( sK0 != k1_tarski(sK1)
    | ~ r1_tarski(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <~> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,k1_tarski(X1))
      <=> ( k1_tarski(X1) = X0
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_zfmisc_1)).

fof(f145,plain,(
    sK0 = k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(subsumption_resolution,[],[f144,f94])).

fof(f94,plain,(
    r2_hidden(sK1,sK0) ),
    inference(subsumption_resolution,[],[f93,f57])).

fof(f57,plain,(
    k1_xboole_0 != sK0 ),
    inference(subsumption_resolution,[],[f56,f18])).

fof(f18,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f56,plain,
    ( k1_xboole_0 != sK0
    | ~ r1_tarski(k1_xboole_0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(inner_rewriting,[],[f41])).

fof(f41,plain,
    ( k1_xboole_0 != sK0
    | ~ r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f15,f38])).

fof(f15,plain,
    ( k1_xboole_0 != sK0
    | ~ r1_tarski(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f93,plain,
    ( r2_hidden(sK1,sK0)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f20,f87])).

fof(f87,plain,(
    sK1 = sK2(sK0) ),
    inference(resolution,[],[f86,f48])).

fof(f48,plain,(
    ! [X2,X0] :
      ( X0 = X2
      | ~ r2_hidden(X2,k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f27,f38])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f86,plain,(
    r2_hidden(sK2(sK0),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(subsumption_resolution,[],[f80,f57])).

fof(f80,plain,
    ( r2_hidden(sK2(sK0),k2_enumset1(sK1,sK1,sK1,sK1))
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f76,f20])).

fof(f76,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK0)
      | r2_hidden(X4,k2_enumset1(sK1,sK1,sK1,sK1)) ) ),
    inference(superposition,[],[f52,f66])).

fof(f66,plain,(
    sK0 = k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(subsumption_resolution,[],[f65,f57])).

fof(f65,plain,
    ( k1_xboole_0 = sK0
    | sK0 = k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(subsumption_resolution,[],[f62,f55])).

fof(f62,plain,
    ( sK0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | k1_xboole_0 = sK0
    | sK0 = k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(resolution,[],[f39,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f39,plain,
    ( r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1))
    | sK0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | k1_xboole_0 = sK0 ),
    inference(definition_unfolding,[],[f17,f38,f38])).

fof(f17,plain,
    ( k1_xboole_0 = sK0
    | sK0 = k1_tarski(sK1)
    | r1_tarski(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(sK2(X0),X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f144,plain,
    ( ~ r2_hidden(sK1,sK0)
    | sK0 = k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(trivial_inequality_removal,[],[f142])).

fof(f142,plain,
    ( ~ r2_hidden(sK1,sK0)
    | sK1 != sK1
    | sK0 = k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(superposition,[],[f42,f136])).

fof(f136,plain,(
    sK1 = sK3(sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f135])).

fof(f135,plain,
    ( sK0 != sK0
    | sK1 = sK3(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f134])).

fof(f134,plain,
    ( sK0 != sK0
    | sK1 = sK3(sK1,sK0)
    | sK1 = sK3(sK1,sK0) ),
    inference(superposition,[],[f55,f98])).

fof(f98,plain,(
    ! [X0] :
      ( sK0 = k2_enumset1(X0,X0,X0,X0)
      | sK3(X0,sK0) = X0
      | sK1 = sK3(X0,sK0) ) ),
    inference(resolution,[],[f81,f48])).

fof(f81,plain,(
    ! [X4] :
      ( r2_hidden(sK3(X4,sK0),k2_enumset1(sK1,sK1,sK1,sK1))
      | sK3(X4,sK0) = X4
      | sK0 = k2_enumset1(X4,X4,X4,X4) ) ),
    inference(resolution,[],[f76,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( sK3(X0,X1) = X0
      | r2_hidden(sK3(X0,X1),X1)
      | k2_enumset1(X0,X0,X0,X0) = X1 ) ),
    inference(definition_unfolding,[],[f28,f38])).

fof(f28,plain,(
    ! [X0,X1] :
      ( sK3(X0,X1) = X0
      | r2_hidden(sK3(X0,X1),X1)
      | k1_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f42,plain,(
    ! [X0,X1] :
      ( sK3(X0,X1) != X0
      | ~ r2_hidden(sK3(X0,X1),X1)
      | k2_enumset1(X0,X0,X0,X0) = X1 ) ),
    inference(definition_unfolding,[],[f29,f38])).

fof(f29,plain,(
    ! [X0,X1] :
      ( sK3(X0,X1) != X0
      | ~ r2_hidden(sK3(X0,X1),X1)
      | k1_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:18:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.48  % (28882)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.49  % (28874)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.49  % (28882)Refutation not found, incomplete strategy% (28882)------------------------------
% 0.20/0.49  % (28882)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (28882)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (28882)Memory used [KB]: 10618
% 0.20/0.49  % (28882)Time elapsed: 0.065 s
% 0.20/0.49  % (28882)------------------------------
% 0.20/0.49  % (28882)------------------------------
% 0.20/0.53  % (28871)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.53  % (28868)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.55  % (28883)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.55  % (28879)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.55  % (28883)Refutation found. Thanks to Tanya!
% 0.20/0.55  % SZS status Theorem for theBenchmark
% 0.20/0.55  % SZS output start Proof for theBenchmark
% 0.20/0.55  fof(f146,plain,(
% 0.20/0.55    $false),
% 0.20/0.55    inference(subsumption_resolution,[],[f145,f55])).
% 0.20/0.55  fof(f55,plain,(
% 0.20/0.55    sK0 != k2_enumset1(sK1,sK1,sK1,sK1)),
% 0.20/0.55    inference(subsumption_resolution,[],[f54,f47])).
% 0.20/0.55  fof(f47,plain,(
% 0.20/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.55    inference(equality_resolution,[],[f23])).
% 0.20/0.55  fof(f23,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.20/0.55    inference(cnf_transformation,[],[f3])).
% 0.20/0.55  fof(f3,axiom,(
% 0.20/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.55  fof(f54,plain,(
% 0.20/0.55    sK0 != k2_enumset1(sK1,sK1,sK1,sK1) | ~r1_tarski(sK0,sK0)),
% 0.20/0.55    inference(inner_rewriting,[],[f40])).
% 0.20/0.55  fof(f40,plain,(
% 0.20/0.55    sK0 != k2_enumset1(sK1,sK1,sK1,sK1) | ~r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.20/0.55    inference(definition_unfolding,[],[f16,f38,f38])).
% 0.20/0.55  fof(f38,plain,(
% 0.20/0.55    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.20/0.55    inference(definition_unfolding,[],[f19,f37])).
% 0.20/0.55  fof(f37,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.20/0.55    inference(definition_unfolding,[],[f21,f30])).
% 0.20/0.55  fof(f30,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f9])).
% 0.20/0.55  fof(f9,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.55  fof(f21,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f8])).
% 0.20/0.55  fof(f8,axiom,(
% 0.20/0.55    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.55  fof(f19,plain,(
% 0.20/0.55    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f7])).
% 0.20/0.55  fof(f7,axiom,(
% 0.20/0.55    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.55  fof(f16,plain,(
% 0.20/0.55    sK0 != k1_tarski(sK1) | ~r1_tarski(sK0,k1_tarski(sK1))),
% 0.20/0.55    inference(cnf_transformation,[],[f12])).
% 0.20/0.55  fof(f12,plain,(
% 0.20/0.55    ? [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <~> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f11])).
% 0.20/0.55  fof(f11,negated_conjecture,(
% 0.20/0.55    ~! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.20/0.55    inference(negated_conjecture,[],[f10])).
% 0.20/0.55  fof(f10,conjecture,(
% 0.20/0.55    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_zfmisc_1)).
% 0.20/0.55  fof(f145,plain,(
% 0.20/0.55    sK0 = k2_enumset1(sK1,sK1,sK1,sK1)),
% 0.20/0.55    inference(subsumption_resolution,[],[f144,f94])).
% 0.20/0.55  fof(f94,plain,(
% 0.20/0.55    r2_hidden(sK1,sK0)),
% 0.20/0.55    inference(subsumption_resolution,[],[f93,f57])).
% 0.20/0.55  fof(f57,plain,(
% 0.20/0.55    k1_xboole_0 != sK0),
% 0.20/0.55    inference(subsumption_resolution,[],[f56,f18])).
% 0.20/0.55  fof(f18,plain,(
% 0.20/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f5])).
% 0.20/0.55  fof(f5,axiom,(
% 0.20/0.55    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.55  fof(f56,plain,(
% 0.20/0.55    k1_xboole_0 != sK0 | ~r1_tarski(k1_xboole_0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.20/0.55    inference(inner_rewriting,[],[f41])).
% 0.20/0.55  fof(f41,plain,(
% 0.20/0.55    k1_xboole_0 != sK0 | ~r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.20/0.55    inference(definition_unfolding,[],[f15,f38])).
% 0.20/0.55  fof(f15,plain,(
% 0.20/0.55    k1_xboole_0 != sK0 | ~r1_tarski(sK0,k1_tarski(sK1))),
% 0.20/0.55    inference(cnf_transformation,[],[f12])).
% 0.20/0.55  fof(f93,plain,(
% 0.20/0.55    r2_hidden(sK1,sK0) | k1_xboole_0 = sK0),
% 0.20/0.55    inference(superposition,[],[f20,f87])).
% 0.20/0.55  fof(f87,plain,(
% 0.20/0.55    sK1 = sK2(sK0)),
% 0.20/0.55    inference(resolution,[],[f86,f48])).
% 0.20/0.55  fof(f48,plain,(
% 0.20/0.55    ( ! [X2,X0] : (X0 = X2 | ~r2_hidden(X2,k2_enumset1(X0,X0,X0,X0))) )),
% 0.20/0.55    inference(equality_resolution,[],[f44])).
% 0.20/0.55  fof(f44,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 0.20/0.55    inference(definition_unfolding,[],[f27,f38])).
% 0.20/0.55  fof(f27,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 0.20/0.55    inference(cnf_transformation,[],[f6])).
% 0.20/0.55  fof(f6,axiom,(
% 0.20/0.55    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.20/0.55  fof(f86,plain,(
% 0.20/0.55    r2_hidden(sK2(sK0),k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.20/0.55    inference(subsumption_resolution,[],[f80,f57])).
% 0.20/0.55  fof(f80,plain,(
% 0.20/0.55    r2_hidden(sK2(sK0),k2_enumset1(sK1,sK1,sK1,sK1)) | k1_xboole_0 = sK0),
% 0.20/0.55    inference(resolution,[],[f76,f20])).
% 0.20/0.55  fof(f76,plain,(
% 0.20/0.55    ( ! [X4] : (~r2_hidden(X4,sK0) | r2_hidden(X4,k2_enumset1(sK1,sK1,sK1,sK1))) )),
% 0.20/0.55    inference(superposition,[],[f52,f66])).
% 0.20/0.55  fof(f66,plain,(
% 0.20/0.55    sK0 = k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.20/0.55    inference(subsumption_resolution,[],[f65,f57])).
% 0.20/0.55  fof(f65,plain,(
% 0.20/0.55    k1_xboole_0 = sK0 | sK0 = k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.20/0.55    inference(subsumption_resolution,[],[f62,f55])).
% 0.20/0.55  fof(f62,plain,(
% 0.20/0.55    sK0 = k2_enumset1(sK1,sK1,sK1,sK1) | k1_xboole_0 = sK0 | sK0 = k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.20/0.55    inference(resolution,[],[f39,f22])).
% 0.20/0.55  fof(f22,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.20/0.55    inference(cnf_transformation,[],[f14])).
% 0.20/0.55  fof(f14,plain,(
% 0.20/0.55    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.55    inference(ennf_transformation,[],[f4])).
% 0.20/0.55  fof(f4,axiom,(
% 0.20/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.55  fof(f39,plain,(
% 0.20/0.55    r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | sK0 = k2_enumset1(sK1,sK1,sK1,sK1) | k1_xboole_0 = sK0),
% 0.20/0.55    inference(definition_unfolding,[],[f17,f38,f38])).
% 0.20/0.55  fof(f17,plain,(
% 0.20/0.55    k1_xboole_0 = sK0 | sK0 = k1_tarski(sK1) | r1_tarski(sK0,k1_tarski(sK1))),
% 0.20/0.55    inference(cnf_transformation,[],[f12])).
% 0.20/0.55  fof(f52,plain,(
% 0.20/0.55    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,k3_xboole_0(X0,X1))) )),
% 0.20/0.55    inference(equality_resolution,[],[f35])).
% 0.20/0.55  fof(f35,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.20/0.55    inference(cnf_transformation,[],[f1])).
% 0.20/0.55  fof(f1,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.20/0.55  fof(f20,plain,(
% 0.20/0.55    ( ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK2(X0),X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f13])).
% 0.20/0.55  fof(f13,plain,(
% 0.20/0.55    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.20/0.55    inference(ennf_transformation,[],[f2])).
% 0.20/0.55  fof(f2,axiom,(
% 0.20/0.55    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.20/0.55  fof(f144,plain,(
% 0.20/0.55    ~r2_hidden(sK1,sK0) | sK0 = k2_enumset1(sK1,sK1,sK1,sK1)),
% 0.20/0.55    inference(trivial_inequality_removal,[],[f142])).
% 0.20/0.55  fof(f142,plain,(
% 0.20/0.55    ~r2_hidden(sK1,sK0) | sK1 != sK1 | sK0 = k2_enumset1(sK1,sK1,sK1,sK1)),
% 0.20/0.55    inference(superposition,[],[f42,f136])).
% 0.20/0.55  fof(f136,plain,(
% 0.20/0.55    sK1 = sK3(sK1,sK0)),
% 0.20/0.55    inference(trivial_inequality_removal,[],[f135])).
% 0.20/0.55  fof(f135,plain,(
% 0.20/0.55    sK0 != sK0 | sK1 = sK3(sK1,sK0)),
% 0.20/0.55    inference(duplicate_literal_removal,[],[f134])).
% 0.20/0.55  fof(f134,plain,(
% 0.20/0.55    sK0 != sK0 | sK1 = sK3(sK1,sK0) | sK1 = sK3(sK1,sK0)),
% 0.20/0.55    inference(superposition,[],[f55,f98])).
% 0.20/0.55  fof(f98,plain,(
% 0.20/0.55    ( ! [X0] : (sK0 = k2_enumset1(X0,X0,X0,X0) | sK3(X0,sK0) = X0 | sK1 = sK3(X0,sK0)) )),
% 0.20/0.55    inference(resolution,[],[f81,f48])).
% 0.20/0.55  fof(f81,plain,(
% 0.20/0.55    ( ! [X4] : (r2_hidden(sK3(X4,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) | sK3(X4,sK0) = X4 | sK0 = k2_enumset1(X4,X4,X4,X4)) )),
% 0.20/0.55    inference(resolution,[],[f76,f43])).
% 0.20/0.55  fof(f43,plain,(
% 0.20/0.55    ( ! [X0,X1] : (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1) | k2_enumset1(X0,X0,X0,X0) = X1) )),
% 0.20/0.55    inference(definition_unfolding,[],[f28,f38])).
% 0.20/0.55  fof(f28,plain,(
% 0.20/0.55    ( ! [X0,X1] : (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1) | k1_tarski(X0) = X1) )),
% 0.20/0.55    inference(cnf_transformation,[],[f6])).
% 0.20/0.55  fof(f42,plain,(
% 0.20/0.55    ( ! [X0,X1] : (sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1) | k2_enumset1(X0,X0,X0,X0) = X1) )),
% 0.20/0.55    inference(definition_unfolding,[],[f29,f38])).
% 0.20/0.55  fof(f29,plain,(
% 0.20/0.55    ( ! [X0,X1] : (sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1) | k1_tarski(X0) = X1) )),
% 0.20/0.55    inference(cnf_transformation,[],[f6])).
% 0.20/0.55  % SZS output end Proof for theBenchmark
% 0.20/0.55  % (28883)------------------------------
% 0.20/0.55  % (28883)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (28883)Termination reason: Refutation
% 0.20/0.55  
% 0.20/0.55  % (28883)Memory used [KB]: 1791
% 0.20/0.55  % (28883)Time elapsed: 0.129 s
% 0.20/0.55  % (28883)------------------------------
% 0.20/0.55  % (28883)------------------------------
% 0.20/0.55  % (28865)Success in time 0.187 s
%------------------------------------------------------------------------------
