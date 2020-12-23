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
% DateTime   : Thu Dec  3 12:40:20 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 150 expanded)
%              Number of leaves         :   12 (  46 expanded)
%              Depth                    :   15
%              Number of atoms          :   98 ( 237 expanded)
%              Number of equality atoms :   34 ( 139 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f390,plain,(
    $false ),
    inference(subsumption_resolution,[],[f382,f20])).

fof(f20,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( X0 != X1
      & r2_hidden(X1,X2)
      & k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( X0 != X1
          & r2_hidden(X1,X2)
          & k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ~ ( X0 != X1
        & r2_hidden(X1,X2)
        & k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_zfmisc_1)).

fof(f382,plain,(
    sK0 = sK1 ),
    inference(resolution,[],[f379,f48])).

fof(f48,plain,(
    ! [X2,X0] :
      ( X0 = X2
      | ~ r2_hidden(X2,k1_enumset1(X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f30,f38])).

fof(f38,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f21,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f21,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f379,plain,(
    r2_hidden(sK1,k1_enumset1(sK0,sK0,sK0)) ),
    inference(subsumption_resolution,[],[f371,f19])).

fof(f19,plain,(
    r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f371,plain,
    ( ~ r2_hidden(sK1,sK2)
    | r2_hidden(sK1,k1_enumset1(sK0,sK0,sK0)) ),
    inference(resolution,[],[f362,f185])).

fof(f185,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k3_xboole_0(sK2,k1_enumset1(sK0,sK0,sK0)))
      | ~ r2_hidden(X1,sK2)
      | r2_hidden(X1,k1_enumset1(sK0,sK0,sK0)) ) ),
    inference(duplicate_literal_removal,[],[f177])).

fof(f177,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k3_xboole_0(sK2,k1_enumset1(sK0,sK0,sK0)))
      | ~ r2_hidden(X1,sK2)
      | r2_hidden(X1,k1_enumset1(sK0,sK0,sK0))
      | ~ r2_hidden(X1,sK2) ) ),
    inference(resolution,[],[f110,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1)
      | r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f110,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k5_xboole_0(sK2,k1_enumset1(sK0,sK0,sK0)))
      | ~ r2_hidden(X1,k3_xboole_0(sK2,k1_enumset1(sK0,sK0,sK0)))
      | ~ r2_hidden(X1,sK2) ) ),
    inference(superposition,[],[f34,f85])).

fof(f85,plain,(
    k5_xboole_0(sK2,k1_enumset1(sK0,sK0,sK0)) = k5_xboole_0(sK2,k3_xboole_0(sK2,k1_enumset1(sK0,sK0,sK0))) ),
    inference(superposition,[],[f42,f76])).

fof(f76,plain,(
    k1_enumset1(sK0,sK0,sK0) = k3_xboole_0(sK2,k1_enumset1(sK0,sK0,sK1)) ),
    inference(superposition,[],[f39,f23])).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f39,plain,(
    k1_enumset1(sK0,sK0,sK0) = k3_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2) ),
    inference(definition_unfolding,[],[f18,f38,f25])).

fof(f18,plain,(
    k1_tarski(sK0) = k3_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f42,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f27,f26,f26])).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f362,plain,(
    r2_hidden(sK1,k3_xboole_0(sK2,k1_enumset1(sK0,sK0,sK0))) ),
    inference(resolution,[],[f349,f97])).

fof(f97,plain,(
    r1_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(sK2,k1_enumset1(sK0,sK0,sK0))) ),
    inference(resolution,[],[f87,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f87,plain,(
    r1_xboole_0(k5_xboole_0(sK2,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK1)) ),
    inference(forward_demodulation,[],[f86,f85])).

fof(f86,plain,(
    r1_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,k1_enumset1(sK0,sK0,sK0))),k1_enumset1(sK0,sK0,sK1)) ),
    inference(superposition,[],[f41,f76])).

fof(f41,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))),X1) ),
    inference(definition_unfolding,[],[f24,f26])).

fof(f24,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_xboole_1)).

fof(f349,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(k1_enumset1(X0,X0,sK1),k5_xboole_0(sK2,k1_enumset1(sK0,sK0,sK0)))
      | r2_hidden(sK1,k3_xboole_0(sK2,k1_enumset1(sK0,sK0,sK0))) ) ),
    inference(superposition,[],[f277,f40])).

fof(f40,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f22,f25,f25])).

fof(f22,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f277,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(k1_enumset1(sK1,sK1,X0),k5_xboole_0(sK2,k1_enumset1(sK0,sK0,sK0)))
      | r2_hidden(sK1,k3_xboole_0(sK2,k1_enumset1(sK0,sK0,sK0))) ) ),
    inference(resolution,[],[f271,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(k1_enumset1(X0,X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f37,f25])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(f271,plain,
    ( r2_hidden(sK1,k5_xboole_0(sK2,k1_enumset1(sK0,sK0,sK0)))
    | r2_hidden(sK1,k3_xboole_0(sK2,k1_enumset1(sK0,sK0,sK0))) ),
    inference(resolution,[],[f112,f19])).

fof(f112,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK2)
      | r2_hidden(X3,k3_xboole_0(sK2,k1_enumset1(sK0,sK0,sK0)))
      | r2_hidden(X3,k5_xboole_0(sK2,k1_enumset1(sK0,sK0,sK0))) ) ),
    inference(superposition,[],[f36,f85])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:16:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (5516)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.48  % (5523)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.50  % (5533)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.50  % (5533)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f390,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(subsumption_resolution,[],[f382,f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    sK0 != sK1),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ? [X0,X1,X2] : (X0 != X1 & r2_hidden(X1,X2) & k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X1),X2))),
% 0.20/0.50    inference(ennf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,negated_conjecture,(
% 0.20/0.50    ~! [X0,X1,X2] : ~(X0 != X1 & r2_hidden(X1,X2) & k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X1),X2))),
% 0.20/0.50    inference(negated_conjecture,[],[f12])).
% 0.20/0.50  fof(f12,conjecture,(
% 0.20/0.50    ! [X0,X1,X2] : ~(X0 != X1 & r2_hidden(X1,X2) & k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X1),X2))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_zfmisc_1)).
% 0.20/0.50  fof(f382,plain,(
% 0.20/0.50    sK0 = sK1),
% 0.20/0.50    inference(resolution,[],[f379,f48])).
% 0.20/0.50  fof(f48,plain,(
% 0.20/0.50    ( ! [X2,X0] : (X0 = X2 | ~r2_hidden(X2,k1_enumset1(X0,X0,X0))) )),
% 0.20/0.50    inference(equality_resolution,[],[f45])).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_enumset1(X0,X0,X0) != X1) )),
% 0.20/0.50    inference(definition_unfolding,[],[f30,f38])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.20/0.50    inference(definition_unfolding,[],[f21,f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,axiom,(
% 0.20/0.50    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,axiom,(
% 0.20/0.50    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.20/0.50  fof(f379,plain,(
% 0.20/0.50    r2_hidden(sK1,k1_enumset1(sK0,sK0,sK0))),
% 0.20/0.50    inference(subsumption_resolution,[],[f371,f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    r2_hidden(sK1,sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  fof(f371,plain,(
% 0.20/0.50    ~r2_hidden(sK1,sK2) | r2_hidden(sK1,k1_enumset1(sK0,sK0,sK0))),
% 0.20/0.50    inference(resolution,[],[f362,f185])).
% 0.20/0.50  fof(f185,plain,(
% 0.20/0.50    ( ! [X1] : (~r2_hidden(X1,k3_xboole_0(sK2,k1_enumset1(sK0,sK0,sK0))) | ~r2_hidden(X1,sK2) | r2_hidden(X1,k1_enumset1(sK0,sK0,sK0))) )),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f177])).
% 0.20/0.50  fof(f177,plain,(
% 0.20/0.50    ( ! [X1] : (~r2_hidden(X1,k3_xboole_0(sK2,k1_enumset1(sK0,sK0,sK0))) | ~r2_hidden(X1,sK2) | r2_hidden(X1,k1_enumset1(sK0,sK0,sK0)) | ~r2_hidden(X1,sK2)) )),
% 0.20/0.50    inference(resolution,[],[f110,f36])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r2_hidden(X0,X1) | r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 0.20/0.51    inference(ennf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).
% 0.20/0.51  fof(f110,plain,(
% 0.20/0.51    ( ! [X1] : (~r2_hidden(X1,k5_xboole_0(sK2,k1_enumset1(sK0,sK0,sK0))) | ~r2_hidden(X1,k3_xboole_0(sK2,k1_enumset1(sK0,sK0,sK0))) | ~r2_hidden(X1,sK2)) )),
% 0.20/0.51    inference(superposition,[],[f34,f85])).
% 0.20/0.51  fof(f85,plain,(
% 0.20/0.51    k5_xboole_0(sK2,k1_enumset1(sK0,sK0,sK0)) = k5_xboole_0(sK2,k3_xboole_0(sK2,k1_enumset1(sK0,sK0,sK0)))),
% 0.20/0.51    inference(superposition,[],[f42,f76])).
% 0.20/0.51  fof(f76,plain,(
% 0.20/0.51    k1_enumset1(sK0,sK0,sK0) = k3_xboole_0(sK2,k1_enumset1(sK0,sK0,sK1))),
% 0.20/0.51    inference(superposition,[],[f39,f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    k1_enumset1(sK0,sK0,sK0) = k3_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2)),
% 0.20/0.51    inference(definition_unfolding,[],[f18,f38,f25])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    k1_tarski(sK0) = k3_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f14])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 0.20/0.51    inference(definition_unfolding,[],[f27,f26,f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f362,plain,(
% 0.20/0.51    r2_hidden(sK1,k3_xboole_0(sK2,k1_enumset1(sK0,sK0,sK0)))),
% 0.20/0.51    inference(resolution,[],[f349,f97])).
% 0.20/0.51  fof(f97,plain,(
% 0.20/0.51    r1_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(sK2,k1_enumset1(sK0,sK0,sK0)))),
% 0.20/0.51    inference(resolution,[],[f87,f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.20/0.51  fof(f87,plain,(
% 0.20/0.51    r1_xboole_0(k5_xboole_0(sK2,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK1))),
% 0.20/0.51    inference(forward_demodulation,[],[f86,f85])).
% 0.20/0.51  fof(f86,plain,(
% 0.20/0.51    r1_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,k1_enumset1(sK0,sK0,sK0))),k1_enumset1(sK0,sK0,sK1))),
% 0.20/0.51    inference(superposition,[],[f41,f76])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))),X1)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f24,f26])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_xboole_1)).
% 0.20/0.51  fof(f349,plain,(
% 0.20/0.51    ( ! [X0] : (~r1_xboole_0(k1_enumset1(X0,X0,sK1),k5_xboole_0(sK2,k1_enumset1(sK0,sK0,sK0))) | r2_hidden(sK1,k3_xboole_0(sK2,k1_enumset1(sK0,sK0,sK0)))) )),
% 0.20/0.51    inference(superposition,[],[f277,f40])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f22,f25,f25])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.20/0.51  fof(f277,plain,(
% 0.20/0.51    ( ! [X0] : (~r1_xboole_0(k1_enumset1(sK1,sK1,X0),k5_xboole_0(sK2,k1_enumset1(sK0,sK0,sK0))) | r2_hidden(sK1,k3_xboole_0(sK2,k1_enumset1(sK0,sK0,sK0)))) )),
% 0.20/0.51    inference(resolution,[],[f271,f47])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r1_xboole_0(k1_enumset1(X0,X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f37,f25])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r1_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2))),
% 0.20/0.51    inference(ennf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).
% 0.20/0.51  fof(f271,plain,(
% 0.20/0.51    r2_hidden(sK1,k5_xboole_0(sK2,k1_enumset1(sK0,sK0,sK0))) | r2_hidden(sK1,k3_xboole_0(sK2,k1_enumset1(sK0,sK0,sK0)))),
% 0.20/0.51    inference(resolution,[],[f112,f19])).
% 0.20/0.51  fof(f112,plain,(
% 0.20/0.51    ( ! [X3] : (~r2_hidden(X3,sK2) | r2_hidden(X3,k3_xboole_0(sK2,k1_enumset1(sK0,sK0,sK0))) | r2_hidden(X3,k5_xboole_0(sK2,k1_enumset1(sK0,sK0,sK0)))) )),
% 0.20/0.51    inference(superposition,[],[f36,f85])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (5533)------------------------------
% 0.20/0.51  % (5533)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (5533)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (5533)Memory used [KB]: 1791
% 0.20/0.51  % (5533)Time elapsed: 0.112 s
% 0.20/0.51  % (5533)------------------------------
% 0.20/0.51  % (5533)------------------------------
% 0.20/0.51  % (5525)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.51  % (5528)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.52  % (5522)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (5541)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.52  % (5520)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.52  % (5518)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.52  % (5538)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.52  % (5515)Success in time 0.175 s
%------------------------------------------------------------------------------
