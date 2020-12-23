%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:48 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   36 ( 107 expanded)
%              Number of leaves         :   10 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :   46 ( 124 expanded)
%              Number of equality atoms :   31 ( 102 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f48,plain,(
    $false ),
    inference(resolution,[],[f47,f37])).

fof(f37,plain,(
    r2_hidden(sK0,sK0) ),
    inference(trivial_inequality_removal,[],[f36])).

fof(f36,plain,
    ( sK0 != sK0
    | r2_hidden(sK0,sK0) ),
    inference(superposition,[],[f32,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k6_subset_1(X0,k2_enumset1(X1,X1,X1,X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f24,f20,f27])).

fof(f27,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f18,f26])).

fof(f26,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f21,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f21,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f18,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f20,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
     => k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ),
    inference(unused_predicate_definition_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f32,plain,(
    sK0 != k6_subset_1(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f29,f30])).

fof(f30,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k6_subset_1(k2_xboole_0(X0,X1),X1) ),
    inference(definition_unfolding,[],[f22,f20,f20])).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f29,plain,(
    sK0 != k6_subset_1(k2_xboole_0(sK0,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(definition_unfolding,[],[f17,f28,f27])).

fof(f28,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k2_enumset1(X0,X0,X0,X0)) ),
    inference(definition_unfolding,[],[f19,f27])).

fof(f19,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f17,plain,(
    sK0 != k6_subset_1(k1_ordinal1(sK0),k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    sK0 != k6_subset_1(k1_ordinal1(sK0),k1_tarski(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f15])).

fof(f15,plain,
    ( ? [X0] : k6_subset_1(k1_ordinal1(X0),k1_tarski(X0)) != X0
   => sK0 != k6_subset_1(k1_ordinal1(sK0),k1_tarski(sK0)) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] : k6_subset_1(k1_ordinal1(X0),k1_tarski(X0)) != X0 ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] : k6_subset_1(k1_ordinal1(X0),k1_tarski(X0)) = X0 ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] : k6_subset_1(k1_ordinal1(X0),k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_ordinal1)).

fof(f47,plain,(
    ~ r2_hidden(sK0,sK0) ),
    inference(resolution,[],[f37,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:24:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.46  % (26009)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.46  % (26001)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.46  % (26001)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f48,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(resolution,[],[f47,f37])).
% 0.20/0.46  fof(f37,plain,(
% 0.20/0.46    r2_hidden(sK0,sK0)),
% 0.20/0.46    inference(trivial_inequality_removal,[],[f36])).
% 0.20/0.46  fof(f36,plain,(
% 0.20/0.46    sK0 != sK0 | r2_hidden(sK0,sK0)),
% 0.20/0.46    inference(superposition,[],[f32,f31])).
% 0.20/0.46  fof(f31,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k6_subset_1(X0,k2_enumset1(X1,X1,X1,X1)) = X0 | r2_hidden(X1,X0)) )),
% 0.20/0.46    inference(definition_unfolding,[],[f24,f20,f27])).
% 0.20/0.46  fof(f27,plain,(
% 0.20/0.46    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.20/0.46    inference(definition_unfolding,[],[f18,f26])).
% 0.20/0.46  fof(f26,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.20/0.46    inference(definition_unfolding,[],[f21,f25])).
% 0.20/0.46  fof(f25,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f5])).
% 0.20/0.46  fof(f5,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f4])).
% 0.20/0.46  fof(f4,axiom,(
% 0.20/0.46    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f7])).
% 0.20/0.46  fof(f7,axiom,(
% 0.20/0.46    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f14])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f11])).
% 0.20/0.46  fof(f11,plain,(
% 0.20/0.46    ! [X0,X1] : (~r2_hidden(X1,X0) => k4_xboole_0(X0,k1_tarski(X1)) = X0)),
% 0.20/0.46    inference(unused_predicate_definition_removal,[],[f6])).
% 0.20/0.46  fof(f6,axiom,(
% 0.20/0.46    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.20/0.46  fof(f32,plain,(
% 0.20/0.46    sK0 != k6_subset_1(sK0,k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.20/0.46    inference(superposition,[],[f29,f30])).
% 0.20/0.46  fof(f30,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k6_subset_1(k2_xboole_0(X0,X1),X1)) )),
% 0.20/0.46    inference(definition_unfolding,[],[f22,f20,f20])).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 0.20/0.46  fof(f29,plain,(
% 0.20/0.46    sK0 != k6_subset_1(k2_xboole_0(sK0,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.20/0.46    inference(definition_unfolding,[],[f17,f28,f27])).
% 0.20/0.46  fof(f28,plain,(
% 0.20/0.46    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k2_enumset1(X0,X0,X0,X0))) )),
% 0.20/0.46    inference(definition_unfolding,[],[f19,f27])).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f8])).
% 0.20/0.46  fof(f8,axiom,(
% 0.20/0.46    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    sK0 != k6_subset_1(k1_ordinal1(sK0),k1_tarski(sK0))),
% 0.20/0.46    inference(cnf_transformation,[],[f16])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    sK0 != k6_subset_1(k1_ordinal1(sK0),k1_tarski(sK0))),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f15])).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    ? [X0] : k6_subset_1(k1_ordinal1(X0),k1_tarski(X0)) != X0 => sK0 != k6_subset_1(k1_ordinal1(sK0),k1_tarski(sK0))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f12,plain,(
% 0.20/0.46    ? [X0] : k6_subset_1(k1_ordinal1(X0),k1_tarski(X0)) != X0),
% 0.20/0.46    inference(ennf_transformation,[],[f10])).
% 0.20/0.46  fof(f10,negated_conjecture,(
% 0.20/0.46    ~! [X0] : k6_subset_1(k1_ordinal1(X0),k1_tarski(X0)) = X0),
% 0.20/0.46    inference(negated_conjecture,[],[f9])).
% 0.20/0.46  fof(f9,conjecture,(
% 0.20/0.46    ! [X0] : k6_subset_1(k1_ordinal1(X0),k1_tarski(X0)) = X0),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_ordinal1)).
% 0.20/0.46  fof(f47,plain,(
% 0.20/0.46    ~r2_hidden(sK0,sK0)),
% 0.20/0.46    inference(resolution,[],[f37,f23])).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f13])).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (26001)------------------------------
% 0.20/0.46  % (26001)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (26001)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (26001)Memory used [KB]: 6012
% 0.20/0.46  % (26001)Time elapsed: 0.052 s
% 0.20/0.46  % (26001)------------------------------
% 0.20/0.46  % (26001)------------------------------
% 0.20/0.46  % (25996)Success in time 0.107 s
%------------------------------------------------------------------------------
