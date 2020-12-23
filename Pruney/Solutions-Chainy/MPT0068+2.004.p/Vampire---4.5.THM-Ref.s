%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:24 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   31 (  40 expanded)
%              Number of leaves         :    7 (  13 expanded)
%              Depth                    :   10
%              Number of atoms          :   63 (  83 expanded)
%              Number of equality atoms :   20 (  30 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f57,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f18,f50,f24])).

fof(f24,plain,(
    ! [X0] :
      ( sQ1_eqProxy(k1_xboole_0,X0)
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(equality_proxy_replacement,[],[f17,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( sQ1_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ1_eqProxy])])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f50,plain,(
    ~ sQ1_eqProxy(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK0)) ),
    inference(resolution,[],[f41,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( sQ1_eqProxy(X1,X0)
      | ~ sQ1_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f22])).

fof(f41,plain,(
    ~ sQ1_eqProxy(k4_xboole_0(k1_xboole_0,sK0),k1_xboole_0) ),
    inference(resolution,[],[f27,f36])).

fof(f36,plain,(
    ~ r1_tarski(k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f35,f16])).

fof(f16,plain,(
    ~ r2_xboole_0(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ r2_xboole_0(k1_xboole_0,sK0)
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f12])).

fof(f12,plain,
    ( ? [X0] :
        ( ~ r2_xboole_0(k1_xboole_0,X0)
        & k1_xboole_0 != X0 )
   => ( ~ r2_xboole_0(k1_xboole_0,sK0)
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ~ r2_xboole_0(k1_xboole_0,X0)
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( k1_xboole_0 != X0
       => r2_xboole_0(k1_xboole_0,X0) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => r2_xboole_0(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_xboole_1)).

fof(f35,plain,
    ( r2_xboole_0(k1_xboole_0,sK0)
    | ~ r1_tarski(k1_xboole_0,sK0) ),
    inference(resolution,[],[f25,f23])).

fof(f23,plain,(
    ~ sQ1_eqProxy(k1_xboole_0,sK0) ),
    inference(equality_proxy_replacement,[],[f15,f22])).

fof(f15,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f13])).

fof(f25,plain,(
    ! [X0,X1] :
      ( sQ1_eqProxy(X0,X1)
      | r2_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(equality_proxy_replacement,[],[f19,f22])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ sQ1_eqProxy(k4_xboole_0(X0,X1),k1_xboole_0) ) ),
    inference(equality_proxy_replacement,[],[f20,f22])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f18,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n017.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 14:49:31 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.47  % (26980)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.47  % (26980)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f57,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f18,f50,f24])).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    ( ! [X0] : (sQ1_eqProxy(k1_xboole_0,X0) | ~r1_tarski(X0,k1_xboole_0)) )),
% 0.22/0.47    inference(equality_proxy_replacement,[],[f17,f22])).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    ! [X1,X0] : (sQ1_eqProxy(X0,X1) <=> X0 = X1)),
% 0.22/0.47    introduced(equality_proxy_definition,[new_symbols(naming,[sQ1_eqProxy])])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f9])).
% 0.22/0.47  fof(f9,plain,(
% 0.22/0.47    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.22/0.47    inference(ennf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.22/0.47  fof(f50,plain,(
% 0.22/0.47    ~sQ1_eqProxy(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK0))),
% 0.22/0.47    inference(resolution,[],[f41,f32])).
% 0.22/0.47  fof(f32,plain,(
% 0.22/0.47    ( ! [X0,X1] : (sQ1_eqProxy(X1,X0) | ~sQ1_eqProxy(X0,X1)) )),
% 0.22/0.47    inference(equality_proxy_axiom,[],[f22])).
% 0.22/0.47  fof(f41,plain,(
% 0.22/0.47    ~sQ1_eqProxy(k4_xboole_0(k1_xboole_0,sK0),k1_xboole_0)),
% 0.22/0.47    inference(resolution,[],[f27,f36])).
% 0.22/0.47  fof(f36,plain,(
% 0.22/0.47    ~r1_tarski(k1_xboole_0,sK0)),
% 0.22/0.47    inference(subsumption_resolution,[],[f35,f16])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    ~r2_xboole_0(k1_xboole_0,sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f13])).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    ~r2_xboole_0(k1_xboole_0,sK0) & k1_xboole_0 != sK0),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f12])).
% 0.22/0.47  fof(f12,plain,(
% 0.22/0.47    ? [X0] : (~r2_xboole_0(k1_xboole_0,X0) & k1_xboole_0 != X0) => (~r2_xboole_0(k1_xboole_0,sK0) & k1_xboole_0 != sK0)),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f8,plain,(
% 0.22/0.47    ? [X0] : (~r2_xboole_0(k1_xboole_0,X0) & k1_xboole_0 != X0)),
% 0.22/0.47    inference(ennf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,negated_conjecture,(
% 0.22/0.47    ~! [X0] : (k1_xboole_0 != X0 => r2_xboole_0(k1_xboole_0,X0))),
% 0.22/0.47    inference(negated_conjecture,[],[f5])).
% 0.22/0.47  fof(f5,conjecture,(
% 0.22/0.47    ! [X0] : (k1_xboole_0 != X0 => r2_xboole_0(k1_xboole_0,X0))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_xboole_1)).
% 0.22/0.47  fof(f35,plain,(
% 0.22/0.47    r2_xboole_0(k1_xboole_0,sK0) | ~r1_tarski(k1_xboole_0,sK0)),
% 0.22/0.47    inference(resolution,[],[f25,f23])).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    ~sQ1_eqProxy(k1_xboole_0,sK0)),
% 0.22/0.47    inference(equality_proxy_replacement,[],[f15,f22])).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    k1_xboole_0 != sK0),
% 0.22/0.47    inference(cnf_transformation,[],[f13])).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    ( ! [X0,X1] : (sQ1_eqProxy(X0,X1) | r2_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.47    inference(equality_proxy_replacement,[],[f19,f22])).
% 0.22/0.47  fof(f19,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f11])).
% 0.22/0.47  fof(f11,plain,(
% 0.22/0.47    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.47    inference(flattening,[],[f10])).
% 0.22/0.47  fof(f10,plain,(
% 0.22/0.47    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 0.22/0.47    inference(ennf_transformation,[],[f7])).
% 0.22/0.47  fof(f7,plain,(
% 0.22/0.47    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 0.22/0.47    inference(unused_predicate_definition_removal,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.22/0.47  fof(f27,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~sQ1_eqProxy(k4_xboole_0(X0,X1),k1_xboole_0)) )),
% 0.22/0.47    inference(equality_proxy_replacement,[],[f20,f22])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.22/0.47    inference(cnf_transformation,[],[f14])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.22/0.47    inference(nnf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (26980)------------------------------
% 0.22/0.47  % (26980)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (26980)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (26980)Memory used [KB]: 6012
% 0.22/0.47  % (26980)Time elapsed: 0.052 s
% 0.22/0.47  % (26980)------------------------------
% 0.22/0.47  % (26980)------------------------------
% 0.22/0.48  % (26972)Success in time 0.111 s
%------------------------------------------------------------------------------
