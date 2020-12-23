%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:11 EST 2020

% Result     : Theorem 1.17s
% Output     : Refutation 1.17s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 203 expanded)
%              Number of leaves         :   11 (  65 expanded)
%              Depth                    :   12
%              Number of atoms          :  136 ( 339 expanded)
%              Number of equality atoms :   89 ( 277 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f101,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f84,f83,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f27,f37])).

fof(f37,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f24,f36])).

fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f25,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f25,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f24,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f83,plain,(
    ~ r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(unit_resulting_resolution,[],[f80,f50])).

fof(f50,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f30,f37])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f20])).

% (4574)Refutation not found, incomplete strategy% (4574)------------------------------
% (4574)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (4574)Termination reason: Refutation not found, incomplete strategy

% (4574)Memory used [KB]: 1663
% (4574)Time elapsed: 0.078 s
% (4574)------------------------------
% (4574)------------------------------
fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f80,plain,(
    sK0 != sK1 ),
    inference(subsumption_resolution,[],[f79,f51])).

fof(f51,plain,(
    ! [X1] : ~ r1_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f34,f37,f37])).

fof(f34,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( X0 = X1
        & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_zfmisc_1)).

fof(f79,plain,
    ( r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0))
    | sK0 != sK1 ),
    inference(trivial_inequality_removal,[],[f78])).

fof(f78,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k2_enumset1(sK0,sK0,sK0,sK0)
    | r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0))
    | sK0 != sK1 ),
    inference(superposition,[],[f41,f52])).

fof(f52,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)))
    | sK0 != sK1 ),
    inference(inner_rewriting,[],[f39])).

fof(f39,plain,
    ( sK0 != sK1
    | k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f22,f37,f26,f37,f37])).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f22,plain,
    ( sK0 != sK1
    | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ( sK0 = sK1
      | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) )
    & ( sK0 != sK1
      | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).

fof(f15,plain,
    ( ? [X0,X1] :
        ( ( X0 = X1
          | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
        & ( X0 != X1
          | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) )
   => ( ( sK0 = sK1
        | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) )
      & ( sK0 != sK1
        | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ( X0 = X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
      & ( X0 != X1
        | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <~> X0 != X1 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      <=> X0 != X1 ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f29,f26])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f84,plain,(
    ~ r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(subsumption_resolution,[],[f75,f80])).

fof(f75,plain,
    ( sK0 = sK1
    | ~ r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(trivial_inequality_removal,[],[f74])).

fof(f74,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k2_enumset1(sK0,sK0,sK0,sK0)
    | sK0 = sK1
    | ~ r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(superposition,[],[f38,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f28,f26])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f38,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)))
    | sK0 = sK1 ),
    inference(definition_unfolding,[],[f23,f37,f26,f37,f37])).

fof(f23,plain,
    ( sK0 = sK1
    | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n007.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 19:44:21 EST 2020
% 0.15/0.36  % CPUTime    : 
% 1.17/0.53  % (4571)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.17/0.54  % (4564)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.17/0.54  % (4571)Refutation not found, incomplete strategy% (4571)------------------------------
% 1.17/0.54  % (4571)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.17/0.54  % (4571)Termination reason: Refutation not found, incomplete strategy
% 1.17/0.54  
% 1.17/0.54  % (4571)Memory used [KB]: 6140
% 1.17/0.54  % (4571)Time elapsed: 0.119 s
% 1.17/0.54  % (4571)------------------------------
% 1.17/0.54  % (4571)------------------------------
% 1.17/0.55  % (4562)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.17/0.55  % (4574)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.17/0.55  % (4564)Refutation found. Thanks to Tanya!
% 1.17/0.55  % SZS status Theorem for theBenchmark
% 1.17/0.55  % SZS output start Proof for theBenchmark
% 1.17/0.55  fof(f101,plain,(
% 1.17/0.55    $false),
% 1.17/0.55    inference(unit_resulting_resolution,[],[f84,f83,f40])).
% 1.17/0.55  fof(f40,plain,(
% 1.17/0.55    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 1.17/0.55    inference(definition_unfolding,[],[f27,f37])).
% 1.17/0.55  fof(f37,plain,(
% 1.17/0.55    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.17/0.55    inference(definition_unfolding,[],[f24,f36])).
% 1.17/0.55  fof(f36,plain,(
% 1.17/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.17/0.55    inference(definition_unfolding,[],[f25,f35])).
% 1.17/0.55  fof(f35,plain,(
% 1.17/0.55    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.17/0.55    inference(cnf_transformation,[],[f6])).
% 1.17/0.55  fof(f6,axiom,(
% 1.17/0.55    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.17/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.17/0.55  fof(f25,plain,(
% 1.17/0.55    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.17/0.55    inference(cnf_transformation,[],[f5])).
% 1.17/0.55  fof(f5,axiom,(
% 1.17/0.55    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.17/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.17/0.55  fof(f24,plain,(
% 1.17/0.55    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.17/0.55    inference(cnf_transformation,[],[f4])).
% 1.17/0.55  fof(f4,axiom,(
% 1.17/0.55    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.17/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.17/0.55  fof(f27,plain,(
% 1.17/0.55    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.17/0.55    inference(cnf_transformation,[],[f12])).
% 1.17/0.55  fof(f12,plain,(
% 1.17/0.55    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.17/0.55    inference(ennf_transformation,[],[f7])).
% 1.17/0.55  fof(f7,axiom,(
% 1.17/0.55    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.17/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.17/0.55  fof(f83,plain,(
% 1.17/0.55    ~r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.17/0.55    inference(unit_resulting_resolution,[],[f80,f50])).
% 1.17/0.55  fof(f50,plain,(
% 1.17/0.55    ( ! [X0,X3] : (~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) | X0 = X3) )),
% 1.17/0.55    inference(equality_resolution,[],[f46])).
% 1.17/0.55  fof(f46,plain,(
% 1.17/0.55    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 1.17/0.55    inference(definition_unfolding,[],[f30,f37])).
% 1.17/0.55  fof(f30,plain,(
% 1.17/0.55    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.17/0.55    inference(cnf_transformation,[],[f21])).
% 1.17/0.55  fof(f21,plain,(
% 1.17/0.55    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.17/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f20])).
% 1.17/0.55  % (4574)Refutation not found, incomplete strategy% (4574)------------------------------
% 1.17/0.55  % (4574)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.17/0.55  % (4574)Termination reason: Refutation not found, incomplete strategy
% 1.17/0.55  
% 1.17/0.55  % (4574)Memory used [KB]: 1663
% 1.17/0.55  % (4574)Time elapsed: 0.078 s
% 1.17/0.55  % (4574)------------------------------
% 1.17/0.55  % (4574)------------------------------
% 1.17/0.55  fof(f20,plain,(
% 1.17/0.55    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 1.17/0.55    introduced(choice_axiom,[])).
% 1.17/0.55  fof(f19,plain,(
% 1.17/0.55    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.17/0.55    inference(rectify,[],[f18])).
% 1.17/0.55  fof(f18,plain,(
% 1.17/0.55    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.17/0.55    inference(nnf_transformation,[],[f3])).
% 1.17/0.55  fof(f3,axiom,(
% 1.17/0.55    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.17/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.17/0.55  fof(f80,plain,(
% 1.17/0.55    sK0 != sK1),
% 1.17/0.55    inference(subsumption_resolution,[],[f79,f51])).
% 1.17/0.55  fof(f51,plain,(
% 1.17/0.55    ( ! [X1] : (~r1_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1))) )),
% 1.17/0.55    inference(equality_resolution,[],[f47])).
% 1.17/0.55  fof(f47,plain,(
% 1.17/0.55    ( ! [X0,X1] : (X0 != X1 | ~r1_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))) )),
% 1.17/0.55    inference(definition_unfolding,[],[f34,f37,f37])).
% 1.17/0.55  fof(f34,plain,(
% 1.17/0.55    ( ! [X0,X1] : (X0 != X1 | ~r1_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.17/0.55    inference(cnf_transformation,[],[f13])).
% 1.17/0.55  fof(f13,plain,(
% 1.17/0.55    ! [X0,X1] : (X0 != X1 | ~r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 1.17/0.55    inference(ennf_transformation,[],[f8])).
% 1.17/0.55  fof(f8,axiom,(
% 1.17/0.55    ! [X0,X1] : ~(X0 = X1 & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 1.17/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_zfmisc_1)).
% 1.17/0.55  fof(f79,plain,(
% 1.17/0.55    r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)) | sK0 != sK1),
% 1.17/0.55    inference(trivial_inequality_removal,[],[f78])).
% 1.17/0.55  fof(f78,plain,(
% 1.17/0.55    k2_enumset1(sK0,sK0,sK0,sK0) != k2_enumset1(sK0,sK0,sK0,sK0) | r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)) | sK0 != sK1),
% 1.17/0.55    inference(superposition,[],[f41,f52])).
% 1.17/0.55  fof(f52,plain,(
% 1.17/0.55    k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0))) | sK0 != sK1),
% 1.17/0.55    inference(inner_rewriting,[],[f39])).
% 1.17/0.55  fof(f39,plain,(
% 1.17/0.55    sK0 != sK1 | k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)))),
% 1.17/0.55    inference(definition_unfolding,[],[f22,f37,f26,f37,f37])).
% 1.17/0.55  fof(f26,plain,(
% 1.17/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.17/0.55    inference(cnf_transformation,[],[f1])).
% 1.17/0.55  fof(f1,axiom,(
% 1.17/0.55    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.17/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.17/0.55  fof(f22,plain,(
% 1.17/0.55    sK0 != sK1 | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.17/0.55    inference(cnf_transformation,[],[f16])).
% 1.17/0.55  fof(f16,plain,(
% 1.17/0.55    (sK0 = sK1 | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) & (sK0 != sK1 | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 1.17/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).
% 1.17/0.55  fof(f15,plain,(
% 1.17/0.55    ? [X0,X1] : ((X0 = X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) & (X0 != X1 | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))) => ((sK0 = sK1 | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) & (sK0 != sK1 | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))))),
% 1.17/0.55    introduced(choice_axiom,[])).
% 1.17/0.55  fof(f14,plain,(
% 1.17/0.55    ? [X0,X1] : ((X0 = X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) & (X0 != X1 | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 1.17/0.55    inference(nnf_transformation,[],[f11])).
% 1.17/0.55  fof(f11,plain,(
% 1.17/0.55    ? [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <~> X0 != X1)),
% 1.17/0.55    inference(ennf_transformation,[],[f10])).
% 1.17/0.55  fof(f10,negated_conjecture,(
% 1.17/0.55    ~! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 1.17/0.55    inference(negated_conjecture,[],[f9])).
% 1.17/0.55  fof(f9,conjecture,(
% 1.17/0.55    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 1.17/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 1.17/0.55  fof(f41,plain,(
% 1.17/0.55    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0 | r1_xboole_0(X0,X1)) )),
% 1.17/0.55    inference(definition_unfolding,[],[f29,f26])).
% 1.17/0.55  fof(f29,plain,(
% 1.17/0.55    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 1.17/0.55    inference(cnf_transformation,[],[f17])).
% 1.17/0.55  fof(f17,plain,(
% 1.17/0.55    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 1.17/0.55    inference(nnf_transformation,[],[f2])).
% 1.17/0.55  fof(f2,axiom,(
% 1.17/0.55    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.17/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.17/0.55  fof(f84,plain,(
% 1.17/0.55    ~r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.17/0.55    inference(subsumption_resolution,[],[f75,f80])).
% 1.17/0.55  fof(f75,plain,(
% 1.17/0.55    sK0 = sK1 | ~r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.17/0.55    inference(trivial_inequality_removal,[],[f74])).
% 1.17/0.55  fof(f74,plain,(
% 1.17/0.55    k2_enumset1(sK0,sK0,sK0,sK0) != k2_enumset1(sK0,sK0,sK0,sK0) | sK0 = sK1 | ~r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.17/0.55    inference(superposition,[],[f38,f42])).
% 1.17/0.55  fof(f42,plain,(
% 1.17/0.55    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.17/0.55    inference(definition_unfolding,[],[f28,f26])).
% 1.17/0.55  fof(f28,plain,(
% 1.17/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.17/0.55    inference(cnf_transformation,[],[f17])).
% 1.17/0.55  fof(f38,plain,(
% 1.17/0.55    k2_enumset1(sK0,sK0,sK0,sK0) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))) | sK0 = sK1),
% 1.17/0.55    inference(definition_unfolding,[],[f23,f37,f26,f37,f37])).
% 1.17/0.55  fof(f23,plain,(
% 1.17/0.55    sK0 = sK1 | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.17/0.55    inference(cnf_transformation,[],[f16])).
% 1.17/0.55  % SZS output end Proof for theBenchmark
% 1.17/0.55  % (4564)------------------------------
% 1.17/0.55  % (4564)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.17/0.55  % (4564)Termination reason: Refutation
% 1.17/0.55  
% 1.17/0.55  % (4564)Memory used [KB]: 1791
% 1.17/0.55  % (4564)Time elapsed: 0.123 s
% 1.17/0.55  % (4564)------------------------------
% 1.17/0.55  % (4564)------------------------------
% 1.17/0.55  % (4588)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.17/0.55  % (4559)Success in time 0.176 s
%------------------------------------------------------------------------------
