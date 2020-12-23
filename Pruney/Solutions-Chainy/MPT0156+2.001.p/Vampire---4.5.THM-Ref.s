%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:41 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   43 (  69 expanded)
%              Number of leaves         :   12 (  25 expanded)
%              Depth                    :    7
%              Number of atoms          :   60 (  92 expanded)
%              Number of equality atoms :   28 (  51 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f109,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f77,f107])).

fof(f107,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f103])).

fof(f103,plain,
    ( $false
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f76,f86,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f44,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f44,plain,(
    ! [X4,X2,X3] : r1_tarski(X2,k2_xboole_0(k2_xboole_0(X2,X3),X4)) ),
    inference(resolution,[],[f30,f31])).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f86,plain,(
    ! [X21,X22,X20] : r1_tarski(k1_enumset1(X20,X20,X20),k1_enumset1(X20,X21,X22)) ),
    inference(superposition,[],[f31,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2)) ),
    inference(definition_unfolding,[],[f29,f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)) ),
    inference(definition_unfolding,[],[f23,f32,f32])).

fof(f32,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_enumset1)).

fof(f29,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f76,plain,
    ( ~ r1_tarski(k1_enumset1(sK0,sK0,sK0),k2_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl4_2
  <=> r1_tarski(k1_enumset1(sK0,sK0,sK0),k2_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f77,plain,
    ( ~ spl4_2
    | spl4_1 ),
    inference(avatar_split_clause,[],[f72,f66,f74])).

fof(f66,plain,
    ( spl4_1
  <=> k2_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)) = k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k2_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f72,plain,
    ( ~ r1_tarski(k1_enumset1(sK0,sK0,sK0),k2_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)))
    | spl4_1 ),
    inference(trivial_inequality_removal,[],[f71])).

fof(f71,plain,
    ( k2_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)) != k2_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3))
    | ~ r1_tarski(k1_enumset1(sK0,sK0,sK0),k2_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)))
    | spl4_1 ),
    inference(superposition,[],[f68,f27])).

fof(f68,plain,
    ( k2_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)) != k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k2_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f66])).

fof(f69,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f39,f66])).

fof(f39,plain,(
    k2_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)) != k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k2_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3))) ),
    inference(definition_unfolding,[],[f22,f35,f37])).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X0,X0),k2_xboole_0(k1_enumset1(X1,X1,X2),k1_enumset1(X3,X3,X4))) ),
    inference(definition_unfolding,[],[f28,f36,f35])).

fof(f36,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f33,f32])).

fof(f33,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f28,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

fof(f22,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k3_enumset1(X0,X0,X1,X2,X3)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:27:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.49  % (26880)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (26889)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.50  % (26897)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.50  % (26881)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.50  % (26888)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.51  % (26888)Refutation not found, incomplete strategy% (26888)------------------------------
% 0.20/0.51  % (26888)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (26888)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (26888)Memory used [KB]: 1663
% 0.20/0.51  % (26888)Time elapsed: 0.108 s
% 0.20/0.51  % (26888)------------------------------
% 0.20/0.51  % (26888)------------------------------
% 0.20/0.52  % (26874)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.52  % (26898)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.52  % (26897)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f109,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f69,f77,f107])).
% 0.20/0.52  fof(f107,plain,(
% 0.20/0.52    spl4_2),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f103])).
% 0.20/0.52  fof(f103,plain,(
% 0.20/0.52    $false | spl4_2),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f76,f86,f47])).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(superposition,[],[f44,f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f14])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    ( ! [X4,X2,X3] : (r1_tarski(X2,k2_xboole_0(k2_xboole_0(X2,X3),X4))) )),
% 0.20/0.52    inference(resolution,[],[f30,f31])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.20/0.52    inference(ennf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.20/0.52  fof(f86,plain,(
% 0.20/0.52    ( ! [X21,X22,X20] : (r1_tarski(k1_enumset1(X20,X20,X20),k1_enumset1(X20,X21,X22))) )),
% 0.20/0.52    inference(superposition,[],[f31,f38])).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2))) )),
% 0.20/0.52    inference(definition_unfolding,[],[f29,f35])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) )),
% 0.20/0.52    inference(definition_unfolding,[],[f23,f32,f32])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,axiom,(
% 0.20/0.52    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_enumset1)).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.52  fof(f76,plain,(
% 0.20/0.52    ~r1_tarski(k1_enumset1(sK0,sK0,sK0),k2_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3))) | spl4_2),
% 0.20/0.52    inference(avatar_component_clause,[],[f74])).
% 0.20/0.52  fof(f74,plain,(
% 0.20/0.52    spl4_2 <=> r1_tarski(k1_enumset1(sK0,sK0,sK0),k2_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.52  fof(f77,plain,(
% 0.20/0.52    ~spl4_2 | spl4_1),
% 0.20/0.52    inference(avatar_split_clause,[],[f72,f66,f74])).
% 0.20/0.52  fof(f66,plain,(
% 0.20/0.52    spl4_1 <=> k2_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)) = k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k2_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.52  fof(f72,plain,(
% 0.20/0.52    ~r1_tarski(k1_enumset1(sK0,sK0,sK0),k2_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3))) | spl4_1),
% 0.20/0.52    inference(trivial_inequality_removal,[],[f71])).
% 0.20/0.52  fof(f71,plain,(
% 0.20/0.52    k2_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)) != k2_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)) | ~r1_tarski(k1_enumset1(sK0,sK0,sK0),k2_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3))) | spl4_1),
% 0.20/0.52    inference(superposition,[],[f68,f27])).
% 0.20/0.52  fof(f68,plain,(
% 0.20/0.52    k2_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)) != k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k2_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3))) | spl4_1),
% 0.20/0.52    inference(avatar_component_clause,[],[f66])).
% 0.20/0.52  fof(f69,plain,(
% 0.20/0.52    ~spl4_1),
% 0.20/0.52    inference(avatar_split_clause,[],[f39,f66])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    k2_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)) != k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k2_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)))),
% 0.20/0.52    inference(definition_unfolding,[],[f22,f35,f37])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X0,X0),k2_xboole_0(k1_enumset1(X1,X1,X2),k1_enumset1(X3,X3,X4)))) )),
% 0.20/0.52    inference(definition_unfolding,[],[f28,f36,f35])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f33,f32])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    k2_enumset1(sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3)),
% 0.20/0.52    inference(cnf_transformation,[],[f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    k2_enumset1(sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3)),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k3_enumset1(X0,X0,X1,X2,X3) => k2_enumset1(sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3)),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k3_enumset1(X0,X0,X1,X2,X3)),
% 0.20/0.52    inference(ennf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,negated_conjecture,(
% 0.20/0.52    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.20/0.52    inference(negated_conjecture,[],[f11])).
% 0.20/0.52  fof(f11,conjecture,(
% 0.20/0.52    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (26897)------------------------------
% 0.20/0.52  % (26897)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (26897)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (26897)Memory used [KB]: 10746
% 0.20/0.52  % (26897)Time elapsed: 0.107 s
% 0.20/0.52  % (26897)------------------------------
% 0.20/0.52  % (26897)------------------------------
% 0.20/0.52  % (26873)Success in time 0.165 s
%------------------------------------------------------------------------------
