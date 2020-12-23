%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:40 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   20 (  21 expanded)
%              Number of leaves         :    5 (   6 expanded)
%              Depth                    :    8
%              Number of atoms          :   27 (  29 expanded)
%              Number of equality atoms :   14 (  15 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f25,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f16,f24])).

fof(f24,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f23])).

fof(f23,plain,
    ( $false
    | spl2_1 ),
    inference(trivial_inequality_removal,[],[f22])).

fof(f22,plain,
    ( sK0 != sK0
    | spl2_1 ),
    inference(superposition,[],[f15,f18])).

fof(f18,plain,(
    ! [X2,X3] : k2_xboole_0(X2,k3_xboole_0(X2,X3)) = X2 ),
    inference(superposition,[],[f17,f10])).

fof(f10,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0 ),
    inference(resolution,[],[f11,f9])).

fof(f9,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f15,plain,
    ( sK0 != k2_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f13])).

fof(f13,plain,
    ( spl2_1
  <=> sK0 = k2_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f16,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f8,f13])).

fof(f8,plain,(
    sK0 != k2_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) != X0 ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:31:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.40  % (5516)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.19/0.41  % (5508)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.19/0.41  % (5508)Refutation found. Thanks to Tanya!
% 0.19/0.41  % SZS status Theorem for theBenchmark
% 0.19/0.41  % SZS output start Proof for theBenchmark
% 0.19/0.41  fof(f25,plain,(
% 0.19/0.41    $false),
% 0.19/0.41    inference(avatar_sat_refutation,[],[f16,f24])).
% 0.19/0.41  fof(f24,plain,(
% 0.19/0.41    spl2_1),
% 0.19/0.41    inference(avatar_contradiction_clause,[],[f23])).
% 0.19/0.41  fof(f23,plain,(
% 0.19/0.41    $false | spl2_1),
% 0.19/0.41    inference(trivial_inequality_removal,[],[f22])).
% 0.19/0.41  fof(f22,plain,(
% 0.19/0.41    sK0 != sK0 | spl2_1),
% 0.19/0.41    inference(superposition,[],[f15,f18])).
% 0.19/0.41  fof(f18,plain,(
% 0.19/0.41    ( ! [X2,X3] : (k2_xboole_0(X2,k3_xboole_0(X2,X3)) = X2) )),
% 0.19/0.41    inference(superposition,[],[f17,f10])).
% 0.19/0.41  fof(f10,plain,(
% 0.19/0.41    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.19/0.41    inference(cnf_transformation,[],[f1])).
% 0.19/0.41  fof(f1,axiom,(
% 0.19/0.41    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.19/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.19/0.41  fof(f17,plain,(
% 0.19/0.41    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0) )),
% 0.19/0.41    inference(resolution,[],[f11,f9])).
% 0.19/0.41  fof(f9,plain,(
% 0.19/0.41    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.19/0.41    inference(cnf_transformation,[],[f3])).
% 0.19/0.41  fof(f3,axiom,(
% 0.19/0.41    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.19/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.19/0.41  fof(f11,plain,(
% 0.19/0.41    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.19/0.41    inference(cnf_transformation,[],[f7])).
% 0.19/0.41  fof(f7,plain,(
% 0.19/0.41    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.19/0.41    inference(ennf_transformation,[],[f2])).
% 0.19/0.41  fof(f2,axiom,(
% 0.19/0.41    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.19/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.19/0.41  fof(f15,plain,(
% 0.19/0.41    sK0 != k2_xboole_0(sK0,k3_xboole_0(sK0,sK1)) | spl2_1),
% 0.19/0.41    inference(avatar_component_clause,[],[f13])).
% 0.19/0.41  fof(f13,plain,(
% 0.19/0.41    spl2_1 <=> sK0 = k2_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.19/0.41  fof(f16,plain,(
% 0.19/0.41    ~spl2_1),
% 0.19/0.41    inference(avatar_split_clause,[],[f8,f13])).
% 0.19/0.41  fof(f8,plain,(
% 0.19/0.41    sK0 != k2_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.19/0.41    inference(cnf_transformation,[],[f6])).
% 0.19/0.41  fof(f6,plain,(
% 0.19/0.41    ? [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) != X0),
% 0.19/0.41    inference(ennf_transformation,[],[f5])).
% 0.19/0.41  fof(f5,negated_conjecture,(
% 0.19/0.41    ~! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.19/0.41    inference(negated_conjecture,[],[f4])).
% 0.19/0.41  fof(f4,conjecture,(
% 0.19/0.41    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.19/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.19/0.41  % SZS output end Proof for theBenchmark
% 0.19/0.41  % (5508)------------------------------
% 0.19/0.41  % (5508)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.41  % (5508)Termination reason: Refutation
% 0.19/0.41  
% 0.19/0.41  % (5508)Memory used [KB]: 10490
% 0.19/0.41  % (5508)Time elapsed: 0.005 s
% 0.19/0.41  % (5508)------------------------------
% 0.19/0.41  % (5508)------------------------------
% 0.19/0.41  % (5506)Success in time 0.062 s
%------------------------------------------------------------------------------
