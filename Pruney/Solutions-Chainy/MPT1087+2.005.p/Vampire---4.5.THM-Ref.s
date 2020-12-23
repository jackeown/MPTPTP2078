%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:23 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   26 (  33 expanded)
%              Number of leaves         :    7 (  11 expanded)
%              Depth                    :    7
%              Number of atoms          :   49 (  65 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f37,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f21,f26,f36])).

fof(f36,plain,
    ( ~ spl2_1
    | spl2_2 ),
    inference(avatar_contradiction_clause,[],[f35])).

fof(f35,plain,
    ( $false
    | ~ spl2_1
    | spl2_2 ),
    inference(subsumption_resolution,[],[f27,f20])).

fof(f20,plain,
    ( v1_finset_1(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f18])).

fof(f18,plain,
    ( spl2_1
  <=> v1_finset_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f27,plain,
    ( ~ v1_finset_1(sK0)
    | spl2_2 ),
    inference(unit_resulting_resolution,[],[f13,f25,f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ v1_finset_1(X1)
      | v1_finset_1(X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( v1_finset_1(X0)
      | ~ v1_finset_1(X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( v1_finset_1(X0)
      | ~ v1_finset_1(X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_finset_1(X1)
        & r1_tarski(X0,X1) )
     => v1_finset_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_finset_1)).

fof(f25,plain,
    ( ~ v1_finset_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f23])).

fof(f23,plain,
    ( spl2_2
  <=> v1_finset_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f13,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f26,plain,(
    ~ spl2_2 ),
    inference(avatar_split_clause,[],[f16,f23])).

fof(f16,plain,(
    ~ v1_finset_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f12,f14])).

fof(f14,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f12,plain,(
    ~ v1_finset_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( ~ v1_finset_1(k3_xboole_0(sK0,sK1))
    & v1_finset_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f9])).

fof(f9,plain,
    ( ? [X0,X1] :
        ( ~ v1_finset_1(k3_xboole_0(X0,X1))
        & v1_finset_1(X0) )
   => ( ~ v1_finset_1(k3_xboole_0(sK0,sK1))
      & v1_finset_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ~ v1_finset_1(k3_xboole_0(X0,X1))
      & v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_finset_1(X0)
       => v1_finset_1(k3_xboole_0(X0,X1)) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( v1_finset_1(X0)
     => v1_finset_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_finset_1)).

fof(f21,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f11,f18])).

fof(f11,plain,(
    v1_finset_1(sK0) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:05:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.44  % (28278)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.47  % (28283)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.47  % (28283)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f21,f26,f36])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    ~spl2_1 | spl2_2),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f35])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    $false | (~spl2_1 | spl2_2)),
% 0.20/0.47    inference(subsumption_resolution,[],[f27,f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    v1_finset_1(sK0) | ~spl2_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    spl2_1 <=> v1_finset_1(sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ~v1_finset_1(sK0) | spl2_2),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f13,f25,f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~v1_finset_1(X1) | v1_finset_1(X0) | ~r1_tarski(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,plain,(
% 0.20/0.47    ! [X0,X1] : (v1_finset_1(X0) | ~v1_finset_1(X1) | ~r1_tarski(X0,X1))),
% 0.20/0.47    inference(flattening,[],[f7])).
% 0.20/0.47  fof(f7,plain,(
% 0.20/0.47    ! [X0,X1] : (v1_finset_1(X0) | (~v1_finset_1(X1) | ~r1_tarski(X0,X1)))),
% 0.20/0.47    inference(ennf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1] : ((v1_finset_1(X1) & r1_tarski(X0,X1)) => v1_finset_1(X0))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_finset_1)).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ~v1_finset_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    spl2_2 <=> v1_finset_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ~spl2_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f16,f23])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ~v1_finset_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 0.20/0.47    inference(definition_unfolding,[],[f12,f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ~v1_finset_1(k3_xboole_0(sK0,sK1))),
% 0.20/0.47    inference(cnf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    ~v1_finset_1(k3_xboole_0(sK0,sK1)) & v1_finset_1(sK0)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f9])).
% 0.20/0.47  fof(f9,plain,(
% 0.20/0.47    ? [X0,X1] : (~v1_finset_1(k3_xboole_0(X0,X1)) & v1_finset_1(X0)) => (~v1_finset_1(k3_xboole_0(sK0,sK1)) & v1_finset_1(sK0))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f6,plain,(
% 0.20/0.47    ? [X0,X1] : (~v1_finset_1(k3_xboole_0(X0,X1)) & v1_finset_1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1] : (v1_finset_1(X0) => v1_finset_1(k3_xboole_0(X0,X1)))),
% 0.20/0.47    inference(negated_conjecture,[],[f4])).
% 0.20/0.47  fof(f4,conjecture,(
% 0.20/0.47    ! [X0,X1] : (v1_finset_1(X0) => v1_finset_1(k3_xboole_0(X0,X1)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_finset_1)).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    spl2_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f11,f18])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    v1_finset_1(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f10])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (28283)------------------------------
% 0.20/0.47  % (28283)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (28283)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (28283)Memory used [KB]: 10618
% 0.20/0.47  % (28283)Time elapsed: 0.052 s
% 0.20/0.47  % (28283)------------------------------
% 0.20/0.47  % (28283)------------------------------
% 0.20/0.47  % (28266)Success in time 0.112 s
%------------------------------------------------------------------------------
