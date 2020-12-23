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
% DateTime   : Thu Dec  3 12:51:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   49 (  72 expanded)
%              Number of leaves         :   11 (  20 expanded)
%              Depth                    :   12
%              Number of atoms          :  104 ( 175 expanded)
%              Number of equality atoms :   23 (  47 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f140,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f121,f123,f139])).

fof(f139,plain,(
    ~ spl3_10 ),
    inference(avatar_contradiction_clause,[],[f138])).

fof(f138,plain,
    ( $false
    | ~ spl3_10 ),
    inference(trivial_inequality_removal,[],[f137])).

fof(f137,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl3_10 ),
    inference(superposition,[],[f22,f129])).

fof(f129,plain,
    ( k1_xboole_0 = k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0)
    | ~ spl3_10 ),
    inference(resolution,[],[f120,f35])).

fof(f35,plain,(
    ! [X0] : r1_xboole_0(sK0,k6_subset_1(X0,sK1)) ),
    inference(resolution,[],[f34,f32])).

fof(f32,plain,(
    ! [X0,X1] : r1_xboole_0(X0,k6_subset_1(X1,X0)) ),
    inference(resolution,[],[f28,f30])).

fof(f30,plain,(
    ! [X0,X1] : r1_xboole_0(k6_subset_1(X0,X1),X1) ),
    inference(definition_unfolding,[],[f24,f25])).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f24,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f34,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(sK1,X0)
      | r1_xboole_0(sK0,X0) ) ),
    inference(resolution,[],[f29,f21])).

fof(f21,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0)
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0)
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t216_relat_1)).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f120,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X1,k6_subset_1(k1_relat_1(sK2),X0))
        | k1_xboole_0 = k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,X0)),X1) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl3_10
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,X0)),X1)
        | ~ r1_xboole_0(X1,k6_subset_1(k1_relat_1(sK2),X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f22,plain,(
    k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f123,plain,(
    spl3_9 ),
    inference(avatar_contradiction_clause,[],[f122])).

fof(f122,plain,
    ( $false
    | spl3_9 ),
    inference(resolution,[],[f117,f20])).

fof(f20,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f117,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_9 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl3_9
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f121,plain,
    ( ~ spl3_9
    | spl3_10 ),
    inference(avatar_split_clause,[],[f111,f119,f115])).

fof(f111,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,X0)),X1)
      | ~ r1_xboole_0(X1,k6_subset_1(k1_relat_1(sK2),X0))
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f44,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k6_subset_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f26,f25])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_relat_1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,X0)))
      | k1_xboole_0 = k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,X0)),X1)
      | ~ r1_xboole_0(X1,k6_subset_1(k1_relat_1(sK2),X0)) ) ),
    inference(superposition,[],[f23,f41])).

fof(f41,plain,(
    ! [X0] : k1_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,X0))) = k6_subset_1(k1_relat_1(sK2),X0) ),
    inference(resolution,[],[f27,f20])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t212_relat_1)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,k1_relat_1(X0))
      | k7_relat_1(X0,X1) = k1_xboole_0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_relat_1(X0,X1) = k1_xboole_0
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k7_relat_1(X0,X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n009.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:49:41 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.46  % (29402)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.46  % (29400)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.47  % (29401)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (29404)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (29413)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.47  % (29401)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f140,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f121,f123,f139])).
% 0.21/0.47  fof(f139,plain,(
% 0.21/0.47    ~spl3_10),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f138])).
% 0.21/0.47  fof(f138,plain,(
% 0.21/0.47    $false | ~spl3_10),
% 0.21/0.47    inference(trivial_inequality_removal,[],[f137])).
% 0.21/0.47  fof(f137,plain,(
% 0.21/0.47    k1_xboole_0 != k1_xboole_0 | ~spl3_10),
% 0.21/0.47    inference(superposition,[],[f22,f129])).
% 0.21/0.47  fof(f129,plain,(
% 0.21/0.47    k1_xboole_0 = k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) | ~spl3_10),
% 0.21/0.47    inference(resolution,[],[f120,f35])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ( ! [X0] : (r1_xboole_0(sK0,k6_subset_1(X0,sK1))) )),
% 0.21/0.47    inference(resolution,[],[f34,f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_xboole_0(X0,k6_subset_1(X1,X0))) )),
% 0.21/0.47    inference(resolution,[],[f28,f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_xboole_0(k6_subset_1(X0,X1),X1)) )),
% 0.21/0.47    inference(definition_unfolding,[],[f24,f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ( ! [X0] : (~r1_xboole_0(sK1,X0) | r1_xboole_0(sK0,X0)) )),
% 0.21/0.47    inference(resolution,[],[f29,f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    r1_tarski(sK0,sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ? [X0,X1,X2] : (k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ? [X0,X1,X2] : (k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 0.21/0.47    inference(flattening,[],[f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ? [X0,X1,X2] : ((k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 0.21/0.47    inference(ennf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)))),
% 0.21/0.47    inference(negated_conjecture,[],[f8])).
% 0.21/0.47  fof(f8,conjecture,(
% 0.21/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t216_relat_1)).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.47    inference(flattening,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.21/0.47  fof(f120,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_xboole_0(X1,k6_subset_1(k1_relat_1(sK2),X0)) | k1_xboole_0 = k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,X0)),X1)) ) | ~spl3_10),
% 0.21/0.47    inference(avatar_component_clause,[],[f119])).
% 0.21/0.47  fof(f119,plain,(
% 0.21/0.47    spl3_10 <=> ! [X1,X0] : (k1_xboole_0 = k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,X0)),X1) | ~r1_xboole_0(X1,k6_subset_1(k1_relat_1(sK2),X0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f19])).
% 0.21/0.47  fof(f123,plain,(
% 0.21/0.47    spl3_9),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f122])).
% 0.21/0.47  fof(f122,plain,(
% 0.21/0.47    $false | spl3_9),
% 0.21/0.47    inference(resolution,[],[f117,f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    v1_relat_1(sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f19])).
% 0.21/0.47  fof(f117,plain,(
% 0.21/0.47    ~v1_relat_1(sK2) | spl3_9),
% 0.21/0.47    inference(avatar_component_clause,[],[f115])).
% 0.21/0.47  fof(f115,plain,(
% 0.21/0.47    spl3_9 <=> v1_relat_1(sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.47  fof(f121,plain,(
% 0.21/0.47    ~spl3_9 | spl3_10),
% 0.21/0.47    inference(avatar_split_clause,[],[f111,f119,f115])).
% 0.21/0.47  fof(f111,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,X0)),X1) | ~r1_xboole_0(X1,k6_subset_1(k1_relat_1(sK2),X0)) | ~v1_relat_1(sK2)) )),
% 0.21/0.47    inference(resolution,[],[f44,f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v1_relat_1(k6_subset_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(definition_unfolding,[],[f26,f25])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k4_xboole_0(X0,X1)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_relat_1)).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,X0))) | k1_xboole_0 = k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,X0)),X1) | ~r1_xboole_0(X1,k6_subset_1(k1_relat_1(sK2),X0))) )),
% 0.21/0.47    inference(superposition,[],[f23,f41])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    ( ! [X0] : (k1_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,X0))) = k6_subset_1(k1_relat_1(sK2),X0)) )),
% 0.21/0.47    inference(resolution,[],[f27,f20])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0,X1] : (k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t212_relat_1)).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_xboole_0(X1,k1_relat_1(X0)) | k7_relat_1(X0,X1) = k1_xboole_0 | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (k7_relat_1(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k7_relat_1(X0,X1) = k1_xboole_0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (29401)------------------------------
% 0.21/0.47  % (29401)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (29401)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (29401)Memory used [KB]: 6140
% 0.21/0.47  % (29401)Time elapsed: 0.065 s
% 0.21/0.47  % (29401)------------------------------
% 0.21/0.47  % (29401)------------------------------
% 0.21/0.47  % (29405)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (29410)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (29397)Success in time 0.115 s
%------------------------------------------------------------------------------
