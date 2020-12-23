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
% DateTime   : Thu Dec  3 12:50:56 EST 2020

% Result     : Theorem 1.56s
% Output     : Refutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :   46 (  66 expanded)
%              Number of leaves         :   12 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   97 ( 131 expanded)
%              Number of equality atoms :   36 (  54 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f93,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f47,f80,f88,f92])).

fof(f92,plain,(
    spl2_7 ),
    inference(avatar_contradiction_clause,[],[f89])).

fof(f89,plain,
    ( $false
    | spl2_7 ),
    inference(unit_resulting_resolution,[],[f36,f87])).

fof(f87,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1))
    | spl2_7 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl2_7
  <=> r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f36,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f88,plain,
    ( ~ spl2_1
    | ~ spl2_7
    | spl2_6 ),
    inference(avatar_split_clause,[],[f83,f77,f85,f39])).

fof(f39,plain,
    ( spl2_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f77,plain,
    ( spl2_6
  <=> k7_relat_1(sK1,sK0) = k7_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f83,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | spl2_6 ),
    inference(trivial_inequality_removal,[],[f81])).

fof(f81,plain,
    ( k7_relat_1(sK1,sK0) != k7_relat_1(sK1,sK0)
    | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | spl2_6 ),
    inference(superposition,[],[f79,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f79,plain,
    ( k7_relat_1(sK1,sK0) != k7_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),sK0)
    | spl2_6 ),
    inference(avatar_component_clause,[],[f77])).

% (30052)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
fof(f80,plain,
    ( ~ spl2_1
    | ~ spl2_6
    | spl2_2 ),
    inference(avatar_split_clause,[],[f66,f44,f77,f39])).

fof(f44,plain,
    ( spl2_2
  <=> k7_relat_1(sK1,sK0) = k7_relat_1(sK1,k1_setfam_1(k2_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f66,plain,
    ( k7_relat_1(sK1,sK0) != k7_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),sK0)
    | ~ v1_relat_1(sK1)
    | spl2_2 ),
    inference(superposition,[],[f46,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f22,f32])).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f23,f31])).

fof(f31,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f25,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f25,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f23,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(f46,plain,
    ( k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k1_setfam_1(k2_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),sK0)))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f47,plain,(
    ~ spl2_2 ),
    inference(avatar_split_clause,[],[f33,f44])).

fof(f33,plain,(
    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k1_setfam_1(k2_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),sK0))) ),
    inference(definition_unfolding,[],[f21,f32])).

fof(f21,plain,(
    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f16])).

fof(f16,plain,
    ( ? [X0,X1] :
        ( k7_relat_1(X1,X0) != k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
        & v1_relat_1(X1) )
   => ( k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] :
      ( k7_relat_1(X1,X0) != k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).

fof(f42,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f20,f39])).

fof(f20,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:23:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 1.27/0.55  % (30047)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.27/0.56  % (30068)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.27/0.56  % (30060)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.27/0.56  % (30045)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.56/0.57  % (30068)Refutation found. Thanks to Tanya!
% 1.56/0.57  % SZS status Theorem for theBenchmark
% 1.56/0.57  % SZS output start Proof for theBenchmark
% 1.56/0.57  fof(f93,plain,(
% 1.56/0.57    $false),
% 1.56/0.57    inference(avatar_sat_refutation,[],[f42,f47,f80,f88,f92])).
% 1.56/0.57  fof(f92,plain,(
% 1.56/0.57    spl2_7),
% 1.56/0.57    inference(avatar_contradiction_clause,[],[f89])).
% 1.56/0.57  fof(f89,plain,(
% 1.56/0.57    $false | spl2_7),
% 1.56/0.57    inference(unit_resulting_resolution,[],[f36,f87])).
% 1.56/0.57  fof(f87,plain,(
% 1.56/0.57    ~r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) | spl2_7),
% 1.56/0.57    inference(avatar_component_clause,[],[f85])).
% 1.56/0.57  fof(f85,plain,(
% 1.56/0.57    spl2_7 <=> r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1))),
% 1.56/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 1.56/0.57  fof(f36,plain,(
% 1.56/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.56/0.57    inference(equality_resolution,[],[f28])).
% 1.56/0.57  fof(f28,plain,(
% 1.56/0.57    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.56/0.57    inference(cnf_transformation,[],[f19])).
% 1.56/0.57  fof(f19,plain,(
% 1.56/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.56/0.57    inference(flattening,[],[f18])).
% 1.56/0.57  fof(f18,plain,(
% 1.56/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.56/0.57    inference(nnf_transformation,[],[f1])).
% 1.56/0.57  fof(f1,axiom,(
% 1.56/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.56/0.57  fof(f88,plain,(
% 1.56/0.57    ~spl2_1 | ~spl2_7 | spl2_6),
% 1.56/0.57    inference(avatar_split_clause,[],[f83,f77,f85,f39])).
% 1.56/0.57  fof(f39,plain,(
% 1.56/0.57    spl2_1 <=> v1_relat_1(sK1)),
% 1.56/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.56/0.57  fof(f77,plain,(
% 1.56/0.57    spl2_6 <=> k7_relat_1(sK1,sK0) = k7_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),sK0)),
% 1.56/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 1.56/0.57  fof(f83,plain,(
% 1.56/0.57    ~r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) | ~v1_relat_1(sK1) | spl2_6),
% 1.56/0.57    inference(trivial_inequality_removal,[],[f81])).
% 1.56/0.57  fof(f81,plain,(
% 1.56/0.57    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,sK0) | ~r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) | ~v1_relat_1(sK1) | spl2_6),
% 1.56/0.57    inference(superposition,[],[f79,f24])).
% 1.56/0.57  fof(f24,plain,(
% 1.56/0.57    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f15])).
% 1.56/0.57  fof(f15,plain,(
% 1.56/0.57    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.56/0.57    inference(flattening,[],[f14])).
% 1.56/0.57  fof(f14,plain,(
% 1.56/0.57    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.56/0.57    inference(ennf_transformation,[],[f9])).
% 1.56/0.57  fof(f9,axiom,(
% 1.56/0.57    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 1.56/0.57  fof(f79,plain,(
% 1.56/0.57    k7_relat_1(sK1,sK0) != k7_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),sK0) | spl2_6),
% 1.56/0.57    inference(avatar_component_clause,[],[f77])).
% 1.56/0.57  % (30052)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.56/0.57  fof(f80,plain,(
% 1.56/0.57    ~spl2_1 | ~spl2_6 | spl2_2),
% 1.56/0.57    inference(avatar_split_clause,[],[f66,f44,f77,f39])).
% 1.56/0.57  fof(f44,plain,(
% 1.56/0.57    spl2_2 <=> k7_relat_1(sK1,sK0) = k7_relat_1(sK1,k1_setfam_1(k2_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),sK0)))),
% 1.56/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.56/0.57  fof(f66,plain,(
% 1.56/0.57    k7_relat_1(sK1,sK0) != k7_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),sK0) | ~v1_relat_1(sK1) | spl2_2),
% 1.56/0.57    inference(superposition,[],[f46,f34])).
% 1.56/0.57  fof(f34,plain,(
% 1.56/0.57    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) | ~v1_relat_1(X2)) )),
% 1.56/0.57    inference(definition_unfolding,[],[f22,f32])).
% 1.56/0.57  fof(f32,plain,(
% 1.56/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 1.56/0.57    inference(definition_unfolding,[],[f23,f31])).
% 1.56/0.57  fof(f31,plain,(
% 1.56/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.56/0.57    inference(definition_unfolding,[],[f25,f30])).
% 1.56/0.57  fof(f30,plain,(
% 1.56/0.57    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f4])).
% 1.56/0.57  fof(f4,axiom,(
% 1.56/0.57    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.56/0.57  fof(f25,plain,(
% 1.56/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f3])).
% 1.56/0.57  fof(f3,axiom,(
% 1.56/0.57    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.56/0.57  fof(f23,plain,(
% 1.56/0.57    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f7])).
% 1.56/0.57  fof(f7,axiom,(
% 1.56/0.57    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.56/0.57  fof(f22,plain,(
% 1.56/0.57    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f13])).
% 1.56/0.57  fof(f13,plain,(
% 1.56/0.57    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 1.56/0.57    inference(ennf_transformation,[],[f8])).
% 1.56/0.57  fof(f8,axiom,(
% 1.56/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).
% 1.56/0.57  fof(f46,plain,(
% 1.56/0.57    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k1_setfam_1(k2_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),sK0))) | spl2_2),
% 1.56/0.57    inference(avatar_component_clause,[],[f44])).
% 1.56/0.57  fof(f47,plain,(
% 1.56/0.57    ~spl2_2),
% 1.56/0.57    inference(avatar_split_clause,[],[f33,f44])).
% 1.56/0.57  fof(f33,plain,(
% 1.56/0.57    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k1_setfam_1(k2_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),sK0)))),
% 1.56/0.57    inference(definition_unfolding,[],[f21,f32])).
% 1.56/0.57  fof(f21,plain,(
% 1.56/0.57    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))),
% 1.56/0.57    inference(cnf_transformation,[],[f17])).
% 1.56/0.57  fof(f17,plain,(
% 1.56/0.57    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0)) & v1_relat_1(sK1)),
% 1.56/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f16])).
% 1.56/0.57  fof(f16,plain,(
% 1.56/0.57    ? [X0,X1] : (k7_relat_1(X1,X0) != k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1)) => (k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0)) & v1_relat_1(sK1))),
% 1.56/0.57    introduced(choice_axiom,[])).
% 1.56/0.57  fof(f12,plain,(
% 1.56/0.57    ? [X0,X1] : (k7_relat_1(X1,X0) != k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 1.56/0.57    inference(ennf_transformation,[],[f11])).
% 1.56/0.57  fof(f11,negated_conjecture,(
% 1.56/0.57    ~! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 1.56/0.57    inference(negated_conjecture,[],[f10])).
% 1.56/0.57  fof(f10,conjecture,(
% 1.56/0.57    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).
% 1.56/0.57  fof(f42,plain,(
% 1.56/0.57    spl2_1),
% 1.56/0.57    inference(avatar_split_clause,[],[f20,f39])).
% 1.56/0.57  fof(f20,plain,(
% 1.56/0.57    v1_relat_1(sK1)),
% 1.56/0.57    inference(cnf_transformation,[],[f17])).
% 1.56/0.57  % SZS output end Proof for theBenchmark
% 1.56/0.57  % (30068)------------------------------
% 1.56/0.57  % (30068)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.57  % (30068)Termination reason: Refutation
% 1.56/0.57  
% 1.56/0.57  % (30068)Memory used [KB]: 10746
% 1.56/0.57  % (30068)Time elapsed: 0.092 s
% 1.56/0.57  % (30068)------------------------------
% 1.56/0.57  % (30068)------------------------------
% 1.56/0.58  % (30046)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.56/0.58  % (30063)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.56/0.58  % (30059)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.56/0.58  % (30044)Success in time 0.211 s
%------------------------------------------------------------------------------
