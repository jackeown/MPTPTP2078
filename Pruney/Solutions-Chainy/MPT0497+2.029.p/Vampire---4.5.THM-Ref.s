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
% DateTime   : Thu Dec  3 12:48:27 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 103 expanded)
%              Number of leaves         :   10 (  29 expanded)
%              Depth                    :   15
%              Number of atoms          :  139 ( 310 expanded)
%              Number of equality atoms :   53 ( 122 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f69,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f43,f59,f68])).

fof(f68,plain,
    ( ~ spl2_1
    | spl2_2 ),
    inference(avatar_contradiction_clause,[],[f67])).

fof(f67,plain,
    ( $false
    | ~ spl2_1
    | spl2_2 ),
    inference(subsumption_resolution,[],[f66,f40])).

fof(f40,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl2_2
  <=> r1_xboole_0(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f66,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl2_1 ),
    inference(subsumption_resolution,[],[f65,f22])).

fof(f22,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f65,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl2_1 ),
    inference(superposition,[],[f53,f37])).

fof(f37,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl2_1
  <=> k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f53,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(k7_relat_1(sK1,X0))
      | r1_xboole_0(k1_relat_1(sK1),X0) ) ),
    inference(superposition,[],[f32,f49])).

fof(f49,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0)) ),
    inference(resolution,[],[f31,f19])).

fof(f19,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 != k7_relat_1(sK1,sK0) )
    & ( r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 = k7_relat_1(sK1,sK0) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f16])).

fof(f16,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 = k7_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
        | k1_xboole_0 != k7_relat_1(sK1,sK0) )
      & ( r1_xboole_0(k1_relat_1(sK1),sK0)
        | k1_xboole_0 = k7_relat_1(sK1,sK0) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k7_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k7_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <~> r1_xboole_0(k1_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k7_relat_1(X1,X0)
        <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(X1),X0)) ) ),
    inference(definition_unfolding,[],[f28,f26])).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_setfam_1(k2_tarski(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f30,f26])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f59,plain,
    ( spl2_1
    | ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f58])).

fof(f58,plain,
    ( $false
    | spl2_1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f57,f19])).

fof(f57,plain,
    ( ~ v1_relat_1(sK1)
    | spl2_1
    | ~ spl2_2 ),
    inference(resolution,[],[f56,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f56,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | spl2_1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f55,f36])).

fof(f36,plain,
    ( k1_xboole_0 != k7_relat_1(sK1,sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f55,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl2_2 ),
    inference(trivial_inequality_removal,[],[f54])).

fof(f54,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl2_2 ),
    inference(superposition,[],[f24,f51])).

fof(f51,plain,
    ( k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl2_2 ),
    inference(superposition,[],[f49,f46])).

fof(f46,plain,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(k1_relat_1(sK1),sK0))
    | ~ spl2_2 ),
    inference(resolution,[],[f33,f41])).

fof(f41,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) ) ),
    inference(definition_unfolding,[],[f29,f26])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f43,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f21,f39,f35])).

fof(f21,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 != k7_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f42,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f20,f39,f35])).

fof(f20,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:17:31 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.43  % (2358)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.19/0.43  % (2363)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.19/0.43  % (2363)Refutation found. Thanks to Tanya!
% 0.19/0.43  % SZS status Theorem for theBenchmark
% 0.19/0.43  % SZS output start Proof for theBenchmark
% 0.19/0.43  fof(f69,plain,(
% 0.19/0.43    $false),
% 0.19/0.43    inference(avatar_sat_refutation,[],[f42,f43,f59,f68])).
% 0.19/0.43  fof(f68,plain,(
% 0.19/0.43    ~spl2_1 | spl2_2),
% 0.19/0.43    inference(avatar_contradiction_clause,[],[f67])).
% 0.19/0.43  fof(f67,plain,(
% 0.19/0.43    $false | (~spl2_1 | spl2_2)),
% 0.19/0.43    inference(subsumption_resolution,[],[f66,f40])).
% 0.19/0.43  fof(f40,plain,(
% 0.19/0.43    ~r1_xboole_0(k1_relat_1(sK1),sK0) | spl2_2),
% 0.19/0.43    inference(avatar_component_clause,[],[f39])).
% 0.19/0.43  fof(f39,plain,(
% 0.19/0.43    spl2_2 <=> r1_xboole_0(k1_relat_1(sK1),sK0)),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.19/0.43  fof(f66,plain,(
% 0.19/0.43    r1_xboole_0(k1_relat_1(sK1),sK0) | ~spl2_1),
% 0.19/0.43    inference(subsumption_resolution,[],[f65,f22])).
% 0.19/0.43  fof(f22,plain,(
% 0.19/0.43    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.19/0.43    inference(cnf_transformation,[],[f4])).
% 0.19/0.43  fof(f4,axiom,(
% 0.19/0.43    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.19/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.19/0.43  fof(f65,plain,(
% 0.19/0.43    k1_xboole_0 != k1_relat_1(k1_xboole_0) | r1_xboole_0(k1_relat_1(sK1),sK0) | ~spl2_1),
% 0.19/0.43    inference(superposition,[],[f53,f37])).
% 0.19/0.43  fof(f37,plain,(
% 0.19/0.43    k1_xboole_0 = k7_relat_1(sK1,sK0) | ~spl2_1),
% 0.19/0.43    inference(avatar_component_clause,[],[f35])).
% 0.19/0.43  fof(f35,plain,(
% 0.19/0.43    spl2_1 <=> k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.19/0.43  fof(f53,plain,(
% 0.19/0.43    ( ! [X0] : (k1_xboole_0 != k1_relat_1(k7_relat_1(sK1,X0)) | r1_xboole_0(k1_relat_1(sK1),X0)) )),
% 0.19/0.43    inference(superposition,[],[f32,f49])).
% 0.19/0.43  fof(f49,plain,(
% 0.19/0.43    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0))) )),
% 0.19/0.43    inference(resolution,[],[f31,f19])).
% 0.19/0.43  fof(f19,plain,(
% 0.19/0.43    v1_relat_1(sK1)),
% 0.19/0.43    inference(cnf_transformation,[],[f17])).
% 0.19/0.43  fof(f17,plain,(
% 0.19/0.43    (~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k7_relat_1(sK1,sK0)) & (r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)) & v1_relat_1(sK1)),
% 0.19/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f16])).
% 0.19/0.43  fof(f16,plain,(
% 0.19/0.43    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k7_relat_1(sK1,sK0)) & (r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)) & v1_relat_1(sK1))),
% 0.19/0.43    introduced(choice_axiom,[])).
% 0.19/0.43  fof(f15,plain,(
% 0.19/0.43    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) & v1_relat_1(X1))),
% 0.19/0.43    inference(flattening,[],[f14])).
% 0.19/0.43  fof(f14,plain,(
% 0.19/0.43    ? [X0,X1] : (((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0))) & v1_relat_1(X1))),
% 0.19/0.43    inference(nnf_transformation,[],[f9])).
% 0.19/0.43  fof(f9,plain,(
% 0.19/0.43    ? [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <~> r1_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 0.19/0.43    inference(ennf_transformation,[],[f8])).
% 0.19/0.43  fof(f8,negated_conjecture,(
% 0.19/0.43    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.19/0.43    inference(negated_conjecture,[],[f7])).
% 0.19/0.43  fof(f7,conjecture,(
% 0.19/0.43    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.19/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).
% 0.19/0.43  fof(f31,plain,(
% 0.19/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(X1),X0))) )),
% 0.19/0.43    inference(definition_unfolding,[],[f28,f26])).
% 0.19/0.43  fof(f26,plain,(
% 0.19/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.19/0.43    inference(cnf_transformation,[],[f2])).
% 0.19/0.43  fof(f2,axiom,(
% 0.19/0.43    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.19/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.19/0.43  fof(f28,plain,(
% 0.19/0.43    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.19/0.43    inference(cnf_transformation,[],[f13])).
% 0.19/0.43  fof(f13,plain,(
% 0.19/0.43    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.19/0.43    inference(ennf_transformation,[],[f6])).
% 0.19/0.43  fof(f6,axiom,(
% 0.19/0.43    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.19/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 0.19/0.43  fof(f32,plain,(
% 0.19/0.43    ( ! [X0,X1] : (k1_xboole_0 != k1_setfam_1(k2_tarski(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.19/0.43    inference(definition_unfolding,[],[f30,f26])).
% 0.19/0.43  fof(f30,plain,(
% 0.19/0.43    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.19/0.43    inference(cnf_transformation,[],[f18])).
% 0.19/0.43  fof(f18,plain,(
% 0.19/0.43    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.19/0.43    inference(nnf_transformation,[],[f1])).
% 0.19/0.43  fof(f1,axiom,(
% 0.19/0.43    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.19/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.19/0.43  fof(f59,plain,(
% 0.19/0.43    spl2_1 | ~spl2_2),
% 0.19/0.43    inference(avatar_contradiction_clause,[],[f58])).
% 0.19/0.43  fof(f58,plain,(
% 0.19/0.43    $false | (spl2_1 | ~spl2_2)),
% 0.19/0.43    inference(subsumption_resolution,[],[f57,f19])).
% 0.19/0.43  fof(f57,plain,(
% 0.19/0.43    ~v1_relat_1(sK1) | (spl2_1 | ~spl2_2)),
% 0.19/0.43    inference(resolution,[],[f56,f27])).
% 0.19/0.43  fof(f27,plain,(
% 0.19/0.43    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.19/0.43    inference(cnf_transformation,[],[f12])).
% 0.19/0.43  fof(f12,plain,(
% 0.19/0.43    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.19/0.43    inference(ennf_transformation,[],[f3])).
% 0.19/0.43  fof(f3,axiom,(
% 0.19/0.43    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.19/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.19/0.43  fof(f56,plain,(
% 0.19/0.43    ~v1_relat_1(k7_relat_1(sK1,sK0)) | (spl2_1 | ~spl2_2)),
% 0.19/0.43    inference(subsumption_resolution,[],[f55,f36])).
% 0.19/0.43  fof(f36,plain,(
% 0.19/0.43    k1_xboole_0 != k7_relat_1(sK1,sK0) | spl2_1),
% 0.19/0.43    inference(avatar_component_clause,[],[f35])).
% 0.19/0.43  fof(f55,plain,(
% 0.19/0.43    k1_xboole_0 = k7_relat_1(sK1,sK0) | ~v1_relat_1(k7_relat_1(sK1,sK0)) | ~spl2_2),
% 0.19/0.43    inference(trivial_inequality_removal,[],[f54])).
% 0.19/0.43  fof(f54,plain,(
% 0.19/0.43    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k7_relat_1(sK1,sK0) | ~v1_relat_1(k7_relat_1(sK1,sK0)) | ~spl2_2),
% 0.19/0.43    inference(superposition,[],[f24,f51])).
% 0.19/0.43  fof(f51,plain,(
% 0.19/0.43    k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0)) | ~spl2_2),
% 0.19/0.43    inference(superposition,[],[f49,f46])).
% 0.19/0.43  fof(f46,plain,(
% 0.19/0.43    k1_xboole_0 = k1_setfam_1(k2_tarski(k1_relat_1(sK1),sK0)) | ~spl2_2),
% 0.19/0.43    inference(resolution,[],[f33,f41])).
% 0.19/0.43  fof(f41,plain,(
% 0.19/0.43    r1_xboole_0(k1_relat_1(sK1),sK0) | ~spl2_2),
% 0.19/0.43    inference(avatar_component_clause,[],[f39])).
% 0.19/0.43  fof(f33,plain,(
% 0.19/0.43    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.19/0.43    inference(definition_unfolding,[],[f29,f26])).
% 0.19/0.43  fof(f29,plain,(
% 0.19/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.19/0.43    inference(cnf_transformation,[],[f18])).
% 0.19/0.43  fof(f24,plain,(
% 0.19/0.43    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 0.19/0.43    inference(cnf_transformation,[],[f11])).
% 0.19/0.43  fof(f11,plain,(
% 0.19/0.43    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.19/0.43    inference(flattening,[],[f10])).
% 0.19/0.43  fof(f10,plain,(
% 0.19/0.43    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.19/0.43    inference(ennf_transformation,[],[f5])).
% 0.19/0.43  fof(f5,axiom,(
% 0.19/0.43    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.19/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 0.19/0.43  fof(f43,plain,(
% 0.19/0.43    ~spl2_1 | ~spl2_2),
% 0.19/0.43    inference(avatar_split_clause,[],[f21,f39,f35])).
% 0.19/0.43  fof(f21,plain,(
% 0.19/0.43    ~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k7_relat_1(sK1,sK0)),
% 0.19/0.43    inference(cnf_transformation,[],[f17])).
% 0.19/0.43  fof(f42,plain,(
% 0.19/0.43    spl2_1 | spl2_2),
% 0.19/0.43    inference(avatar_split_clause,[],[f20,f39,f35])).
% 0.19/0.43  fof(f20,plain,(
% 0.19/0.43    r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.19/0.43    inference(cnf_transformation,[],[f17])).
% 0.19/0.43  % SZS output end Proof for theBenchmark
% 0.19/0.43  % (2363)------------------------------
% 0.19/0.43  % (2363)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.43  % (2363)Termination reason: Refutation
% 0.19/0.43  
% 0.19/0.43  % (2363)Memory used [KB]: 10618
% 0.19/0.43  % (2363)Time elapsed: 0.036 s
% 0.19/0.43  % (2363)------------------------------
% 0.19/0.43  % (2363)------------------------------
% 0.19/0.43  % (2367)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.19/0.44  % (2353)Success in time 0.089 s
%------------------------------------------------------------------------------
