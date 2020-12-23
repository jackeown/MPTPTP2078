%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   62 (  95 expanded)
%              Number of leaves         :   16 (  42 expanded)
%              Depth                    :    6
%              Number of atoms          :  184 ( 270 expanded)
%              Number of equality atoms :   31 (  47 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f86,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f33,f37,f41,f49,f57,f63,f70,f75,f81,f85])).

fof(f85,plain,
    ( spl1_1
    | ~ spl1_2
    | ~ spl1_10
    | ~ spl1_12 ),
    inference(avatar_contradiction_clause,[],[f84])).

fof(f84,plain,
    ( $false
    | spl1_1
    | ~ spl1_2
    | ~ spl1_10
    | ~ spl1_12 ),
    inference(subsumption_resolution,[],[f83,f32])).

fof(f32,plain,
    ( v1_relat_1(sK0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl1_2
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f83,plain,
    ( ~ v1_relat_1(sK0)
    | spl1_1
    | ~ spl1_10
    | ~ spl1_12 ),
    inference(subsumption_resolution,[],[f82,f27])).

fof(f27,plain,
    ( sK0 != k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0)))
    | spl1_1 ),
    inference(avatar_component_clause,[],[f25])).

fof(f25,plain,
    ( spl1_1
  <=> sK0 = k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f82,plain,
    ( sK0 = k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0)))
    | ~ v1_relat_1(sK0)
    | ~ spl1_10
    | ~ spl1_12 ),
    inference(resolution,[],[f80,f69])).

fof(f69,plain,
    ( r1_tarski(sK0,sK0)
    | ~ spl1_10 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl1_10
  <=> r1_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f80,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK0,X0)
        | sK0 = k5_relat_1(sK0,k6_relat_1(k2_relat_1(X0)))
        | ~ v1_relat_1(X0) )
    | ~ spl1_12 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl1_12
  <=> ! [X0] :
        ( sK0 = k5_relat_1(sK0,k6_relat_1(k2_relat_1(X0)))
        | ~ r1_tarski(sK0,X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).

fof(f81,plain,
    ( spl1_12
    | ~ spl1_2
    | ~ spl1_4
    | ~ spl1_11 ),
    inference(avatar_split_clause,[],[f77,f73,f39,f30,f79])).

fof(f39,plain,
    ( spl1_4
  <=> ! [X1,X0] :
        ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f73,plain,
    ( spl1_11
  <=> ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK0),X0)
        | sK0 = k5_relat_1(sK0,k6_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f77,plain,
    ( ! [X0] :
        ( sK0 = k5_relat_1(sK0,k6_relat_1(k2_relat_1(X0)))
        | ~ r1_tarski(sK0,X0)
        | ~ v1_relat_1(X0) )
    | ~ spl1_2
    | ~ spl1_4
    | ~ spl1_11 ),
    inference(subsumption_resolution,[],[f76,f32])).

fof(f76,plain,
    ( ! [X0] :
        ( sK0 = k5_relat_1(sK0,k6_relat_1(k2_relat_1(X0)))
        | ~ r1_tarski(sK0,X0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(sK0) )
    | ~ spl1_4
    | ~ spl1_11 ),
    inference(resolution,[],[f74,f40])).

fof(f40,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f39])).

fof(f74,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK0),X0)
        | sK0 = k5_relat_1(sK0,k6_relat_1(X0)) )
    | ~ spl1_11 ),
    inference(avatar_component_clause,[],[f73])).

fof(f75,plain,
    ( spl1_11
    | ~ spl1_2
    | ~ spl1_8 ),
    inference(avatar_split_clause,[],[f71,f55,f30,f73])).

fof(f55,plain,
    ( spl1_8
  <=> ! [X1,X0] :
        ( k5_relat_1(X1,k6_relat_1(X0)) = X1
        | ~ r1_tarski(k2_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f71,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK0),X0)
        | sK0 = k5_relat_1(sK0,k6_relat_1(X0)) )
    | ~ spl1_2
    | ~ spl1_8 ),
    inference(resolution,[],[f56,f32])).

fof(f56,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ r1_tarski(k2_relat_1(X1),X0)
        | k5_relat_1(X1,k6_relat_1(X0)) = X1 )
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f55])).

fof(f70,plain,
    ( spl1_10
    | ~ spl1_2
    | ~ spl1_6
    | ~ spl1_9 ),
    inference(avatar_split_clause,[],[f65,f60,f47,f30,f67])).

fof(f47,plain,
    ( spl1_6
  <=> ! [X1,X0] :
        ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f60,plain,
    ( spl1_9
  <=> sK0 = k5_relat_1(k6_relat_1(k1_relat_1(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f65,plain,
    ( r1_tarski(sK0,sK0)
    | ~ spl1_2
    | ~ spl1_6
    | ~ spl1_9 ),
    inference(subsumption_resolution,[],[f64,f32])).

fof(f64,plain,
    ( r1_tarski(sK0,sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_6
    | ~ spl1_9 ),
    inference(superposition,[],[f48,f62])).

fof(f62,plain,
    ( sK0 = k5_relat_1(k6_relat_1(k1_relat_1(sK0)),sK0)
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f60])).

fof(f48,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        | ~ v1_relat_1(X1) )
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f47])).

fof(f63,plain,
    ( spl1_9
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f58,f35,f30,f60])).

fof(f35,plain,
    ( spl1_3
  <=> ! [X0] :
        ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f58,plain,
    ( sK0 = k5_relat_1(k6_relat_1(k1_relat_1(sK0)),sK0)
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(resolution,[],[f36,f32])).

fof(f36,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 )
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f35])).

fof(f57,plain,(
    spl1_8 ),
    inference(avatar_split_clause,[],[f23,f55])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(f49,plain,(
    spl1_6 ),
    inference(avatar_split_clause,[],[f22,f47])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).

fof(f41,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f20,f39])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f37,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f18,f35])).

fof(f18,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

fof(f33,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f16,f30])).

fof(f16,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( sK0 != k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0)))
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f14])).

fof(f14,plain,
    ( ? [X0] :
        ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) != X0
        & v1_relat_1(X0) )
   => ( sK0 != k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0)))
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) != X0
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(f28,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f17,f25])).

fof(f17,plain,(
    sK0 != k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0))) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:33:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.41  % (8356)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.43  % (8355)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.43  % (8355)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f86,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(avatar_sat_refutation,[],[f28,f33,f37,f41,f49,f57,f63,f70,f75,f81,f85])).
% 0.21/0.43  fof(f85,plain,(
% 0.21/0.43    spl1_1 | ~spl1_2 | ~spl1_10 | ~spl1_12),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f84])).
% 0.21/0.43  fof(f84,plain,(
% 0.21/0.43    $false | (spl1_1 | ~spl1_2 | ~spl1_10 | ~spl1_12)),
% 0.21/0.43    inference(subsumption_resolution,[],[f83,f32])).
% 0.21/0.43  fof(f32,plain,(
% 0.21/0.43    v1_relat_1(sK0) | ~spl1_2),
% 0.21/0.43    inference(avatar_component_clause,[],[f30])).
% 0.21/0.43  fof(f30,plain,(
% 0.21/0.43    spl1_2 <=> v1_relat_1(sK0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.21/0.43  fof(f83,plain,(
% 0.21/0.43    ~v1_relat_1(sK0) | (spl1_1 | ~spl1_10 | ~spl1_12)),
% 0.21/0.43    inference(subsumption_resolution,[],[f82,f27])).
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    sK0 != k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0))) | spl1_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f25])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    spl1_1 <=> sK0 = k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.43  fof(f82,plain,(
% 0.21/0.43    sK0 = k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0))) | ~v1_relat_1(sK0) | (~spl1_10 | ~spl1_12)),
% 0.21/0.43    inference(resolution,[],[f80,f69])).
% 0.21/0.43  fof(f69,plain,(
% 0.21/0.43    r1_tarski(sK0,sK0) | ~spl1_10),
% 0.21/0.43    inference(avatar_component_clause,[],[f67])).
% 0.21/0.43  fof(f67,plain,(
% 0.21/0.43    spl1_10 <=> r1_tarski(sK0,sK0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).
% 0.21/0.43  fof(f80,plain,(
% 0.21/0.43    ( ! [X0] : (~r1_tarski(sK0,X0) | sK0 = k5_relat_1(sK0,k6_relat_1(k2_relat_1(X0))) | ~v1_relat_1(X0)) ) | ~spl1_12),
% 0.21/0.43    inference(avatar_component_clause,[],[f79])).
% 0.21/0.43  fof(f79,plain,(
% 0.21/0.43    spl1_12 <=> ! [X0] : (sK0 = k5_relat_1(sK0,k6_relat_1(k2_relat_1(X0))) | ~r1_tarski(sK0,X0) | ~v1_relat_1(X0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).
% 0.21/0.43  fof(f81,plain,(
% 0.21/0.43    spl1_12 | ~spl1_2 | ~spl1_4 | ~spl1_11),
% 0.21/0.43    inference(avatar_split_clause,[],[f77,f73,f39,f30,f79])).
% 0.21/0.43  fof(f39,plain,(
% 0.21/0.43    spl1_4 <=> ! [X1,X0] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.21/0.43  fof(f73,plain,(
% 0.21/0.43    spl1_11 <=> ! [X0] : (~r1_tarski(k2_relat_1(sK0),X0) | sK0 = k5_relat_1(sK0,k6_relat_1(X0)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).
% 0.21/0.43  fof(f77,plain,(
% 0.21/0.43    ( ! [X0] : (sK0 = k5_relat_1(sK0,k6_relat_1(k2_relat_1(X0))) | ~r1_tarski(sK0,X0) | ~v1_relat_1(X0)) ) | (~spl1_2 | ~spl1_4 | ~spl1_11)),
% 0.21/0.43    inference(subsumption_resolution,[],[f76,f32])).
% 0.21/0.43  fof(f76,plain,(
% 0.21/0.43    ( ! [X0] : (sK0 = k5_relat_1(sK0,k6_relat_1(k2_relat_1(X0))) | ~r1_tarski(sK0,X0) | ~v1_relat_1(X0) | ~v1_relat_1(sK0)) ) | (~spl1_4 | ~spl1_11)),
% 0.21/0.43    inference(resolution,[],[f74,f40])).
% 0.21/0.43  fof(f40,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl1_4),
% 0.21/0.43    inference(avatar_component_clause,[],[f39])).
% 0.21/0.43  fof(f74,plain,(
% 0.21/0.43    ( ! [X0] : (~r1_tarski(k2_relat_1(sK0),X0) | sK0 = k5_relat_1(sK0,k6_relat_1(X0))) ) | ~spl1_11),
% 0.21/0.43    inference(avatar_component_clause,[],[f73])).
% 0.21/0.43  fof(f75,plain,(
% 0.21/0.43    spl1_11 | ~spl1_2 | ~spl1_8),
% 0.21/0.43    inference(avatar_split_clause,[],[f71,f55,f30,f73])).
% 0.21/0.43  fof(f55,plain,(
% 0.21/0.43    spl1_8 <=> ! [X1,X0] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.21/0.43  fof(f71,plain,(
% 0.21/0.43    ( ! [X0] : (~r1_tarski(k2_relat_1(sK0),X0) | sK0 = k5_relat_1(sK0,k6_relat_1(X0))) ) | (~spl1_2 | ~spl1_8)),
% 0.21/0.43    inference(resolution,[],[f56,f32])).
% 0.21/0.43  fof(f56,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1) ) | ~spl1_8),
% 0.21/0.43    inference(avatar_component_clause,[],[f55])).
% 0.21/0.43  fof(f70,plain,(
% 0.21/0.43    spl1_10 | ~spl1_2 | ~spl1_6 | ~spl1_9),
% 0.21/0.43    inference(avatar_split_clause,[],[f65,f60,f47,f30,f67])).
% 0.21/0.43  fof(f47,plain,(
% 0.21/0.43    spl1_6 <=> ! [X1,X0] : (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) | ~v1_relat_1(X1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.21/0.43  fof(f60,plain,(
% 0.21/0.43    spl1_9 <=> sK0 = k5_relat_1(k6_relat_1(k1_relat_1(sK0)),sK0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.21/0.43  fof(f65,plain,(
% 0.21/0.43    r1_tarski(sK0,sK0) | (~spl1_2 | ~spl1_6 | ~spl1_9)),
% 0.21/0.43    inference(subsumption_resolution,[],[f64,f32])).
% 0.21/0.43  fof(f64,plain,(
% 0.21/0.43    r1_tarski(sK0,sK0) | ~v1_relat_1(sK0) | (~spl1_6 | ~spl1_9)),
% 0.21/0.43    inference(superposition,[],[f48,f62])).
% 0.21/0.43  fof(f62,plain,(
% 0.21/0.43    sK0 = k5_relat_1(k6_relat_1(k1_relat_1(sK0)),sK0) | ~spl1_9),
% 0.21/0.43    inference(avatar_component_clause,[],[f60])).
% 0.21/0.43  fof(f48,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) | ~v1_relat_1(X1)) ) | ~spl1_6),
% 0.21/0.43    inference(avatar_component_clause,[],[f47])).
% 0.21/0.43  fof(f63,plain,(
% 0.21/0.43    spl1_9 | ~spl1_2 | ~spl1_3),
% 0.21/0.43    inference(avatar_split_clause,[],[f58,f35,f30,f60])).
% 0.21/0.43  fof(f35,plain,(
% 0.21/0.43    spl1_3 <=> ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.21/0.43  fof(f58,plain,(
% 0.21/0.43    sK0 = k5_relat_1(k6_relat_1(k1_relat_1(sK0)),sK0) | (~spl1_2 | ~spl1_3)),
% 0.21/0.43    inference(resolution,[],[f36,f32])).
% 0.21/0.43  fof(f36,plain,(
% 0.21/0.43    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0) ) | ~spl1_3),
% 0.21/0.43    inference(avatar_component_clause,[],[f35])).
% 0.21/0.43  fof(f57,plain,(
% 0.21/0.43    spl1_8),
% 0.21/0.43    inference(avatar_split_clause,[],[f23,f55])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f13])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.43    inference(flattening,[],[f12])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).
% 0.21/0.43  fof(f49,plain,(
% 0.21/0.43    spl1_6),
% 0.21/0.43    inference(avatar_split_clause,[],[f22,f47])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) | ~v1_relat_1(X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f11])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).
% 0.21/0.43  fof(f41,plain,(
% 0.21/0.43    spl1_4),
% 0.21/0.43    inference(avatar_split_clause,[],[f20,f39])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f10])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.43    inference(flattening,[],[f9])).
% 0.21/0.43  fof(f9,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 0.21/0.43  fof(f37,plain,(
% 0.21/0.43    spl1_3),
% 0.21/0.43    inference(avatar_split_clause,[],[f18,f35])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f8])).
% 0.21/0.43  fof(f8,plain,(
% 0.21/0.43    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).
% 0.21/0.43  fof(f33,plain,(
% 0.21/0.43    spl1_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f16,f30])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    v1_relat_1(sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f15])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    sK0 != k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0))) & v1_relat_1(sK0)),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f14])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ? [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) != X0 & v1_relat_1(X0)) => (sK0 != k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0))) & v1_relat_1(sK0))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f7,plain,(
% 0.21/0.43    ? [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) != X0 & v1_relat_1(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f6])).
% 0.21/0.43  fof(f6,negated_conjecture,(
% 0.21/0.43    ~! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 0.21/0.43    inference(negated_conjecture,[],[f5])).
% 0.21/0.43  fof(f5,conjecture,(
% 0.21/0.43    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).
% 0.21/0.43  fof(f28,plain,(
% 0.21/0.43    ~spl1_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f17,f25])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    sK0 != k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0)))),
% 0.21/0.43    inference(cnf_transformation,[],[f15])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (8355)------------------------------
% 0.21/0.43  % (8355)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (8355)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (8355)Memory used [KB]: 10490
% 0.21/0.43  % (8355)Time elapsed: 0.009 s
% 0.21/0.43  % (8355)------------------------------
% 0.21/0.43  % (8355)------------------------------
% 0.21/0.44  % (8349)Success in time 0.081 s
%------------------------------------------------------------------------------
