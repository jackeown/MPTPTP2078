%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:00 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 139 expanded)
%              Number of leaves         :   21 (  64 expanded)
%              Depth                    :    7
%              Number of atoms          :  229 ( 399 expanded)
%              Number of equality atoms :   24 (  49 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f297,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f33,f38,f42,f46,f50,f54,f64,f70,f80,f96,f212,f229,f271,f281,f296])).

fof(f296,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | spl3_49 ),
    inference(avatar_contradiction_clause,[],[f295])).

fof(f295,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_4
    | spl3_49 ),
    inference(subsumption_resolution,[],[f294,f37])).

fof(f37,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl3_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f294,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl3_4
    | spl3_49 ),
    inference(resolution,[],[f280,f41])).

fof(f41,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k8_relat_1(X0,X1))
        | ~ v1_relat_1(X1) )
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl3_4
  <=> ! [X1,X0] :
        ( v1_relat_1(k8_relat_1(X0,X1))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f280,plain,
    ( ~ v1_relat_1(k8_relat_1(sK0,sK2))
    | spl3_49 ),
    inference(avatar_component_clause,[],[f278])).

fof(f278,plain,
    ( spl3_49
  <=> v1_relat_1(k8_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).

fof(f281,plain,
    ( ~ spl3_49
    | spl3_1
    | ~ spl3_6
    | ~ spl3_48 ),
    inference(avatar_split_clause,[],[f276,f268,f48,f25,f278])).

fof(f25,plain,
    ( spl3_1
  <=> k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f48,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( k8_relat_1(X0,X1) = X1
        | ~ r1_tarski(k2_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f268,plain,
    ( spl3_48
  <=> r1_tarski(k2_relat_1(k8_relat_1(sK0,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).

fof(f276,plain,
    ( ~ v1_relat_1(k8_relat_1(sK0,sK2))
    | spl3_1
    | ~ spl3_6
    | ~ spl3_48 ),
    inference(subsumption_resolution,[],[f272,f27])).

fof(f27,plain,
    ( k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f25])).

fof(f272,plain,
    ( k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2))
    | ~ v1_relat_1(k8_relat_1(sK0,sK2))
    | ~ spl3_6
    | ~ spl3_48 ),
    inference(resolution,[],[f270,f49])).

fof(f49,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(X1),X0)
        | k8_relat_1(X0,X1) = X1
        | ~ v1_relat_1(X1) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f48])).

fof(f270,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(sK0,sK2)),sK1)
    | ~ spl3_48 ),
    inference(avatar_component_clause,[],[f268])).

fof(f271,plain,
    ( spl3_48
    | ~ spl3_15
    | ~ spl3_39 ),
    inference(avatar_split_clause,[],[f250,f227,f94,f268])).

fof(f94,plain,
    ( spl3_15
  <=> ! [X0] : k8_relat_1(X0,sK2) = k8_relat_1(X0,k8_relat_1(X0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f227,plain,
    ( spl3_39
  <=> ! [X0] : r1_tarski(k2_relat_1(k8_relat_1(sK0,k8_relat_1(X0,sK2))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f250,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(sK0,sK2)),sK1)
    | ~ spl3_15
    | ~ spl3_39 ),
    inference(superposition,[],[f228,f95])).

fof(f95,plain,
    ( ! [X0] : k8_relat_1(X0,sK2) = k8_relat_1(X0,k8_relat_1(X0,sK2))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f94])).

fof(f228,plain,
    ( ! [X0] : r1_tarski(k2_relat_1(k8_relat_1(sK0,k8_relat_1(X0,sK2))),sK1)
    | ~ spl3_39 ),
    inference(avatar_component_clause,[],[f227])).

fof(f229,plain,
    ( spl3_39
    | ~ spl3_2
    | ~ spl3_36 ),
    inference(avatar_split_clause,[],[f221,f210,f30,f227])).

fof(f30,plain,
    ( spl3_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f210,plain,
    ( spl3_36
  <=> ! [X1,X0,X2] :
        ( ~ r1_tarski(X0,X1)
        | r1_tarski(k2_relat_1(k8_relat_1(X0,k8_relat_1(X2,sK2))),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f221,plain,
    ( ! [X0] : r1_tarski(k2_relat_1(k8_relat_1(sK0,k8_relat_1(X0,sK2))),sK1)
    | ~ spl3_2
    | ~ spl3_36 ),
    inference(resolution,[],[f211,f32])).

fof(f32,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f30])).

fof(f211,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | r1_tarski(k2_relat_1(k8_relat_1(X0,k8_relat_1(X2,sK2))),X1) )
    | ~ spl3_36 ),
    inference(avatar_component_clause,[],[f210])).

fof(f212,plain,
    ( spl3_36
    | ~ spl3_3
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f206,f78,f35,f210])).

fof(f78,plain,
    ( spl3_12
  <=> ! [X3,X5,X2,X4] :
        ( r1_tarski(k2_relat_1(k8_relat_1(X2,k8_relat_1(X3,X4))),X5)
        | ~ r1_tarski(X2,X5)
        | ~ v1_relat_1(X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f206,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | r1_tarski(k2_relat_1(k8_relat_1(X0,k8_relat_1(X2,sK2))),X1) )
    | ~ spl3_3
    | ~ spl3_12 ),
    inference(resolution,[],[f79,f37])).

fof(f79,plain,
    ( ! [X4,X2,X5,X3] :
        ( ~ v1_relat_1(X4)
        | ~ r1_tarski(X2,X5)
        | r1_tarski(k2_relat_1(k8_relat_1(X2,k8_relat_1(X3,X4))),X5) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f78])).

fof(f96,plain,
    ( spl3_15
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f91,f68,f35,f94])).

fof(f68,plain,
    ( spl3_10
  <=> ! [X1,X0] :
        ( k8_relat_1(X0,X1) = k8_relat_1(X0,k8_relat_1(X0,X1))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f91,plain,
    ( ! [X0] : k8_relat_1(X0,sK2) = k8_relat_1(X0,k8_relat_1(X0,sK2))
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(resolution,[],[f69,f37])).

fof(f69,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k8_relat_1(X0,X1) = k8_relat_1(X0,k8_relat_1(X0,X1)) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f68])).

fof(f80,plain,
    ( spl3_12
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f72,f62,f40,f78])).

fof(f62,plain,
    ( spl3_9
  <=> ! [X1,X3,X2] :
        ( ~ r1_tarski(X1,X2)
        | r1_tarski(k2_relat_1(k8_relat_1(X1,X3)),X2)
        | ~ v1_relat_1(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f72,plain,
    ( ! [X4,X2,X5,X3] :
        ( r1_tarski(k2_relat_1(k8_relat_1(X2,k8_relat_1(X3,X4))),X5)
        | ~ r1_tarski(X2,X5)
        | ~ v1_relat_1(X4) )
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(resolution,[],[f63,f41])).

fof(f63,plain,
    ( ! [X2,X3,X1] :
        ( ~ v1_relat_1(X3)
        | r1_tarski(k2_relat_1(k8_relat_1(X1,X3)),X2)
        | ~ r1_tarski(X1,X2) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f62])).

fof(f70,plain,
    ( spl3_10
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f66,f48,f44,f40,f68])).

fof(f44,plain,
    ( spl3_5
  <=> ! [X1,X0] :
        ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f66,plain,
    ( ! [X0,X1] :
        ( k8_relat_1(X0,X1) = k8_relat_1(X0,k8_relat_1(X0,X1))
        | ~ v1_relat_1(X1) )
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f65,f41])).

fof(f65,plain,
    ( ! [X0,X1] :
        ( k8_relat_1(X0,X1) = k8_relat_1(X0,k8_relat_1(X0,X1))
        | ~ v1_relat_1(k8_relat_1(X0,X1))
        | ~ v1_relat_1(X1) )
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(resolution,[],[f49,f45])).

fof(f45,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
        | ~ v1_relat_1(X1) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f44])).

fof(f64,plain,
    ( spl3_9
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f56,f52,f44,f62])).

fof(f52,plain,
    ( spl3_7
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,X2)
        | ~ r1_tarski(X1,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f56,plain,
    ( ! [X2,X3,X1] :
        ( ~ r1_tarski(X1,X2)
        | r1_tarski(k2_relat_1(k8_relat_1(X1,X3)),X2)
        | ~ v1_relat_1(X3) )
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(resolution,[],[f53,f45])).

fof(f53,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_tarski(X1,X2)
        | r1_tarski(X0,X2) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f52])).

fof(f54,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f23,f52])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f50,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f22,f48])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

fof(f46,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f21,f44])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_relat_1)).

fof(f42,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f20,f40])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f38,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f17,f35])).

fof(f17,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2))
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2))
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2))
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_relat_1)).

fof(f33,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f18,f30])).

fof(f18,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f28,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f19,f25])).

fof(f19,plain,(
    k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n012.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:39:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.42  % (29672)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.42  % (29672)Refutation found. Thanks to Tanya!
% 0.22/0.42  % SZS status Theorem for theBenchmark
% 0.22/0.42  % SZS output start Proof for theBenchmark
% 0.22/0.42  fof(f297,plain,(
% 0.22/0.42    $false),
% 0.22/0.42    inference(avatar_sat_refutation,[],[f28,f33,f38,f42,f46,f50,f54,f64,f70,f80,f96,f212,f229,f271,f281,f296])).
% 0.22/0.42  fof(f296,plain,(
% 0.22/0.42    ~spl3_3 | ~spl3_4 | spl3_49),
% 0.22/0.42    inference(avatar_contradiction_clause,[],[f295])).
% 0.22/0.42  fof(f295,plain,(
% 0.22/0.42    $false | (~spl3_3 | ~spl3_4 | spl3_49)),
% 0.22/0.42    inference(subsumption_resolution,[],[f294,f37])).
% 0.22/0.42  fof(f37,plain,(
% 0.22/0.42    v1_relat_1(sK2) | ~spl3_3),
% 0.22/0.42    inference(avatar_component_clause,[],[f35])).
% 0.22/0.42  fof(f35,plain,(
% 0.22/0.42    spl3_3 <=> v1_relat_1(sK2)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.42  fof(f294,plain,(
% 0.22/0.42    ~v1_relat_1(sK2) | (~spl3_4 | spl3_49)),
% 0.22/0.42    inference(resolution,[],[f280,f41])).
% 0.22/0.42  fof(f41,plain,(
% 0.22/0.42    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) ) | ~spl3_4),
% 0.22/0.42    inference(avatar_component_clause,[],[f40])).
% 0.22/0.42  fof(f40,plain,(
% 0.22/0.42    spl3_4 <=> ! [X1,X0] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.42  fof(f280,plain,(
% 0.22/0.42    ~v1_relat_1(k8_relat_1(sK0,sK2)) | spl3_49),
% 0.22/0.42    inference(avatar_component_clause,[],[f278])).
% 0.22/0.42  fof(f278,plain,(
% 0.22/0.42    spl3_49 <=> v1_relat_1(k8_relat_1(sK0,sK2))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).
% 0.22/0.42  fof(f281,plain,(
% 0.22/0.42    ~spl3_49 | spl3_1 | ~spl3_6 | ~spl3_48),
% 0.22/0.42    inference(avatar_split_clause,[],[f276,f268,f48,f25,f278])).
% 0.22/0.42  fof(f25,plain,(
% 0.22/0.42    spl3_1 <=> k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.42  fof(f48,plain,(
% 0.22/0.42    spl3_6 <=> ! [X1,X0] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.42  fof(f268,plain,(
% 0.22/0.42    spl3_48 <=> r1_tarski(k2_relat_1(k8_relat_1(sK0,sK2)),sK1)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).
% 0.22/0.42  fof(f276,plain,(
% 0.22/0.42    ~v1_relat_1(k8_relat_1(sK0,sK2)) | (spl3_1 | ~spl3_6 | ~spl3_48)),
% 0.22/0.42    inference(subsumption_resolution,[],[f272,f27])).
% 0.22/0.42  fof(f27,plain,(
% 0.22/0.42    k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2)) | spl3_1),
% 0.22/0.42    inference(avatar_component_clause,[],[f25])).
% 0.22/0.42  fof(f272,plain,(
% 0.22/0.42    k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2)) | ~v1_relat_1(k8_relat_1(sK0,sK2)) | (~spl3_6 | ~spl3_48)),
% 0.22/0.42    inference(resolution,[],[f270,f49])).
% 0.22/0.42  fof(f49,plain,(
% 0.22/0.42    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | k8_relat_1(X0,X1) = X1 | ~v1_relat_1(X1)) ) | ~spl3_6),
% 0.22/0.42    inference(avatar_component_clause,[],[f48])).
% 0.22/0.42  fof(f270,plain,(
% 0.22/0.42    r1_tarski(k2_relat_1(k8_relat_1(sK0,sK2)),sK1) | ~spl3_48),
% 0.22/0.42    inference(avatar_component_clause,[],[f268])).
% 0.22/0.42  fof(f271,plain,(
% 0.22/0.42    spl3_48 | ~spl3_15 | ~spl3_39),
% 0.22/0.42    inference(avatar_split_clause,[],[f250,f227,f94,f268])).
% 0.22/0.43  fof(f94,plain,(
% 0.22/0.43    spl3_15 <=> ! [X0] : k8_relat_1(X0,sK2) = k8_relat_1(X0,k8_relat_1(X0,sK2))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.22/0.43  fof(f227,plain,(
% 0.22/0.43    spl3_39 <=> ! [X0] : r1_tarski(k2_relat_1(k8_relat_1(sK0,k8_relat_1(X0,sK2))),sK1)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 0.22/0.43  fof(f250,plain,(
% 0.22/0.43    r1_tarski(k2_relat_1(k8_relat_1(sK0,sK2)),sK1) | (~spl3_15 | ~spl3_39)),
% 0.22/0.43    inference(superposition,[],[f228,f95])).
% 0.22/0.43  fof(f95,plain,(
% 0.22/0.43    ( ! [X0] : (k8_relat_1(X0,sK2) = k8_relat_1(X0,k8_relat_1(X0,sK2))) ) | ~spl3_15),
% 0.22/0.43    inference(avatar_component_clause,[],[f94])).
% 0.22/0.43  fof(f228,plain,(
% 0.22/0.43    ( ! [X0] : (r1_tarski(k2_relat_1(k8_relat_1(sK0,k8_relat_1(X0,sK2))),sK1)) ) | ~spl3_39),
% 0.22/0.43    inference(avatar_component_clause,[],[f227])).
% 0.22/0.43  fof(f229,plain,(
% 0.22/0.43    spl3_39 | ~spl3_2 | ~spl3_36),
% 0.22/0.43    inference(avatar_split_clause,[],[f221,f210,f30,f227])).
% 0.22/0.43  fof(f30,plain,(
% 0.22/0.43    spl3_2 <=> r1_tarski(sK0,sK1)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.43  fof(f210,plain,(
% 0.22/0.43    spl3_36 <=> ! [X1,X0,X2] : (~r1_tarski(X0,X1) | r1_tarski(k2_relat_1(k8_relat_1(X0,k8_relat_1(X2,sK2))),X1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.22/0.43  fof(f221,plain,(
% 0.22/0.43    ( ! [X0] : (r1_tarski(k2_relat_1(k8_relat_1(sK0,k8_relat_1(X0,sK2))),sK1)) ) | (~spl3_2 | ~spl3_36)),
% 0.22/0.43    inference(resolution,[],[f211,f32])).
% 0.22/0.43  fof(f32,plain,(
% 0.22/0.43    r1_tarski(sK0,sK1) | ~spl3_2),
% 0.22/0.43    inference(avatar_component_clause,[],[f30])).
% 0.22/0.43  fof(f211,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k2_relat_1(k8_relat_1(X0,k8_relat_1(X2,sK2))),X1)) ) | ~spl3_36),
% 0.22/0.43    inference(avatar_component_clause,[],[f210])).
% 0.22/0.43  fof(f212,plain,(
% 0.22/0.43    spl3_36 | ~spl3_3 | ~spl3_12),
% 0.22/0.43    inference(avatar_split_clause,[],[f206,f78,f35,f210])).
% 0.22/0.43  fof(f78,plain,(
% 0.22/0.43    spl3_12 <=> ! [X3,X5,X2,X4] : (r1_tarski(k2_relat_1(k8_relat_1(X2,k8_relat_1(X3,X4))),X5) | ~r1_tarski(X2,X5) | ~v1_relat_1(X4))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.43  fof(f206,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k2_relat_1(k8_relat_1(X0,k8_relat_1(X2,sK2))),X1)) ) | (~spl3_3 | ~spl3_12)),
% 0.22/0.43    inference(resolution,[],[f79,f37])).
% 0.22/0.43  fof(f79,plain,(
% 0.22/0.43    ( ! [X4,X2,X5,X3] : (~v1_relat_1(X4) | ~r1_tarski(X2,X5) | r1_tarski(k2_relat_1(k8_relat_1(X2,k8_relat_1(X3,X4))),X5)) ) | ~spl3_12),
% 0.22/0.43    inference(avatar_component_clause,[],[f78])).
% 0.22/0.43  fof(f96,plain,(
% 0.22/0.43    spl3_15 | ~spl3_3 | ~spl3_10),
% 0.22/0.43    inference(avatar_split_clause,[],[f91,f68,f35,f94])).
% 0.22/0.43  fof(f68,plain,(
% 0.22/0.43    spl3_10 <=> ! [X1,X0] : (k8_relat_1(X0,X1) = k8_relat_1(X0,k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.43  fof(f91,plain,(
% 0.22/0.43    ( ! [X0] : (k8_relat_1(X0,sK2) = k8_relat_1(X0,k8_relat_1(X0,sK2))) ) | (~spl3_3 | ~spl3_10)),
% 0.22/0.43    inference(resolution,[],[f69,f37])).
% 0.22/0.43  fof(f69,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k8_relat_1(X0,k8_relat_1(X0,X1))) ) | ~spl3_10),
% 0.22/0.43    inference(avatar_component_clause,[],[f68])).
% 0.22/0.43  fof(f80,plain,(
% 0.22/0.43    spl3_12 | ~spl3_4 | ~spl3_9),
% 0.22/0.43    inference(avatar_split_clause,[],[f72,f62,f40,f78])).
% 0.22/0.43  fof(f62,plain,(
% 0.22/0.43    spl3_9 <=> ! [X1,X3,X2] : (~r1_tarski(X1,X2) | r1_tarski(k2_relat_1(k8_relat_1(X1,X3)),X2) | ~v1_relat_1(X3))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.43  fof(f72,plain,(
% 0.22/0.43    ( ! [X4,X2,X5,X3] : (r1_tarski(k2_relat_1(k8_relat_1(X2,k8_relat_1(X3,X4))),X5) | ~r1_tarski(X2,X5) | ~v1_relat_1(X4)) ) | (~spl3_4 | ~spl3_9)),
% 0.22/0.43    inference(resolution,[],[f63,f41])).
% 0.22/0.43  fof(f63,plain,(
% 0.22/0.43    ( ! [X2,X3,X1] : (~v1_relat_1(X3) | r1_tarski(k2_relat_1(k8_relat_1(X1,X3)),X2) | ~r1_tarski(X1,X2)) ) | ~spl3_9),
% 0.22/0.43    inference(avatar_component_clause,[],[f62])).
% 0.22/0.43  fof(f70,plain,(
% 0.22/0.43    spl3_10 | ~spl3_4 | ~spl3_5 | ~spl3_6),
% 0.22/0.43    inference(avatar_split_clause,[],[f66,f48,f44,f40,f68])).
% 0.22/0.43  fof(f44,plain,(
% 0.22/0.43    spl3_5 <=> ! [X1,X0] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.43  fof(f66,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k8_relat_1(X0,k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) ) | (~spl3_4 | ~spl3_5 | ~spl3_6)),
% 0.22/0.43    inference(subsumption_resolution,[],[f65,f41])).
% 0.22/0.43  fof(f65,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k8_relat_1(X0,k8_relat_1(X0,X1)) | ~v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) ) | (~spl3_5 | ~spl3_6)),
% 0.22/0.43    inference(resolution,[],[f49,f45])).
% 0.22/0.43  fof(f45,plain,(
% 0.22/0.43    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1)) ) | ~spl3_5),
% 0.22/0.43    inference(avatar_component_clause,[],[f44])).
% 0.22/0.43  fof(f64,plain,(
% 0.22/0.43    spl3_9 | ~spl3_5 | ~spl3_7),
% 0.22/0.43    inference(avatar_split_clause,[],[f56,f52,f44,f62])).
% 0.22/0.43  fof(f52,plain,(
% 0.22/0.43    spl3_7 <=> ! [X1,X0,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.43  fof(f56,plain,(
% 0.22/0.43    ( ! [X2,X3,X1] : (~r1_tarski(X1,X2) | r1_tarski(k2_relat_1(k8_relat_1(X1,X3)),X2) | ~v1_relat_1(X3)) ) | (~spl3_5 | ~spl3_7)),
% 0.22/0.43    inference(resolution,[],[f53,f45])).
% 0.22/0.43  fof(f53,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) ) | ~spl3_7),
% 0.22/0.43    inference(avatar_component_clause,[],[f52])).
% 0.22/0.43  fof(f54,plain,(
% 0.22/0.43    spl3_7),
% 0.22/0.43    inference(avatar_split_clause,[],[f23,f52])).
% 0.22/0.43  fof(f23,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f14])).
% 0.22/0.43  fof(f14,plain,(
% 0.22/0.43    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.43    inference(flattening,[],[f13])).
% 0.22/0.43  fof(f13,plain,(
% 0.22/0.43    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.43    inference(ennf_transformation,[],[f1])).
% 0.22/0.43  fof(f1,axiom,(
% 0.22/0.43    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.22/0.43  fof(f50,plain,(
% 0.22/0.43    spl3_6),
% 0.22/0.43    inference(avatar_split_clause,[],[f22,f48])).
% 0.22/0.43  fof(f22,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f12])).
% 0.22/0.43  fof(f12,plain,(
% 0.22/0.43    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.43    inference(flattening,[],[f11])).
% 0.22/0.43  fof(f11,plain,(
% 0.22/0.43    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.43    inference(ennf_transformation,[],[f4])).
% 0.22/0.43  fof(f4,axiom,(
% 0.22/0.43    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).
% 0.22/0.43  fof(f46,plain,(
% 0.22/0.43    spl3_5),
% 0.22/0.43    inference(avatar_split_clause,[],[f21,f44])).
% 0.22/0.43  fof(f21,plain,(
% 0.22/0.43    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f10])).
% 0.22/0.43  fof(f10,plain,(
% 0.22/0.43    ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1))),
% 0.22/0.43    inference(ennf_transformation,[],[f3])).
% 0.22/0.43  fof(f3,axiom,(
% 0.22/0.43    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_relat_1)).
% 0.22/0.43  fof(f42,plain,(
% 0.22/0.43    spl3_4),
% 0.22/0.43    inference(avatar_split_clause,[],[f20,f40])).
% 0.22/0.43  fof(f20,plain,(
% 0.22/0.43    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f9])).
% 0.22/0.43  fof(f9,plain,(
% 0.22/0.43    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 0.22/0.43    inference(ennf_transformation,[],[f2])).
% 0.22/0.43  fof(f2,axiom,(
% 0.22/0.43    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).
% 0.22/0.43  fof(f38,plain,(
% 0.22/0.43    spl3_3),
% 0.22/0.43    inference(avatar_split_clause,[],[f17,f35])).
% 0.22/0.43  fof(f17,plain,(
% 0.22/0.43    v1_relat_1(sK2)),
% 0.22/0.43    inference(cnf_transformation,[],[f16])).
% 0.22/0.43  fof(f16,plain,(
% 0.22/0.43    k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2)) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f15])).
% 0.22/0.43  fof(f15,plain,(
% 0.22/0.43    ? [X0,X1,X2] : (k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2)) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2)) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f8,plain,(
% 0.22/0.43    ? [X0,X1,X2] : (k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2)) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 0.22/0.43    inference(flattening,[],[f7])).
% 0.22/0.43  fof(f7,plain,(
% 0.22/0.43    ? [X0,X1,X2] : ((k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2)) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 0.22/0.43    inference(ennf_transformation,[],[f6])).
% 0.22/0.43  fof(f6,negated_conjecture,(
% 0.22/0.43    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))))),
% 0.22/0.43    inference(negated_conjecture,[],[f5])).
% 0.22/0.43  fof(f5,conjecture,(
% 0.22/0.43    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_relat_1)).
% 0.22/0.43  fof(f33,plain,(
% 0.22/0.43    spl3_2),
% 0.22/0.43    inference(avatar_split_clause,[],[f18,f30])).
% 0.22/0.43  fof(f18,plain,(
% 0.22/0.43    r1_tarski(sK0,sK1)),
% 0.22/0.43    inference(cnf_transformation,[],[f16])).
% 0.22/0.43  fof(f28,plain,(
% 0.22/0.43    ~spl3_1),
% 0.22/0.43    inference(avatar_split_clause,[],[f19,f25])).
% 0.22/0.43  fof(f19,plain,(
% 0.22/0.43    k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2))),
% 0.22/0.43    inference(cnf_transformation,[],[f16])).
% 0.22/0.43  % SZS output end Proof for theBenchmark
% 0.22/0.43  % (29672)------------------------------
% 0.22/0.43  % (29672)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (29672)Termination reason: Refutation
% 0.22/0.43  
% 0.22/0.43  % (29672)Memory used [KB]: 10746
% 0.22/0.43  % (29672)Time elapsed: 0.011 s
% 0.22/0.43  % (29672)------------------------------
% 0.22/0.43  % (29672)------------------------------
% 0.22/0.43  % (29666)Success in time 0.069 s
%------------------------------------------------------------------------------
