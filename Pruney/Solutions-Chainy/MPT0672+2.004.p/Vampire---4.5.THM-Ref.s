%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:24 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 150 expanded)
%              Number of leaves         :   23 (  66 expanded)
%              Depth                    :    8
%              Number of atoms          :  265 ( 457 expanded)
%              Number of equality atoms :   46 (  92 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (5037)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
fof(f480,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f42,f47,f51,f55,f59,f63,f67,f73,f82,f94,f110,f135,f138,f154,f427,f475])).

fof(f475,plain,
    ( spl3_2
    | ~ spl3_4
    | ~ spl3_67 ),
    inference(avatar_contradiction_clause,[],[f474])).

fof(f474,plain,
    ( $false
    | spl3_2
    | ~ spl3_4
    | ~ spl3_67 ),
    inference(subsumption_resolution,[],[f468,f36])).

fof(f36,plain,
    ( k8_relat_1(sK0,k8_relat_1(sK1,sK2)) != k8_relat_1(sK0,sK2)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl3_2
  <=> k8_relat_1(sK0,k8_relat_1(sK1,sK2)) = k8_relat_1(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f468,plain,
    ( k8_relat_1(sK0,k8_relat_1(sK1,sK2)) = k8_relat_1(sK0,sK2)
    | ~ spl3_4
    | ~ spl3_67 ),
    inference(resolution,[],[f426,f46])).

fof(f46,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl3_4
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f426,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k8_relat_1(sK0,X0) = k8_relat_1(sK0,k8_relat_1(sK1,X0)) )
    | ~ spl3_67 ),
    inference(avatar_component_clause,[],[f425])).

fof(f425,plain,
    ( spl3_67
  <=> ! [X0] :
        ( k8_relat_1(sK0,X0) = k8_relat_1(sK0,k8_relat_1(sK1,X0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_67])])).

fof(f427,plain,
    ( spl3_67
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f413,f61,f39,f425])).

fof(f39,plain,
    ( spl3_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f61,plain,
    ( spl3_8
  <=> ! [X1,X0,X2] :
        ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2)
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f413,plain,
    ( ! [X0] :
        ( k8_relat_1(sK0,X0) = k8_relat_1(sK0,k8_relat_1(sK1,X0))
        | ~ v1_relat_1(X0) )
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(resolution,[],[f62,f41])).

fof(f41,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f39])).

fof(f62,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2)
        | ~ v1_relat_1(X2) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f61])).

fof(f154,plain,
    ( spl3_1
    | ~ spl3_7
    | ~ spl3_21
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f153,f132,f128,f57,f30])).

fof(f30,plain,
    ( spl3_1
  <=> k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f57,plain,
    ( spl3_7
  <=> ! [X1,X0] :
        ( k8_relat_1(X0,X1) = X1
        | ~ r1_tarski(k2_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f128,plain,
    ( spl3_21
  <=> v1_relat_1(k8_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f132,plain,
    ( spl3_22
  <=> r1_tarski(k2_relat_1(k8_relat_1(sK0,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f153,plain,
    ( k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2))
    | ~ spl3_7
    | ~ spl3_21
    | ~ spl3_22 ),
    inference(subsumption_resolution,[],[f144,f129])).

fof(f129,plain,
    ( v1_relat_1(k8_relat_1(sK0,sK2))
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f128])).

fof(f144,plain,
    ( k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2))
    | ~ v1_relat_1(k8_relat_1(sK0,sK2))
    | ~ spl3_7
    | ~ spl3_22 ),
    inference(resolution,[],[f134,f58])).

fof(f58,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(X1),X0)
        | k8_relat_1(X0,X1) = X1
        | ~ v1_relat_1(X1) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f57])).

fof(f134,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(sK0,sK2)),sK1)
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f132])).

fof(f138,plain,
    ( ~ spl3_4
    | ~ spl3_5
    | spl3_21 ),
    inference(avatar_contradiction_clause,[],[f137])).

fof(f137,plain,
    ( $false
    | ~ spl3_4
    | ~ spl3_5
    | spl3_21 ),
    inference(subsumption_resolution,[],[f136,f46])).

fof(f136,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl3_5
    | spl3_21 ),
    inference(resolution,[],[f130,f50])).

fof(f50,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k8_relat_1(X0,X1))
        | ~ v1_relat_1(X1) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl3_5
  <=> ! [X1,X0] :
        ( v1_relat_1(k8_relat_1(X0,X1))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f130,plain,
    ( ~ v1_relat_1(k8_relat_1(sK0,sK2))
    | spl3_21 ),
    inference(avatar_component_clause,[],[f128])).

fof(f135,plain,
    ( ~ spl3_21
    | spl3_22
    | ~ spl3_12
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f118,f108,f80,f132,f128])).

fof(f80,plain,
    ( spl3_12
  <=> ! [X0] :
        ( r1_tarski(k2_relat_1(k8_relat_1(sK0,X0)),sK1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f108,plain,
    ( spl3_17
  <=> ! [X0] : k8_relat_1(X0,sK2) = k8_relat_1(X0,k8_relat_1(X0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f118,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(sK0,sK2)),sK1)
    | ~ v1_relat_1(k8_relat_1(sK0,sK2))
    | ~ spl3_12
    | ~ spl3_17 ),
    inference(superposition,[],[f81,f109])).

fof(f109,plain,
    ( ! [X0] : k8_relat_1(X0,sK2) = k8_relat_1(X0,k8_relat_1(X0,sK2))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f108])).

fof(f81,plain,
    ( ! [X0] :
        ( r1_tarski(k2_relat_1(k8_relat_1(sK0,X0)),sK1)
        | ~ v1_relat_1(X0) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f80])).

fof(f110,plain,
    ( spl3_17
    | ~ spl3_4
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f105,f92,f44,f108])).

fof(f92,plain,
    ( spl3_14
  <=> ! [X1,X0] :
        ( k8_relat_1(X0,X1) = k8_relat_1(X0,k8_relat_1(X0,X1))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f105,plain,
    ( ! [X0] : k8_relat_1(X0,sK2) = k8_relat_1(X0,k8_relat_1(X0,sK2))
    | ~ spl3_4
    | ~ spl3_14 ),
    inference(resolution,[],[f93,f46])).

fof(f93,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k8_relat_1(X0,X1) = k8_relat_1(X0,k8_relat_1(X0,X1)) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f92])).

fof(f94,plain,
    ( spl3_14
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f90,f57,f53,f49,f92])).

fof(f53,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f90,plain,
    ( ! [X0,X1] :
        ( k8_relat_1(X0,X1) = k8_relat_1(X0,k8_relat_1(X0,X1))
        | ~ v1_relat_1(X1) )
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f88,f50])).

fof(f88,plain,
    ( ! [X0,X1] :
        ( k8_relat_1(X0,X1) = k8_relat_1(X0,k8_relat_1(X0,X1))
        | ~ v1_relat_1(k8_relat_1(X0,X1))
        | ~ v1_relat_1(X1) )
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(resolution,[],[f58,f54])).

fof(f54,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
        | ~ v1_relat_1(X1) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f53])).

fof(f82,plain,
    ( spl3_12
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f78,f71,f53,f80])).

fof(f71,plain,
    ( spl3_10
  <=> ! [X0] :
        ( r1_tarski(X0,sK1)
        | ~ r1_tarski(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f78,plain,
    ( ! [X0] :
        ( r1_tarski(k2_relat_1(k8_relat_1(sK0,X0)),sK1)
        | ~ v1_relat_1(X0) )
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(resolution,[],[f72,f54])).

fof(f72,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | r1_tarski(X0,sK1) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f71])).

fof(f73,plain,
    ( spl3_10
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f68,f65,f39,f71])).

fof(f65,plain,
    ( spl3_9
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,X2)
        | ~ r1_tarski(X1,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f68,plain,
    ( ! [X0] :
        ( r1_tarski(X0,sK1)
        | ~ r1_tarski(X0,sK0) )
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(resolution,[],[f66,f41])).

fof(f66,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X1,X2)
        | r1_tarski(X0,X2)
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f65])).

fof(f67,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f28,f65])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
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

fof(f63,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f27,f61])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_relat_1)).

fof(f59,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f26,f57])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
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

fof(f55,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f25,f53])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_relat_1)).

fof(f51,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f24,f49])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f47,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f21,f44])).

fof(f21,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ( k8_relat_1(sK0,k8_relat_1(sK1,sK2)) != k8_relat_1(sK0,sK2)
      | k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2)) )
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( ( k8_relat_1(X0,k8_relat_1(X1,X2)) != k8_relat_1(X0,X2)
          | k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2)) )
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( ( k8_relat_1(sK0,k8_relat_1(sK1,sK2)) != k8_relat_1(sK0,sK2)
        | k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2)) )
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relat_1(X0,k8_relat_1(X1,X2)) != k8_relat_1(X0,X2)
        | k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2)) )
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relat_1(X0,k8_relat_1(X1,X2)) != k8_relat_1(X0,X2)
        | k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2)) )
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2)
            & k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r1_tarski(X0,X1)
         => ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2)
            & k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r1_tarski(X0,X1)
       => ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2)
          & k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_funct_1)).

fof(f42,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f22,f39])).

fof(f22,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f37,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f23,f34,f30])).

fof(f23,plain,
    ( k8_relat_1(sK0,k8_relat_1(sK1,sK2)) != k8_relat_1(sK0,sK2)
    | k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:04:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.42  % (5043)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.20/0.42  % (5042)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.20/0.43  % (5039)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.20/0.43  % (5043)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.20/0.43  % (5037)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.20/0.43  fof(f480,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(avatar_sat_refutation,[],[f37,f42,f47,f51,f55,f59,f63,f67,f73,f82,f94,f110,f135,f138,f154,f427,f475])).
% 0.20/0.43  fof(f475,plain,(
% 0.20/0.43    spl3_2 | ~spl3_4 | ~spl3_67),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f474])).
% 0.20/0.43  fof(f474,plain,(
% 0.20/0.43    $false | (spl3_2 | ~spl3_4 | ~spl3_67)),
% 0.20/0.43    inference(subsumption_resolution,[],[f468,f36])).
% 0.20/0.43  fof(f36,plain,(
% 0.20/0.43    k8_relat_1(sK0,k8_relat_1(sK1,sK2)) != k8_relat_1(sK0,sK2) | spl3_2),
% 0.20/0.43    inference(avatar_component_clause,[],[f34])).
% 0.20/0.43  fof(f34,plain,(
% 0.20/0.43    spl3_2 <=> k8_relat_1(sK0,k8_relat_1(sK1,sK2)) = k8_relat_1(sK0,sK2)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.43  fof(f468,plain,(
% 0.20/0.43    k8_relat_1(sK0,k8_relat_1(sK1,sK2)) = k8_relat_1(sK0,sK2) | (~spl3_4 | ~spl3_67)),
% 0.20/0.43    inference(resolution,[],[f426,f46])).
% 0.20/0.43  fof(f46,plain,(
% 0.20/0.43    v1_relat_1(sK2) | ~spl3_4),
% 0.20/0.43    inference(avatar_component_clause,[],[f44])).
% 0.20/0.43  fof(f44,plain,(
% 0.20/0.43    spl3_4 <=> v1_relat_1(sK2)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.43  fof(f426,plain,(
% 0.20/0.43    ( ! [X0] : (~v1_relat_1(X0) | k8_relat_1(sK0,X0) = k8_relat_1(sK0,k8_relat_1(sK1,X0))) ) | ~spl3_67),
% 0.20/0.43    inference(avatar_component_clause,[],[f425])).
% 0.20/0.43  fof(f425,plain,(
% 0.20/0.43    spl3_67 <=> ! [X0] : (k8_relat_1(sK0,X0) = k8_relat_1(sK0,k8_relat_1(sK1,X0)) | ~v1_relat_1(X0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_67])])).
% 0.20/0.43  fof(f427,plain,(
% 0.20/0.43    spl3_67 | ~spl3_3 | ~spl3_8),
% 0.20/0.43    inference(avatar_split_clause,[],[f413,f61,f39,f425])).
% 0.20/0.43  fof(f39,plain,(
% 0.20/0.43    spl3_3 <=> r1_tarski(sK0,sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.43  fof(f61,plain,(
% 0.20/0.43    spl3_8 <=> ! [X1,X0,X2] : (k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.43  fof(f413,plain,(
% 0.20/0.43    ( ! [X0] : (k8_relat_1(sK0,X0) = k8_relat_1(sK0,k8_relat_1(sK1,X0)) | ~v1_relat_1(X0)) ) | (~spl3_3 | ~spl3_8)),
% 0.20/0.43    inference(resolution,[],[f62,f41])).
% 0.20/0.43  fof(f41,plain,(
% 0.20/0.43    r1_tarski(sK0,sK1) | ~spl3_3),
% 0.20/0.43    inference(avatar_component_clause,[],[f39])).
% 0.20/0.43  fof(f62,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2) | ~v1_relat_1(X2)) ) | ~spl3_8),
% 0.20/0.43    inference(avatar_component_clause,[],[f61])).
% 0.20/0.43  fof(f154,plain,(
% 0.20/0.43    spl3_1 | ~spl3_7 | ~spl3_21 | ~spl3_22),
% 0.20/0.43    inference(avatar_split_clause,[],[f153,f132,f128,f57,f30])).
% 0.20/0.43  fof(f30,plain,(
% 0.20/0.43    spl3_1 <=> k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.43  fof(f57,plain,(
% 0.20/0.43    spl3_7 <=> ! [X1,X0] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.43  fof(f128,plain,(
% 0.20/0.43    spl3_21 <=> v1_relat_1(k8_relat_1(sK0,sK2))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.20/0.43  fof(f132,plain,(
% 0.20/0.43    spl3_22 <=> r1_tarski(k2_relat_1(k8_relat_1(sK0,sK2)),sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.20/0.43  fof(f153,plain,(
% 0.20/0.43    k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2)) | (~spl3_7 | ~spl3_21 | ~spl3_22)),
% 0.20/0.43    inference(subsumption_resolution,[],[f144,f129])).
% 0.20/0.43  fof(f129,plain,(
% 0.20/0.43    v1_relat_1(k8_relat_1(sK0,sK2)) | ~spl3_21),
% 0.20/0.43    inference(avatar_component_clause,[],[f128])).
% 0.20/0.43  fof(f144,plain,(
% 0.20/0.43    k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2)) | ~v1_relat_1(k8_relat_1(sK0,sK2)) | (~spl3_7 | ~spl3_22)),
% 0.20/0.43    inference(resolution,[],[f134,f58])).
% 0.20/0.43  fof(f58,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | k8_relat_1(X0,X1) = X1 | ~v1_relat_1(X1)) ) | ~spl3_7),
% 0.20/0.43    inference(avatar_component_clause,[],[f57])).
% 0.20/0.43  fof(f134,plain,(
% 0.20/0.43    r1_tarski(k2_relat_1(k8_relat_1(sK0,sK2)),sK1) | ~spl3_22),
% 0.20/0.43    inference(avatar_component_clause,[],[f132])).
% 0.20/0.43  fof(f138,plain,(
% 0.20/0.43    ~spl3_4 | ~spl3_5 | spl3_21),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f137])).
% 0.20/0.43  fof(f137,plain,(
% 0.20/0.43    $false | (~spl3_4 | ~spl3_5 | spl3_21)),
% 0.20/0.43    inference(subsumption_resolution,[],[f136,f46])).
% 0.20/0.43  fof(f136,plain,(
% 0.20/0.43    ~v1_relat_1(sK2) | (~spl3_5 | spl3_21)),
% 0.20/0.43    inference(resolution,[],[f130,f50])).
% 0.20/0.43  fof(f50,plain,(
% 0.20/0.43    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) ) | ~spl3_5),
% 0.20/0.43    inference(avatar_component_clause,[],[f49])).
% 0.20/0.43  fof(f49,plain,(
% 0.20/0.43    spl3_5 <=> ! [X1,X0] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.43  fof(f130,plain,(
% 0.20/0.43    ~v1_relat_1(k8_relat_1(sK0,sK2)) | spl3_21),
% 0.20/0.43    inference(avatar_component_clause,[],[f128])).
% 0.20/0.43  fof(f135,plain,(
% 0.20/0.43    ~spl3_21 | spl3_22 | ~spl3_12 | ~spl3_17),
% 0.20/0.43    inference(avatar_split_clause,[],[f118,f108,f80,f132,f128])).
% 0.20/0.43  fof(f80,plain,(
% 0.20/0.43    spl3_12 <=> ! [X0] : (r1_tarski(k2_relat_1(k8_relat_1(sK0,X0)),sK1) | ~v1_relat_1(X0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.43  fof(f108,plain,(
% 0.20/0.43    spl3_17 <=> ! [X0] : k8_relat_1(X0,sK2) = k8_relat_1(X0,k8_relat_1(X0,sK2))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.20/0.43  fof(f118,plain,(
% 0.20/0.43    r1_tarski(k2_relat_1(k8_relat_1(sK0,sK2)),sK1) | ~v1_relat_1(k8_relat_1(sK0,sK2)) | (~spl3_12 | ~spl3_17)),
% 0.20/0.43    inference(superposition,[],[f81,f109])).
% 0.20/0.43  fof(f109,plain,(
% 0.20/0.43    ( ! [X0] : (k8_relat_1(X0,sK2) = k8_relat_1(X0,k8_relat_1(X0,sK2))) ) | ~spl3_17),
% 0.20/0.43    inference(avatar_component_clause,[],[f108])).
% 0.20/0.43  fof(f81,plain,(
% 0.20/0.43    ( ! [X0] : (r1_tarski(k2_relat_1(k8_relat_1(sK0,X0)),sK1) | ~v1_relat_1(X0)) ) | ~spl3_12),
% 0.20/0.43    inference(avatar_component_clause,[],[f80])).
% 0.20/0.43  fof(f110,plain,(
% 0.20/0.43    spl3_17 | ~spl3_4 | ~spl3_14),
% 0.20/0.43    inference(avatar_split_clause,[],[f105,f92,f44,f108])).
% 0.20/0.43  fof(f92,plain,(
% 0.20/0.43    spl3_14 <=> ! [X1,X0] : (k8_relat_1(X0,X1) = k8_relat_1(X0,k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.43  fof(f105,plain,(
% 0.20/0.43    ( ! [X0] : (k8_relat_1(X0,sK2) = k8_relat_1(X0,k8_relat_1(X0,sK2))) ) | (~spl3_4 | ~spl3_14)),
% 0.20/0.43    inference(resolution,[],[f93,f46])).
% 0.20/0.43  fof(f93,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k8_relat_1(X0,k8_relat_1(X0,X1))) ) | ~spl3_14),
% 0.20/0.43    inference(avatar_component_clause,[],[f92])).
% 0.20/0.43  fof(f94,plain,(
% 0.20/0.43    spl3_14 | ~spl3_5 | ~spl3_6 | ~spl3_7),
% 0.20/0.43    inference(avatar_split_clause,[],[f90,f57,f53,f49,f92])).
% 0.20/0.43  fof(f53,plain,(
% 0.20/0.43    spl3_6 <=> ! [X1,X0] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.43  fof(f90,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k8_relat_1(X0,k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) ) | (~spl3_5 | ~spl3_6 | ~spl3_7)),
% 0.20/0.43    inference(subsumption_resolution,[],[f88,f50])).
% 0.20/0.43  fof(f88,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k8_relat_1(X0,k8_relat_1(X0,X1)) | ~v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) ) | (~spl3_6 | ~spl3_7)),
% 0.20/0.43    inference(resolution,[],[f58,f54])).
% 0.20/0.43  fof(f54,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1)) ) | ~spl3_6),
% 0.20/0.43    inference(avatar_component_clause,[],[f53])).
% 0.20/0.43  fof(f82,plain,(
% 0.20/0.43    spl3_12 | ~spl3_6 | ~spl3_10),
% 0.20/0.43    inference(avatar_split_clause,[],[f78,f71,f53,f80])).
% 0.20/0.43  fof(f71,plain,(
% 0.20/0.43    spl3_10 <=> ! [X0] : (r1_tarski(X0,sK1) | ~r1_tarski(X0,sK0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.43  fof(f78,plain,(
% 0.20/0.43    ( ! [X0] : (r1_tarski(k2_relat_1(k8_relat_1(sK0,X0)),sK1) | ~v1_relat_1(X0)) ) | (~spl3_6 | ~spl3_10)),
% 0.20/0.43    inference(resolution,[],[f72,f54])).
% 0.20/0.43  fof(f72,plain,(
% 0.20/0.43    ( ! [X0] : (~r1_tarski(X0,sK0) | r1_tarski(X0,sK1)) ) | ~spl3_10),
% 0.20/0.43    inference(avatar_component_clause,[],[f71])).
% 0.20/0.43  fof(f73,plain,(
% 0.20/0.43    spl3_10 | ~spl3_3 | ~spl3_9),
% 0.20/0.43    inference(avatar_split_clause,[],[f68,f65,f39,f71])).
% 0.20/0.43  fof(f65,plain,(
% 0.20/0.43    spl3_9 <=> ! [X1,X0,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.43  fof(f68,plain,(
% 0.20/0.43    ( ! [X0] : (r1_tarski(X0,sK1) | ~r1_tarski(X0,sK0)) ) | (~spl3_3 | ~spl3_9)),
% 0.20/0.43    inference(resolution,[],[f66,f41])).
% 0.20/0.43  fof(f66,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) ) | ~spl3_9),
% 0.20/0.43    inference(avatar_component_clause,[],[f65])).
% 0.20/0.43  fof(f67,plain,(
% 0.20/0.43    spl3_9),
% 0.20/0.43    inference(avatar_split_clause,[],[f28,f65])).
% 0.20/0.43  fof(f28,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f18])).
% 0.20/0.43  fof(f18,plain,(
% 0.20/0.43    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.43    inference(flattening,[],[f17])).
% 0.20/0.43  fof(f17,plain,(
% 0.20/0.43    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.43    inference(ennf_transformation,[],[f1])).
% 0.20/0.43  fof(f1,axiom,(
% 0.20/0.43    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.20/0.43  fof(f63,plain,(
% 0.20/0.43    spl3_8),
% 0.20/0.43    inference(avatar_split_clause,[],[f27,f61])).
% 0.20/0.43  fof(f27,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f16])).
% 0.20/0.43  fof(f16,plain,(
% 0.20/0.43    ! [X0,X1,X2] : (k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.20/0.43    inference(flattening,[],[f15])).
% 0.20/0.43  fof(f15,plain,(
% 0.20/0.43    ! [X0,X1,X2] : ((k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.20/0.43    inference(ennf_transformation,[],[f5])).
% 0.20/0.43  fof(f5,axiom,(
% 0.20/0.43    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_relat_1)).
% 0.20/0.43  fof(f59,plain,(
% 0.20/0.43    spl3_7),
% 0.20/0.43    inference(avatar_split_clause,[],[f26,f57])).
% 0.20/0.43  fof(f26,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f14])).
% 0.20/0.43  fof(f14,plain,(
% 0.20/0.43    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.43    inference(flattening,[],[f13])).
% 0.20/0.43  fof(f13,plain,(
% 0.20/0.43    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f4])).
% 0.20/0.43  fof(f4,axiom,(
% 0.20/0.43    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).
% 0.20/0.43  fof(f55,plain,(
% 0.20/0.43    spl3_6),
% 0.20/0.43    inference(avatar_split_clause,[],[f25,f53])).
% 0.20/0.43  fof(f25,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f12])).
% 0.20/0.43  fof(f12,plain,(
% 0.20/0.43    ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f3])).
% 0.20/0.43  fof(f3,axiom,(
% 0.20/0.43    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_relat_1)).
% 0.20/0.43  fof(f51,plain,(
% 0.20/0.43    spl3_5),
% 0.20/0.43    inference(avatar_split_clause,[],[f24,f49])).
% 0.20/0.43  fof(f24,plain,(
% 0.20/0.43    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f11])).
% 0.20/0.43  fof(f11,plain,(
% 0.20/0.43    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f2])).
% 0.20/0.43  fof(f2,axiom,(
% 0.20/0.43    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).
% 0.20/0.43  fof(f47,plain,(
% 0.20/0.43    spl3_4),
% 0.20/0.43    inference(avatar_split_clause,[],[f21,f44])).
% 0.20/0.43  fof(f21,plain,(
% 0.20/0.43    v1_relat_1(sK2)),
% 0.20/0.43    inference(cnf_transformation,[],[f20])).
% 0.20/0.43  fof(f20,plain,(
% 0.20/0.43    (k8_relat_1(sK0,k8_relat_1(sK1,sK2)) != k8_relat_1(sK0,sK2) | k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2))) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f19])).
% 0.20/0.43  fof(f19,plain,(
% 0.20/0.43    ? [X0,X1,X2] : ((k8_relat_1(X0,k8_relat_1(X1,X2)) != k8_relat_1(X0,X2) | k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2))) & r1_tarski(X0,X1) & v1_relat_1(X2)) => ((k8_relat_1(sK0,k8_relat_1(sK1,sK2)) != k8_relat_1(sK0,sK2) | k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2))) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f10,plain,(
% 0.20/0.43    ? [X0,X1,X2] : ((k8_relat_1(X0,k8_relat_1(X1,X2)) != k8_relat_1(X0,X2) | k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2))) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 0.20/0.43    inference(flattening,[],[f9])).
% 0.20/0.43  fof(f9,plain,(
% 0.20/0.43    ? [X0,X1,X2] : (((k8_relat_1(X0,k8_relat_1(X1,X2)) != k8_relat_1(X0,X2) | k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2))) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 0.20/0.43    inference(ennf_transformation,[],[f8])).
% 0.20/0.43  fof(f8,plain,(
% 0.20/0.43    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => (k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2) & k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)))))),
% 0.20/0.43    inference(pure_predicate_removal,[],[f7])).
% 0.20/0.43  fof(f7,negated_conjecture,(
% 0.20/0.43    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r1_tarski(X0,X1) => (k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2) & k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)))))),
% 0.20/0.43    inference(negated_conjecture,[],[f6])).
% 0.20/0.43  fof(f6,conjecture,(
% 0.20/0.43    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r1_tarski(X0,X1) => (k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2) & k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)))))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_funct_1)).
% 0.20/0.43  fof(f42,plain,(
% 0.20/0.43    spl3_3),
% 0.20/0.43    inference(avatar_split_clause,[],[f22,f39])).
% 0.20/0.43  fof(f22,plain,(
% 0.20/0.43    r1_tarski(sK0,sK1)),
% 0.20/0.43    inference(cnf_transformation,[],[f20])).
% 0.20/0.43  fof(f37,plain,(
% 0.20/0.43    ~spl3_1 | ~spl3_2),
% 0.20/0.43    inference(avatar_split_clause,[],[f23,f34,f30])).
% 0.20/0.43  fof(f23,plain,(
% 0.20/0.43    k8_relat_1(sK0,k8_relat_1(sK1,sK2)) != k8_relat_1(sK0,sK2) | k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2))),
% 0.20/0.43    inference(cnf_transformation,[],[f20])).
% 0.20/0.43  % SZS output end Proof for theBenchmark
% 0.20/0.43  % (5043)------------------------------
% 0.20/0.43  % (5043)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (5043)Termination reason: Refutation
% 0.20/0.43  
% 0.20/0.43  % (5043)Memory used [KB]: 6396
% 0.20/0.43  % (5043)Time elapsed: 0.014 s
% 0.20/0.43  % (5043)------------------------------
% 0.20/0.43  % (5043)------------------------------
% 0.20/0.44  % (5032)Success in time 0.076 s
%------------------------------------------------------------------------------
