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
% DateTime   : Thu Dec  3 12:53:23 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   66 (  99 expanded)
%              Number of leaves         :   17 (  42 expanded)
%              Depth                    :    7
%              Number of atoms          :  197 ( 283 expanded)
%              Number of equality atoms :    8 (  15 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f138,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f33,f43,f51,f59,f63,f71,f75,f82,f97,f103,f137])).

fof(f137,plain,
    ( spl2_1
    | ~ spl2_3
    | ~ spl2_7
    | ~ spl2_15
    | ~ spl2_16 ),
    inference(avatar_contradiction_clause,[],[f136])).

fof(f136,plain,
    ( $false
    | spl2_1
    | ~ spl2_3
    | ~ spl2_7
    | ~ spl2_15
    | ~ spl2_16 ),
    inference(subsumption_resolution,[],[f135,f102])).

fof(f102,plain,
    ( ! [X1] : v1_relat_1(k8_relat_1(X1,sK1))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl2_16
  <=> ! [X1] : v1_relat_1(k8_relat_1(X1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f135,plain,
    ( ~ v1_relat_1(k8_relat_1(sK0,sK1))
    | spl2_1
    | ~ spl2_3
    | ~ spl2_7
    | ~ spl2_15 ),
    inference(subsumption_resolution,[],[f134,f42])).

fof(f42,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl2_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f134,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k8_relat_1(sK0,sK1))
    | spl2_1
    | ~ spl2_7
    | ~ spl2_15 ),
    inference(subsumption_resolution,[],[f133,f96])).

fof(f96,plain,
    ( ! [X0] : r1_tarski(k8_relat_1(X0,sK1),sK1)
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl2_15
  <=> ! [X0] : r1_tarski(k8_relat_1(X0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f133,plain,
    ( ~ r1_tarski(k8_relat_1(sK0,sK1),sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k8_relat_1(sK0,sK1))
    | spl2_1
    | ~ spl2_7 ),
    inference(resolution,[],[f58,f32])).

fof(f32,plain,
    ( ~ r1_tarski(k1_relat_1(k8_relat_1(sK0,sK1)),k1_relat_1(sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl2_1
  <=> r1_tarski(k1_relat_1(k8_relat_1(sK0,sK1)),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

% (18709)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
fof(f58,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl2_7
  <=> ! [X1,X0] :
        ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f103,plain,
    ( spl2_16
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_11
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f99,f80,f73,f49,f40,f101])).

fof(f49,plain,
    ( spl2_5
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f73,plain,
    ( spl2_11
  <=> ! [X1,X0] :
        ( v1_relat_1(k5_relat_1(X0,X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f80,plain,
    ( spl2_12
  <=> ! [X0] : k8_relat_1(X0,sK1) = k5_relat_1(sK1,k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f99,plain,
    ( ! [X1] : v1_relat_1(k8_relat_1(X1,sK1))
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_11
    | ~ spl2_12 ),
    inference(subsumption_resolution,[],[f98,f42])).

fof(f98,plain,
    ( ! [X1] :
        ( v1_relat_1(k8_relat_1(X1,sK1))
        | ~ v1_relat_1(sK1) )
    | ~ spl2_5
    | ~ spl2_11
    | ~ spl2_12 ),
    inference(subsumption_resolution,[],[f92,f50])).

fof(f50,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f49])).

fof(f92,plain,
    ( ! [X1] :
        ( v1_relat_1(k8_relat_1(X1,sK1))
        | ~ v1_relat_1(k6_relat_1(X1))
        | ~ v1_relat_1(sK1) )
    | ~ spl2_11
    | ~ spl2_12 ),
    inference(superposition,[],[f74,f81])).

fof(f81,plain,
    ( ! [X0] : k8_relat_1(X0,sK1) = k5_relat_1(sK1,k6_relat_1(X0))
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f80])).

fof(f74,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k5_relat_1(X0,X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f73])).

fof(f97,plain,
    ( spl2_15
    | ~ spl2_3
    | ~ spl2_10
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f93,f80,f69,f40,f95])).

fof(f69,plain,
    ( spl2_10
  <=> ! [X1,X0] :
        ( r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f93,plain,
    ( ! [X0] : r1_tarski(k8_relat_1(X0,sK1),sK1)
    | ~ spl2_3
    | ~ spl2_10
    | ~ spl2_12 ),
    inference(subsumption_resolution,[],[f91,f42])).

fof(f91,plain,
    ( ! [X0] :
        ( r1_tarski(k8_relat_1(X0,sK1),sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl2_10
    | ~ spl2_12 ),
    inference(superposition,[],[f70,f81])).

fof(f70,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)
        | ~ v1_relat_1(X1) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f69])).

fof(f82,plain,
    ( spl2_12
    | ~ spl2_3
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f76,f61,f40,f80])).

fof(f61,plain,
    ( spl2_8
  <=> ! [X1,X0] :
        ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f76,plain,
    ( ! [X0] : k8_relat_1(X0,sK1) = k5_relat_1(sK1,k6_relat_1(X0))
    | ~ spl2_3
    | ~ spl2_8 ),
    inference(resolution,[],[f62,f42])).

fof(f62,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f61])).

fof(f75,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f28,f73])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f71,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f26,f69])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).

fof(f63,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f25,f61])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(f59,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f23,f57])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(f51,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f21,f49])).

fof(f21,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f43,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f18,f40])).

fof(f18,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ~ r1_tarski(k1_relat_1(k8_relat_1(sK0,sK1)),k1_relat_1(sK1))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f16])).

fof(f16,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k1_relat_1(k8_relat_1(sK0,sK1)),k1_relat_1(sK1))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1)) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_funct_1)).

fof(f33,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f20,f30])).

fof(f20,plain,(
    ~ r1_tarski(k1_relat_1(k8_relat_1(sK0,sK1)),k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:19:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (18713)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.41  % (18713)Refutation found. Thanks to Tanya!
% 0.21/0.41  % SZS status Theorem for theBenchmark
% 0.21/0.41  % SZS output start Proof for theBenchmark
% 0.21/0.41  fof(f138,plain,(
% 0.21/0.41    $false),
% 0.21/0.41    inference(avatar_sat_refutation,[],[f33,f43,f51,f59,f63,f71,f75,f82,f97,f103,f137])).
% 0.21/0.41  fof(f137,plain,(
% 0.21/0.41    spl2_1 | ~spl2_3 | ~spl2_7 | ~spl2_15 | ~spl2_16),
% 0.21/0.41    inference(avatar_contradiction_clause,[],[f136])).
% 0.21/0.41  fof(f136,plain,(
% 0.21/0.41    $false | (spl2_1 | ~spl2_3 | ~spl2_7 | ~spl2_15 | ~spl2_16)),
% 0.21/0.41    inference(subsumption_resolution,[],[f135,f102])).
% 0.21/0.41  fof(f102,plain,(
% 0.21/0.41    ( ! [X1] : (v1_relat_1(k8_relat_1(X1,sK1))) ) | ~spl2_16),
% 0.21/0.41    inference(avatar_component_clause,[],[f101])).
% 0.21/0.41  fof(f101,plain,(
% 0.21/0.41    spl2_16 <=> ! [X1] : v1_relat_1(k8_relat_1(X1,sK1))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.21/0.41  fof(f135,plain,(
% 0.21/0.41    ~v1_relat_1(k8_relat_1(sK0,sK1)) | (spl2_1 | ~spl2_3 | ~spl2_7 | ~spl2_15)),
% 0.21/0.41    inference(subsumption_resolution,[],[f134,f42])).
% 0.21/0.41  fof(f42,plain,(
% 0.21/0.41    v1_relat_1(sK1) | ~spl2_3),
% 0.21/0.41    inference(avatar_component_clause,[],[f40])).
% 0.21/0.41  fof(f40,plain,(
% 0.21/0.41    spl2_3 <=> v1_relat_1(sK1)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.41  fof(f134,plain,(
% 0.21/0.41    ~v1_relat_1(sK1) | ~v1_relat_1(k8_relat_1(sK0,sK1)) | (spl2_1 | ~spl2_7 | ~spl2_15)),
% 0.21/0.41    inference(subsumption_resolution,[],[f133,f96])).
% 0.21/0.41  fof(f96,plain,(
% 0.21/0.41    ( ! [X0] : (r1_tarski(k8_relat_1(X0,sK1),sK1)) ) | ~spl2_15),
% 0.21/0.41    inference(avatar_component_clause,[],[f95])).
% 0.21/0.41  fof(f95,plain,(
% 0.21/0.41    spl2_15 <=> ! [X0] : r1_tarski(k8_relat_1(X0,sK1),sK1)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.21/0.41  fof(f133,plain,(
% 0.21/0.41    ~r1_tarski(k8_relat_1(sK0,sK1),sK1) | ~v1_relat_1(sK1) | ~v1_relat_1(k8_relat_1(sK0,sK1)) | (spl2_1 | ~spl2_7)),
% 0.21/0.41    inference(resolution,[],[f58,f32])).
% 0.21/0.41  fof(f32,plain,(
% 0.21/0.41    ~r1_tarski(k1_relat_1(k8_relat_1(sK0,sK1)),k1_relat_1(sK1)) | spl2_1),
% 0.21/0.41    inference(avatar_component_clause,[],[f30])).
% 0.21/0.41  fof(f30,plain,(
% 0.21/0.41    spl2_1 <=> r1_tarski(k1_relat_1(k8_relat_1(sK0,sK1)),k1_relat_1(sK1))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.41  % (18709)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.21/0.41  fof(f58,plain,(
% 0.21/0.41    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl2_7),
% 0.21/0.41    inference(avatar_component_clause,[],[f57])).
% 0.21/0.41  fof(f57,plain,(
% 0.21/0.41    spl2_7 <=> ! [X1,X0] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.41  fof(f103,plain,(
% 0.21/0.41    spl2_16 | ~spl2_3 | ~spl2_5 | ~spl2_11 | ~spl2_12),
% 0.21/0.41    inference(avatar_split_clause,[],[f99,f80,f73,f49,f40,f101])).
% 0.21/0.41  fof(f49,plain,(
% 0.21/0.41    spl2_5 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.41  fof(f73,plain,(
% 0.21/0.41    spl2_11 <=> ! [X1,X0] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.41  fof(f80,plain,(
% 0.21/0.41    spl2_12 <=> ! [X0] : k8_relat_1(X0,sK1) = k5_relat_1(sK1,k6_relat_1(X0))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.21/0.41  fof(f99,plain,(
% 0.21/0.41    ( ! [X1] : (v1_relat_1(k8_relat_1(X1,sK1))) ) | (~spl2_3 | ~spl2_5 | ~spl2_11 | ~spl2_12)),
% 0.21/0.41    inference(subsumption_resolution,[],[f98,f42])).
% 0.21/0.41  fof(f98,plain,(
% 0.21/0.41    ( ! [X1] : (v1_relat_1(k8_relat_1(X1,sK1)) | ~v1_relat_1(sK1)) ) | (~spl2_5 | ~spl2_11 | ~spl2_12)),
% 0.21/0.41    inference(subsumption_resolution,[],[f92,f50])).
% 0.21/0.41  fof(f50,plain,(
% 0.21/0.41    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl2_5),
% 0.21/0.41    inference(avatar_component_clause,[],[f49])).
% 0.21/0.41  fof(f92,plain,(
% 0.21/0.41    ( ! [X1] : (v1_relat_1(k8_relat_1(X1,sK1)) | ~v1_relat_1(k6_relat_1(X1)) | ~v1_relat_1(sK1)) ) | (~spl2_11 | ~spl2_12)),
% 0.21/0.41    inference(superposition,[],[f74,f81])).
% 0.21/0.41  fof(f81,plain,(
% 0.21/0.41    ( ! [X0] : (k8_relat_1(X0,sK1) = k5_relat_1(sK1,k6_relat_1(X0))) ) | ~spl2_12),
% 0.21/0.41    inference(avatar_component_clause,[],[f80])).
% 0.21/0.41  fof(f74,plain,(
% 0.21/0.41    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl2_11),
% 0.21/0.41    inference(avatar_component_clause,[],[f73])).
% 0.21/0.41  fof(f97,plain,(
% 0.21/0.41    spl2_15 | ~spl2_3 | ~spl2_10 | ~spl2_12),
% 0.21/0.41    inference(avatar_split_clause,[],[f93,f80,f69,f40,f95])).
% 0.21/0.41  fof(f69,plain,(
% 0.21/0.41    spl2_10 <=> ! [X1,X0] : (r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) | ~v1_relat_1(X1))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.41  fof(f93,plain,(
% 0.21/0.41    ( ! [X0] : (r1_tarski(k8_relat_1(X0,sK1),sK1)) ) | (~spl2_3 | ~spl2_10 | ~spl2_12)),
% 0.21/0.41    inference(subsumption_resolution,[],[f91,f42])).
% 0.21/0.41  fof(f91,plain,(
% 0.21/0.41    ( ! [X0] : (r1_tarski(k8_relat_1(X0,sK1),sK1) | ~v1_relat_1(sK1)) ) | (~spl2_10 | ~spl2_12)),
% 0.21/0.41    inference(superposition,[],[f70,f81])).
% 0.21/0.41  fof(f70,plain,(
% 0.21/0.41    ( ! [X0,X1] : (r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) | ~v1_relat_1(X1)) ) | ~spl2_10),
% 0.21/0.41    inference(avatar_component_clause,[],[f69])).
% 0.21/0.41  fof(f82,plain,(
% 0.21/0.41    spl2_12 | ~spl2_3 | ~spl2_8),
% 0.21/0.41    inference(avatar_split_clause,[],[f76,f61,f40,f80])).
% 0.21/0.41  fof(f61,plain,(
% 0.21/0.41    spl2_8 <=> ! [X1,X0] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.41  fof(f76,plain,(
% 0.21/0.41    ( ! [X0] : (k8_relat_1(X0,sK1) = k5_relat_1(sK1,k6_relat_1(X0))) ) | (~spl2_3 | ~spl2_8)),
% 0.21/0.41    inference(resolution,[],[f62,f42])).
% 0.21/0.41  fof(f62,plain,(
% 0.21/0.41    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) ) | ~spl2_8),
% 0.21/0.41    inference(avatar_component_clause,[],[f61])).
% 0.21/0.41  fof(f75,plain,(
% 0.21/0.41    spl2_11),
% 0.21/0.41    inference(avatar_split_clause,[],[f28,f73])).
% 0.21/0.41  fof(f28,plain,(
% 0.21/0.41    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f15])).
% 0.21/0.41  fof(f15,plain,(
% 0.21/0.41    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.21/0.41    inference(flattening,[],[f14])).
% 0.21/0.41  fof(f14,plain,(
% 0.21/0.41    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.21/0.41    inference(ennf_transformation,[],[f1])).
% 0.21/0.41  fof(f1,axiom,(
% 0.21/0.41    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.21/0.41  fof(f71,plain,(
% 0.21/0.41    spl2_10),
% 0.21/0.41    inference(avatar_split_clause,[],[f26,f69])).
% 0.21/0.41  fof(f26,plain,(
% 0.21/0.41    ( ! [X0,X1] : (r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) | ~v1_relat_1(X1)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f13])).
% 0.21/0.41  fof(f13,plain,(
% 0.21/0.41    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 0.21/0.41    inference(ennf_transformation,[],[f4])).
% 0.21/0.41  fof(f4,axiom,(
% 0.21/0.41    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).
% 0.21/0.41  fof(f63,plain,(
% 0.21/0.41    spl2_8),
% 0.21/0.41    inference(avatar_split_clause,[],[f25,f61])).
% 0.21/0.41  fof(f25,plain,(
% 0.21/0.41    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f12])).
% 0.21/0.41  fof(f12,plain,(
% 0.21/0.41    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.21/0.41    inference(ennf_transformation,[],[f2])).
% 0.21/0.41  fof(f2,axiom,(
% 0.21/0.41    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).
% 0.21/0.41  fof(f59,plain,(
% 0.21/0.41    spl2_7),
% 0.21/0.41    inference(avatar_split_clause,[],[f23,f57])).
% 0.21/0.41  fof(f23,plain,(
% 0.21/0.41    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f11])).
% 0.21/0.41  fof(f11,plain,(
% 0.21/0.41    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.41    inference(flattening,[],[f10])).
% 0.21/0.41  fof(f10,plain,(
% 0.21/0.41    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.41    inference(ennf_transformation,[],[f3])).
% 0.21/0.41  fof(f3,axiom,(
% 0.21/0.41    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).
% 0.21/0.41  fof(f51,plain,(
% 0.21/0.41    spl2_5),
% 0.21/0.41    inference(avatar_split_clause,[],[f21,f49])).
% 0.21/0.41  fof(f21,plain,(
% 0.21/0.41    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.41    inference(cnf_transformation,[],[f5])).
% 0.21/0.41  fof(f5,axiom,(
% 0.21/0.41    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.21/0.41  fof(f43,plain,(
% 0.21/0.41    spl2_3),
% 0.21/0.41    inference(avatar_split_clause,[],[f18,f40])).
% 0.21/0.41  fof(f18,plain,(
% 0.21/0.41    v1_relat_1(sK1)),
% 0.21/0.41    inference(cnf_transformation,[],[f17])).
% 0.21/0.41  fof(f17,plain,(
% 0.21/0.41    ~r1_tarski(k1_relat_1(k8_relat_1(sK0,sK1)),k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.21/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f16])).
% 0.21/0.41  fof(f16,plain,(
% 0.21/0.41    ? [X0,X1] : (~r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) => (~r1_tarski(k1_relat_1(k8_relat_1(sK0,sK1)),k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.21/0.41    introduced(choice_axiom,[])).
% 0.21/0.41  fof(f9,plain,(
% 0.21/0.41    ? [X0,X1] : (~r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.41    inference(flattening,[],[f8])).
% 0.21/0.41  fof(f8,plain,(
% 0.21/0.41    ? [X0,X1] : (~r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.21/0.41    inference(ennf_transformation,[],[f7])).
% 0.21/0.41  fof(f7,negated_conjecture,(
% 0.21/0.41    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1)))),
% 0.21/0.41    inference(negated_conjecture,[],[f6])).
% 0.21/0.41  fof(f6,conjecture,(
% 0.21/0.41    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1)))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_funct_1)).
% 0.21/0.41  fof(f33,plain,(
% 0.21/0.41    ~spl2_1),
% 0.21/0.41    inference(avatar_split_clause,[],[f20,f30])).
% 0.21/0.41  fof(f20,plain,(
% 0.21/0.41    ~r1_tarski(k1_relat_1(k8_relat_1(sK0,sK1)),k1_relat_1(sK1))),
% 0.21/0.41    inference(cnf_transformation,[],[f17])).
% 0.21/0.41  % SZS output end Proof for theBenchmark
% 0.21/0.41  % (18713)------------------------------
% 0.21/0.41  % (18713)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.41  % (18713)Termination reason: Refutation
% 0.21/0.41  
% 0.21/0.41  % (18713)Memory used [KB]: 10618
% 0.21/0.41  % (18713)Time elapsed: 0.006 s
% 0.21/0.41  % (18713)------------------------------
% 0.21/0.41  % (18713)------------------------------
% 0.21/0.42  % (18707)Success in time 0.063 s
%------------------------------------------------------------------------------
