%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:46 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 129 expanded)
%              Number of leaves         :   21 (  56 expanded)
%              Depth                    :    7
%              Number of atoms          :  265 ( 500 expanded)
%              Number of equality atoms :    8 (  12 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f118,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f52,f53,f54,f58,f62,f70,f78,f82,f88,f95,f102,f108,f113,f117])).

fof(f117,plain,
    ( ~ spl1_1
    | spl1_2
    | ~ spl1_15
    | ~ spl1_17 ),
    inference(avatar_contradiction_clause,[],[f116])).

fof(f116,plain,
    ( $false
    | ~ spl1_1
    | spl1_2
    | ~ spl1_15
    | ~ spl1_17 ),
    inference(subsumption_resolution,[],[f115,f38])).

fof(f38,plain,
    ( ~ v5_relat_1(sK0,k2_relat_1(sK0))
    | spl1_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl1_2
  <=> v5_relat_1(sK0,k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f115,plain,
    ( v5_relat_1(sK0,k2_relat_1(sK0))
    | ~ spl1_1
    | ~ spl1_15
    | ~ spl1_17 ),
    inference(subsumption_resolution,[],[f114,f33])).

fof(f33,plain,
    ( v1_relat_1(sK0)
    | ~ spl1_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl1_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f114,plain,
    ( ~ v1_relat_1(sK0)
    | v5_relat_1(sK0,k2_relat_1(sK0))
    | ~ spl1_15
    | ~ spl1_17 ),
    inference(resolution,[],[f112,f101])).

fof(f101,plain,
    ( r1_tarski(sK0,sK0)
    | ~ spl1_15 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl1_15
  <=> r1_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_15])])).

fof(f112,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK0,X0)
        | ~ v1_relat_1(X0)
        | v5_relat_1(sK0,k2_relat_1(X0)) )
    | ~ spl1_17 ),
    inference(avatar_component_clause,[],[f111])).

% (3444)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
fof(f111,plain,
    ( spl1_17
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ r1_tarski(sK0,X0)
        | v5_relat_1(sK0,k2_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_17])])).

fof(f113,plain,
    ( spl1_17
    | ~ spl1_1
    | ~ spl1_16 ),
    inference(avatar_split_clause,[],[f109,f106,f32,f111])).

fof(f106,plain,
    ( spl1_16
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0)
        | v5_relat_1(X0,k2_relat_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_16])])).

fof(f109,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ r1_tarski(sK0,X0)
        | v5_relat_1(sK0,k2_relat_1(X0)) )
    | ~ spl1_1
    | ~ spl1_16 ),
    inference(resolution,[],[f107,f33])).

fof(f107,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(X0,X1)
        | v5_relat_1(X0,k2_relat_1(X1)) )
    | ~ spl1_16 ),
    inference(avatar_component_clause,[],[f106])).

fof(f108,plain,
    ( spl1_16
    | ~ spl1_7
    | ~ spl1_12 ),
    inference(avatar_split_clause,[],[f104,f80,f60,f106])).

fof(f60,plain,
    ( spl1_7
  <=> ! [X1,X0] :
        ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f80,plain,
    ( spl1_12
  <=> ! [X1,X0] :
        ( v5_relat_1(X1,X0)
        | ~ r1_tarski(k2_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).

fof(f104,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0)
        | v5_relat_1(X0,k2_relat_1(X1)) )
    | ~ spl1_7
    | ~ spl1_12 ),
    inference(duplicate_literal_removal,[],[f103])).

fof(f103,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0)
        | v5_relat_1(X0,k2_relat_1(X1))
        | ~ v1_relat_1(X0) )
    | ~ spl1_7
    | ~ spl1_12 ),
    inference(resolution,[],[f61,f81])).

fof(f81,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(X1),X0)
        | v5_relat_1(X1,X0)
        | ~ v1_relat_1(X1) )
    | ~ spl1_12 ),
    inference(avatar_component_clause,[],[f80])).

% (3445)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
fof(f61,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f60])).

fof(f102,plain,
    ( spl1_15
    | ~ spl1_1
    | ~ spl1_11
    | ~ spl1_14 ),
    inference(avatar_split_clause,[],[f97,f92,f76,f32,f99])).

fof(f76,plain,
    ( spl1_11
  <=> ! [X1,X0] :
        ( r1_tarski(k8_relat_1(X0,X1),X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f92,plain,
    ( spl1_14
  <=> sK0 = k8_relat_1(k2_relat_1(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).

fof(f97,plain,
    ( r1_tarski(sK0,sK0)
    | ~ spl1_1
    | ~ spl1_11
    | ~ spl1_14 ),
    inference(subsumption_resolution,[],[f96,f33])).

fof(f96,plain,
    ( r1_tarski(sK0,sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_11
    | ~ spl1_14 ),
    inference(superposition,[],[f77,f94])).

fof(f94,plain,
    ( sK0 = k8_relat_1(k2_relat_1(sK0),sK0)
    | ~ spl1_14 ),
    inference(avatar_component_clause,[],[f92])).

fof(f77,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k8_relat_1(X0,X1),X1)
        | ~ v1_relat_1(X1) )
    | ~ spl1_11 ),
    inference(avatar_component_clause,[],[f76])).

fof(f95,plain,
    ( spl1_14
    | ~ spl1_1
    | ~ spl1_6 ),
    inference(avatar_split_clause,[],[f90,f56,f32,f92])).

fof(f56,plain,
    ( spl1_6
  <=> ! [X0] :
        ( k8_relat_1(k2_relat_1(X0),X0) = X0
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f90,plain,
    ( sK0 = k8_relat_1(k2_relat_1(sK0),sK0)
    | ~ spl1_1
    | ~ spl1_6 ),
    inference(resolution,[],[f57,f33])).

fof(f57,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k8_relat_1(k2_relat_1(X0),X0) = X0 )
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f56])).

fof(f88,plain,
    ( spl1_4
    | ~ spl1_5
    | ~ spl1_9 ),
    inference(avatar_split_clause,[],[f87,f68,f49,f44])).

fof(f44,plain,
    ( spl1_4
  <=> v5_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f49,plain,
    ( spl1_5
  <=> v3_ordinal1(k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f68,plain,
    ( spl1_9
  <=> ! [X0] :
        ( v5_ordinal1(X0)
        | ~ v3_ordinal1(k1_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f87,plain,
    ( v5_ordinal1(sK0)
    | ~ spl1_5
    | ~ spl1_9 ),
    inference(resolution,[],[f69,f51])).

fof(f51,plain,
    ( v3_ordinal1(k1_relat_1(sK0))
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f49])).

fof(f69,plain,
    ( ! [X0] :
        ( ~ v3_ordinal1(k1_relat_1(X0))
        | v5_ordinal1(X0) )
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f68])).

fof(f82,plain,(
    spl1_12 ),
    inference(avatar_split_clause,[],[f30,f80])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v5_relat_1(X1,X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f78,plain,(
    spl1_11 ),
    inference(avatar_split_clause,[],[f28,f76])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k8_relat_1(X0,X1),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).

fof(f70,plain,(
    spl1_9 ),
    inference(avatar_split_clause,[],[f27,f68])).

fof(f27,plain,(
    ! [X0] :
      ( v5_ordinal1(X0)
      | ~ v3_ordinal1(k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v5_ordinal1(X0)
        | ~ v3_ordinal1(k1_relat_1(X0)) )
      & ( v3_ordinal1(k1_relat_1(X0))
        | ~ v5_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v5_ordinal1(X0)
    <=> v3_ordinal1(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_ordinal1)).

fof(f62,plain,(
    spl1_7 ),
    inference(avatar_split_clause,[],[f25,f60])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f58,plain,(
    spl1_6 ),
    inference(avatar_split_clause,[],[f23,f56])).

fof(f23,plain,(
    ! [X0] :
      ( k8_relat_1(k2_relat_1(X0),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k8_relat_1(k2_relat_1(X0),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k8_relat_1(k2_relat_1(X0),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t126_relat_1)).

fof(f54,plain,(
    spl1_1 ),
    inference(avatar_split_clause,[],[f19,f32])).

fof(f19,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ( ~ v5_ordinal1(sK0)
      | ~ v1_funct_1(sK0)
      | ~ v5_relat_1(sK0,k2_relat_1(sK0))
      | ~ v1_relat_1(sK0) )
    & v3_ordinal1(k1_relat_1(sK0))
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f15])).

fof(f15,plain,
    ( ? [X0] :
        ( ( ~ v5_ordinal1(X0)
          | ~ v1_funct_1(X0)
          | ~ v5_relat_1(X0,k2_relat_1(X0))
          | ~ v1_relat_1(X0) )
        & v3_ordinal1(k1_relat_1(X0))
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( ~ v5_ordinal1(sK0)
        | ~ v1_funct_1(sK0)
        | ~ v5_relat_1(sK0,k2_relat_1(sK0))
        | ~ v1_relat_1(sK0) )
      & v3_ordinal1(k1_relat_1(sK0))
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ( ~ v5_ordinal1(X0)
        | ~ v1_funct_1(X0)
        | ~ v5_relat_1(X0,k2_relat_1(X0))
        | ~ v1_relat_1(X0) )
      & v3_ordinal1(k1_relat_1(X0))
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ( ~ v5_ordinal1(X0)
        | ~ v1_funct_1(X0)
        | ~ v5_relat_1(X0,k2_relat_1(X0))
        | ~ v1_relat_1(X0) )
      & v3_ordinal1(k1_relat_1(X0))
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v3_ordinal1(k1_relat_1(X0))
         => ( v5_ordinal1(X0)
            & v1_funct_1(X0)
            & v5_relat_1(X0,k2_relat_1(X0))
            & v1_relat_1(X0) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v3_ordinal1(k1_relat_1(X0))
       => ( v5_ordinal1(X0)
          & v1_funct_1(X0)
          & v5_relat_1(X0,k2_relat_1(X0))
          & v1_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_ordinal1)).

fof(f53,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f20,f40])).

fof(f40,plain,
    ( spl1_3
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f20,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f52,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f21,f49])).

fof(f21,plain,(
    v3_ordinal1(k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f47,plain,
    ( ~ spl1_1
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f22,f44,f40,f36,f32])).

fof(f22,plain,
    ( ~ v5_ordinal1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v5_relat_1(sK0,k2_relat_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:48:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.44  % (3443)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.44  % (3442)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.44  % (3442)Refutation found. Thanks to Tanya!
% 0.22/0.44  % SZS status Theorem for theBenchmark
% 0.22/0.44  % SZS output start Proof for theBenchmark
% 0.22/0.44  fof(f118,plain,(
% 0.22/0.44    $false),
% 0.22/0.44    inference(avatar_sat_refutation,[],[f47,f52,f53,f54,f58,f62,f70,f78,f82,f88,f95,f102,f108,f113,f117])).
% 0.22/0.44  fof(f117,plain,(
% 0.22/0.44    ~spl1_1 | spl1_2 | ~spl1_15 | ~spl1_17),
% 0.22/0.44    inference(avatar_contradiction_clause,[],[f116])).
% 0.22/0.44  fof(f116,plain,(
% 0.22/0.44    $false | (~spl1_1 | spl1_2 | ~spl1_15 | ~spl1_17)),
% 0.22/0.44    inference(subsumption_resolution,[],[f115,f38])).
% 0.22/0.44  fof(f38,plain,(
% 0.22/0.44    ~v5_relat_1(sK0,k2_relat_1(sK0)) | spl1_2),
% 0.22/0.44    inference(avatar_component_clause,[],[f36])).
% 0.22/0.44  fof(f36,plain,(
% 0.22/0.44    spl1_2 <=> v5_relat_1(sK0,k2_relat_1(sK0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.22/0.44  fof(f115,plain,(
% 0.22/0.44    v5_relat_1(sK0,k2_relat_1(sK0)) | (~spl1_1 | ~spl1_15 | ~spl1_17)),
% 0.22/0.44    inference(subsumption_resolution,[],[f114,f33])).
% 0.22/0.44  fof(f33,plain,(
% 0.22/0.44    v1_relat_1(sK0) | ~spl1_1),
% 0.22/0.44    inference(avatar_component_clause,[],[f32])).
% 0.22/0.44  fof(f32,plain,(
% 0.22/0.44    spl1_1 <=> v1_relat_1(sK0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.22/0.44  fof(f114,plain,(
% 0.22/0.44    ~v1_relat_1(sK0) | v5_relat_1(sK0,k2_relat_1(sK0)) | (~spl1_15 | ~spl1_17)),
% 0.22/0.44    inference(resolution,[],[f112,f101])).
% 0.22/0.44  fof(f101,plain,(
% 0.22/0.44    r1_tarski(sK0,sK0) | ~spl1_15),
% 0.22/0.44    inference(avatar_component_clause,[],[f99])).
% 0.22/0.44  fof(f99,plain,(
% 0.22/0.44    spl1_15 <=> r1_tarski(sK0,sK0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_15])])).
% 0.22/0.44  fof(f112,plain,(
% 0.22/0.44    ( ! [X0] : (~r1_tarski(sK0,X0) | ~v1_relat_1(X0) | v5_relat_1(sK0,k2_relat_1(X0))) ) | ~spl1_17),
% 0.22/0.44    inference(avatar_component_clause,[],[f111])).
% 0.22/0.44  % (3444)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.22/0.44  fof(f111,plain,(
% 0.22/0.44    spl1_17 <=> ! [X0] : (~v1_relat_1(X0) | ~r1_tarski(sK0,X0) | v5_relat_1(sK0,k2_relat_1(X0)))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_17])])).
% 0.22/0.44  fof(f113,plain,(
% 0.22/0.44    spl1_17 | ~spl1_1 | ~spl1_16),
% 0.22/0.44    inference(avatar_split_clause,[],[f109,f106,f32,f111])).
% 0.22/0.44  fof(f106,plain,(
% 0.22/0.44    spl1_16 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | v5_relat_1(X0,k2_relat_1(X1)))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_16])])).
% 0.22/0.44  fof(f109,plain,(
% 0.22/0.44    ( ! [X0] : (~v1_relat_1(X0) | ~r1_tarski(sK0,X0) | v5_relat_1(sK0,k2_relat_1(X0))) ) | (~spl1_1 | ~spl1_16)),
% 0.22/0.44    inference(resolution,[],[f107,f33])).
% 0.22/0.44  fof(f107,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~r1_tarski(X0,X1) | v5_relat_1(X0,k2_relat_1(X1))) ) | ~spl1_16),
% 0.22/0.44    inference(avatar_component_clause,[],[f106])).
% 0.22/0.44  fof(f108,plain,(
% 0.22/0.44    spl1_16 | ~spl1_7 | ~spl1_12),
% 0.22/0.44    inference(avatar_split_clause,[],[f104,f80,f60,f106])).
% 0.22/0.44  fof(f60,plain,(
% 0.22/0.44    spl1_7 <=> ! [X1,X0] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.22/0.44  fof(f80,plain,(
% 0.22/0.44    spl1_12 <=> ! [X1,X0] : (v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).
% 0.22/0.44  fof(f104,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | v5_relat_1(X0,k2_relat_1(X1))) ) | (~spl1_7 | ~spl1_12)),
% 0.22/0.44    inference(duplicate_literal_removal,[],[f103])).
% 0.22/0.44  fof(f103,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | v5_relat_1(X0,k2_relat_1(X1)) | ~v1_relat_1(X0)) ) | (~spl1_7 | ~spl1_12)),
% 0.22/0.44    inference(resolution,[],[f61,f81])).
% 0.22/0.44  fof(f81,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | v5_relat_1(X1,X0) | ~v1_relat_1(X1)) ) | ~spl1_12),
% 0.22/0.44    inference(avatar_component_clause,[],[f80])).
% 0.22/0.44  % (3445)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.22/0.44  fof(f61,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl1_7),
% 0.22/0.44    inference(avatar_component_clause,[],[f60])).
% 0.22/0.44  fof(f102,plain,(
% 0.22/0.44    spl1_15 | ~spl1_1 | ~spl1_11 | ~spl1_14),
% 0.22/0.44    inference(avatar_split_clause,[],[f97,f92,f76,f32,f99])).
% 0.22/0.44  fof(f76,plain,(
% 0.22/0.44    spl1_11 <=> ! [X1,X0] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).
% 0.22/0.44  fof(f92,plain,(
% 0.22/0.44    spl1_14 <=> sK0 = k8_relat_1(k2_relat_1(sK0),sK0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).
% 0.22/0.44  fof(f97,plain,(
% 0.22/0.44    r1_tarski(sK0,sK0) | (~spl1_1 | ~spl1_11 | ~spl1_14)),
% 0.22/0.44    inference(subsumption_resolution,[],[f96,f33])).
% 0.22/0.44  fof(f96,plain,(
% 0.22/0.44    r1_tarski(sK0,sK0) | ~v1_relat_1(sK0) | (~spl1_11 | ~spl1_14)),
% 0.22/0.44    inference(superposition,[],[f77,f94])).
% 0.22/0.44  fof(f94,plain,(
% 0.22/0.44    sK0 = k8_relat_1(k2_relat_1(sK0),sK0) | ~spl1_14),
% 0.22/0.44    inference(avatar_component_clause,[],[f92])).
% 0.22/0.44  fof(f77,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1)) ) | ~spl1_11),
% 0.22/0.44    inference(avatar_component_clause,[],[f76])).
% 0.22/0.44  fof(f95,plain,(
% 0.22/0.44    spl1_14 | ~spl1_1 | ~spl1_6),
% 0.22/0.44    inference(avatar_split_clause,[],[f90,f56,f32,f92])).
% 0.22/0.44  fof(f56,plain,(
% 0.22/0.44    spl1_6 <=> ! [X0] : (k8_relat_1(k2_relat_1(X0),X0) = X0 | ~v1_relat_1(X0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.22/0.44  fof(f90,plain,(
% 0.22/0.44    sK0 = k8_relat_1(k2_relat_1(sK0),sK0) | (~spl1_1 | ~spl1_6)),
% 0.22/0.44    inference(resolution,[],[f57,f33])).
% 0.22/0.44  fof(f57,plain,(
% 0.22/0.44    ( ! [X0] : (~v1_relat_1(X0) | k8_relat_1(k2_relat_1(X0),X0) = X0) ) | ~spl1_6),
% 0.22/0.44    inference(avatar_component_clause,[],[f56])).
% 0.22/0.44  fof(f88,plain,(
% 0.22/0.44    spl1_4 | ~spl1_5 | ~spl1_9),
% 0.22/0.44    inference(avatar_split_clause,[],[f87,f68,f49,f44])).
% 0.22/0.44  fof(f44,plain,(
% 0.22/0.44    spl1_4 <=> v5_ordinal1(sK0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.22/0.44  fof(f49,plain,(
% 0.22/0.44    spl1_5 <=> v3_ordinal1(k1_relat_1(sK0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.22/0.44  fof(f68,plain,(
% 0.22/0.44    spl1_9 <=> ! [X0] : (v5_ordinal1(X0) | ~v3_ordinal1(k1_relat_1(X0)))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.22/0.44  fof(f87,plain,(
% 0.22/0.44    v5_ordinal1(sK0) | (~spl1_5 | ~spl1_9)),
% 0.22/0.44    inference(resolution,[],[f69,f51])).
% 0.22/0.44  fof(f51,plain,(
% 0.22/0.44    v3_ordinal1(k1_relat_1(sK0)) | ~spl1_5),
% 0.22/0.44    inference(avatar_component_clause,[],[f49])).
% 0.22/0.44  fof(f69,plain,(
% 0.22/0.44    ( ! [X0] : (~v3_ordinal1(k1_relat_1(X0)) | v5_ordinal1(X0)) ) | ~spl1_9),
% 0.22/0.44    inference(avatar_component_clause,[],[f68])).
% 0.22/0.44  fof(f82,plain,(
% 0.22/0.44    spl1_12),
% 0.22/0.44    inference(avatar_split_clause,[],[f30,f80])).
% 0.22/0.44  fof(f30,plain,(
% 0.22/0.44    ( ! [X0,X1] : (v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f18])).
% 0.22/0.44  fof(f18,plain,(
% 0.22/0.44    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.22/0.44    inference(nnf_transformation,[],[f14])).
% 0.22/0.44  fof(f14,plain,(
% 0.22/0.44    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f1])).
% 0.22/0.44  fof(f1,axiom,(
% 0.22/0.44    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.22/0.44  fof(f78,plain,(
% 0.22/0.44    spl1_11),
% 0.22/0.44    inference(avatar_split_clause,[],[f28,f76])).
% 0.22/0.44  fof(f28,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f13])).
% 0.22/0.44  fof(f13,plain,(
% 0.22/0.44    ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f2])).
% 0.22/0.44  fof(f2,axiom,(
% 0.22/0.44    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k8_relat_1(X0,X1),X1))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).
% 0.22/0.44  fof(f70,plain,(
% 0.22/0.44    spl1_9),
% 0.22/0.44    inference(avatar_split_clause,[],[f27,f68])).
% 0.22/0.44  fof(f27,plain,(
% 0.22/0.44    ( ! [X0] : (v5_ordinal1(X0) | ~v3_ordinal1(k1_relat_1(X0))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f17])).
% 0.22/0.44  fof(f17,plain,(
% 0.22/0.44    ! [X0] : ((v5_ordinal1(X0) | ~v3_ordinal1(k1_relat_1(X0))) & (v3_ordinal1(k1_relat_1(X0)) | ~v5_ordinal1(X0)))),
% 0.22/0.44    inference(nnf_transformation,[],[f5])).
% 0.22/0.44  fof(f5,axiom,(
% 0.22/0.44    ! [X0] : (v5_ordinal1(X0) <=> v3_ordinal1(k1_relat_1(X0)))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_ordinal1)).
% 0.22/0.44  fof(f62,plain,(
% 0.22/0.44    spl1_7),
% 0.22/0.44    inference(avatar_split_clause,[],[f25,f60])).
% 0.22/0.44  fof(f25,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f12])).
% 0.22/0.44  fof(f12,plain,(
% 0.22/0.44    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.44    inference(flattening,[],[f11])).
% 0.22/0.44  fof(f11,plain,(
% 0.22/0.44    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.44    inference(ennf_transformation,[],[f4])).
% 0.22/0.44  fof(f4,axiom,(
% 0.22/0.44    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 0.22/0.44  fof(f58,plain,(
% 0.22/0.44    spl1_6),
% 0.22/0.44    inference(avatar_split_clause,[],[f23,f56])).
% 0.22/0.44  fof(f23,plain,(
% 0.22/0.44    ( ! [X0] : (k8_relat_1(k2_relat_1(X0),X0) = X0 | ~v1_relat_1(X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f10])).
% 0.22/0.44  fof(f10,plain,(
% 0.22/0.44    ! [X0] : (k8_relat_1(k2_relat_1(X0),X0) = X0 | ~v1_relat_1(X0))),
% 0.22/0.44    inference(ennf_transformation,[],[f3])).
% 0.22/0.44  fof(f3,axiom,(
% 0.22/0.44    ! [X0] : (v1_relat_1(X0) => k8_relat_1(k2_relat_1(X0),X0) = X0)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t126_relat_1)).
% 0.22/0.44  fof(f54,plain,(
% 0.22/0.44    spl1_1),
% 0.22/0.44    inference(avatar_split_clause,[],[f19,f32])).
% 0.22/0.44  fof(f19,plain,(
% 0.22/0.44    v1_relat_1(sK0)),
% 0.22/0.44    inference(cnf_transformation,[],[f16])).
% 0.22/0.44  fof(f16,plain,(
% 0.22/0.44    (~v5_ordinal1(sK0) | ~v1_funct_1(sK0) | ~v5_relat_1(sK0,k2_relat_1(sK0)) | ~v1_relat_1(sK0)) & v3_ordinal1(k1_relat_1(sK0)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f15])).
% 0.22/0.44  fof(f15,plain,(
% 0.22/0.44    ? [X0] : ((~v5_ordinal1(X0) | ~v1_funct_1(X0) | ~v5_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0)) & v3_ordinal1(k1_relat_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0)) => ((~v5_ordinal1(sK0) | ~v1_funct_1(sK0) | ~v5_relat_1(sK0,k2_relat_1(sK0)) | ~v1_relat_1(sK0)) & v3_ordinal1(k1_relat_1(sK0)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f9,plain,(
% 0.22/0.44    ? [X0] : ((~v5_ordinal1(X0) | ~v1_funct_1(X0) | ~v5_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0)) & v3_ordinal1(k1_relat_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.22/0.44    inference(flattening,[],[f8])).
% 0.22/0.44  fof(f8,plain,(
% 0.22/0.44    ? [X0] : (((~v5_ordinal1(X0) | ~v1_funct_1(X0) | ~v5_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0)) & v3_ordinal1(k1_relat_1(X0))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.22/0.44    inference(ennf_transformation,[],[f7])).
% 0.22/0.44  fof(f7,negated_conjecture,(
% 0.22/0.44    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v3_ordinal1(k1_relat_1(X0)) => (v5_ordinal1(X0) & v1_funct_1(X0) & v5_relat_1(X0,k2_relat_1(X0)) & v1_relat_1(X0))))),
% 0.22/0.44    inference(negated_conjecture,[],[f6])).
% 0.22/0.44  fof(f6,conjecture,(
% 0.22/0.44    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v3_ordinal1(k1_relat_1(X0)) => (v5_ordinal1(X0) & v1_funct_1(X0) & v5_relat_1(X0,k2_relat_1(X0)) & v1_relat_1(X0))))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_ordinal1)).
% 0.22/0.44  fof(f53,plain,(
% 0.22/0.44    spl1_3),
% 0.22/0.44    inference(avatar_split_clause,[],[f20,f40])).
% 0.22/0.44  fof(f40,plain,(
% 0.22/0.44    spl1_3 <=> v1_funct_1(sK0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.22/0.44  fof(f20,plain,(
% 0.22/0.44    v1_funct_1(sK0)),
% 0.22/0.44    inference(cnf_transformation,[],[f16])).
% 0.22/0.44  fof(f52,plain,(
% 0.22/0.44    spl1_5),
% 0.22/0.44    inference(avatar_split_clause,[],[f21,f49])).
% 0.22/0.44  fof(f21,plain,(
% 0.22/0.44    v3_ordinal1(k1_relat_1(sK0))),
% 0.22/0.44    inference(cnf_transformation,[],[f16])).
% 0.22/0.44  fof(f47,plain,(
% 0.22/0.44    ~spl1_1 | ~spl1_2 | ~spl1_3 | ~spl1_4),
% 0.22/0.44    inference(avatar_split_clause,[],[f22,f44,f40,f36,f32])).
% 0.22/0.44  fof(f22,plain,(
% 0.22/0.44    ~v5_ordinal1(sK0) | ~v1_funct_1(sK0) | ~v5_relat_1(sK0,k2_relat_1(sK0)) | ~v1_relat_1(sK0)),
% 0.22/0.44    inference(cnf_transformation,[],[f16])).
% 0.22/0.44  % SZS output end Proof for theBenchmark
% 0.22/0.44  % (3442)------------------------------
% 0.22/0.44  % (3442)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (3442)Termination reason: Refutation
% 0.22/0.44  
% 0.22/0.45  % (3442)Memory used [KB]: 10618
% 0.22/0.45  % (3442)Time elapsed: 0.005 s
% 0.22/0.45  % (3442)------------------------------
% 0.22/0.45  % (3442)------------------------------
% 0.22/0.45  % (3436)Success in time 0.076 s
%------------------------------------------------------------------------------
