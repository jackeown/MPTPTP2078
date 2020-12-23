%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:27 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 210 expanded)
%              Number of leaves         :   31 (  91 expanded)
%              Depth                    :    9
%              Number of atoms          :  345 ( 697 expanded)
%              Number of equality atoms :   40 ( 104 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f342,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f74,f78,f83,f96,f112,f118,f140,f145,f204,f232,f265,f266,f321,f332,f336])).

fof(f336,plain,
    ( spl11_10
    | ~ spl11_2
    | ~ spl11_5 ),
    inference(avatar_split_clause,[],[f335,f80,f66,f128])).

fof(f128,plain,
    ( spl11_10
  <=> sK2 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f66,plain,
    ( spl11_2
  <=> sK2 = k1_relset_1(sK2,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f80,plain,
    ( spl11_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f335,plain,
    ( sK2 = k1_relat_1(sK3)
    | ~ spl11_2
    | ~ spl11_5 ),
    inference(forward_demodulation,[],[f313,f67])).

fof(f67,plain,
    ( sK2 = k1_relset_1(sK2,sK1,sK3)
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f313,plain,
    ( k1_relset_1(sK2,sK1,sK3) = k1_relat_1(sK3)
    | ~ spl11_5 ),
    inference(unit_resulting_resolution,[],[f82,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f82,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl11_5 ),
    inference(avatar_component_clause,[],[f80])).

fof(f332,plain,
    ( ~ spl11_1
    | ~ spl11_3
    | ~ spl11_15 ),
    inference(avatar_contradiction_clause,[],[f331])).

fof(f331,plain,
    ( $false
    | ~ spl11_1
    | ~ spl11_3
    | ~ spl11_15 ),
    inference(subsumption_resolution,[],[f330,f64])).

fof(f64,plain,
    ( ! [X4] : ~ r2_hidden(k4_tarski(sK4,X4),sK3)
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl11_1
  <=> ! [X4] : ~ r2_hidden(k4_tarski(sK4,X4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f330,plain,
    ( r2_hidden(k4_tarski(sK4,sK8(sK3,sK4)),sK3)
    | ~ spl11_3
    | ~ spl11_15 ),
    inference(unit_resulting_resolution,[],[f176,f73,f46])).

fof(f46,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK6(X0,X1),X3),X0)
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0)
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f29,f32,f31,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK6(X0,X1),X3),X0)
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0)
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

% (24671)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
fof(f16,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f73,plain,
    ( r2_hidden(sK4,sK2)
    | ~ spl11_3 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl11_3
  <=> r2_hidden(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f176,plain,
    ( sP0(sK3,sK2)
    | ~ spl11_15 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl11_15
  <=> sP0(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_15])])).

fof(f321,plain,
    ( spl11_2
    | ~ spl11_5
    | ~ spl11_10 ),
    inference(avatar_split_clause,[],[f315,f128,f80,f66])).

fof(f315,plain,
    ( sK2 = k1_relset_1(sK2,sK1,sK3)
    | ~ spl11_5
    | ~ spl11_10 ),
    inference(forward_demodulation,[],[f313,f130])).

fof(f130,plain,
    ( sK2 = k1_relat_1(sK3)
    | ~ spl11_10 ),
    inference(avatar_component_clause,[],[f128])).

fof(f266,plain,
    ( spl11_12
    | ~ spl11_18 ),
    inference(avatar_split_clause,[],[f257,f201,f142])).

fof(f142,plain,
    ( spl11_12
  <=> r2_hidden(sK9(k1_relat_1(sK3),sK2),k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f201,plain,
    ( spl11_18
  <=> sP10(sK9(k1_relat_1(sK3),sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).

fof(f257,plain,
    ( r2_hidden(sK9(k1_relat_1(sK3),sK2),k1_relat_1(sK3))
    | ~ spl11_18 ),
    inference(unit_resulting_resolution,[],[f59,f203,f61])).

fof(f61,plain,(
    ! [X0,X5,X1] :
      ( ~ sP10(X5,X0)
      | ~ sP0(X0,X1)
      | r2_hidden(X5,X1) ) ),
    inference(general_splitting,[],[f47,f60_D])).

fof(f60,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X0)
      | sP10(X5,X0) ) ),
    inference(cnf_transformation,[],[f60_D])).

fof(f60_D,plain,(
    ! [X0,X5] :
      ( ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0)
    <=> ~ sP10(X5,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP10])])).

fof(f47,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f203,plain,
    ( sP10(sK9(k1_relat_1(sK3),sK2),sK3)
    | ~ spl11_18 ),
    inference(avatar_component_clause,[],[f201])).

fof(f59,plain,(
    ! [X0] : sP0(X0,k1_relat_1(X0)) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ~ sP0(X0,X1) )
      & ( sP0(X0,X1)
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> sP0(X0,X1) ) ),
    inference(definition_folding,[],[f4,f16])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f265,plain,
    ( spl11_9
    | spl11_10
    | ~ spl11_8 ),
    inference(avatar_split_clause,[],[f236,f115,f128,f124])).

fof(f124,plain,
    ( spl11_9
  <=> r2_xboole_0(k1_relat_1(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).

fof(f115,plain,
    ( spl11_8
  <=> r1_tarski(k1_relat_1(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f236,plain,
    ( sK2 = k1_relat_1(sK3)
    | r2_xboole_0(k1_relat_1(sK3),sK2)
    | ~ spl11_8 ),
    inference(resolution,[],[f117,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f117,plain,
    ( r1_tarski(k1_relat_1(sK3),sK2)
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f115])).

fof(f232,plain,
    ( ~ spl11_10
    | spl11_15 ),
    inference(avatar_contradiction_clause,[],[f231])).

fof(f231,plain,
    ( $false
    | ~ spl11_10
    | spl11_15 ),
    inference(subsumption_resolution,[],[f228,f177])).

fof(f177,plain,
    ( ~ sP0(sK3,sK2)
    | spl11_15 ),
    inference(avatar_component_clause,[],[f175])).

fof(f228,plain,
    ( sP0(sK3,sK2)
    | ~ spl11_10 ),
    inference(superposition,[],[f59,f130])).

fof(f204,plain,
    ( spl11_18
    | ~ spl11_4
    | ~ spl11_11 ),
    inference(avatar_split_clause,[],[f192,f137,f76,f201])).

fof(f76,plain,
    ( spl11_4
  <=> ! [X5] :
        ( r2_hidden(k4_tarski(X5,sK5(X5)),sK3)
        | ~ r2_hidden(X5,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f137,plain,
    ( spl11_11
  <=> r2_hidden(sK9(k1_relat_1(sK3),sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).

fof(f192,plain,
    ( sP10(sK9(k1_relat_1(sK3),sK2),sK3)
    | ~ spl11_4
    | ~ spl11_11 ),
    inference(unit_resulting_resolution,[],[f139,f97])).

fof(f97,plain,
    ( ! [X0] :
        ( sP10(X0,sK3)
        | ~ r2_hidden(X0,sK2) )
    | ~ spl11_4 ),
    inference(resolution,[],[f60,f77])).

fof(f77,plain,
    ( ! [X5] :
        ( r2_hidden(k4_tarski(X5,sK5(X5)),sK3)
        | ~ r2_hidden(X5,sK2) )
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f76])).

fof(f139,plain,
    ( r2_hidden(sK9(k1_relat_1(sK3),sK2),sK2)
    | ~ spl11_11 ),
    inference(avatar_component_clause,[],[f137])).

fof(f145,plain,
    ( ~ spl11_12
    | ~ spl11_9 ),
    inference(avatar_split_clause,[],[f132,f124,f142])).

fof(f132,plain,
    ( ~ r2_hidden(sK9(k1_relat_1(sK3),sK2),k1_relat_1(sK3))
    | ~ spl11_9 ),
    inference(unit_resulting_resolution,[],[f126,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK9(X0,X1),X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ~ r2_hidden(sK9(X0,X1),X0)
        & r2_hidden(sK9(X0,X1),X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f12,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(sK9(X0,X1),X0)
        & r2_hidden(sK9(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

% (24674)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ~ r2_hidden(X2,X0)
              & r2_hidden(X2,X1) )
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).

fof(f126,plain,
    ( r2_xboole_0(k1_relat_1(sK3),sK2)
    | ~ spl11_9 ),
    inference(avatar_component_clause,[],[f124])).

fof(f140,plain,
    ( spl11_11
    | ~ spl11_9 ),
    inference(avatar_split_clause,[],[f133,f124,f137])).

fof(f133,plain,
    ( r2_hidden(sK9(k1_relat_1(sK3),sK2),sK2)
    | ~ spl11_9 ),
    inference(unit_resulting_resolution,[],[f126,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK9(X0,X1),X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f118,plain,
    ( spl11_8
    | ~ spl11_6
    | ~ spl11_7 ),
    inference(avatar_split_clause,[],[f113,f108,f92,f115])).

fof(f92,plain,
    ( spl11_6
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f108,plain,
    ( spl11_7
  <=> v4_relat_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f113,plain,
    ( r1_tarski(k1_relat_1(sK3),sK2)
    | ~ spl11_6
    | ~ spl11_7 ),
    inference(unit_resulting_resolution,[],[f94,f110,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f110,plain,
    ( v4_relat_1(sK3,sK2)
    | ~ spl11_7 ),
    inference(avatar_component_clause,[],[f108])).

fof(f94,plain,
    ( v1_relat_1(sK3)
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f92])).

fof(f112,plain,
    ( spl11_7
    | ~ spl11_5 ),
    inference(avatar_split_clause,[],[f106,f80,f108])).

fof(f106,plain,
    ( v4_relat_1(sK3,sK2)
    | ~ spl11_5 ),
    inference(resolution,[],[f56,f82])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f96,plain,
    ( spl11_6
    | ~ spl11_5 ),
    inference(avatar_split_clause,[],[f90,f80,f92])).

fof(f90,plain,
    ( v1_relat_1(sK3)
    | ~ spl11_5 ),
    inference(resolution,[],[f54,f82])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f83,plain,(
    spl11_5 ),
    inference(avatar_split_clause,[],[f37,f80])).

fof(f37,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ( sK2 != k1_relset_1(sK2,sK1,sK3)
      | ( ! [X4] : ~ r2_hidden(k4_tarski(sK4,X4),sK3)
        & r2_hidden(sK4,sK2) ) )
    & ( sK2 = k1_relset_1(sK2,sK1,sK3)
      | ! [X5] :
          ( r2_hidden(k4_tarski(X5,sK5(X5)),sK3)
          | ~ r2_hidden(X5,sK2) ) )
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f20,f23,f22,f21])).

fof(f21,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_relset_1(X1,X0,X2) != X1
          | ? [X3] :
              ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) ) )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ! [X5] :
              ( ? [X6] : r2_hidden(k4_tarski(X5,X6),X2)
              | ~ r2_hidden(X5,X1) ) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
   => ( ( sK2 != k1_relset_1(sK2,sK1,sK3)
        | ? [X3] :
            ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),sK3)
            & r2_hidden(X3,sK2) ) )
      & ( sK2 = k1_relset_1(sK2,sK1,sK3)
        | ! [X5] :
            ( ? [X6] : r2_hidden(k4_tarski(X5,X6),sK3)
            | ~ r2_hidden(X5,sK2) ) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X3] :
        ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),sK3)
        & r2_hidden(X3,sK2) )
   => ( ! [X4] : ~ r2_hidden(k4_tarski(sK4,X4),sK3)
      & r2_hidden(sK4,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X5] :
      ( ? [X6] : r2_hidden(k4_tarski(X5,X6),sK3)
     => r2_hidden(k4_tarski(X5,sK5(X5)),sK3) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ( k1_relset_1(X1,X0,X2) != X1
        | ? [X3] :
            ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
            & r2_hidden(X3,X1) ) )
      & ( k1_relset_1(X1,X0,X2) = X1
        | ! [X5] :
            ( ? [X6] : r2_hidden(k4_tarski(X5,X6),X2)
            | ~ r2_hidden(X5,X1) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ( k1_relset_1(X1,X0,X2) != X1
        | ? [X3] :
            ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
            & r2_hidden(X3,X1) ) )
      & ( k1_relset_1(X1,X0,X2) = X1
        | ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ( k1_relset_1(X1,X0,X2) != X1
        | ? [X3] :
            ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
            & r2_hidden(X3,X1) ) )
      & ( k1_relset_1(X1,X0,X2) = X1
        | ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) )
      <~> k1_relset_1(X1,X0,X2) = X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ( ! [X3] :
              ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
                & r2_hidden(X3,X1) )
        <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).

fof(f78,plain,
    ( spl11_4
    | spl11_2 ),
    inference(avatar_split_clause,[],[f38,f66,f76])).

fof(f38,plain,(
    ! [X5] :
      ( sK2 = k1_relset_1(sK2,sK1,sK3)
      | r2_hidden(k4_tarski(X5,sK5(X5)),sK3)
      | ~ r2_hidden(X5,sK2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f74,plain,
    ( spl11_3
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f39,f66,f71])).

fof(f39,plain,
    ( sK2 != k1_relset_1(sK2,sK1,sK3)
    | r2_hidden(sK4,sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f69,plain,
    ( spl11_1
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f40,f66,f63])).

fof(f40,plain,(
    ! [X4] :
      ( sK2 != k1_relset_1(sK2,sK1,sK3)
      | ~ r2_hidden(k4_tarski(sK4,X4),sK3) ) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:11:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (24679)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.47  % (24681)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.47  % (24682)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.48  % (24681)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f342,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f69,f74,f78,f83,f96,f112,f118,f140,f145,f204,f232,f265,f266,f321,f332,f336])).
% 0.20/0.48  fof(f336,plain,(
% 0.20/0.48    spl11_10 | ~spl11_2 | ~spl11_5),
% 0.20/0.48    inference(avatar_split_clause,[],[f335,f80,f66,f128])).
% 0.20/0.48  fof(f128,plain,(
% 0.20/0.48    spl11_10 <=> sK2 = k1_relat_1(sK3)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).
% 0.20/0.48  fof(f66,plain,(
% 0.20/0.48    spl11_2 <=> sK2 = k1_relset_1(sK2,sK1,sK3)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 0.20/0.48  fof(f80,plain,(
% 0.20/0.48    spl11_5 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).
% 0.20/0.48  fof(f335,plain,(
% 0.20/0.48    sK2 = k1_relat_1(sK3) | (~spl11_2 | ~spl11_5)),
% 0.20/0.48    inference(forward_demodulation,[],[f313,f67])).
% 0.20/0.48  fof(f67,plain,(
% 0.20/0.48    sK2 = k1_relset_1(sK2,sK1,sK3) | ~spl11_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f66])).
% 0.20/0.48  fof(f313,plain,(
% 0.20/0.48    k1_relset_1(sK2,sK1,sK3) = k1_relat_1(sK3) | ~spl11_5),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f82,f55])).
% 0.20/0.48  fof(f55,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.48  fof(f82,plain,(
% 0.20/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~spl11_5),
% 0.20/0.48    inference(avatar_component_clause,[],[f80])).
% 0.20/0.48  fof(f332,plain,(
% 0.20/0.48    ~spl11_1 | ~spl11_3 | ~spl11_15),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f331])).
% 0.20/0.48  fof(f331,plain,(
% 0.20/0.48    $false | (~spl11_1 | ~spl11_3 | ~spl11_15)),
% 0.20/0.48    inference(subsumption_resolution,[],[f330,f64])).
% 0.20/0.48  fof(f64,plain,(
% 0.20/0.48    ( ! [X4] : (~r2_hidden(k4_tarski(sK4,X4),sK3)) ) | ~spl11_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f63])).
% 0.20/0.48  fof(f63,plain,(
% 0.20/0.48    spl11_1 <=> ! [X4] : ~r2_hidden(k4_tarski(sK4,X4),sK3)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 0.20/0.48  fof(f330,plain,(
% 0.20/0.48    r2_hidden(k4_tarski(sK4,sK8(sK3,sK4)),sK3) | (~spl11_3 | ~spl11_15)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f176,f73,f46])).
% 0.20/0.48  fof(f46,plain,(
% 0.20/0.48    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) | ~r2_hidden(X5,X1) | ~sP0(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f33])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ! [X0,X1] : ((sP0(X0,X1) | ((! [X3] : ~r2_hidden(k4_tarski(sK6(X0,X1),X3),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) | ~r2_hidden(X5,X1))) | ~sP0(X0,X1)))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f29,f32,f31,f30])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK6(X0,X1),X3),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0) | r2_hidden(sK6(X0,X1),X1))))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | ~sP0(X0,X1)))),
% 0.20/0.48    inference(rectify,[],[f28])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | ~sP0(X0,X1)))),
% 0.20/0.48    inference(nnf_transformation,[],[f16])).
% 0.20/0.48  % (24671)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0,X1] : (sP0(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.20/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.48  fof(f73,plain,(
% 0.20/0.48    r2_hidden(sK4,sK2) | ~spl11_3),
% 0.20/0.48    inference(avatar_component_clause,[],[f71])).
% 0.20/0.48  fof(f71,plain,(
% 0.20/0.48    spl11_3 <=> r2_hidden(sK4,sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).
% 0.20/0.48  fof(f176,plain,(
% 0.20/0.48    sP0(sK3,sK2) | ~spl11_15),
% 0.20/0.48    inference(avatar_component_clause,[],[f175])).
% 0.20/0.48  fof(f175,plain,(
% 0.20/0.48    spl11_15 <=> sP0(sK3,sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl11_15])])).
% 0.20/0.48  fof(f321,plain,(
% 0.20/0.48    spl11_2 | ~spl11_5 | ~spl11_10),
% 0.20/0.48    inference(avatar_split_clause,[],[f315,f128,f80,f66])).
% 0.20/0.48  fof(f315,plain,(
% 0.20/0.48    sK2 = k1_relset_1(sK2,sK1,sK3) | (~spl11_5 | ~spl11_10)),
% 0.20/0.48    inference(forward_demodulation,[],[f313,f130])).
% 0.20/0.48  fof(f130,plain,(
% 0.20/0.48    sK2 = k1_relat_1(sK3) | ~spl11_10),
% 0.20/0.48    inference(avatar_component_clause,[],[f128])).
% 0.20/0.48  fof(f266,plain,(
% 0.20/0.48    spl11_12 | ~spl11_18),
% 0.20/0.48    inference(avatar_split_clause,[],[f257,f201,f142])).
% 0.20/0.48  fof(f142,plain,(
% 0.20/0.48    spl11_12 <=> r2_hidden(sK9(k1_relat_1(sK3),sK2),k1_relat_1(sK3))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).
% 0.20/0.48  fof(f201,plain,(
% 0.20/0.48    spl11_18 <=> sP10(sK9(k1_relat_1(sK3),sK2),sK3)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).
% 0.20/0.48  fof(f257,plain,(
% 0.20/0.48    r2_hidden(sK9(k1_relat_1(sK3),sK2),k1_relat_1(sK3)) | ~spl11_18),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f59,f203,f61])).
% 0.20/0.48  fof(f61,plain,(
% 0.20/0.48    ( ! [X0,X5,X1] : (~sP10(X5,X0) | ~sP0(X0,X1) | r2_hidden(X5,X1)) )),
% 0.20/0.48    inference(general_splitting,[],[f47,f60_D])).
% 0.20/0.48  fof(f60,plain,(
% 0.20/0.48    ( ! [X6,X0,X5] : (~r2_hidden(k4_tarski(X5,X6),X0) | sP10(X5,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f60_D])).
% 0.20/0.48  fof(f60_D,plain,(
% 0.20/0.48    ( ! [X0,X5] : (( ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0) ) <=> ~sP10(X5,X0)) )),
% 0.20/0.48    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP10])])).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~sP0(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f33])).
% 0.20/0.48  fof(f203,plain,(
% 0.20/0.48    sP10(sK9(k1_relat_1(sK3),sK2),sK3) | ~spl11_18),
% 0.20/0.48    inference(avatar_component_clause,[],[f201])).
% 0.20/0.48  fof(f59,plain,(
% 0.20/0.48    ( ! [X0] : (sP0(X0,k1_relat_1(X0))) )),
% 0.20/0.48    inference(equality_resolution,[],[f50])).
% 0.20/0.48  fof(f50,plain,(
% 0.20/0.48    ( ! [X0,X1] : (sP0(X0,X1) | k1_relat_1(X0) != X1) )),
% 0.20/0.48    inference(cnf_transformation,[],[f34])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ~sP0(X0,X1)) & (sP0(X0,X1) | k1_relat_1(X0) != X1))),
% 0.20/0.48    inference(nnf_transformation,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> sP0(X0,X1))),
% 0.20/0.48    inference(definition_folding,[],[f4,f16])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 0.20/0.48  fof(f265,plain,(
% 0.20/0.48    spl11_9 | spl11_10 | ~spl11_8),
% 0.20/0.48    inference(avatar_split_clause,[],[f236,f115,f128,f124])).
% 0.20/0.48  fof(f124,plain,(
% 0.20/0.48    spl11_9 <=> r2_xboole_0(k1_relat_1(sK3),sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).
% 0.20/0.48  fof(f115,plain,(
% 0.20/0.48    spl11_8 <=> r1_tarski(k1_relat_1(sK3),sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).
% 0.20/0.48  fof(f236,plain,(
% 0.20/0.48    sK2 = k1_relat_1(sK3) | r2_xboole_0(k1_relat_1(sK3),sK2) | ~spl11_8),
% 0.20/0.48    inference(resolution,[],[f117,f45])).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f27])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.20/0.48    inference(flattening,[],[f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.20/0.48    inference(nnf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.20/0.48  fof(f117,plain,(
% 0.20/0.48    r1_tarski(k1_relat_1(sK3),sK2) | ~spl11_8),
% 0.20/0.48    inference(avatar_component_clause,[],[f115])).
% 0.20/0.48  fof(f232,plain,(
% 0.20/0.48    ~spl11_10 | spl11_15),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f231])).
% 0.20/0.48  fof(f231,plain,(
% 0.20/0.48    $false | (~spl11_10 | spl11_15)),
% 0.20/0.48    inference(subsumption_resolution,[],[f228,f177])).
% 0.20/0.48  fof(f177,plain,(
% 0.20/0.48    ~sP0(sK3,sK2) | spl11_15),
% 0.20/0.48    inference(avatar_component_clause,[],[f175])).
% 0.20/0.48  fof(f228,plain,(
% 0.20/0.48    sP0(sK3,sK2) | ~spl11_10),
% 0.20/0.48    inference(superposition,[],[f59,f130])).
% 0.20/0.48  fof(f204,plain,(
% 0.20/0.48    spl11_18 | ~spl11_4 | ~spl11_11),
% 0.20/0.48    inference(avatar_split_clause,[],[f192,f137,f76,f201])).
% 0.20/0.48  fof(f76,plain,(
% 0.20/0.48    spl11_4 <=> ! [X5] : (r2_hidden(k4_tarski(X5,sK5(X5)),sK3) | ~r2_hidden(X5,sK2))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).
% 0.20/0.48  fof(f137,plain,(
% 0.20/0.48    spl11_11 <=> r2_hidden(sK9(k1_relat_1(sK3),sK2),sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).
% 0.20/0.48  fof(f192,plain,(
% 0.20/0.48    sP10(sK9(k1_relat_1(sK3),sK2),sK3) | (~spl11_4 | ~spl11_11)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f139,f97])).
% 0.20/0.48  fof(f97,plain,(
% 0.20/0.48    ( ! [X0] : (sP10(X0,sK3) | ~r2_hidden(X0,sK2)) ) | ~spl11_4),
% 0.20/0.48    inference(resolution,[],[f60,f77])).
% 0.20/0.48  fof(f77,plain,(
% 0.20/0.48    ( ! [X5] : (r2_hidden(k4_tarski(X5,sK5(X5)),sK3) | ~r2_hidden(X5,sK2)) ) | ~spl11_4),
% 0.20/0.48    inference(avatar_component_clause,[],[f76])).
% 0.20/0.48  fof(f139,plain,(
% 0.20/0.48    r2_hidden(sK9(k1_relat_1(sK3),sK2),sK2) | ~spl11_11),
% 0.20/0.48    inference(avatar_component_clause,[],[f137])).
% 0.20/0.48  fof(f145,plain,(
% 0.20/0.48    ~spl11_12 | ~spl11_9),
% 0.20/0.48    inference(avatar_split_clause,[],[f132,f124,f142])).
% 0.20/0.48  fof(f132,plain,(
% 0.20/0.48    ~r2_hidden(sK9(k1_relat_1(sK3),sK2),k1_relat_1(sK3)) | ~spl11_9),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f126,f53])).
% 0.20/0.48  fof(f53,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r2_hidden(sK9(X0,X1),X0) | ~r2_xboole_0(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f36])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    ! [X0,X1] : ((~r2_hidden(sK9(X0,X1),X0) & r2_hidden(sK9(X0,X1),X1)) | ~r2_xboole_0(X0,X1))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f12,f35])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) => (~r2_hidden(sK9(X0,X1),X0) & r2_hidden(sK9(X0,X1),X1)))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ! [X0,X1] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | ~r2_xboole_0(X0,X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  % (24674)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1] : ~(! [X2] : ~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & r2_xboole_0(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).
% 0.20/0.48  fof(f126,plain,(
% 0.20/0.48    r2_xboole_0(k1_relat_1(sK3),sK2) | ~spl11_9),
% 0.20/0.48    inference(avatar_component_clause,[],[f124])).
% 0.20/0.48  fof(f140,plain,(
% 0.20/0.48    spl11_11 | ~spl11_9),
% 0.20/0.48    inference(avatar_split_clause,[],[f133,f124,f137])).
% 0.20/0.48  fof(f133,plain,(
% 0.20/0.48    r2_hidden(sK9(k1_relat_1(sK3),sK2),sK2) | ~spl11_9),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f126,f52])).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r2_hidden(sK9(X0,X1),X1) | ~r2_xboole_0(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f36])).
% 0.20/0.48  fof(f118,plain,(
% 0.20/0.48    spl11_8 | ~spl11_6 | ~spl11_7),
% 0.20/0.48    inference(avatar_split_clause,[],[f113,f108,f92,f115])).
% 0.20/0.48  fof(f92,plain,(
% 0.20/0.48    spl11_6 <=> v1_relat_1(sK3)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).
% 0.20/0.48  fof(f108,plain,(
% 0.20/0.48    spl11_7 <=> v4_relat_1(sK3,sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).
% 0.20/0.48  fof(f113,plain,(
% 0.20/0.48    r1_tarski(k1_relat_1(sK3),sK2) | (~spl11_6 | ~spl11_7)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f94,f110,f41])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f25])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(nnf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.20/0.48  fof(f110,plain,(
% 0.20/0.48    v4_relat_1(sK3,sK2) | ~spl11_7),
% 0.20/0.48    inference(avatar_component_clause,[],[f108])).
% 0.20/0.48  fof(f94,plain,(
% 0.20/0.48    v1_relat_1(sK3) | ~spl11_6),
% 0.20/0.48    inference(avatar_component_clause,[],[f92])).
% 0.20/0.48  fof(f112,plain,(
% 0.20/0.48    spl11_7 | ~spl11_5),
% 0.20/0.48    inference(avatar_split_clause,[],[f106,f80,f108])).
% 0.20/0.48  fof(f106,plain,(
% 0.20/0.48    v4_relat_1(sK3,sK2) | ~spl11_5),
% 0.20/0.48    inference(resolution,[],[f56,f82])).
% 0.20/0.48  fof(f56,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.48  fof(f96,plain,(
% 0.20/0.48    spl11_6 | ~spl11_5),
% 0.20/0.48    inference(avatar_split_clause,[],[f90,f80,f92])).
% 0.20/0.48  fof(f90,plain,(
% 0.20/0.48    v1_relat_1(sK3) | ~spl11_5),
% 0.20/0.48    inference(resolution,[],[f54,f82])).
% 0.20/0.48  fof(f54,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.48  fof(f83,plain,(
% 0.20/0.48    spl11_5),
% 0.20/0.48    inference(avatar_split_clause,[],[f37,f80])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.20/0.48    inference(cnf_transformation,[],[f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    (sK2 != k1_relset_1(sK2,sK1,sK3) | (! [X4] : ~r2_hidden(k4_tarski(sK4,X4),sK3) & r2_hidden(sK4,sK2))) & (sK2 = k1_relset_1(sK2,sK1,sK3) | ! [X5] : (r2_hidden(k4_tarski(X5,sK5(X5)),sK3) | ~r2_hidden(X5,sK2))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f20,f23,f22,f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ? [X0,X1,X2] : ((k1_relset_1(X1,X0,X2) != X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1))) & (k1_relset_1(X1,X0,X2) = X1 | ! [X5] : (? [X6] : r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(X5,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => ((sK2 != k1_relset_1(sK2,sK1,sK3) | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),sK3) & r2_hidden(X3,sK2))) & (sK2 = k1_relset_1(sK2,sK1,sK3) | ! [X5] : (? [X6] : r2_hidden(k4_tarski(X5,X6),sK3) | ~r2_hidden(X5,sK2))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),sK3) & r2_hidden(X3,sK2)) => (! [X4] : ~r2_hidden(k4_tarski(sK4,X4),sK3) & r2_hidden(sK4,sK2))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ! [X5] : (? [X6] : r2_hidden(k4_tarski(X5,X6),sK3) => r2_hidden(k4_tarski(X5,sK5(X5)),sK3))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ? [X0,X1,X2] : ((k1_relset_1(X1,X0,X2) != X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1))) & (k1_relset_1(X1,X0,X2) = X1 | ! [X5] : (? [X6] : r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(X5,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.20/0.48    inference(rectify,[],[f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ? [X0,X1,X2] : ((k1_relset_1(X1,X0,X2) != X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1))) & (k1_relset_1(X1,X0,X2) = X1 | ! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.20/0.48    inference(flattening,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ? [X0,X1,X2] : (((k1_relset_1(X1,X0,X2) != X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1))) & (k1_relset_1(X1,X0,X2) = X1 | ! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.20/0.48    inference(nnf_transformation,[],[f10])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    ? [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) <~> k1_relset_1(X1,X0,X2) = X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.20/0.48    inference(ennf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 0.20/0.48    inference(negated_conjecture,[],[f8])).
% 0.20/0.48  fof(f8,conjecture,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).
% 0.20/0.48  fof(f78,plain,(
% 0.20/0.48    spl11_4 | spl11_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f38,f66,f76])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    ( ! [X5] : (sK2 = k1_relset_1(sK2,sK1,sK3) | r2_hidden(k4_tarski(X5,sK5(X5)),sK3) | ~r2_hidden(X5,sK2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f24])).
% 0.20/0.48  fof(f74,plain,(
% 0.20/0.48    spl11_3 | ~spl11_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f39,f66,f71])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    sK2 != k1_relset_1(sK2,sK1,sK3) | r2_hidden(sK4,sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f24])).
% 0.20/0.48  fof(f69,plain,(
% 0.20/0.48    spl11_1 | ~spl11_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f40,f66,f63])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    ( ! [X4] : (sK2 != k1_relset_1(sK2,sK1,sK3) | ~r2_hidden(k4_tarski(sK4,X4),sK3)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f24])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (24681)------------------------------
% 0.20/0.48  % (24681)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (24681)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (24681)Memory used [KB]: 10746
% 0.20/0.48  % (24681)Time elapsed: 0.017 s
% 0.20/0.48  % (24681)------------------------------
% 0.20/0.48  % (24681)------------------------------
% 0.20/0.48  % (24673)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.48  % (24664)Success in time 0.129 s
%------------------------------------------------------------------------------
