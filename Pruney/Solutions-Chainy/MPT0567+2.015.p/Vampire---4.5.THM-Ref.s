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
% DateTime   : Thu Dec  3 12:50:06 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 106 expanded)
%              Number of leaves         :   23 (  48 expanded)
%              Depth                    :    7
%              Number of atoms          :  219 ( 294 expanded)
%              Number of equality atoms :   18 (  28 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f129,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f44,f49,f53,f57,f65,f69,f77,f91,f97,f103,f108,f120,f128])).

fof(f128,plain,
    ( spl3_1
    | ~ spl3_13
    | ~ spl3_18 ),
    inference(avatar_contradiction_clause,[],[f127])).

fof(f127,plain,
    ( $false
    | spl3_1
    | ~ spl3_13
    | ~ spl3_18 ),
    inference(subsumption_resolution,[],[f125,f38])).

fof(f38,plain,
    ( k1_xboole_0 != k10_relat_1(sK0,k1_xboole_0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl3_1
  <=> k1_xboole_0 = k10_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f125,plain,
    ( k1_xboole_0 = k10_relat_1(sK0,k1_xboole_0)
    | ~ spl3_13
    | ~ spl3_18 ),
    inference(resolution,[],[f119,f90])).

fof(f90,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl3_13
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f119,plain,
    ( v1_xboole_0(k10_relat_1(sK0,k1_xboole_0))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl3_18
  <=> v1_xboole_0(k10_relat_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f120,plain,
    ( spl3_18
    | ~ spl3_14
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f110,f106,f95,f117])).

fof(f95,plain,
    ( spl3_14
  <=> ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f106,plain,
    ( spl3_16
  <=> ! [X0] :
        ( r2_hidden(sK2(sK1(k10_relat_1(sK0,X0)),X0,sK0),X0)
        | v1_xboole_0(k10_relat_1(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f110,plain,
    ( v1_xboole_0(k10_relat_1(sK0,k1_xboole_0))
    | ~ spl3_14
    | ~ spl3_16 ),
    inference(resolution,[],[f107,f96])).

fof(f96,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f95])).

fof(f107,plain,
    ( ! [X0] :
        ( r2_hidden(sK2(sK1(k10_relat_1(sK0,X0)),X0,sK0),X0)
        | v1_xboole_0(k10_relat_1(sK0,X0)) )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f106])).

fof(f108,plain,
    ( spl3_16
    | ~ spl3_5
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f104,f101,f55,f106])).

fof(f55,plain,
    ( spl3_5
  <=> ! [X0] :
        ( v1_xboole_0(X0)
        | r2_hidden(sK1(X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f101,plain,
    ( spl3_15
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k10_relat_1(sK0,X1))
        | r2_hidden(sK2(X0,X1,sK0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f104,plain,
    ( ! [X0] :
        ( r2_hidden(sK2(sK1(k10_relat_1(sK0,X0)),X0,sK0),X0)
        | v1_xboole_0(k10_relat_1(sK0,X0)) )
    | ~ spl3_5
    | ~ spl3_15 ),
    inference(resolution,[],[f102,f56])).

fof(f56,plain,
    ( ! [X0] :
        ( r2_hidden(sK1(X0),X0)
        | v1_xboole_0(X0) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f55])).

fof(f102,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k10_relat_1(sK0,X1))
        | r2_hidden(sK2(X0,X1,sK0),X1) )
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f101])).

fof(f103,plain,
    ( spl3_15
    | ~ spl3_2
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f99,f75,f41,f101])).

fof(f41,plain,
    ( spl3_2
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f75,plain,
    ( spl3_10
  <=> ! [X1,X0,X2] :
        ( r2_hidden(sK2(X0,X1,X2),X1)
        | ~ r2_hidden(X0,k10_relat_1(X2,X1))
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f99,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k10_relat_1(sK0,X1))
        | r2_hidden(sK2(X0,X1,sK0),X1) )
    | ~ spl3_2
    | ~ spl3_10 ),
    inference(resolution,[],[f76,f43])).

fof(f43,plain,
    ( v1_relat_1(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f76,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X2)
        | ~ r2_hidden(X0,k10_relat_1(X2,X1))
        | r2_hidden(sK2(X0,X1,X2),X1) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f75])).

fof(f97,plain,
    ( spl3_14
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f93,f67,f51,f95])).

fof(f51,plain,
    ( spl3_4
  <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f67,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,X1)
        | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f93,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(resolution,[],[f68,f52])).

fof(f52,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f51])).

fof(f68,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f67])).

fof(f91,plain,
    ( spl3_13
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f87,f63,f46,f89])).

fof(f46,plain,
    ( spl3_3
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f63,plain,
    ( spl3_7
  <=> ! [X1,X0] :
        ( ~ v1_xboole_0(X1)
        | X0 = X1
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f87,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) )
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(resolution,[],[f64,f48])).

fof(f48,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f46])).

fof(f64,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(X0)
        | X0 = X1
        | ~ v1_xboole_0(X1) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f63])).

fof(f77,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f33,f75])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ( r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(X0,sK2(X0,X1,X2)),X2)
            & r2_hidden(sK2(X0,X1,X2),k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f21])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK2(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK2(X0,X1,X2)),X2)
        & r2_hidden(sK2(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X0,X4),X2)
              & r2_hidden(X4,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X0,X3),X2)
              & r2_hidden(X3,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

fof(f69,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f30,f67])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(f65,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f29,f63])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(f57,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f28,f55])).

fof(f28,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK1(X0),X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK1(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f17])).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f53,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f26,f51])).

fof(f26,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f49,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f25,f46])).

fof(f25,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f44,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f23,f41])).

fof(f23,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( k1_xboole_0 != k10_relat_1(sK0,k1_xboole_0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f13])).

fof(f13,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k10_relat_1(X0,k1_xboole_0)
        & v1_relat_1(X0) )
   => ( k1_xboole_0 != k10_relat_1(sK0,k1_xboole_0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( k1_xboole_0 != k10_relat_1(X0,k1_xboole_0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_relat_1)).

fof(f39,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f24,f36])).

fof(f24,plain,(
    k1_xboole_0 != k10_relat_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:40:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.42  % (24778)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.42  % (24777)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.42  % (24777)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f129,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(avatar_sat_refutation,[],[f39,f44,f49,f53,f57,f65,f69,f77,f91,f97,f103,f108,f120,f128])).
% 0.21/0.42  fof(f128,plain,(
% 0.21/0.42    spl3_1 | ~spl3_13 | ~spl3_18),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f127])).
% 0.21/0.42  fof(f127,plain,(
% 0.21/0.42    $false | (spl3_1 | ~spl3_13 | ~spl3_18)),
% 0.21/0.42    inference(subsumption_resolution,[],[f125,f38])).
% 0.21/0.42  fof(f38,plain,(
% 0.21/0.42    k1_xboole_0 != k10_relat_1(sK0,k1_xboole_0) | spl3_1),
% 0.21/0.42    inference(avatar_component_clause,[],[f36])).
% 0.21/0.42  fof(f36,plain,(
% 0.21/0.42    spl3_1 <=> k1_xboole_0 = k10_relat_1(sK0,k1_xboole_0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.42  fof(f125,plain,(
% 0.21/0.42    k1_xboole_0 = k10_relat_1(sK0,k1_xboole_0) | (~spl3_13 | ~spl3_18)),
% 0.21/0.42    inference(resolution,[],[f119,f90])).
% 0.21/0.42  fof(f90,plain,(
% 0.21/0.42    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl3_13),
% 0.21/0.42    inference(avatar_component_clause,[],[f89])).
% 0.21/0.42  fof(f89,plain,(
% 0.21/0.42    spl3_13 <=> ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.42  fof(f119,plain,(
% 0.21/0.42    v1_xboole_0(k10_relat_1(sK0,k1_xboole_0)) | ~spl3_18),
% 0.21/0.42    inference(avatar_component_clause,[],[f117])).
% 0.21/0.42  fof(f117,plain,(
% 0.21/0.42    spl3_18 <=> v1_xboole_0(k10_relat_1(sK0,k1_xboole_0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.42  fof(f120,plain,(
% 0.21/0.42    spl3_18 | ~spl3_14 | ~spl3_16),
% 0.21/0.42    inference(avatar_split_clause,[],[f110,f106,f95,f117])).
% 0.21/0.42  fof(f95,plain,(
% 0.21/0.42    spl3_14 <=> ! [X0] : ~r2_hidden(X0,k1_xboole_0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.42  fof(f106,plain,(
% 0.21/0.42    spl3_16 <=> ! [X0] : (r2_hidden(sK2(sK1(k10_relat_1(sK0,X0)),X0,sK0),X0) | v1_xboole_0(k10_relat_1(sK0,X0)))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.42  fof(f110,plain,(
% 0.21/0.42    v1_xboole_0(k10_relat_1(sK0,k1_xboole_0)) | (~spl3_14 | ~spl3_16)),
% 0.21/0.42    inference(resolution,[],[f107,f96])).
% 0.21/0.42  fof(f96,plain,(
% 0.21/0.42    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl3_14),
% 0.21/0.42    inference(avatar_component_clause,[],[f95])).
% 0.21/0.42  fof(f107,plain,(
% 0.21/0.42    ( ! [X0] : (r2_hidden(sK2(sK1(k10_relat_1(sK0,X0)),X0,sK0),X0) | v1_xboole_0(k10_relat_1(sK0,X0))) ) | ~spl3_16),
% 0.21/0.42    inference(avatar_component_clause,[],[f106])).
% 0.21/0.42  fof(f108,plain,(
% 0.21/0.42    spl3_16 | ~spl3_5 | ~spl3_15),
% 0.21/0.42    inference(avatar_split_clause,[],[f104,f101,f55,f106])).
% 0.21/0.42  fof(f55,plain,(
% 0.21/0.42    spl3_5 <=> ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK1(X0),X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.42  fof(f101,plain,(
% 0.21/0.42    spl3_15 <=> ! [X1,X0] : (~r2_hidden(X0,k10_relat_1(sK0,X1)) | r2_hidden(sK2(X0,X1,sK0),X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.42  fof(f104,plain,(
% 0.21/0.42    ( ! [X0] : (r2_hidden(sK2(sK1(k10_relat_1(sK0,X0)),X0,sK0),X0) | v1_xboole_0(k10_relat_1(sK0,X0))) ) | (~spl3_5 | ~spl3_15)),
% 0.21/0.42    inference(resolution,[],[f102,f56])).
% 0.21/0.42  fof(f56,plain,(
% 0.21/0.42    ( ! [X0] : (r2_hidden(sK1(X0),X0) | v1_xboole_0(X0)) ) | ~spl3_5),
% 0.21/0.42    inference(avatar_component_clause,[],[f55])).
% 0.21/0.42  fof(f102,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r2_hidden(X0,k10_relat_1(sK0,X1)) | r2_hidden(sK2(X0,X1,sK0),X1)) ) | ~spl3_15),
% 0.21/0.42    inference(avatar_component_clause,[],[f101])).
% 0.21/0.42  fof(f103,plain,(
% 0.21/0.42    spl3_15 | ~spl3_2 | ~spl3_10),
% 0.21/0.42    inference(avatar_split_clause,[],[f99,f75,f41,f101])).
% 0.21/0.42  fof(f41,plain,(
% 0.21/0.42    spl3_2 <=> v1_relat_1(sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.42  fof(f75,plain,(
% 0.21/0.42    spl3_10 <=> ! [X1,X0,X2] : (r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.42  fof(f99,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r2_hidden(X0,k10_relat_1(sK0,X1)) | r2_hidden(sK2(X0,X1,sK0),X1)) ) | (~spl3_2 | ~spl3_10)),
% 0.21/0.42    inference(resolution,[],[f76,f43])).
% 0.21/0.42  fof(f43,plain,(
% 0.21/0.42    v1_relat_1(sK0) | ~spl3_2),
% 0.21/0.42    inference(avatar_component_clause,[],[f41])).
% 0.21/0.42  fof(f76,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | r2_hidden(sK2(X0,X1,X2),X1)) ) | ~spl3_10),
% 0.21/0.42    inference(avatar_component_clause,[],[f75])).
% 0.21/0.42  fof(f97,plain,(
% 0.21/0.42    spl3_14 | ~spl3_4 | ~spl3_8),
% 0.21/0.42    inference(avatar_split_clause,[],[f93,f67,f51,f95])).
% 0.21/0.42  fof(f51,plain,(
% 0.21/0.42    spl3_4 <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.42  fof(f67,plain,(
% 0.21/0.42    spl3_8 <=> ! [X1,X0] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.42  fof(f93,plain,(
% 0.21/0.42    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | (~spl3_4 | ~spl3_8)),
% 0.21/0.42    inference(resolution,[],[f68,f52])).
% 0.21/0.42  fof(f52,plain,(
% 0.21/0.42    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | ~spl3_4),
% 0.21/0.42    inference(avatar_component_clause,[],[f51])).
% 0.21/0.42  fof(f68,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) ) | ~spl3_8),
% 0.21/0.42    inference(avatar_component_clause,[],[f67])).
% 0.21/0.42  fof(f91,plain,(
% 0.21/0.42    spl3_13 | ~spl3_3 | ~spl3_7),
% 0.21/0.42    inference(avatar_split_clause,[],[f87,f63,f46,f89])).
% 0.21/0.42  fof(f46,plain,(
% 0.21/0.42    spl3_3 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.42  fof(f63,plain,(
% 0.21/0.42    spl3_7 <=> ! [X1,X0] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.42  fof(f87,plain,(
% 0.21/0.42    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) ) | (~spl3_3 | ~spl3_7)),
% 0.21/0.42    inference(resolution,[],[f64,f48])).
% 0.21/0.42  fof(f48,plain,(
% 0.21/0.42    v1_xboole_0(k1_xboole_0) | ~spl3_3),
% 0.21/0.42    inference(avatar_component_clause,[],[f46])).
% 0.21/0.42  fof(f64,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~v1_xboole_0(X0) | X0 = X1 | ~v1_xboole_0(X1)) ) | ~spl3_7),
% 0.21/0.42    inference(avatar_component_clause,[],[f63])).
% 0.21/0.42  fof(f77,plain,(
% 0.21/0.42    spl3_10),
% 0.21/0.42    inference(avatar_split_clause,[],[f33,f75])).
% 0.21/0.42  fof(f33,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f22])).
% 0.21/0.42  fof(f22,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK2(X0,X1,X2)),X2) & r2_hidden(sK2(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f21])).
% 0.21/0.42  fof(f21,plain,(
% 0.21/0.42    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK2(X0,X1,X2)),X2) & r2_hidden(sK2(X0,X1,X2),k2_relat_1(X2))))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f20,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.42    inference(rectify,[],[f19])).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.42    inference(nnf_transformation,[],[f12])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.21/0.42    inference(ennf_transformation,[],[f6])).
% 0.21/0.42  fof(f6,axiom,(
% 0.21/0.42    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).
% 0.21/0.42  fof(f69,plain,(
% 0.21/0.42    spl3_8),
% 0.21/0.42    inference(avatar_split_clause,[],[f30,f67])).
% 0.21/0.42  fof(f30,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f11])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f5])).
% 0.21/0.42  fof(f5,axiom,(
% 0.21/0.42    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).
% 0.21/0.42  fof(f65,plain,(
% 0.21/0.42    spl3_7),
% 0.21/0.42    inference(avatar_split_clause,[],[f29,f63])).
% 0.21/0.42  fof(f29,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f10])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,axiom,(
% 0.21/0.42    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
% 0.21/0.42  fof(f57,plain,(
% 0.21/0.42    spl3_5),
% 0.21/0.42    inference(avatar_split_clause,[],[f28,f55])).
% 0.21/0.42  fof(f28,plain,(
% 0.21/0.42    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK1(X0),X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f18])).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK1(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f17])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.42    inference(rectify,[],[f15])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.42    inference(nnf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.42  fof(f53,plain,(
% 0.21/0.42    spl3_4),
% 0.21/0.42    inference(avatar_split_clause,[],[f26,f51])).
% 0.21/0.42  fof(f26,plain,(
% 0.21/0.42    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.42  fof(f49,plain,(
% 0.21/0.42    spl3_3),
% 0.21/0.42    inference(avatar_split_clause,[],[f25,f46])).
% 0.21/0.42  fof(f25,plain,(
% 0.21/0.42    v1_xboole_0(k1_xboole_0)),
% 0.21/0.42    inference(cnf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    v1_xboole_0(k1_xboole_0)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.42  fof(f44,plain,(
% 0.21/0.42    spl3_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f23,f41])).
% 0.21/0.42  fof(f23,plain,(
% 0.21/0.42    v1_relat_1(sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f14])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    k1_xboole_0 != k10_relat_1(sK0,k1_xboole_0) & v1_relat_1(sK0)),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f13])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    ? [X0] : (k1_xboole_0 != k10_relat_1(X0,k1_xboole_0) & v1_relat_1(X0)) => (k1_xboole_0 != k10_relat_1(sK0,k1_xboole_0) & v1_relat_1(sK0))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f9,plain,(
% 0.21/0.42    ? [X0] : (k1_xboole_0 != k10_relat_1(X0,k1_xboole_0) & v1_relat_1(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f8])).
% 0.21/0.42  fof(f8,negated_conjecture,(
% 0.21/0.42    ~! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0))),
% 0.21/0.42    inference(negated_conjecture,[],[f7])).
% 0.21/0.42  fof(f7,conjecture,(
% 0.21/0.42    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_relat_1)).
% 0.21/0.42  fof(f39,plain,(
% 0.21/0.42    ~spl3_1),
% 0.21/0.42    inference(avatar_split_clause,[],[f24,f36])).
% 0.21/0.42  fof(f24,plain,(
% 0.21/0.42    k1_xboole_0 != k10_relat_1(sK0,k1_xboole_0)),
% 0.21/0.42    inference(cnf_transformation,[],[f14])).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (24777)------------------------------
% 0.21/0.42  % (24777)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (24777)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (24777)Memory used [KB]: 10618
% 0.21/0.42  % (24777)Time elapsed: 0.007 s
% 0.21/0.42  % (24777)------------------------------
% 0.21/0.42  % (24777)------------------------------
% 0.21/0.43  % (24771)Success in time 0.065 s
%------------------------------------------------------------------------------
