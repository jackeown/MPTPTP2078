%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   67 (  96 expanded)
%              Number of leaves         :   19 (  42 expanded)
%              Depth                    :    7
%              Number of atoms          :  205 ( 294 expanded)
%              Number of equality atoms :   21 (  33 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f108,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f39,f44,f48,f52,f56,f64,f79,f85,f94,f99,f103])).

fof(f103,plain,
    ( spl3_1
    | ~ spl3_3
    | ~ spl3_15 ),
    inference(avatar_contradiction_clause,[],[f102])).

fof(f102,plain,
    ( $false
    | spl3_1
    | ~ spl3_3
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f100,f33])).

fof(f33,plain,
    ( k1_xboole_0 != k10_relat_1(sK0,k1_xboole_0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl3_1
  <=> k1_xboole_0 = k10_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f100,plain,
    ( k1_xboole_0 = k10_relat_1(sK0,k1_xboole_0)
    | ~ spl3_3
    | ~ spl3_15 ),
    inference(resolution,[],[f98,f43])).

fof(f43,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl3_3
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f98,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = k10_relat_1(sK0,X0) )
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl3_15
  <=> ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = k10_relat_1(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f99,plain,
    ( spl3_15
    | ~ spl3_2
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f95,f92,f36,f97])).

fof(f36,plain,
    ( spl3_2
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f92,plain,
    ( spl3_14
  <=> ! [X1,X0] :
        ( ~ v1_xboole_0(X0)
        | ~ v1_relat_1(X1)
        | k1_xboole_0 = k10_relat_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f95,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = k10_relat_1(sK0,X0) )
    | ~ spl3_2
    | ~ spl3_14 ),
    inference(resolution,[],[f93,f38])).

fof(f38,plain,
    ( v1_relat_1(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f93,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ v1_xboole_0(X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f92])).

fof(f94,plain,
    ( spl3_14
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f90,f83,f46,f92])).

fof(f46,plain,
    ( spl3_4
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f83,plain,
    ( spl3_12
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_xboole_0(X1)
        | v1_xboole_0(k10_relat_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f90,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(X0)
        | ~ v1_relat_1(X1)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(resolution,[],[f84,f47])).

fof(f47,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f46])).

fof(f84,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(k10_relat_1(X0,X1))
        | ~ v1_xboole_0(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f83])).

fof(f85,plain,
    ( spl3_12
    | ~ spl3_5
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f80,f77,f50,f83])).

fof(f50,plain,
    ( spl3_5
  <=> ! [X0] :
        ( v1_xboole_0(X0)
        | r2_hidden(sK1(X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f77,plain,
    ( spl3_11
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
        | ~ v1_relat_1(X1)
        | ~ v1_xboole_0(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f80,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_xboole_0(X1)
        | v1_xboole_0(k10_relat_1(X0,X1)) )
    | ~ spl3_5
    | ~ spl3_11 ),
    inference(resolution,[],[f78,f51])).

fof(f51,plain,
    ( ! [X0] :
        ( r2_hidden(sK1(X0),X0)
        | v1_xboole_0(X0) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f50])).

fof(f78,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
        | ~ v1_relat_1(X1)
        | ~ v1_xboole_0(X2) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f77])).

fof(f79,plain,
    ( spl3_11
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f75,f62,f54,f77])).

fof(f54,plain,
    ( spl3_6
  <=> ! [X0,X2] :
        ( ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f62,plain,
    ( spl3_8
  <=> ! [X1,X0,X2] :
        ( r2_hidden(sK2(X0,X1,X2),X1)
        | ~ r2_hidden(X0,k10_relat_1(X2,X1))
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f75,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
        | ~ v1_relat_1(X1)
        | ~ v1_xboole_0(X2) )
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(resolution,[],[f63,f55])).

fof(f55,plain,
    ( ! [X2,X0] :
        ( ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f54])).

fof(f63,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(sK2(X0,X1,X2),X1)
        | ~ r2_hidden(X0,k10_relat_1(X2,X1))
        | ~ v1_relat_1(X2) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f62])).

fof(f64,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f28,f62])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f18])).

fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK2(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK2(X0,X1,X2)),X2)
        & r2_hidden(sK2(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
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
    inference(rectify,[],[f16])).

fof(f16,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

fof(f56,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f24,f54])).

fof(f24,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK1(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f14])).

fof(f14,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f12])).

fof(f12,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f52,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f25,f50])).

fof(f25,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK1(X0),X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f48,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f23,f46])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f44,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f22,f41])).

fof(f22,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f39,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f20,f36])).

fof(f20,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( k1_xboole_0 != k10_relat_1(sK0,k1_xboole_0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f10])).

fof(f10,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k10_relat_1(X0,k1_xboole_0)
        & v1_relat_1(X0) )
   => ( k1_xboole_0 != k10_relat_1(sK0,k1_xboole_0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( k1_xboole_0 != k10_relat_1(X0,k1_xboole_0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_relat_1)).

fof(f34,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f21,f31])).

fof(f21,plain,(
    k1_xboole_0 != k10_relat_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:21:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.42  % (6854)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.43  % (6858)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.21/0.43  % (6856)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.21/0.43  % (6858)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f108,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(avatar_sat_refutation,[],[f34,f39,f44,f48,f52,f56,f64,f79,f85,f94,f99,f103])).
% 0.21/0.43  fof(f103,plain,(
% 0.21/0.43    spl3_1 | ~spl3_3 | ~spl3_15),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f102])).
% 0.21/0.43  fof(f102,plain,(
% 0.21/0.43    $false | (spl3_1 | ~spl3_3 | ~spl3_15)),
% 0.21/0.43    inference(subsumption_resolution,[],[f100,f33])).
% 0.21/0.43  fof(f33,plain,(
% 0.21/0.43    k1_xboole_0 != k10_relat_1(sK0,k1_xboole_0) | spl3_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f31])).
% 0.21/0.43  fof(f31,plain,(
% 0.21/0.43    spl3_1 <=> k1_xboole_0 = k10_relat_1(sK0,k1_xboole_0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.43  fof(f100,plain,(
% 0.21/0.43    k1_xboole_0 = k10_relat_1(sK0,k1_xboole_0) | (~spl3_3 | ~spl3_15)),
% 0.21/0.43    inference(resolution,[],[f98,f43])).
% 0.21/0.43  fof(f43,plain,(
% 0.21/0.43    v1_xboole_0(k1_xboole_0) | ~spl3_3),
% 0.21/0.43    inference(avatar_component_clause,[],[f41])).
% 0.21/0.43  fof(f41,plain,(
% 0.21/0.43    spl3_3 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.43  fof(f98,plain,(
% 0.21/0.43    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = k10_relat_1(sK0,X0)) ) | ~spl3_15),
% 0.21/0.43    inference(avatar_component_clause,[],[f97])).
% 0.21/0.43  fof(f97,plain,(
% 0.21/0.43    spl3_15 <=> ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = k10_relat_1(sK0,X0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.43  fof(f99,plain,(
% 0.21/0.43    spl3_15 | ~spl3_2 | ~spl3_14),
% 0.21/0.43    inference(avatar_split_clause,[],[f95,f92,f36,f97])).
% 0.21/0.43  fof(f36,plain,(
% 0.21/0.43    spl3_2 <=> v1_relat_1(sK0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.43  fof(f92,plain,(
% 0.21/0.43    spl3_14 <=> ! [X1,X0] : (~v1_xboole_0(X0) | ~v1_relat_1(X1) | k1_xboole_0 = k10_relat_1(X1,X0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.43  fof(f95,plain,(
% 0.21/0.43    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = k10_relat_1(sK0,X0)) ) | (~spl3_2 | ~spl3_14)),
% 0.21/0.43    inference(resolution,[],[f93,f38])).
% 0.21/0.43  fof(f38,plain,(
% 0.21/0.43    v1_relat_1(sK0) | ~spl3_2),
% 0.21/0.43    inference(avatar_component_clause,[],[f36])).
% 0.21/0.43  fof(f93,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_xboole_0(X0) | k1_xboole_0 = k10_relat_1(X1,X0)) ) | ~spl3_14),
% 0.21/0.43    inference(avatar_component_clause,[],[f92])).
% 0.21/0.43  fof(f94,plain,(
% 0.21/0.43    spl3_14 | ~spl3_4 | ~spl3_12),
% 0.21/0.43    inference(avatar_split_clause,[],[f90,f83,f46,f92])).
% 0.21/0.43  fof(f46,plain,(
% 0.21/0.43    spl3_4 <=> ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.43  fof(f83,plain,(
% 0.21/0.43    spl3_12 <=> ! [X1,X0] : (~v1_relat_1(X0) | ~v1_xboole_0(X1) | v1_xboole_0(k10_relat_1(X0,X1)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.43  fof(f90,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~v1_relat_1(X1) | k1_xboole_0 = k10_relat_1(X1,X0)) ) | (~spl3_4 | ~spl3_12)),
% 0.21/0.43    inference(resolution,[],[f84,f47])).
% 0.21/0.43  fof(f47,plain,(
% 0.21/0.43    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl3_4),
% 0.21/0.43    inference(avatar_component_clause,[],[f46])).
% 0.21/0.43  fof(f84,plain,(
% 0.21/0.43    ( ! [X0,X1] : (v1_xboole_0(k10_relat_1(X0,X1)) | ~v1_xboole_0(X1) | ~v1_relat_1(X0)) ) | ~spl3_12),
% 0.21/0.43    inference(avatar_component_clause,[],[f83])).
% 0.21/0.43  fof(f85,plain,(
% 0.21/0.43    spl3_12 | ~spl3_5 | ~spl3_11),
% 0.21/0.43    inference(avatar_split_clause,[],[f80,f77,f50,f83])).
% 0.21/0.43  fof(f50,plain,(
% 0.21/0.43    spl3_5 <=> ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK1(X0),X0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.43  fof(f77,plain,(
% 0.21/0.43    spl3_11 <=> ! [X1,X0,X2] : (~r2_hidden(X0,k10_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_xboole_0(X2))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.43  fof(f80,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_xboole_0(X1) | v1_xboole_0(k10_relat_1(X0,X1))) ) | (~spl3_5 | ~spl3_11)),
% 0.21/0.43    inference(resolution,[],[f78,f51])).
% 0.21/0.43  fof(f51,plain,(
% 0.21/0.43    ( ! [X0] : (r2_hidden(sK1(X0),X0) | v1_xboole_0(X0)) ) | ~spl3_5),
% 0.21/0.43    inference(avatar_component_clause,[],[f50])).
% 0.21/0.43  fof(f78,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~r2_hidden(X0,k10_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_xboole_0(X2)) ) | ~spl3_11),
% 0.21/0.43    inference(avatar_component_clause,[],[f77])).
% 0.21/0.43  fof(f79,plain,(
% 0.21/0.43    spl3_11 | ~spl3_6 | ~spl3_8),
% 0.21/0.43    inference(avatar_split_clause,[],[f75,f62,f54,f77])).
% 0.21/0.43  fof(f54,plain,(
% 0.21/0.43    spl3_6 <=> ! [X0,X2] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.43  fof(f62,plain,(
% 0.21/0.43    spl3_8 <=> ! [X1,X0,X2] : (r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.43  fof(f75,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~r2_hidden(X0,k10_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_xboole_0(X2)) ) | (~spl3_6 | ~spl3_8)),
% 0.21/0.43    inference(resolution,[],[f63,f55])).
% 0.21/0.43  fof(f55,plain,(
% 0.21/0.43    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) ) | ~spl3_6),
% 0.21/0.43    inference(avatar_component_clause,[],[f54])).
% 0.21/0.43  fof(f63,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) ) | ~spl3_8),
% 0.21/0.43    inference(avatar_component_clause,[],[f62])).
% 0.21/0.43  fof(f64,plain,(
% 0.21/0.43    spl3_8),
% 0.21/0.43    inference(avatar_split_clause,[],[f28,f62])).
% 0.21/0.43  fof(f28,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f19])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK2(X0,X1,X2)),X2) & r2_hidden(sK2(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f18])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK2(X0,X1,X2)),X2) & r2_hidden(sK2(X0,X1,X2),k2_relat_1(X2))))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.43    inference(rectify,[],[f16])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.43    inference(nnf_transformation,[],[f9])).
% 0.21/0.43  fof(f9,plain,(
% 0.21/0.43    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.21/0.43    inference(ennf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).
% 0.21/0.43  fof(f56,plain,(
% 0.21/0.43    spl3_6),
% 0.21/0.43    inference(avatar_split_clause,[],[f24,f54])).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f15])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK1(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f14])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.43    inference(rectify,[],[f12])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.43    inference(nnf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.43  fof(f52,plain,(
% 0.21/0.43    spl3_5),
% 0.21/0.43    inference(avatar_split_clause,[],[f25,f50])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK1(X0),X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f15])).
% 0.21/0.43  fof(f48,plain,(
% 0.21/0.43    spl3_4),
% 0.21/0.43    inference(avatar_split_clause,[],[f23,f46])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f8])).
% 0.21/0.43  fof(f8,plain,(
% 0.21/0.43    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.43  fof(f44,plain,(
% 0.21/0.43    spl3_3),
% 0.21/0.43    inference(avatar_split_clause,[],[f22,f41])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    v1_xboole_0(k1_xboole_0)),
% 0.21/0.43    inference(cnf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    v1_xboole_0(k1_xboole_0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.43  fof(f39,plain,(
% 0.21/0.43    spl3_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f20,f36])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    v1_relat_1(sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f11])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    k1_xboole_0 != k10_relat_1(sK0,k1_xboole_0) & v1_relat_1(sK0)),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f10])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    ? [X0] : (k1_xboole_0 != k10_relat_1(X0,k1_xboole_0) & v1_relat_1(X0)) => (k1_xboole_0 != k10_relat_1(sK0,k1_xboole_0) & v1_relat_1(sK0))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f7,plain,(
% 0.21/0.43    ? [X0] : (k1_xboole_0 != k10_relat_1(X0,k1_xboole_0) & v1_relat_1(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f6])).
% 0.21/0.43  fof(f6,negated_conjecture,(
% 0.21/0.43    ~! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0))),
% 0.21/0.43    inference(negated_conjecture,[],[f5])).
% 0.21/0.43  fof(f5,conjecture,(
% 0.21/0.43    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_relat_1)).
% 0.21/0.43  fof(f34,plain,(
% 0.21/0.43    ~spl3_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f21,f31])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    k1_xboole_0 != k10_relat_1(sK0,k1_xboole_0)),
% 0.21/0.43    inference(cnf_transformation,[],[f11])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (6858)------------------------------
% 0.21/0.43  % (6858)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (6858)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (6858)Memory used [KB]: 6140
% 0.21/0.43  % (6858)Time elapsed: 0.006 s
% 0.21/0.43  % (6858)------------------------------
% 0.21/0.43  % (6858)------------------------------
% 0.21/0.43  % (6843)Success in time 0.072 s
%------------------------------------------------------------------------------
