%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:06 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   61 (  81 expanded)
%              Number of leaves         :   18 (  35 expanded)
%              Depth                    :    7
%              Number of atoms          :  175 ( 228 expanded)
%              Number of equality atoms :   16 (  24 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f107,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f36,f41,f46,f54,f58,f66,f86,f91,f96,f106])).

fof(f106,plain,
    ( spl4_1
    | ~ spl4_6
    | ~ spl4_14 ),
    inference(avatar_contradiction_clause,[],[f105])).

fof(f105,plain,
    ( $false
    | spl4_1
    | ~ spl4_6
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f98,f35])).

fof(f35,plain,
    ( k1_xboole_0 != k10_relat_1(sK0,k1_xboole_0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl4_1
  <=> k1_xboole_0 = k10_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f98,plain,
    ( k1_xboole_0 = k10_relat_1(sK0,k1_xboole_0)
    | ~ spl4_6
    | ~ spl4_14 ),
    inference(resolution,[],[f95,f57])).

fof(f57,plain,
    ( ! [X0] :
        ( r2_hidden(sK2(X0),X0)
        | k1_xboole_0 = X0 )
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl4_6
  <=> ! [X0] :
        ( r2_hidden(sK2(X0),X0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f95,plain,
    ( ! [X0] : ~ r2_hidden(X0,k10_relat_1(sK0,k1_xboole_0))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl4_14
  <=> ! [X0] : ~ r2_hidden(X0,k10_relat_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f96,plain,
    ( spl4_14
    | ~ spl4_3
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f92,f89,f43,f94])).

fof(f43,plain,
    ( spl4_3
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f89,plain,
    ( spl4_13
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k10_relat_1(sK0,X1))
        | ~ v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f92,plain,
    ( ! [X0] : ~ r2_hidden(X0,k10_relat_1(sK0,k1_xboole_0))
    | ~ spl4_3
    | ~ spl4_13 ),
    inference(resolution,[],[f90,f45])).

fof(f45,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f43])).

fof(f90,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(X1)
        | ~ r2_hidden(X0,k10_relat_1(sK0,X1)) )
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f89])).

fof(f91,plain,
    ( spl4_13
    | ~ spl4_5
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f87,f84,f52,f89])).

fof(f52,plain,
    ( spl4_5
  <=> ! [X0,X2] :
        ( ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f84,plain,
    ( spl4_12
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k10_relat_1(sK0,X1))
        | r2_hidden(sK3(X0,X1,sK0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f87,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k10_relat_1(sK0,X1))
        | ~ v1_xboole_0(X1) )
    | ~ spl4_5
    | ~ spl4_12 ),
    inference(resolution,[],[f85,f53])).

fof(f53,plain,
    ( ! [X2,X0] :
        ( ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f52])).

fof(f85,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(X0,X1,sK0),X1)
        | ~ r2_hidden(X0,k10_relat_1(sK0,X1)) )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f84])).

fof(f86,plain,
    ( spl4_12
    | ~ spl4_2
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f82,f64,f38,f84])).

fof(f38,plain,
    ( spl4_2
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f64,plain,
    ( spl4_8
  <=> ! [X1,X0,X2] :
        ( r2_hidden(sK3(X0,X1,X2),X1)
        | ~ r2_hidden(X0,k10_relat_1(X2,X1))
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f82,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k10_relat_1(sK0,X1))
        | r2_hidden(sK3(X0,X1,sK0),X1) )
    | ~ spl4_2
    | ~ spl4_8 ),
    inference(resolution,[],[f65,f40])).

fof(f40,plain,
    ( v1_relat_1(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f38])).

fof(f65,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X2)
        | ~ r2_hidden(X0,k10_relat_1(X2,X1))
        | r2_hidden(sK3(X0,X1,X2),X1) )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f64])).

fof(f66,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f30,f64])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(X0,sK3(X0,X1,X2)),X2)
            & r2_hidden(sK3(X0,X1,X2),k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f20])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK3(X0,X1,X2)),X2)
        & r2_hidden(sK3(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
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
    inference(rectify,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

fof(f58,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f27,f56])).

fof(f27,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f8,f16])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f54,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f25,f52])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f46,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f24,f43])).

fof(f24,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f41,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f22,f38])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_relat_1)).

fof(f36,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f23,f33])).

fof(f23,plain,(
    k1_xboole_0 != k10_relat_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:07:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.42  % (14886)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.20/0.42  % (14888)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.20/0.42  % (14885)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.20/0.43  % (14885)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.20/0.43  fof(f107,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(avatar_sat_refutation,[],[f36,f41,f46,f54,f58,f66,f86,f91,f96,f106])).
% 0.20/0.43  fof(f106,plain,(
% 0.20/0.43    spl4_1 | ~spl4_6 | ~spl4_14),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f105])).
% 0.20/0.43  fof(f105,plain,(
% 0.20/0.43    $false | (spl4_1 | ~spl4_6 | ~spl4_14)),
% 0.20/0.43    inference(subsumption_resolution,[],[f98,f35])).
% 0.20/0.43  fof(f35,plain,(
% 0.20/0.43    k1_xboole_0 != k10_relat_1(sK0,k1_xboole_0) | spl4_1),
% 0.20/0.43    inference(avatar_component_clause,[],[f33])).
% 0.20/0.43  fof(f33,plain,(
% 0.20/0.43    spl4_1 <=> k1_xboole_0 = k10_relat_1(sK0,k1_xboole_0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.43  fof(f98,plain,(
% 0.20/0.43    k1_xboole_0 = k10_relat_1(sK0,k1_xboole_0) | (~spl4_6 | ~spl4_14)),
% 0.20/0.43    inference(resolution,[],[f95,f57])).
% 0.20/0.43  fof(f57,plain,(
% 0.20/0.43    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) ) | ~spl4_6),
% 0.20/0.43    inference(avatar_component_clause,[],[f56])).
% 0.20/0.43  fof(f56,plain,(
% 0.20/0.43    spl4_6 <=> ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.43  fof(f95,plain,(
% 0.20/0.43    ( ! [X0] : (~r2_hidden(X0,k10_relat_1(sK0,k1_xboole_0))) ) | ~spl4_14),
% 0.20/0.43    inference(avatar_component_clause,[],[f94])).
% 0.20/0.43  fof(f94,plain,(
% 0.20/0.43    spl4_14 <=> ! [X0] : ~r2_hidden(X0,k10_relat_1(sK0,k1_xboole_0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.20/0.43  fof(f96,plain,(
% 0.20/0.43    spl4_14 | ~spl4_3 | ~spl4_13),
% 0.20/0.43    inference(avatar_split_clause,[],[f92,f89,f43,f94])).
% 0.20/0.43  fof(f43,plain,(
% 0.20/0.43    spl4_3 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.43  fof(f89,plain,(
% 0.20/0.43    spl4_13 <=> ! [X1,X0] : (~r2_hidden(X0,k10_relat_1(sK0,X1)) | ~v1_xboole_0(X1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.20/0.43  fof(f92,plain,(
% 0.20/0.43    ( ! [X0] : (~r2_hidden(X0,k10_relat_1(sK0,k1_xboole_0))) ) | (~spl4_3 | ~spl4_13)),
% 0.20/0.43    inference(resolution,[],[f90,f45])).
% 0.20/0.43  fof(f45,plain,(
% 0.20/0.43    v1_xboole_0(k1_xboole_0) | ~spl4_3),
% 0.20/0.43    inference(avatar_component_clause,[],[f43])).
% 0.20/0.43  fof(f90,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,k10_relat_1(sK0,X1))) ) | ~spl4_13),
% 0.20/0.43    inference(avatar_component_clause,[],[f89])).
% 0.20/0.43  fof(f91,plain,(
% 0.20/0.43    spl4_13 | ~spl4_5 | ~spl4_12),
% 0.20/0.43    inference(avatar_split_clause,[],[f87,f84,f52,f89])).
% 0.20/0.43  fof(f52,plain,(
% 0.20/0.43    spl4_5 <=> ! [X0,X2] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.43  fof(f84,plain,(
% 0.20/0.43    spl4_12 <=> ! [X1,X0] : (~r2_hidden(X0,k10_relat_1(sK0,X1)) | r2_hidden(sK3(X0,X1,sK0),X1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.20/0.43  fof(f87,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~r2_hidden(X0,k10_relat_1(sK0,X1)) | ~v1_xboole_0(X1)) ) | (~spl4_5 | ~spl4_12)),
% 0.20/0.43    inference(resolution,[],[f85,f53])).
% 0.20/0.43  fof(f53,plain,(
% 0.20/0.43    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) ) | ~spl4_5),
% 0.20/0.43    inference(avatar_component_clause,[],[f52])).
% 0.20/0.43  fof(f85,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1,sK0),X1) | ~r2_hidden(X0,k10_relat_1(sK0,X1))) ) | ~spl4_12),
% 0.20/0.43    inference(avatar_component_clause,[],[f84])).
% 0.20/0.43  fof(f86,plain,(
% 0.20/0.43    spl4_12 | ~spl4_2 | ~spl4_8),
% 0.20/0.43    inference(avatar_split_clause,[],[f82,f64,f38,f84])).
% 0.20/0.43  fof(f38,plain,(
% 0.20/0.43    spl4_2 <=> v1_relat_1(sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.43  fof(f64,plain,(
% 0.20/0.43    spl4_8 <=> ! [X1,X0,X2] : (r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.43  fof(f82,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~r2_hidden(X0,k10_relat_1(sK0,X1)) | r2_hidden(sK3(X0,X1,sK0),X1)) ) | (~spl4_2 | ~spl4_8)),
% 0.20/0.43    inference(resolution,[],[f65,f40])).
% 0.20/0.43  fof(f40,plain,(
% 0.20/0.43    v1_relat_1(sK0) | ~spl4_2),
% 0.20/0.43    inference(avatar_component_clause,[],[f38])).
% 0.20/0.43  fof(f65,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | r2_hidden(sK3(X0,X1,X2),X1)) ) | ~spl4_8),
% 0.20/0.43    inference(avatar_component_clause,[],[f64])).
% 0.20/0.43  fof(f66,plain,(
% 0.20/0.43    spl4_8),
% 0.20/0.43    inference(avatar_split_clause,[],[f30,f64])).
% 0.20/0.43  fof(f30,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f21])).
% 0.20/0.43  fof(f21,plain,(
% 0.20/0.43    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK3(X0,X1,X2)),X2) & r2_hidden(sK3(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f20])).
% 0.20/0.43  fof(f20,plain,(
% 0.20/0.43    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK3(X0,X1,X2)),X2) & r2_hidden(sK3(X0,X1,X2),k2_relat_1(X2))))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f19,plain,(
% 0.20/0.43    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.20/0.43    inference(rectify,[],[f18])).
% 0.20/0.43  fof(f18,plain,(
% 0.20/0.43    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.20/0.43    inference(nnf_transformation,[],[f9])).
% 0.20/0.43  fof(f9,plain,(
% 0.20/0.43    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.20/0.43    inference(ennf_transformation,[],[f4])).
% 0.20/0.43  fof(f4,axiom,(
% 0.20/0.43    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).
% 0.20/0.43  fof(f58,plain,(
% 0.20/0.43    spl4_6),
% 0.20/0.43    inference(avatar_split_clause,[],[f27,f56])).
% 0.20/0.43  fof(f27,plain,(
% 0.20/0.43    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.43    inference(cnf_transformation,[],[f17])).
% 0.20/0.43  fof(f17,plain,(
% 0.20/0.43    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f8,f16])).
% 0.20/0.43  fof(f16,plain,(
% 0.20/0.43    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f8,plain,(
% 0.20/0.43    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.20/0.43    inference(ennf_transformation,[],[f3])).
% 0.20/0.43  fof(f3,axiom,(
% 0.20/0.43    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.20/0.43  fof(f54,plain,(
% 0.20/0.43    spl4_5),
% 0.20/0.43    inference(avatar_split_clause,[],[f25,f52])).
% 0.20/0.43  fof(f25,plain,(
% 0.20/0.43    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f15])).
% 0.20/0.43  fof(f15,plain,(
% 0.20/0.43    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK1(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f14])).
% 0.20/0.43  fof(f14,plain,(
% 0.20/0.43    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f13,plain,(
% 0.20/0.43    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.43    inference(rectify,[],[f12])).
% 0.20/0.43  fof(f12,plain,(
% 0.20/0.43    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.43    inference(nnf_transformation,[],[f1])).
% 0.20/0.43  fof(f1,axiom,(
% 0.20/0.43    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.43  fof(f46,plain,(
% 0.20/0.43    spl4_3),
% 0.20/0.43    inference(avatar_split_clause,[],[f24,f43])).
% 0.20/0.43  fof(f24,plain,(
% 0.20/0.43    v1_xboole_0(k1_xboole_0)),
% 0.20/0.43    inference(cnf_transformation,[],[f2])).
% 0.20/0.43  fof(f2,axiom,(
% 0.20/0.43    v1_xboole_0(k1_xboole_0)),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.43  fof(f41,plain,(
% 0.20/0.43    spl4_2),
% 0.20/0.43    inference(avatar_split_clause,[],[f22,f38])).
% 0.20/0.43  fof(f22,plain,(
% 0.20/0.43    v1_relat_1(sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f11])).
% 0.20/0.43  fof(f11,plain,(
% 0.20/0.43    k1_xboole_0 != k10_relat_1(sK0,k1_xboole_0) & v1_relat_1(sK0)),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f10])).
% 0.20/0.43  fof(f10,plain,(
% 0.20/0.43    ? [X0] : (k1_xboole_0 != k10_relat_1(X0,k1_xboole_0) & v1_relat_1(X0)) => (k1_xboole_0 != k10_relat_1(sK0,k1_xboole_0) & v1_relat_1(sK0))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f7,plain,(
% 0.20/0.43    ? [X0] : (k1_xboole_0 != k10_relat_1(X0,k1_xboole_0) & v1_relat_1(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f6])).
% 0.20/0.43  fof(f6,negated_conjecture,(
% 0.20/0.43    ~! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0))),
% 0.20/0.43    inference(negated_conjecture,[],[f5])).
% 0.20/0.43  fof(f5,conjecture,(
% 0.20/0.43    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_relat_1)).
% 0.20/0.43  fof(f36,plain,(
% 0.20/0.43    ~spl4_1),
% 0.20/0.43    inference(avatar_split_clause,[],[f23,f33])).
% 0.20/0.43  fof(f23,plain,(
% 0.20/0.43    k1_xboole_0 != k10_relat_1(sK0,k1_xboole_0)),
% 0.20/0.43    inference(cnf_transformation,[],[f11])).
% 0.20/0.43  % SZS output end Proof for theBenchmark
% 0.20/0.43  % (14885)------------------------------
% 0.20/0.43  % (14885)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (14885)Termination reason: Refutation
% 0.20/0.43  
% 0.20/0.43  % (14885)Memory used [KB]: 10618
% 0.20/0.43  % (14885)Time elapsed: 0.032 s
% 0.20/0.43  % (14885)------------------------------
% 0.20/0.43  % (14885)------------------------------
% 0.20/0.43  % (14879)Success in time 0.078 s
%------------------------------------------------------------------------------
