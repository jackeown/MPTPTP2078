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
% DateTime   : Thu Dec  3 12:30:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   57 (  85 expanded)
%              Number of leaves         :   16 (  38 expanded)
%              Depth                    :    6
%              Number of atoms          :  143 ( 247 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f77,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f24,f29,f33,f37,f41,f45,f50,f56,f66,f72,f76])).

fof(f76,plain,
    ( spl2_2
    | ~ spl2_11 ),
    inference(avatar_contradiction_clause,[],[f73])).

fof(f73,plain,
    ( $false
    | spl2_2
    | ~ spl2_11 ),
    inference(resolution,[],[f71,f28])).

fof(f28,plain,
    ( ~ r1_xboole_0(sK0,k1_xboole_0)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f26])).

fof(f26,plain,
    ( spl2_2
  <=> r1_xboole_0(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f71,plain,
    ( ! [X1] : r1_xboole_0(X1,k1_xboole_0)
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl2_11
  <=> ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f72,plain,
    ( spl2_11
    | ~ spl2_5
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f68,f64,f39,f70])).

fof(f39,plain,
    ( spl2_5
  <=> ! [X1,X0] :
        ( r2_hidden(sK1(X0,X1),X1)
        | r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f64,plain,
    ( spl2_10
  <=> ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f68,plain,
    ( ! [X1] : r1_xboole_0(X1,k1_xboole_0)
    | ~ spl2_5
    | ~ spl2_10 ),
    inference(resolution,[],[f65,f40])).

fof(f40,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK1(X0,X1),X1)
        | r1_xboole_0(X0,X1) )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f39])).

fof(f65,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f64])).

fof(f66,plain,
    ( spl2_10
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f62,f54,f43,f64])).

fof(f43,plain,
    ( spl2_6
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,X1)
        | ~ r2_hidden(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f54,plain,
    ( spl2_8
  <=> ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f62,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(condensation,[],[f61])).

fof(f61,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_xboole_0) )
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(resolution,[],[f44,f55])).

fof(f55,plain,
    ( ! [X0] : r1_xboole_0(k1_xboole_0,X0)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f54])).

fof(f44,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,X1)
        | ~ r2_hidden(X2,X0) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f43])).

fof(f56,plain,
    ( spl2_8
    | ~ spl2_1
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f52,f48,f21,f54])).

fof(f21,plain,
    ( spl2_1
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f48,plain,
    ( spl2_7
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f52,plain,
    ( ! [X0] : r1_xboole_0(k1_xboole_0,X0)
    | ~ spl2_1
    | ~ spl2_7 ),
    inference(resolution,[],[f49,f23])).

fof(f23,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f21])).

fof(f49,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(X0)
        | r1_xboole_0(X0,X1) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f48])).

fof(f50,plain,
    ( spl2_7
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f46,f35,f31,f48])).

fof(f31,plain,
    ( spl2_3
  <=> ! [X1,X0] :
        ( ~ v1_xboole_0(X1)
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f35,plain,
    ( spl2_4
  <=> ! [X1,X0] :
        ( r2_hidden(sK1(X0,X1),X0)
        | r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f46,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(X0,X1)
        | ~ v1_xboole_0(X0) )
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(resolution,[],[f36,f32])).

fof(f32,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ v1_xboole_0(X1) )
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f31])).

fof(f36,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK1(X0,X1),X0)
        | r1_xboole_0(X0,X1) )
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f35])).

fof(f45,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f18,f43])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f8,f12])).

fof(f12,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f41,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f17,f39])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f37,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f16,f35])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f33,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f19,f31])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f29,plain,(
    ~ spl2_2 ),
    inference(avatar_split_clause,[],[f14,f26])).

fof(f14,plain,(
    ~ r1_xboole_0(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ~ r1_xboole_0(sK0,k1_xboole_0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f10])).

fof(f10,plain,
    ( ? [X0] : ~ r1_xboole_0(X0,k1_xboole_0)
   => ~ r1_xboole_0(sK0,k1_xboole_0) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] : ~ r1_xboole_0(X0,k1_xboole_0) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f24,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f15,f21])).

fof(f15,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:23:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.43  % (10103)dis+1002_8:1_awrs=converge:awrsf=256:anc=all_dependent:br=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:irw=on:nm=64:nwc=1:sas=z3:s2a=on:sp=frequency:thf=on:uwa=interpreted_only:urr=on_7 on theBenchmark
% 0.21/0.48  % (10104)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% 0.21/0.48  % (10115)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.21/0.48  % (10118)dis+1011_4_awrs=decay:awrsf=32:afp=40000:afq=1.0:amm=off:anc=all:bs=on:cond=on:fsr=off:gsp=input_only:lma=on:nm=16:nwc=1:nicw=on:sac=on:sp=frequency:thi=all:updr=off:uhcvi=on_670 on theBenchmark
% 0.21/0.48  % (10118)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f24,f29,f33,f37,f41,f45,f50,f56,f66,f72,f76])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    spl2_2 | ~spl2_11),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f73])).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    $false | (spl2_2 | ~spl2_11)),
% 0.21/0.48    inference(resolution,[],[f71,f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ~r1_xboole_0(sK0,k1_xboole_0) | spl2_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    spl2_2 <=> r1_xboole_0(sK0,k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    ( ! [X1] : (r1_xboole_0(X1,k1_xboole_0)) ) | ~spl2_11),
% 0.21/0.48    inference(avatar_component_clause,[],[f70])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    spl2_11 <=> ! [X1] : r1_xboole_0(X1,k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    spl2_11 | ~spl2_5 | ~spl2_10),
% 0.21/0.48    inference(avatar_split_clause,[],[f68,f64,f39,f70])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    spl2_5 <=> ! [X1,X0] : (r2_hidden(sK1(X0,X1),X1) | r1_xboole_0(X0,X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    spl2_10 <=> ! [X0] : ~r2_hidden(X0,k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    ( ! [X1] : (r1_xboole_0(X1,k1_xboole_0)) ) | (~spl2_5 | ~spl2_10)),
% 0.21/0.48    inference(resolution,[],[f65,f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | r1_xboole_0(X0,X1)) ) | ~spl2_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f39])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl2_10),
% 0.21/0.48    inference(avatar_component_clause,[],[f64])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    spl2_10 | ~spl2_6 | ~spl2_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f62,f54,f43,f64])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    spl2_6 <=> ! [X1,X0,X2] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    spl2_8 <=> ! [X0] : r1_xboole_0(k1_xboole_0,X0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | (~spl2_6 | ~spl2_8)),
% 0.21/0.48    inference(condensation,[],[f61])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X0,k1_xboole_0)) ) | (~spl2_6 | ~spl2_8)),
% 0.21/0.48    inference(resolution,[],[f44,f55])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) ) | ~spl2_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f54])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) ) | ~spl2_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f43])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    spl2_8 | ~spl2_1 | ~spl2_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f52,f48,f21,f54])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    spl2_1 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    spl2_7 <=> ! [X1,X0] : (r1_xboole_0(X0,X1) | ~v1_xboole_0(X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) ) | (~spl2_1 | ~spl2_7)),
% 0.21/0.48    inference(resolution,[],[f49,f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    v1_xboole_0(k1_xboole_0) | ~spl2_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f21])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_xboole_0(X0) | r1_xboole_0(X0,X1)) ) | ~spl2_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f48])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    spl2_7 | ~spl2_3 | ~spl2_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f46,f35,f31,f48])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    spl2_3 <=> ! [X1,X0] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    spl2_4 <=> ! [X1,X0] : (r2_hidden(sK1(X0,X1),X0) | r1_xboole_0(X0,X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~v1_xboole_0(X0)) ) | (~spl2_3 | ~spl2_4)),
% 0.21/0.48    inference(resolution,[],[f36,f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~v1_xboole_0(X1)) ) | ~spl2_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f31])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | r1_xboole_0(X0,X1)) ) | ~spl2_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f35])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    spl2_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f18,f43])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f8,f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,plain,(
% 0.21/0.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.48    inference(rectify,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    spl2_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f17,f39])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    spl2_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f16,f35])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    spl2_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f19,f31])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : ~(v1_xboole_0(X1) & r2_hidden(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ~spl2_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f14,f26])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ~r1_xboole_0(sK0,k1_xboole_0)),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ~r1_xboole_0(sK0,k1_xboole_0)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ? [X0] : ~r1_xboole_0(X0,k1_xboole_0) => ~r1_xboole_0(sK0,k1_xboole_0)),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f7,plain,(
% 0.21/0.48    ? [X0] : ~r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,negated_conjecture,(
% 0.21/0.48    ~! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.48    inference(negated_conjecture,[],[f4])).
% 0.21/0.48  fof(f4,conjecture,(
% 0.21/0.48    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    spl2_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f15,f21])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (10118)------------------------------
% 0.21/0.48  % (10118)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (10118)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (10118)Memory used [KB]: 5373
% 0.21/0.48  % (10118)Time elapsed: 0.068 s
% 0.21/0.48  % (10118)------------------------------
% 0.21/0.48  % (10118)------------------------------
% 0.21/0.49  % (10101)Success in time 0.131 s
%------------------------------------------------------------------------------
