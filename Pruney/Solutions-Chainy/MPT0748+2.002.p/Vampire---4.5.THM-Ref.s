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
% DateTime   : Thu Dec  3 12:55:39 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   58 (  93 expanded)
%              Number of leaves         :   16 (  43 expanded)
%              Depth                    :    6
%              Number of atoms          :  183 ( 309 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f98,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f25,f29,f33,f37,f46,f50,f64,f76,f86,f95,f97])).

fof(f97,plain,
    ( spl3_13
    | ~ spl3_2
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f89,f83,f27,f92])).

fof(f92,plain,
    ( spl3_13
  <=> v3_ordinal1(sK1(sK2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f27,plain,
    ( spl3_2
  <=> ! [X0,X2] :
        ( v3_ordinal1(X2)
        | ~ r2_hidden(X2,sK2(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f83,plain,
    ( spl3_12
  <=> r2_hidden(sK1(sK2(sK0)),sK2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f89,plain,
    ( v3_ordinal1(sK1(sK2(sK0)))
    | ~ spl3_2
    | ~ spl3_12 ),
    inference(resolution,[],[f85,f28])).

fof(f28,plain,
    ( ! [X2,X0] :
        ( ~ r2_hidden(X2,sK2(X0))
        | v3_ordinal1(X2) )
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f27])).

fof(f85,plain,
    ( r2_hidden(sK1(sK2(sK0)),sK2(sK0))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f83])).

fof(f95,plain,
    ( ~ spl3_13
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f87,f83,f35,f92])).

fof(f35,plain,
    ( spl3_4
  <=> ! [X0] :
        ( ~ v3_ordinal1(sK1(X0))
        | ~ r2_hidden(sK1(X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f87,plain,
    ( ~ v3_ordinal1(sK1(sK2(sK0)))
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(resolution,[],[f85,f36])).

fof(f36,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1(X0),X0)
        | ~ v3_ordinal1(sK1(X0)) )
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f35])).

fof(f86,plain,
    ( spl3_12
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f81,f74,f83])).

fof(f74,plain,
    ( spl3_11
  <=> ! [X0] :
        ( r2_hidden(sK1(X0),X0)
        | r2_hidden(sK1(X0),sK2(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f81,plain,
    ( r2_hidden(sK1(sK2(sK0)),sK2(sK0))
    | ~ spl3_11 ),
    inference(factoring,[],[f75])).

fof(f75,plain,
    ( ! [X0] :
        ( r2_hidden(sK1(X0),sK2(sK0))
        | r2_hidden(sK1(X0),X0) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f74])).

fof(f76,plain,
    ( spl3_11
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f72,f62,f31,f74])).

fof(f31,plain,
    ( spl3_3
  <=> ! [X0] :
        ( v3_ordinal1(sK1(X0))
        | r2_hidden(sK1(X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f62,plain,
    ( spl3_9
  <=> ! [X0] :
        ( r2_hidden(sK1(X0),X0)
        | ~ v3_ordinal1(sK1(X0))
        | r2_hidden(sK1(X0),sK2(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f72,plain,
    ( ! [X0] :
        ( r2_hidden(sK1(X0),X0)
        | r2_hidden(sK1(X0),sK2(sK0)) )
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(duplicate_literal_removal,[],[f71])).

fof(f71,plain,
    ( ! [X0] :
        ( r2_hidden(sK1(X0),X0)
        | r2_hidden(sK1(X0),sK2(sK0))
        | r2_hidden(sK1(X0),X0) )
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(resolution,[],[f63,f32])).

fof(f32,plain,
    ( ! [X0] :
        ( v3_ordinal1(sK1(X0))
        | r2_hidden(sK1(X0),X0) )
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f31])).

fof(f63,plain,
    ( ! [X0] :
        ( ~ v3_ordinal1(sK1(X0))
        | r2_hidden(sK1(X0),X0)
        | r2_hidden(sK1(X0),sK2(sK0)) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f62])).

fof(f64,plain,
    ( spl3_9
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f52,f48,f44,f62])).

fof(f44,plain,
    ( spl3_6
  <=> ! [X0,X2] :
        ( r2_hidden(X2,sK2(X0))
        | ~ v3_ordinal1(X2)
        | ~ r2_hidden(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f48,plain,
    ( spl3_7
  <=> ! [X0] :
        ( r2_hidden(sK1(X0),X0)
        | r2_hidden(sK1(X0),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f52,plain,
    ( ! [X0] :
        ( r2_hidden(sK1(X0),X0)
        | ~ v3_ordinal1(sK1(X0))
        | r2_hidden(sK1(X0),sK2(sK0)) )
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(resolution,[],[f49,f45])).

fof(f45,plain,
    ( ! [X2,X0] :
        ( ~ r2_hidden(X2,X0)
        | ~ v3_ordinal1(X2)
        | r2_hidden(X2,sK2(X0)) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f44])).

fof(f49,plain,
    ( ! [X0] :
        ( r2_hidden(sK1(X0),sK0)
        | r2_hidden(sK1(X0),X0) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f48])).

fof(f50,plain,
    ( spl3_7
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f42,f31,f23,f48])).

fof(f23,plain,
    ( spl3_1
  <=> ! [X1] :
        ( r2_hidden(X1,sK0)
        | ~ v3_ordinal1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f42,plain,
    ( ! [X0] :
        ( r2_hidden(sK1(X0),X0)
        | r2_hidden(sK1(X0),sK0) )
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(resolution,[],[f32,f24])).

fof(f24,plain,
    ( ! [X1] :
        ( ~ v3_ordinal1(X1)
        | r2_hidden(X1,sK0) )
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f23])).

fof(f46,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f21,f44])).

fof(f21,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,sK2(X0))
      | ~ v3_ordinal1(X2)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X2] :
      ( ( r2_hidden(X2,sK2(X0))
        | ~ v3_ordinal1(X2)
        | ~ r2_hidden(X2,X0) )
      & ( ( v3_ordinal1(X2)
          & r2_hidden(X2,X0) )
        | ~ r2_hidden(X2,sK2(X0)) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f13,f14])).

fof(f14,plain,(
    ! [X0] :
      ( ? [X1] :
        ! [X2] :
          ( ( r2_hidden(X2,X1)
            | ~ v3_ordinal1(X2)
            | ~ r2_hidden(X2,X0) )
          & ( ( v3_ordinal1(X2)
              & r2_hidden(X2,X0) )
            | ~ r2_hidden(X2,X1) ) )
     => ! [X2] :
          ( ( r2_hidden(X2,sK2(X0))
            | ~ v3_ordinal1(X2)
            | ~ r2_hidden(X2,X0) )
          & ( ( v3_ordinal1(X2)
              & r2_hidden(X2,X0) )
            | ~ r2_hidden(X2,sK2(X0)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0] :
    ? [X1] :
    ! [X2] :
      ( ( r2_hidden(X2,X1)
        | ~ v3_ordinal1(X2)
        | ~ r2_hidden(X2,X0) )
      & ( ( v3_ordinal1(X2)
          & r2_hidden(X2,X0) )
        | ~ r2_hidden(X2,X1) ) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
    ? [X1] :
    ! [X2] :
      ( ( r2_hidden(X2,X1)
        | ~ v3_ordinal1(X2)
        | ~ r2_hidden(X2,X0) )
      & ( ( v3_ordinal1(X2)
          & r2_hidden(X2,X0) )
        | ~ r2_hidden(X2,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
    ? [X1] :
    ! [X2] :
      ( r2_hidden(X2,X1)
    <=> ( v3_ordinal1(X2)
        & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s1_xboole_0__e3_53__ordinal1)).

fof(f37,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f18,f35])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(sK1(X0))
      | ~ r2_hidden(sK1(X0),X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( ~ v3_ordinal1(sK1(X0))
        | ~ r2_hidden(sK1(X0),X0) )
      & ( v3_ordinal1(sK1(X0))
        | r2_hidden(sK1(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f9,f10])).

fof(f10,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ v3_ordinal1(X1)
            | ~ r2_hidden(X1,X0) )
          & ( v3_ordinal1(X1)
            | r2_hidden(X1,X0) ) )
     => ( ( ~ v3_ordinal1(sK1(X0))
          | ~ r2_hidden(sK1(X0),X0) )
        & ( v3_ordinal1(sK1(X0))
          | r2_hidden(sK1(X0),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ! [X0] :
    ? [X1] :
      ( ( ~ v3_ordinal1(X1)
        | ~ r2_hidden(X1,X0) )
      & ( v3_ordinal1(X1)
        | r2_hidden(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0] :
    ? [X1] :
      ( r2_hidden(X1,X0)
    <~> v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ! [X1] :
          ( r2_hidden(X1,X0)
        <=> v3_ordinal1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_ordinal1)).

fof(f33,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f17,f31])).

fof(f17,plain,(
    ! [X0] :
      ( v3_ordinal1(sK1(X0))
      | r2_hidden(sK1(X0),X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f29,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f20,f27])).

fof(f20,plain,(
    ! [X2,X0] :
      ( v3_ordinal1(X2)
      | ~ r2_hidden(X2,sK2(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f25,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f16,f23])).

fof(f16,plain,(
    ! [X1] :
      ( r2_hidden(X1,sK0)
      | ~ v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X1] :
      ( r2_hidden(X1,sK0)
      | ~ v3_ordinal1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f5,f7])).

fof(f7,plain,
    ( ? [X0] :
      ! [X1] :
        ( r2_hidden(X1,X0)
        | ~ v3_ordinal1(X1) )
   => ! [X1] :
        ( r2_hidden(X1,sK0)
        | ~ v3_ordinal1(X1) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0] :
    ! [X1] :
      ( r2_hidden(X1,X0)
      | ~ v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ~ ! [X1] :
            ( v3_ordinal1(X1)
           => r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ~ ! [X1] :
          ( v3_ordinal1(X1)
         => r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_ordinal1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:39:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (1987)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.22/0.47  % (1979)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.22/0.47  % (1990)dis+1011_4_awrs=decay:awrsf=32:afp=40000:afq=1.0:amm=off:anc=all:bs=on:cond=on:fsr=off:gsp=input_only:lma=on:nm=16:nwc=1:nicw=on:sac=on:sp=frequency:thi=all:updr=off:uhcvi=on_670 on theBenchmark
% 0.22/0.48  % (1990)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % (1981)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f98,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f25,f29,f33,f37,f46,f50,f64,f76,f86,f95,f97])).
% 0.22/0.48  fof(f97,plain,(
% 0.22/0.48    spl3_13 | ~spl3_2 | ~spl3_12),
% 0.22/0.48    inference(avatar_split_clause,[],[f89,f83,f27,f92])).
% 0.22/0.48  fof(f92,plain,(
% 0.22/0.48    spl3_13 <=> v3_ordinal1(sK1(sK2(sK0)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    spl3_2 <=> ! [X0,X2] : (v3_ordinal1(X2) | ~r2_hidden(X2,sK2(X0)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.48  fof(f83,plain,(
% 0.22/0.48    spl3_12 <=> r2_hidden(sK1(sK2(sK0)),sK2(sK0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.48  fof(f89,plain,(
% 0.22/0.48    v3_ordinal1(sK1(sK2(sK0))) | (~spl3_2 | ~spl3_12)),
% 0.22/0.48    inference(resolution,[],[f85,f28])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ( ! [X2,X0] : (~r2_hidden(X2,sK2(X0)) | v3_ordinal1(X2)) ) | ~spl3_2),
% 0.22/0.48    inference(avatar_component_clause,[],[f27])).
% 0.22/0.48  fof(f85,plain,(
% 0.22/0.48    r2_hidden(sK1(sK2(sK0)),sK2(sK0)) | ~spl3_12),
% 0.22/0.48    inference(avatar_component_clause,[],[f83])).
% 0.22/0.48  fof(f95,plain,(
% 0.22/0.48    ~spl3_13 | ~spl3_4 | ~spl3_12),
% 0.22/0.48    inference(avatar_split_clause,[],[f87,f83,f35,f92])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    spl3_4 <=> ! [X0] : (~v3_ordinal1(sK1(X0)) | ~r2_hidden(sK1(X0),X0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.48  fof(f87,plain,(
% 0.22/0.48    ~v3_ordinal1(sK1(sK2(sK0))) | (~spl3_4 | ~spl3_12)),
% 0.22/0.48    inference(resolution,[],[f85,f36])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    ( ! [X0] : (~r2_hidden(sK1(X0),X0) | ~v3_ordinal1(sK1(X0))) ) | ~spl3_4),
% 0.22/0.48    inference(avatar_component_clause,[],[f35])).
% 0.22/0.48  fof(f86,plain,(
% 0.22/0.48    spl3_12 | ~spl3_11),
% 0.22/0.48    inference(avatar_split_clause,[],[f81,f74,f83])).
% 0.22/0.48  fof(f74,plain,(
% 0.22/0.48    spl3_11 <=> ! [X0] : (r2_hidden(sK1(X0),X0) | r2_hidden(sK1(X0),sK2(sK0)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.48  fof(f81,plain,(
% 0.22/0.48    r2_hidden(sK1(sK2(sK0)),sK2(sK0)) | ~spl3_11),
% 0.22/0.48    inference(factoring,[],[f75])).
% 0.22/0.48  fof(f75,plain,(
% 0.22/0.48    ( ! [X0] : (r2_hidden(sK1(X0),sK2(sK0)) | r2_hidden(sK1(X0),X0)) ) | ~spl3_11),
% 0.22/0.48    inference(avatar_component_clause,[],[f74])).
% 0.22/0.48  fof(f76,plain,(
% 0.22/0.48    spl3_11 | ~spl3_3 | ~spl3_9),
% 0.22/0.48    inference(avatar_split_clause,[],[f72,f62,f31,f74])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    spl3_3 <=> ! [X0] : (v3_ordinal1(sK1(X0)) | r2_hidden(sK1(X0),X0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.48  fof(f62,plain,(
% 0.22/0.48    spl3_9 <=> ! [X0] : (r2_hidden(sK1(X0),X0) | ~v3_ordinal1(sK1(X0)) | r2_hidden(sK1(X0),sK2(sK0)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.48  fof(f72,plain,(
% 0.22/0.48    ( ! [X0] : (r2_hidden(sK1(X0),X0) | r2_hidden(sK1(X0),sK2(sK0))) ) | (~spl3_3 | ~spl3_9)),
% 0.22/0.48    inference(duplicate_literal_removal,[],[f71])).
% 0.22/0.48  fof(f71,plain,(
% 0.22/0.48    ( ! [X0] : (r2_hidden(sK1(X0),X0) | r2_hidden(sK1(X0),sK2(sK0)) | r2_hidden(sK1(X0),X0)) ) | (~spl3_3 | ~spl3_9)),
% 0.22/0.48    inference(resolution,[],[f63,f32])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ( ! [X0] : (v3_ordinal1(sK1(X0)) | r2_hidden(sK1(X0),X0)) ) | ~spl3_3),
% 0.22/0.48    inference(avatar_component_clause,[],[f31])).
% 0.22/0.48  fof(f63,plain,(
% 0.22/0.48    ( ! [X0] : (~v3_ordinal1(sK1(X0)) | r2_hidden(sK1(X0),X0) | r2_hidden(sK1(X0),sK2(sK0))) ) | ~spl3_9),
% 0.22/0.48    inference(avatar_component_clause,[],[f62])).
% 0.22/0.48  fof(f64,plain,(
% 0.22/0.48    spl3_9 | ~spl3_6 | ~spl3_7),
% 0.22/0.48    inference(avatar_split_clause,[],[f52,f48,f44,f62])).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    spl3_6 <=> ! [X0,X2] : (r2_hidden(X2,sK2(X0)) | ~v3_ordinal1(X2) | ~r2_hidden(X2,X0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.48  fof(f48,plain,(
% 0.22/0.48    spl3_7 <=> ! [X0] : (r2_hidden(sK1(X0),X0) | r2_hidden(sK1(X0),sK0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.48  fof(f52,plain,(
% 0.22/0.48    ( ! [X0] : (r2_hidden(sK1(X0),X0) | ~v3_ordinal1(sK1(X0)) | r2_hidden(sK1(X0),sK2(sK0))) ) | (~spl3_6 | ~spl3_7)),
% 0.22/0.48    inference(resolution,[],[f49,f45])).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v3_ordinal1(X2) | r2_hidden(X2,sK2(X0))) ) | ~spl3_6),
% 0.22/0.48    inference(avatar_component_clause,[],[f44])).
% 0.22/0.48  fof(f49,plain,(
% 0.22/0.48    ( ! [X0] : (r2_hidden(sK1(X0),sK0) | r2_hidden(sK1(X0),X0)) ) | ~spl3_7),
% 0.22/0.48    inference(avatar_component_clause,[],[f48])).
% 0.22/0.48  fof(f50,plain,(
% 0.22/0.48    spl3_7 | ~spl3_1 | ~spl3_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f42,f31,f23,f48])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    spl3_1 <=> ! [X1] : (r2_hidden(X1,sK0) | ~v3_ordinal1(X1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    ( ! [X0] : (r2_hidden(sK1(X0),X0) | r2_hidden(sK1(X0),sK0)) ) | (~spl3_1 | ~spl3_3)),
% 0.22/0.48    inference(resolution,[],[f32,f24])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ( ! [X1] : (~v3_ordinal1(X1) | r2_hidden(X1,sK0)) ) | ~spl3_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f23])).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    spl3_6),
% 0.22/0.48    inference(avatar_split_clause,[],[f21,f44])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ( ! [X2,X0] : (r2_hidden(X2,sK2(X0)) | ~v3_ordinal1(X2) | ~r2_hidden(X2,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ! [X0] : ! [X2] : ((r2_hidden(X2,sK2(X0)) | ~v3_ordinal1(X2) | ~r2_hidden(X2,X0)) & ((v3_ordinal1(X2) & r2_hidden(X2,X0)) | ~r2_hidden(X2,sK2(X0))))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f13,f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ! [X0] : (? [X1] : ! [X2] : ((r2_hidden(X2,X1) | ~v3_ordinal1(X2) | ~r2_hidden(X2,X0)) & ((v3_ordinal1(X2) & r2_hidden(X2,X0)) | ~r2_hidden(X2,X1))) => ! [X2] : ((r2_hidden(X2,sK2(X0)) | ~v3_ordinal1(X2) | ~r2_hidden(X2,X0)) & ((v3_ordinal1(X2) & r2_hidden(X2,X0)) | ~r2_hidden(X2,sK2(X0)))))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ! [X0] : ? [X1] : ! [X2] : ((r2_hidden(X2,X1) | ~v3_ordinal1(X2) | ~r2_hidden(X2,X0)) & ((v3_ordinal1(X2) & r2_hidden(X2,X0)) | ~r2_hidden(X2,X1)))),
% 0.22/0.48    inference(flattening,[],[f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ! [X0] : ? [X1] : ! [X2] : ((r2_hidden(X2,X1) | (~v3_ordinal1(X2) | ~r2_hidden(X2,X0))) & ((v3_ordinal1(X2) & r2_hidden(X2,X0)) | ~r2_hidden(X2,X1)))),
% 0.22/0.48    inference(nnf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0] : ? [X1] : ! [X2] : (r2_hidden(X2,X1) <=> (v3_ordinal1(X2) & r2_hidden(X2,X0)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s1_xboole_0__e3_53__ordinal1)).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    spl3_4),
% 0.22/0.48    inference(avatar_split_clause,[],[f18,f35])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ( ! [X0] : (~v3_ordinal1(sK1(X0)) | ~r2_hidden(sK1(X0),X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f11])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ! [X0] : ((~v3_ordinal1(sK1(X0)) | ~r2_hidden(sK1(X0),X0)) & (v3_ordinal1(sK1(X0)) | r2_hidden(sK1(X0),X0)))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f9,f10])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    ! [X0] : (? [X1] : ((~v3_ordinal1(X1) | ~r2_hidden(X1,X0)) & (v3_ordinal1(X1) | r2_hidden(X1,X0))) => ((~v3_ordinal1(sK1(X0)) | ~r2_hidden(sK1(X0),X0)) & (v3_ordinal1(sK1(X0)) | r2_hidden(sK1(X0),X0))))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f9,plain,(
% 0.22/0.48    ! [X0] : ? [X1] : ((~v3_ordinal1(X1) | ~r2_hidden(X1,X0)) & (v3_ordinal1(X1) | r2_hidden(X1,X0)))),
% 0.22/0.48    inference(nnf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,plain,(
% 0.22/0.48    ! [X0] : ? [X1] : (r2_hidden(X1,X0) <~> v3_ordinal1(X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0] : ~! [X1] : (r2_hidden(X1,X0) <=> v3_ordinal1(X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_ordinal1)).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    spl3_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f17,f31])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ( ! [X0] : (v3_ordinal1(sK1(X0)) | r2_hidden(sK1(X0),X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f11])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    spl3_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f20,f27])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ( ! [X2,X0] : (v3_ordinal1(X2) | ~r2_hidden(X2,sK2(X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f15])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    spl3_1),
% 0.22/0.48    inference(avatar_split_clause,[],[f16,f23])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ( ! [X1] : (r2_hidden(X1,sK0) | ~v3_ordinal1(X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,plain,(
% 0.22/0.48    ! [X1] : (r2_hidden(X1,sK0) | ~v3_ordinal1(X1))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f5,f7])).
% 0.22/0.48  fof(f7,plain,(
% 0.22/0.48    ? [X0] : ! [X1] : (r2_hidden(X1,X0) | ~v3_ordinal1(X1)) => ! [X1] : (r2_hidden(X1,sK0) | ~v3_ordinal1(X1))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f5,plain,(
% 0.22/0.48    ? [X0] : ! [X1] : (r2_hidden(X1,X0) | ~v3_ordinal1(X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,negated_conjecture,(
% 0.22/0.48    ~! [X0] : ~! [X1] : (v3_ordinal1(X1) => r2_hidden(X1,X0))),
% 0.22/0.48    inference(negated_conjecture,[],[f3])).
% 0.22/0.48  fof(f3,conjecture,(
% 0.22/0.48    ! [X0] : ~! [X1] : (v3_ordinal1(X1) => r2_hidden(X1,X0))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_ordinal1)).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (1990)------------------------------
% 0.22/0.48  % (1990)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (1990)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (1990)Memory used [KB]: 5373
% 0.22/0.48  % (1990)Time elapsed: 0.008 s
% 0.22/0.48  % (1990)------------------------------
% 0.22/0.48  % (1990)------------------------------
% 0.22/0.48  % (1972)Success in time 0.122 s
%------------------------------------------------------------------------------
