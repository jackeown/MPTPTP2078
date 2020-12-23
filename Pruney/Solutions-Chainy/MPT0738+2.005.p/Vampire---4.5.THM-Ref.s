%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:18 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 144 expanded)
%              Number of leaves         :   20 (  65 expanded)
%              Depth                    :    7
%              Number of atoms          :  269 ( 478 expanded)
%              Number of equality atoms :   11 (  18 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f166,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f33,f38,f43,f48,f52,f56,f64,f68,f82,f109,f138,f142,f158,f159])).

fof(f159,plain,
    ( spl2_19
    | ~ spl2_10
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f146,f124,f76,f155])).

fof(f155,plain,
    ( spl2_19
  <=> r1_ordinal1(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f76,plain,
    ( spl2_10
  <=> r1_ordinal1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f124,plain,
    ( spl2_15
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f146,plain,
    ( r1_ordinal1(sK0,sK0)
    | ~ spl2_10
    | ~ spl2_15 ),
    inference(backward_demodulation,[],[f78,f126])).

fof(f126,plain,
    ( sK0 = sK1
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f124])).

fof(f78,plain,
    ( r1_ordinal1(sK1,sK0)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f76])).

fof(f158,plain,
    ( ~ spl2_19
    | spl2_2
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f144,f124,f35,f155])).

fof(f35,plain,
    ( spl2_2
  <=> r1_ordinal1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f144,plain,
    ( ~ r1_ordinal1(sK0,sK0)
    | spl2_2
    | ~ spl2_15 ),
    inference(backward_demodulation,[],[f37,f126])).

fof(f37,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f35])).

fof(f142,plain,
    ( ~ spl2_9
    | ~ spl2_14
    | ~ spl2_16 ),
    inference(avatar_contradiction_clause,[],[f141])).

fof(f141,plain,
    ( $false
    | ~ spl2_9
    | ~ spl2_14
    | ~ spl2_16 ),
    inference(subsumption_resolution,[],[f140,f108])).

fof(f108,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f106])).

% (11056)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
fof(f106,plain,
    ( spl2_14
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f140,plain,
    ( ~ r1_tarski(sK1,sK0)
    | ~ spl2_9
    | ~ spl2_16 ),
    inference(resolution,[],[f130,f67])).

fof(f67,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ r1_tarski(X1,X0) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl2_9
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X1,X0)
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f130,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl2_16
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f138,plain,
    ( spl2_15
    | spl2_16
    | spl2_1
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f137,f50,f45,f40,f30,f128,f124])).

fof(f30,plain,
    ( spl2_1
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f40,plain,
    ( spl2_3
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f45,plain,
    ( spl2_4
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

% (11060)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
fof(f50,plain,
    ( spl2_5
  <=> ! [X1,X0] :
        ( r2_hidden(X1,X0)
        | X0 = X1
        | r2_hidden(X0,X1)
        | ~ v3_ordinal1(X1)
        | ~ v3_ordinal1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f137,plain,
    ( r2_hidden(sK0,sK1)
    | sK0 = sK1
    | spl2_1
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f136,f42])).

fof(f42,plain,
    ( v3_ordinal1(sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f40])).

fof(f136,plain,
    ( r2_hidden(sK0,sK1)
    | sK0 = sK1
    | ~ v3_ordinal1(sK1)
    | spl2_1
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f117,f47])).

fof(f47,plain,
    ( v3_ordinal1(sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f45])).

fof(f117,plain,
    ( r2_hidden(sK0,sK1)
    | sK0 = sK1
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK1)
    | spl2_1
    | ~ spl2_5 ),
    inference(resolution,[],[f51,f32])).

fof(f32,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f30])).

fof(f51,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X1,X0)
        | r2_hidden(X0,X1)
        | X0 = X1
        | ~ v3_ordinal1(X1)
        | ~ v3_ordinal1(X0) )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f50])).

fof(f109,plain,
    ( spl2_14
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_8
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f104,f76,f62,f45,f40,f106])).

fof(f62,plain,
    ( spl2_8
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ r1_ordinal1(X0,X1)
        | ~ v3_ordinal1(X1)
        | ~ v3_ordinal1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f104,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_8
    | ~ spl2_10 ),
    inference(subsumption_resolution,[],[f103,f42])).

fof(f103,plain,
    ( r1_tarski(sK1,sK0)
    | ~ v3_ordinal1(sK1)
    | ~ spl2_4
    | ~ spl2_8
    | ~ spl2_10 ),
    inference(subsumption_resolution,[],[f90,f47])).

fof(f90,plain,
    ( r1_tarski(sK1,sK0)
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK1)
    | ~ spl2_8
    | ~ spl2_10 ),
    inference(resolution,[],[f63,f78])).

fof(f63,plain,
    ( ! [X0,X1] :
        ( ~ r1_ordinal1(X0,X1)
        | r1_tarski(X0,X1)
        | ~ v3_ordinal1(X1)
        | ~ v3_ordinal1(X0) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f62])).

fof(f82,plain,
    ( spl2_10
    | spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f81,f54,f45,f40,f35,f76])).

fof(f54,plain,
    ( spl2_6
  <=> ! [X1,X0] :
        ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1)
        | ~ v3_ordinal1(X1)
        | ~ v3_ordinal1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f81,plain,
    ( r1_ordinal1(sK1,sK0)
    | spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f80,f47])).

fof(f80,plain,
    ( r1_ordinal1(sK1,sK0)
    | ~ v3_ordinal1(sK0)
    | spl2_2
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f70,f42])).

fof(f70,plain,
    ( r1_ordinal1(sK1,sK0)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | spl2_2
    | ~ spl2_6 ),
    inference(resolution,[],[f55,f37])).

fof(f55,plain,
    ( ! [X0,X1] :
        ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1)
        | ~ v3_ordinal1(X1)
        | ~ v3_ordinal1(X0) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f54])).

fof(f68,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f28,f66])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f64,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f26,f62])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f56,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f25,f54])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

fof(f52,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f24,f50])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

fof(f48,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f20,f45])).

fof(f20,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ~ r2_hidden(sK1,sK0)
    & ~ r1_ordinal1(sK0,sK1)
    & v3_ordinal1(sK1)
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f17,f16])).

fof(f16,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r2_hidden(X1,X0)
            & ~ r1_ordinal1(X0,X1)
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ~ r2_hidden(X1,sK0)
          & ~ r1_ordinal1(sK0,X1)
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X1] :
        ( ~ r2_hidden(X1,sK0)
        & ~ r1_ordinal1(sK0,X1)
        & v3_ordinal1(X1) )
   => ( ~ r2_hidden(sK1,sK0)
      & ~ r1_ordinal1(sK0,sK1)
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(X1,X0)
          & ~ r1_ordinal1(X0,X1)
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(X1,X0)
          & ~ r1_ordinal1(X0,X1)
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X1,X0)
              | r1_ordinal1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f43,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f21,f40])).

fof(f21,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f38,plain,(
    ~ spl2_2 ),
    inference(avatar_split_clause,[],[f22,f35])).

fof(f22,plain,(
    ~ r1_ordinal1(sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f33,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f23,f30])).

fof(f23,plain,(
    ~ r2_hidden(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n022.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 11:50:26 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.45  % (11057)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.45  % (11061)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.22/0.45  % (11061)Refutation found. Thanks to Tanya!
% 0.22/0.45  % SZS status Theorem for theBenchmark
% 0.22/0.45  % SZS output start Proof for theBenchmark
% 0.22/0.45  fof(f166,plain,(
% 0.22/0.45    $false),
% 0.22/0.45    inference(avatar_sat_refutation,[],[f33,f38,f43,f48,f52,f56,f64,f68,f82,f109,f138,f142,f158,f159])).
% 0.22/0.45  fof(f159,plain,(
% 0.22/0.45    spl2_19 | ~spl2_10 | ~spl2_15),
% 0.22/0.45    inference(avatar_split_clause,[],[f146,f124,f76,f155])).
% 0.22/0.45  fof(f155,plain,(
% 0.22/0.45    spl2_19 <=> r1_ordinal1(sK0,sK0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.22/0.45  fof(f76,plain,(
% 0.22/0.45    spl2_10 <=> r1_ordinal1(sK1,sK0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.22/0.45  fof(f124,plain,(
% 0.22/0.45    spl2_15 <=> sK0 = sK1),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.22/0.45  fof(f146,plain,(
% 0.22/0.45    r1_ordinal1(sK0,sK0) | (~spl2_10 | ~spl2_15)),
% 0.22/0.45    inference(backward_demodulation,[],[f78,f126])).
% 0.22/0.45  fof(f126,plain,(
% 0.22/0.45    sK0 = sK1 | ~spl2_15),
% 0.22/0.45    inference(avatar_component_clause,[],[f124])).
% 0.22/0.45  fof(f78,plain,(
% 0.22/0.45    r1_ordinal1(sK1,sK0) | ~spl2_10),
% 0.22/0.45    inference(avatar_component_clause,[],[f76])).
% 0.22/0.45  fof(f158,plain,(
% 0.22/0.45    ~spl2_19 | spl2_2 | ~spl2_15),
% 0.22/0.45    inference(avatar_split_clause,[],[f144,f124,f35,f155])).
% 0.22/0.45  fof(f35,plain,(
% 0.22/0.45    spl2_2 <=> r1_ordinal1(sK0,sK1)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.45  fof(f144,plain,(
% 0.22/0.45    ~r1_ordinal1(sK0,sK0) | (spl2_2 | ~spl2_15)),
% 0.22/0.45    inference(backward_demodulation,[],[f37,f126])).
% 0.22/0.45  fof(f37,plain,(
% 0.22/0.45    ~r1_ordinal1(sK0,sK1) | spl2_2),
% 0.22/0.45    inference(avatar_component_clause,[],[f35])).
% 0.22/0.45  fof(f142,plain,(
% 0.22/0.45    ~spl2_9 | ~spl2_14 | ~spl2_16),
% 0.22/0.45    inference(avatar_contradiction_clause,[],[f141])).
% 0.22/0.45  fof(f141,plain,(
% 0.22/0.45    $false | (~spl2_9 | ~spl2_14 | ~spl2_16)),
% 0.22/0.45    inference(subsumption_resolution,[],[f140,f108])).
% 0.22/0.45  fof(f108,plain,(
% 0.22/0.45    r1_tarski(sK1,sK0) | ~spl2_14),
% 0.22/0.45    inference(avatar_component_clause,[],[f106])).
% 0.22/0.45  % (11056)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.45  fof(f106,plain,(
% 0.22/0.45    spl2_14 <=> r1_tarski(sK1,sK0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.22/0.45  fof(f140,plain,(
% 0.22/0.45    ~r1_tarski(sK1,sK0) | (~spl2_9 | ~spl2_16)),
% 0.22/0.45    inference(resolution,[],[f130,f67])).
% 0.22/0.45  fof(f67,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) ) | ~spl2_9),
% 0.22/0.45    inference(avatar_component_clause,[],[f66])).
% 0.22/0.45  fof(f66,plain,(
% 0.22/0.45    spl2_9 <=> ! [X1,X0] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.22/0.45  fof(f130,plain,(
% 0.22/0.45    r2_hidden(sK0,sK1) | ~spl2_16),
% 0.22/0.45    inference(avatar_component_clause,[],[f128])).
% 0.22/0.45  fof(f128,plain,(
% 0.22/0.45    spl2_16 <=> r2_hidden(sK0,sK1)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.22/0.45  fof(f138,plain,(
% 0.22/0.45    spl2_15 | spl2_16 | spl2_1 | ~spl2_3 | ~spl2_4 | ~spl2_5),
% 0.22/0.45    inference(avatar_split_clause,[],[f137,f50,f45,f40,f30,f128,f124])).
% 0.22/0.45  fof(f30,plain,(
% 0.22/0.45    spl2_1 <=> r2_hidden(sK1,sK0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.45  fof(f40,plain,(
% 0.22/0.45    spl2_3 <=> v3_ordinal1(sK1)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.45  fof(f45,plain,(
% 0.22/0.45    spl2_4 <=> v3_ordinal1(sK0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.45  % (11060)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.22/0.45  fof(f50,plain,(
% 0.22/0.45    spl2_5 <=> ! [X1,X0] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.45  fof(f137,plain,(
% 0.22/0.45    r2_hidden(sK0,sK1) | sK0 = sK1 | (spl2_1 | ~spl2_3 | ~spl2_4 | ~spl2_5)),
% 0.22/0.45    inference(subsumption_resolution,[],[f136,f42])).
% 0.22/0.45  fof(f42,plain,(
% 0.22/0.45    v3_ordinal1(sK1) | ~spl2_3),
% 0.22/0.45    inference(avatar_component_clause,[],[f40])).
% 0.22/0.45  fof(f136,plain,(
% 0.22/0.45    r2_hidden(sK0,sK1) | sK0 = sK1 | ~v3_ordinal1(sK1) | (spl2_1 | ~spl2_4 | ~spl2_5)),
% 0.22/0.45    inference(subsumption_resolution,[],[f117,f47])).
% 0.22/0.45  fof(f47,plain,(
% 0.22/0.45    v3_ordinal1(sK0) | ~spl2_4),
% 0.22/0.45    inference(avatar_component_clause,[],[f45])).
% 0.22/0.45  fof(f117,plain,(
% 0.22/0.45    r2_hidden(sK0,sK1) | sK0 = sK1 | ~v3_ordinal1(sK0) | ~v3_ordinal1(sK1) | (spl2_1 | ~spl2_5)),
% 0.22/0.45    inference(resolution,[],[f51,f32])).
% 0.22/0.45  fof(f32,plain,(
% 0.22/0.45    ~r2_hidden(sK1,sK0) | spl2_1),
% 0.22/0.45    inference(avatar_component_clause,[],[f30])).
% 0.22/0.45  fof(f51,plain,(
% 0.22/0.45    ( ! [X0,X1] : (r2_hidden(X1,X0) | r2_hidden(X0,X1) | X0 = X1 | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) ) | ~spl2_5),
% 0.22/0.45    inference(avatar_component_clause,[],[f50])).
% 0.22/0.45  fof(f109,plain,(
% 0.22/0.45    spl2_14 | ~spl2_3 | ~spl2_4 | ~spl2_8 | ~spl2_10),
% 0.22/0.45    inference(avatar_split_clause,[],[f104,f76,f62,f45,f40,f106])).
% 0.22/0.45  fof(f62,plain,(
% 0.22/0.45    spl2_8 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.22/0.45  fof(f104,plain,(
% 0.22/0.45    r1_tarski(sK1,sK0) | (~spl2_3 | ~spl2_4 | ~spl2_8 | ~spl2_10)),
% 0.22/0.45    inference(subsumption_resolution,[],[f103,f42])).
% 0.22/0.45  fof(f103,plain,(
% 0.22/0.45    r1_tarski(sK1,sK0) | ~v3_ordinal1(sK1) | (~spl2_4 | ~spl2_8 | ~spl2_10)),
% 0.22/0.45    inference(subsumption_resolution,[],[f90,f47])).
% 0.22/0.45  fof(f90,plain,(
% 0.22/0.45    r1_tarski(sK1,sK0) | ~v3_ordinal1(sK0) | ~v3_ordinal1(sK1) | (~spl2_8 | ~spl2_10)),
% 0.22/0.45    inference(resolution,[],[f63,f78])).
% 0.22/0.45  fof(f63,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~r1_ordinal1(X0,X1) | r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) ) | ~spl2_8),
% 0.22/0.45    inference(avatar_component_clause,[],[f62])).
% 0.22/0.45  fof(f82,plain,(
% 0.22/0.45    spl2_10 | spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_6),
% 0.22/0.45    inference(avatar_split_clause,[],[f81,f54,f45,f40,f35,f76])).
% 0.22/0.45  fof(f54,plain,(
% 0.22/0.45    spl2_6 <=> ! [X1,X0] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.45  fof(f81,plain,(
% 0.22/0.45    r1_ordinal1(sK1,sK0) | (spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_6)),
% 0.22/0.45    inference(subsumption_resolution,[],[f80,f47])).
% 0.22/0.45  fof(f80,plain,(
% 0.22/0.45    r1_ordinal1(sK1,sK0) | ~v3_ordinal1(sK0) | (spl2_2 | ~spl2_3 | ~spl2_6)),
% 0.22/0.45    inference(subsumption_resolution,[],[f70,f42])).
% 0.22/0.45  fof(f70,plain,(
% 0.22/0.45    r1_ordinal1(sK1,sK0) | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | (spl2_2 | ~spl2_6)),
% 0.22/0.45    inference(resolution,[],[f55,f37])).
% 0.22/0.45  fof(f55,plain,(
% 0.22/0.45    ( ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) ) | ~spl2_6),
% 0.22/0.45    inference(avatar_component_clause,[],[f54])).
% 0.22/0.45  fof(f68,plain,(
% 0.22/0.45    spl2_9),
% 0.22/0.45    inference(avatar_split_clause,[],[f28,f66])).
% 0.22/0.45  fof(f28,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f15])).
% 0.22/0.45  fof(f15,plain,(
% 0.22/0.45    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.45    inference(ennf_transformation,[],[f4])).
% 0.22/0.45  fof(f4,axiom,(
% 0.22/0.45    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.22/0.45  fof(f64,plain,(
% 0.22/0.45    spl2_8),
% 0.22/0.45    inference(avatar_split_clause,[],[f26,f62])).
% 0.22/0.45  fof(f26,plain,(
% 0.22/0.45    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f19])).
% 0.22/0.45  fof(f19,plain,(
% 0.22/0.45    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.22/0.45    inference(nnf_transformation,[],[f14])).
% 0.22/0.45  fof(f14,plain,(
% 0.22/0.45    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.22/0.45    inference(flattening,[],[f13])).
% 0.22/0.45  fof(f13,plain,(
% 0.22/0.45    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.22/0.45    inference(ennf_transformation,[],[f2])).
% 0.22/0.45  fof(f2,axiom,(
% 0.22/0.45    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.22/0.45  fof(f56,plain,(
% 0.22/0.45    spl2_6),
% 0.22/0.45    inference(avatar_split_clause,[],[f25,f54])).
% 0.22/0.45  fof(f25,plain,(
% 0.22/0.45    ( ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f12])).
% 0.22/0.45  fof(f12,plain,(
% 0.22/0.45    ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.22/0.45    inference(flattening,[],[f11])).
% 0.22/0.45  fof(f11,plain,(
% 0.22/0.45    ! [X0,X1] : ((r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.22/0.45    inference(ennf_transformation,[],[f1])).
% 0.22/0.45  fof(f1,axiom,(
% 0.22/0.45    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).
% 0.22/0.45  fof(f52,plain,(
% 0.22/0.45    spl2_5),
% 0.22/0.45    inference(avatar_split_clause,[],[f24,f50])).
% 0.22/0.45  fof(f24,plain,(
% 0.22/0.45    ( ! [X0,X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f10])).
% 0.22/0.45  fof(f10,plain,(
% 0.22/0.45    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.45    inference(flattening,[],[f9])).
% 0.22/0.45  fof(f9,plain,(
% 0.22/0.45    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.45    inference(ennf_transformation,[],[f3])).
% 0.22/0.45  fof(f3,axiom,(
% 0.22/0.45    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).
% 0.22/0.45  fof(f48,plain,(
% 0.22/0.45    spl2_4),
% 0.22/0.45    inference(avatar_split_clause,[],[f20,f45])).
% 0.22/0.45  fof(f20,plain,(
% 0.22/0.45    v3_ordinal1(sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f18])).
% 0.22/0.45  fof(f18,plain,(
% 0.22/0.45    (~r2_hidden(sK1,sK0) & ~r1_ordinal1(sK0,sK1) & v3_ordinal1(sK1)) & v3_ordinal1(sK0)),
% 0.22/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f17,f16])).
% 0.22/0.45  fof(f16,plain,(
% 0.22/0.45    ? [X0] : (? [X1] : (~r2_hidden(X1,X0) & ~r1_ordinal1(X0,X1) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : (~r2_hidden(X1,sK0) & ~r1_ordinal1(sK0,X1) & v3_ordinal1(X1)) & v3_ordinal1(sK0))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f17,plain,(
% 0.22/0.45    ? [X1] : (~r2_hidden(X1,sK0) & ~r1_ordinal1(sK0,X1) & v3_ordinal1(X1)) => (~r2_hidden(sK1,sK0) & ~r1_ordinal1(sK0,sK1) & v3_ordinal1(sK1))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f8,plain,(
% 0.22/0.45    ? [X0] : (? [X1] : (~r2_hidden(X1,X0) & ~r1_ordinal1(X0,X1) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.22/0.45    inference(flattening,[],[f7])).
% 0.22/0.45  fof(f7,plain,(
% 0.22/0.45    ? [X0] : (? [X1] : ((~r2_hidden(X1,X0) & ~r1_ordinal1(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.22/0.45    inference(ennf_transformation,[],[f6])).
% 0.22/0.45  fof(f6,negated_conjecture,(
% 0.22/0.45    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 0.22/0.45    inference(negated_conjecture,[],[f5])).
% 0.22/0.45  fof(f5,conjecture,(
% 0.22/0.45    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).
% 0.22/0.45  fof(f43,plain,(
% 0.22/0.45    spl2_3),
% 0.22/0.45    inference(avatar_split_clause,[],[f21,f40])).
% 0.22/0.45  fof(f21,plain,(
% 0.22/0.45    v3_ordinal1(sK1)),
% 0.22/0.45    inference(cnf_transformation,[],[f18])).
% 0.22/0.45  fof(f38,plain,(
% 0.22/0.45    ~spl2_2),
% 0.22/0.45    inference(avatar_split_clause,[],[f22,f35])).
% 0.22/0.45  fof(f22,plain,(
% 0.22/0.45    ~r1_ordinal1(sK0,sK1)),
% 0.22/0.45    inference(cnf_transformation,[],[f18])).
% 0.22/0.45  fof(f33,plain,(
% 0.22/0.45    ~spl2_1),
% 0.22/0.45    inference(avatar_split_clause,[],[f23,f30])).
% 0.22/0.45  fof(f23,plain,(
% 0.22/0.45    ~r2_hidden(sK1,sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f18])).
% 0.22/0.45  % SZS output end Proof for theBenchmark
% 0.22/0.45  % (11061)------------------------------
% 0.22/0.45  % (11061)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.45  % (11061)Termination reason: Refutation
% 0.22/0.45  
% 0.22/0.45  % (11061)Memory used [KB]: 6140
% 0.22/0.45  % (11061)Time elapsed: 0.004 s
% 0.22/0.45  % (11061)------------------------------
% 0.22/0.45  % (11061)------------------------------
% 0.22/0.45  % (11050)Success in time 0.078 s
%------------------------------------------------------------------------------
