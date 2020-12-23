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
% DateTime   : Thu Dec  3 12:48:42 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   59 (  79 expanded)
%              Number of leaves         :   17 (  34 expanded)
%              Depth                    :    6
%              Number of atoms          :  166 ( 221 expanded)
%              Number of equality atoms :   23 (  35 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f110,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f39,f44,f52,f60,f68,f78,f92,f106,f109])).

fof(f109,plain,
    ( spl3_1
    | ~ spl3_3
    | ~ spl3_16 ),
    inference(avatar_contradiction_clause,[],[f108])).

fof(f108,plain,
    ( $false
    | spl3_1
    | ~ spl3_3
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f107,f33])).

fof(f33,plain,
    ( k1_xboole_0 != k7_relat_1(sK0,k1_xboole_0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl3_1
  <=> k1_xboole_0 = k7_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f107,plain,
    ( k1_xboole_0 = k7_relat_1(sK0,k1_xboole_0)
    | ~ spl3_3
    | ~ spl3_16 ),
    inference(resolution,[],[f105,f43])).

fof(f43,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl3_3
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f105,plain,
    ( ! [X1] :
        ( ~ v1_xboole_0(X1)
        | k1_xboole_0 = k7_relat_1(sK0,X1) )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl3_16
  <=> ! [X1] :
        ( k1_xboole_0 = k7_relat_1(sK0,X1)
        | ~ v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f106,plain,
    ( spl3_16
    | ~ spl3_11
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f94,f90,f76,f104])).

fof(f76,plain,
    ( spl3_11
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | ~ v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f90,plain,
    ( spl3_13
  <=> ! [X0] :
        ( ~ r1_xboole_0(k1_relat_1(sK0),X0)
        | k1_xboole_0 = k7_relat_1(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f94,plain,
    ( ! [X1] :
        ( k1_xboole_0 = k7_relat_1(sK0,X1)
        | ~ v1_xboole_0(X1) )
    | ~ spl3_11
    | ~ spl3_13 ),
    inference(resolution,[],[f91,f77])).

fof(f77,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(X0,X1)
        | ~ v1_xboole_0(X1) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f76])).

fof(f91,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(k1_relat_1(sK0),X0)
        | k1_xboole_0 = k7_relat_1(sK0,X0) )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f90])).

fof(f92,plain,
    ( spl3_13
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f88,f66,f36,f90])).

fof(f36,plain,
    ( spl3_2
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f66,plain,
    ( spl3_9
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k7_relat_1(X1,X0)
        | ~ r1_xboole_0(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f88,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(k1_relat_1(sK0),X0)
        | k1_xboole_0 = k7_relat_1(sK0,X0) )
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(resolution,[],[f67,f38])).

fof(f38,plain,
    ( v1_relat_1(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f67,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f66])).

fof(f78,plain,
    ( spl3_11
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f74,f58,f50,f76])).

fof(f50,plain,
    ( spl3_5
  <=> ! [X0,X2] :
        ( ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f58,plain,
    ( spl3_7
  <=> ! [X1,X0] :
        ( r2_hidden(sK2(X0,X1),X1)
        | r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f74,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(X0,X1)
        | ~ v1_xboole_0(X1) )
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(resolution,[],[f59,f51])).

fof(f51,plain,
    ( ! [X2,X0] :
        ( ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f50])).

fof(f59,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK2(X0,X1),X1)
        | r1_xboole_0(X0,X1) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f58])).

fof(f68,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f29,f66])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X1,X0)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k7_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

fof(f60,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f26,f58])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f9,f17])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
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

fof(f52,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f23,f50])).

fof(f23,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK1(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f15])).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f13])).

fof(f13,plain,(
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

fof(f44,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f22,f41])).

fof(f22,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f39,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f20,f36])).

fof(f20,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( k1_xboole_0 != k7_relat_1(sK0,k1_xboole_0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f11])).

fof(f11,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k7_relat_1(X0,k1_xboole_0)
        & v1_relat_1(X0) )
   => ( k1_xboole_0 != k7_relat_1(sK0,k1_xboole_0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( k1_xboole_0 != k7_relat_1(X0,k1_xboole_0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_relat_1)).

fof(f34,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f21,f31])).

fof(f21,plain,(
    k1_xboole_0 != k7_relat_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:38:38 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.42  % (30304)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.22/0.44  % (30302)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.44  % (30301)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.44  % (30303)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.22/0.44  % (30301)Refutation found. Thanks to Tanya!
% 0.22/0.44  % SZS status Theorem for theBenchmark
% 0.22/0.44  % SZS output start Proof for theBenchmark
% 0.22/0.44  fof(f110,plain,(
% 0.22/0.44    $false),
% 0.22/0.44    inference(avatar_sat_refutation,[],[f34,f39,f44,f52,f60,f68,f78,f92,f106,f109])).
% 0.22/0.44  fof(f109,plain,(
% 0.22/0.44    spl3_1 | ~spl3_3 | ~spl3_16),
% 0.22/0.44    inference(avatar_contradiction_clause,[],[f108])).
% 0.22/0.44  fof(f108,plain,(
% 0.22/0.44    $false | (spl3_1 | ~spl3_3 | ~spl3_16)),
% 0.22/0.44    inference(subsumption_resolution,[],[f107,f33])).
% 0.22/0.44  fof(f33,plain,(
% 0.22/0.44    k1_xboole_0 != k7_relat_1(sK0,k1_xboole_0) | spl3_1),
% 0.22/0.44    inference(avatar_component_clause,[],[f31])).
% 0.22/0.44  fof(f31,plain,(
% 0.22/0.44    spl3_1 <=> k1_xboole_0 = k7_relat_1(sK0,k1_xboole_0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.44  fof(f107,plain,(
% 0.22/0.44    k1_xboole_0 = k7_relat_1(sK0,k1_xboole_0) | (~spl3_3 | ~spl3_16)),
% 0.22/0.44    inference(resolution,[],[f105,f43])).
% 0.22/0.44  fof(f43,plain,(
% 0.22/0.44    v1_xboole_0(k1_xboole_0) | ~spl3_3),
% 0.22/0.44    inference(avatar_component_clause,[],[f41])).
% 0.22/0.44  fof(f41,plain,(
% 0.22/0.44    spl3_3 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.44  fof(f105,plain,(
% 0.22/0.44    ( ! [X1] : (~v1_xboole_0(X1) | k1_xboole_0 = k7_relat_1(sK0,X1)) ) | ~spl3_16),
% 0.22/0.44    inference(avatar_component_clause,[],[f104])).
% 0.22/0.44  fof(f104,plain,(
% 0.22/0.44    spl3_16 <=> ! [X1] : (k1_xboole_0 = k7_relat_1(sK0,X1) | ~v1_xboole_0(X1))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.22/0.44  fof(f106,plain,(
% 0.22/0.44    spl3_16 | ~spl3_11 | ~spl3_13),
% 0.22/0.44    inference(avatar_split_clause,[],[f94,f90,f76,f104])).
% 0.22/0.44  fof(f76,plain,(
% 0.22/0.44    spl3_11 <=> ! [X1,X0] : (r1_xboole_0(X0,X1) | ~v1_xboole_0(X1))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.44  fof(f90,plain,(
% 0.22/0.44    spl3_13 <=> ! [X0] : (~r1_xboole_0(k1_relat_1(sK0),X0) | k1_xboole_0 = k7_relat_1(sK0,X0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.44  fof(f94,plain,(
% 0.22/0.44    ( ! [X1] : (k1_xboole_0 = k7_relat_1(sK0,X1) | ~v1_xboole_0(X1)) ) | (~spl3_11 | ~spl3_13)),
% 0.22/0.44    inference(resolution,[],[f91,f77])).
% 0.22/0.44  fof(f77,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~v1_xboole_0(X1)) ) | ~spl3_11),
% 0.22/0.44    inference(avatar_component_clause,[],[f76])).
% 0.22/0.44  fof(f91,plain,(
% 0.22/0.44    ( ! [X0] : (~r1_xboole_0(k1_relat_1(sK0),X0) | k1_xboole_0 = k7_relat_1(sK0,X0)) ) | ~spl3_13),
% 0.22/0.44    inference(avatar_component_clause,[],[f90])).
% 0.22/0.44  fof(f92,plain,(
% 0.22/0.44    spl3_13 | ~spl3_2 | ~spl3_9),
% 0.22/0.44    inference(avatar_split_clause,[],[f88,f66,f36,f90])).
% 0.22/0.44  fof(f36,plain,(
% 0.22/0.44    spl3_2 <=> v1_relat_1(sK0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.44  fof(f66,plain,(
% 0.22/0.44    spl3_9 <=> ! [X1,X0] : (k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.44  fof(f88,plain,(
% 0.22/0.44    ( ! [X0] : (~r1_xboole_0(k1_relat_1(sK0),X0) | k1_xboole_0 = k7_relat_1(sK0,X0)) ) | (~spl3_2 | ~spl3_9)),
% 0.22/0.44    inference(resolution,[],[f67,f38])).
% 0.22/0.44  fof(f38,plain,(
% 0.22/0.44    v1_relat_1(sK0) | ~spl3_2),
% 0.22/0.44    inference(avatar_component_clause,[],[f36])).
% 0.22/0.44  fof(f67,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) ) | ~spl3_9),
% 0.22/0.44    inference(avatar_component_clause,[],[f66])).
% 0.22/0.44  fof(f78,plain,(
% 0.22/0.44    spl3_11 | ~spl3_5 | ~spl3_7),
% 0.22/0.44    inference(avatar_split_clause,[],[f74,f58,f50,f76])).
% 0.22/0.44  fof(f50,plain,(
% 0.22/0.44    spl3_5 <=> ! [X0,X2] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.44  fof(f58,plain,(
% 0.22/0.44    spl3_7 <=> ! [X1,X0] : (r2_hidden(sK2(X0,X1),X1) | r1_xboole_0(X0,X1))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.44  fof(f74,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~v1_xboole_0(X1)) ) | (~spl3_5 | ~spl3_7)),
% 0.22/0.44    inference(resolution,[],[f59,f51])).
% 0.22/0.44  fof(f51,plain,(
% 0.22/0.44    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) ) | ~spl3_5),
% 0.22/0.44    inference(avatar_component_clause,[],[f50])).
% 0.22/0.44  fof(f59,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r1_xboole_0(X0,X1)) ) | ~spl3_7),
% 0.22/0.44    inference(avatar_component_clause,[],[f58])).
% 0.22/0.44  fof(f68,plain,(
% 0.22/0.44    spl3_9),
% 0.22/0.44    inference(avatar_split_clause,[],[f29,f66])).
% 0.22/0.44  fof(f29,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f19])).
% 0.22/0.44  fof(f19,plain,(
% 0.22/0.44    ! [X0,X1] : (((k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.22/0.44    inference(nnf_transformation,[],[f10])).
% 0.22/0.44  fof(f10,plain,(
% 0.22/0.44    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f4])).
% 0.22/0.44  fof(f4,axiom,(
% 0.22/0.44    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).
% 0.22/0.44  fof(f60,plain,(
% 0.22/0.44    spl3_7),
% 0.22/0.44    inference(avatar_split_clause,[],[f26,f58])).
% 0.22/0.44  fof(f26,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f18])).
% 0.22/0.44  fof(f18,plain,(
% 0.22/0.44    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f9,f17])).
% 0.22/0.44  fof(f17,plain,(
% 0.22/0.44    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f9,plain,(
% 0.22/0.44    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.44    inference(ennf_transformation,[],[f7])).
% 0.22/0.44  fof(f7,plain,(
% 0.22/0.44    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.44    inference(rectify,[],[f3])).
% 0.22/0.44  fof(f3,axiom,(
% 0.22/0.44    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.22/0.44  fof(f52,plain,(
% 0.22/0.44    spl3_5),
% 0.22/0.44    inference(avatar_split_clause,[],[f23,f50])).
% 0.22/0.44  fof(f23,plain,(
% 0.22/0.44    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f16])).
% 0.22/0.44  fof(f16,plain,(
% 0.22/0.44    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK1(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f15])).
% 0.22/0.44  fof(f15,plain,(
% 0.22/0.44    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f14,plain,(
% 0.22/0.44    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.44    inference(rectify,[],[f13])).
% 0.22/0.44  fof(f13,plain,(
% 0.22/0.44    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.44    inference(nnf_transformation,[],[f1])).
% 0.22/0.44  fof(f1,axiom,(
% 0.22/0.44    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.44  fof(f44,plain,(
% 0.22/0.44    spl3_3),
% 0.22/0.44    inference(avatar_split_clause,[],[f22,f41])).
% 0.22/0.44  fof(f22,plain,(
% 0.22/0.44    v1_xboole_0(k1_xboole_0)),
% 0.22/0.44    inference(cnf_transformation,[],[f2])).
% 0.22/0.44  fof(f2,axiom,(
% 0.22/0.44    v1_xboole_0(k1_xboole_0)),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.44  fof(f39,plain,(
% 0.22/0.44    spl3_2),
% 0.22/0.44    inference(avatar_split_clause,[],[f20,f36])).
% 0.22/0.44  fof(f20,plain,(
% 0.22/0.44    v1_relat_1(sK0)),
% 0.22/0.44    inference(cnf_transformation,[],[f12])).
% 0.22/0.44  fof(f12,plain,(
% 0.22/0.44    k1_xboole_0 != k7_relat_1(sK0,k1_xboole_0) & v1_relat_1(sK0)),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f11])).
% 0.22/0.44  fof(f11,plain,(
% 0.22/0.44    ? [X0] : (k1_xboole_0 != k7_relat_1(X0,k1_xboole_0) & v1_relat_1(X0)) => (k1_xboole_0 != k7_relat_1(sK0,k1_xboole_0) & v1_relat_1(sK0))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f8,plain,(
% 0.22/0.44    ? [X0] : (k1_xboole_0 != k7_relat_1(X0,k1_xboole_0) & v1_relat_1(X0))),
% 0.22/0.44    inference(ennf_transformation,[],[f6])).
% 0.22/0.44  fof(f6,negated_conjecture,(
% 0.22/0.44    ~! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0))),
% 0.22/0.44    inference(negated_conjecture,[],[f5])).
% 0.22/0.44  fof(f5,conjecture,(
% 0.22/0.44    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_relat_1)).
% 0.22/0.44  fof(f34,plain,(
% 0.22/0.44    ~spl3_1),
% 0.22/0.44    inference(avatar_split_clause,[],[f21,f31])).
% 0.22/0.44  fof(f21,plain,(
% 0.22/0.44    k1_xboole_0 != k7_relat_1(sK0,k1_xboole_0)),
% 0.22/0.44    inference(cnf_transformation,[],[f12])).
% 0.22/0.44  % SZS output end Proof for theBenchmark
% 0.22/0.44  % (30301)------------------------------
% 0.22/0.44  % (30301)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (30301)Termination reason: Refutation
% 0.22/0.44  
% 0.22/0.44  % (30301)Memory used [KB]: 10618
% 0.22/0.44  % (30301)Time elapsed: 0.009 s
% 0.22/0.44  % (30301)------------------------------
% 0.22/0.44  % (30301)------------------------------
% 0.22/0.45  % (30295)Success in time 0.08 s
%------------------------------------------------------------------------------
