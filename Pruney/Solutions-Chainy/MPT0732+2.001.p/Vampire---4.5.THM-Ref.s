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
% DateTime   : Thu Dec  3 12:55:15 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   51 (  83 expanded)
%              Number of leaves         :   14 (  34 expanded)
%              Depth                    :    7
%              Number of atoms          :  160 ( 282 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f98,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f33,f38,f43,f48,f60,f72,f77,f84,f97])).

fof(f97,plain,
    ( ~ spl5_1
    | ~ spl5_3
    | ~ spl5_7
    | spl5_12 ),
    inference(avatar_split_clause,[],[f86,f81,f58,f40,f30])).

fof(f30,plain,
    ( spl5_1
  <=> v1_ordinal1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f40,plain,
    ( spl5_3
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f58,plain,
    ( spl5_7
  <=> ! [X0,X2] :
        ( r1_tarski(X2,X0)
        | ~ r2_hidden(X2,X0)
        | ~ v1_ordinal1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f81,plain,
    ( spl5_12
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f86,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ v1_ordinal1(sK2)
    | ~ spl5_7
    | spl5_12 ),
    inference(resolution,[],[f83,f59])).

fof(f59,plain,
    ( ! [X2,X0] :
        ( r1_tarski(X2,X0)
        | ~ r2_hidden(X2,X0)
        | ~ v1_ordinal1(X0) )
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f58])).

fof(f83,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl5_12 ),
    inference(avatar_component_clause,[],[f81])).

fof(f84,plain,
    ( ~ spl5_12
    | ~ spl5_2
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f78,f75,f35,f81])).

fof(f35,plain,
    ( spl5_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f75,plain,
    ( spl5_11
  <=> ! [X0] :
        ( ~ r2_hidden(sK0,X0)
        | ~ r1_tarski(X0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f78,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ spl5_2
    | ~ spl5_11 ),
    inference(resolution,[],[f76,f37])).

fof(f37,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f35])).

fof(f76,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK0,X0)
        | ~ r1_tarski(X0,sK2) )
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f75])).

fof(f77,plain,
    ( spl5_11
    | spl5_4
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f73,f70,f45,f75])).

fof(f45,plain,
    ( spl5_4
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f70,plain,
    ( spl5_10
  <=> ! [X1,X3,X0] :
        ( r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f73,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK0,X0)
        | ~ r1_tarski(X0,sK2) )
    | spl5_4
    | ~ spl5_10 ),
    inference(resolution,[],[f71,f47])).

fof(f47,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f45])).

fof(f71,plain,
    ( ! [X0,X3,X1] :
        ( r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0)
        | ~ r1_tarski(X0,X1) )
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f70])).

fof(f72,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f26,f70])).

fof(f26,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f16,f17])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f60,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f23,f58])).

fof(f23,plain,(
    ! [X2,X0] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ( ~ r1_tarski(sK3(X0),X0)
          & r2_hidden(sK3(X0),X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f12,f13])).

fof(f13,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X1,X0)
          & r2_hidden(X1,X0) )
     => ( ~ r1_tarski(sK3(X0),X0)
        & r2_hidden(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(rectify,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( r1_tarski(X1,X0)
            | ~ r2_hidden(X1,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).

fof(f48,plain,(
    ~ spl5_4 ),
    inference(avatar_split_clause,[],[f22,f45])).

fof(f22,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( ~ r2_hidden(sK0,sK2)
    & r2_hidden(sK1,sK2)
    & r2_hidden(sK0,sK1)
    & v1_ordinal1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(X0,X2)
        & r2_hidden(X1,X2)
        & r2_hidden(X0,X1)
        & v1_ordinal1(X2) )
   => ( ~ r2_hidden(sK0,sK2)
      & r2_hidden(sK1,sK2)
      & r2_hidden(sK0,sK1)
      & v1_ordinal1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & r2_hidden(X1,X2)
      & r2_hidden(X0,X1)
      & v1_ordinal1(X2) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & r2_hidden(X1,X2)
      & r2_hidden(X0,X1)
      & v1_ordinal1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_ordinal1(X2)
       => ( ( r2_hidden(X1,X2)
            & r2_hidden(X0,X1) )
         => r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( v1_ordinal1(X2)
     => ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X1) )
       => r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_ordinal1)).

fof(f43,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f21,f40])).

fof(f21,plain,(
    r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f38,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f20,f35])).

fof(f20,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f33,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f19,f30])).

fof(f19,plain,(
    v1_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:52:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.44  % (19445)dis+1011_4_awrs=decay:awrsf=32:afp=40000:afq=1.0:amm=off:anc=all:bs=on:cond=on:fsr=off:gsp=input_only:lma=on:nm=16:nwc=1:nicw=on:sac=on:sp=frequency:thi=all:updr=off:uhcvi=on_670 on theBenchmark
% 0.21/0.44  % (19437)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.45  % (19430)dis+1002_8:1_awrs=converge:awrsf=256:anc=all_dependent:br=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:irw=on:nm=64:nwc=1:sas=z3:s2a=on:sp=frequency:thf=on:uwa=interpreted_only:urr=on_7 on theBenchmark
% 0.21/0.45  % (19445)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f98,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(avatar_sat_refutation,[],[f33,f38,f43,f48,f60,f72,f77,f84,f97])).
% 0.21/0.45  fof(f97,plain,(
% 0.21/0.45    ~spl5_1 | ~spl5_3 | ~spl5_7 | spl5_12),
% 0.21/0.45    inference(avatar_split_clause,[],[f86,f81,f58,f40,f30])).
% 0.21/0.45  fof(f30,plain,(
% 0.21/0.45    spl5_1 <=> v1_ordinal1(sK2)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.45  fof(f40,plain,(
% 0.21/0.45    spl5_3 <=> r2_hidden(sK1,sK2)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.45  fof(f58,plain,(
% 0.21/0.45    spl5_7 <=> ! [X0,X2] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X0) | ~v1_ordinal1(X0))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.45  fof(f81,plain,(
% 0.21/0.45    spl5_12 <=> r1_tarski(sK1,sK2)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.45  fof(f86,plain,(
% 0.21/0.45    ~r2_hidden(sK1,sK2) | ~v1_ordinal1(sK2) | (~spl5_7 | spl5_12)),
% 0.21/0.45    inference(resolution,[],[f83,f59])).
% 0.21/0.45  fof(f59,plain,(
% 0.21/0.45    ( ! [X2,X0] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X0) | ~v1_ordinal1(X0)) ) | ~spl5_7),
% 0.21/0.45    inference(avatar_component_clause,[],[f58])).
% 0.21/0.45  fof(f83,plain,(
% 0.21/0.45    ~r1_tarski(sK1,sK2) | spl5_12),
% 0.21/0.45    inference(avatar_component_clause,[],[f81])).
% 0.21/0.45  fof(f84,plain,(
% 0.21/0.45    ~spl5_12 | ~spl5_2 | ~spl5_11),
% 0.21/0.45    inference(avatar_split_clause,[],[f78,f75,f35,f81])).
% 0.21/0.45  fof(f35,plain,(
% 0.21/0.45    spl5_2 <=> r2_hidden(sK0,sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.45  fof(f75,plain,(
% 0.21/0.45    spl5_11 <=> ! [X0] : (~r2_hidden(sK0,X0) | ~r1_tarski(X0,sK2))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.45  fof(f78,plain,(
% 0.21/0.45    ~r1_tarski(sK1,sK2) | (~spl5_2 | ~spl5_11)),
% 0.21/0.45    inference(resolution,[],[f76,f37])).
% 0.21/0.45  fof(f37,plain,(
% 0.21/0.45    r2_hidden(sK0,sK1) | ~spl5_2),
% 0.21/0.45    inference(avatar_component_clause,[],[f35])).
% 0.21/0.45  fof(f76,plain,(
% 0.21/0.45    ( ! [X0] : (~r2_hidden(sK0,X0) | ~r1_tarski(X0,sK2)) ) | ~spl5_11),
% 0.21/0.45    inference(avatar_component_clause,[],[f75])).
% 0.21/0.45  fof(f77,plain,(
% 0.21/0.45    spl5_11 | spl5_4 | ~spl5_10),
% 0.21/0.45    inference(avatar_split_clause,[],[f73,f70,f45,f75])).
% 0.21/0.45  fof(f45,plain,(
% 0.21/0.45    spl5_4 <=> r2_hidden(sK0,sK2)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.45  fof(f70,plain,(
% 0.21/0.45    spl5_10 <=> ! [X1,X3,X0] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.45  fof(f73,plain,(
% 0.21/0.45    ( ! [X0] : (~r2_hidden(sK0,X0) | ~r1_tarski(X0,sK2)) ) | (spl5_4 | ~spl5_10)),
% 0.21/0.45    inference(resolution,[],[f71,f47])).
% 0.21/0.45  fof(f47,plain,(
% 0.21/0.45    ~r2_hidden(sK0,sK2) | spl5_4),
% 0.21/0.45    inference(avatar_component_clause,[],[f45])).
% 0.21/0.45  fof(f71,plain,(
% 0.21/0.45    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) ) | ~spl5_10),
% 0.21/0.45    inference(avatar_component_clause,[],[f70])).
% 0.21/0.45  fof(f72,plain,(
% 0.21/0.45    spl5_10),
% 0.21/0.45    inference(avatar_split_clause,[],[f26,f70])).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f18])).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f16,f17])).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.45    inference(rectify,[],[f15])).
% 0.21/0.45  fof(f15,plain,(
% 0.21/0.45    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.45    inference(nnf_transformation,[],[f8])).
% 0.21/0.45  fof(f8,plain,(
% 0.21/0.45    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.45  fof(f60,plain,(
% 0.21/0.45    spl5_7),
% 0.21/0.45    inference(avatar_split_clause,[],[f23,f58])).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    ( ! [X2,X0] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X0) | ~v1_ordinal1(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f14])).
% 0.21/0.45  fof(f14,plain,(
% 0.21/0.45    ! [X0] : ((v1_ordinal1(X0) | (~r1_tarski(sK3(X0),X0) & r2_hidden(sK3(X0),X0))) & (! [X2] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X0)) | ~v1_ordinal1(X0)))),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f12,f13])).
% 0.21/0.45  fof(f13,plain,(
% 0.21/0.45    ! [X0] : (? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0)) => (~r1_tarski(sK3(X0),X0) & r2_hidden(sK3(X0),X0)))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f12,plain,(
% 0.21/0.45    ! [X0] : ((v1_ordinal1(X0) | ? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0))) & (! [X2] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X0)) | ~v1_ordinal1(X0)))),
% 0.21/0.45    inference(rectify,[],[f11])).
% 0.21/0.45  fof(f11,plain,(
% 0.21/0.45    ! [X0] : ((v1_ordinal1(X0) | ? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0))) & (! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)) | ~v1_ordinal1(X0)))),
% 0.21/0.45    inference(nnf_transformation,[],[f7])).
% 0.21/0.45  fof(f7,plain,(
% 0.21/0.45    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).
% 0.21/0.45  fof(f48,plain,(
% 0.21/0.45    ~spl5_4),
% 0.21/0.45    inference(avatar_split_clause,[],[f22,f45])).
% 0.21/0.45  fof(f22,plain,(
% 0.21/0.45    ~r2_hidden(sK0,sK2)),
% 0.21/0.45    inference(cnf_transformation,[],[f10])).
% 0.21/0.45  fof(f10,plain,(
% 0.21/0.45    ~r2_hidden(sK0,sK2) & r2_hidden(sK1,sK2) & r2_hidden(sK0,sK1) & v1_ordinal1(sK2)),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f9])).
% 0.21/0.45  fof(f9,plain,(
% 0.21/0.45    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r2_hidden(X1,X2) & r2_hidden(X0,X1) & v1_ordinal1(X2)) => (~r2_hidden(sK0,sK2) & r2_hidden(sK1,sK2) & r2_hidden(sK0,sK1) & v1_ordinal1(sK2))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f6,plain,(
% 0.21/0.45    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r2_hidden(X1,X2) & r2_hidden(X0,X1) & v1_ordinal1(X2))),
% 0.21/0.45    inference(flattening,[],[f5])).
% 0.21/0.45  fof(f5,plain,(
% 0.21/0.45    ? [X0,X1,X2] : ((~r2_hidden(X0,X2) & (r2_hidden(X1,X2) & r2_hidden(X0,X1))) & v1_ordinal1(X2))),
% 0.21/0.45    inference(ennf_transformation,[],[f4])).
% 0.21/0.45  fof(f4,negated_conjecture,(
% 0.21/0.45    ~! [X0,X1,X2] : (v1_ordinal1(X2) => ((r2_hidden(X1,X2) & r2_hidden(X0,X1)) => r2_hidden(X0,X2)))),
% 0.21/0.45    inference(negated_conjecture,[],[f3])).
% 0.21/0.45  fof(f3,conjecture,(
% 0.21/0.45    ! [X0,X1,X2] : (v1_ordinal1(X2) => ((r2_hidden(X1,X2) & r2_hidden(X0,X1)) => r2_hidden(X0,X2)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_ordinal1)).
% 0.21/0.45  fof(f43,plain,(
% 0.21/0.45    spl5_3),
% 0.21/0.45    inference(avatar_split_clause,[],[f21,f40])).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    r2_hidden(sK1,sK2)),
% 0.21/0.45    inference(cnf_transformation,[],[f10])).
% 0.21/0.45  fof(f38,plain,(
% 0.21/0.45    spl5_2),
% 0.21/0.45    inference(avatar_split_clause,[],[f20,f35])).
% 0.21/0.45  fof(f20,plain,(
% 0.21/0.45    r2_hidden(sK0,sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f10])).
% 0.21/0.45  fof(f33,plain,(
% 0.21/0.45    spl5_1),
% 0.21/0.45    inference(avatar_split_clause,[],[f19,f30])).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    v1_ordinal1(sK2)),
% 0.21/0.45    inference(cnf_transformation,[],[f10])).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (19445)------------------------------
% 0.21/0.45  % (19445)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (19445)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (19445)Memory used [KB]: 5373
% 0.21/0.45  % (19445)Time elapsed: 0.054 s
% 0.21/0.45  % (19445)------------------------------
% 0.21/0.45  % (19445)------------------------------
% 0.21/0.45  % (19428)Success in time 0.093 s
%------------------------------------------------------------------------------
