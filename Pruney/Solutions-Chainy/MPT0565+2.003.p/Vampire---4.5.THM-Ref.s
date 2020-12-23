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
% DateTime   : Thu Dec  3 12:50:03 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 115 expanded)
%              Number of leaves         :   19 (  47 expanded)
%              Depth                    :   10
%              Number of atoms          :  244 ( 407 expanded)
%              Number of equality atoms :   25 (  54 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f193,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f69,f87,f92,f119,f156,f192])).

fof(f192,plain,
    ( ~ spl9_1
    | ~ spl9_3 ),
    inference(avatar_contradiction_clause,[],[f188])).

fof(f188,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_3 ),
    inference(resolution,[],[f166,f60])).

fof(f60,plain,
    ( r2_hidden(sK1(sK0,k10_relat_1(sK0,k2_relat_1(sK0))),k10_relat_1(sK0,k2_relat_1(sK0)))
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl9_1
  <=> r2_hidden(sK1(sK0,k10_relat_1(sK0,k2_relat_1(sK0))),k10_relat_1(sK0,k2_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

% (24072)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% (24072)Refutation not found, incomplete strategy% (24072)------------------------------
% (24072)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (24072)Termination reason: Refutation not found, incomplete strategy

% (24072)Memory used [KB]: 10618
% (24072)Time elapsed: 0.084 s
% (24072)------------------------------
% (24072)------------------------------
% (24065)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% (24064)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% (24067)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% (24062)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% (24063)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% (24066)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% (24062)Refutation not found, incomplete strategy% (24062)------------------------------
% (24062)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (24075)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% (24062)Termination reason: Refutation not found, incomplete strategy

% (24062)Memory used [KB]: 10490
% (24062)Time elapsed: 0.091 s
% (24062)------------------------------
% (24062)------------------------------
% (24079)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% (24075)Refutation not found, incomplete strategy% (24075)------------------------------
% (24075)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (24075)Termination reason: Refutation not found, incomplete strategy

% (24075)Memory used [KB]: 10618
% (24075)Time elapsed: 0.051 s
% (24075)------------------------------
% (24075)------------------------------
% (24061)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
fof(f166,plain,
    ( ! [X0] : ~ r2_hidden(sK1(sK0,k10_relat_1(sK0,k2_relat_1(sK0))),k10_relat_1(sK0,X0))
    | ~ spl9_3 ),
    inference(resolution,[],[f68,f52])).

fof(f52,plain,(
    ! [X2,X3] :
      ( r2_hidden(k4_tarski(X2,sK7(X2,X3,sK0)),sK0)
      | ~ r2_hidden(X2,k10_relat_1(sK0,X3)) ) ),
    inference(resolution,[],[f26,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,sK7(X0,X1,X2)),X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ( r2_hidden(sK7(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(X0,sK7(X0,X1,X2)),X2)
            & r2_hidden(sK7(X0,X1,X2),k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f23,f24])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK7(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK7(X0,X1,X2)),X2)
        & r2_hidden(sK7(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

fof(f26,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,
    ( k1_relat_1(sK0) != k10_relat_1(sK0,k2_relat_1(sK0))
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f8])).

fof(f8,plain,
    ( ? [X0] :
        ( k1_relat_1(X0) != k10_relat_1(X0,k2_relat_1(X0))
        & v1_relat_1(X0) )
   => ( k1_relat_1(sK0) != k10_relat_1(sK0,k2_relat_1(sK0))
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0] :
      ( k1_relat_1(X0) != k10_relat_1(X0,k2_relat_1(X0))
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f68,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK1(sK0,k10_relat_1(sK0,k2_relat_1(sK0))),X0),sK0)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl9_3
  <=> ! [X0] : ~ r2_hidden(k4_tarski(sK1(sK0,k10_relat_1(sK0,k2_relat_1(sK0))),X0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f156,plain,
    ( ~ spl9_8
    | ~ spl9_2
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f151,f85,f62,f112])).

fof(f112,plain,
    ( spl9_8
  <=> r2_hidden(sK2(sK0,k10_relat_1(sK0,k2_relat_1(sK0))),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f62,plain,
    ( spl9_2
  <=> r2_hidden(k4_tarski(sK1(sK0,k10_relat_1(sK0,k2_relat_1(sK0))),sK2(sK0,k10_relat_1(sK0,k2_relat_1(sK0)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f85,plain,
    ( spl9_5
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK0))
        | ~ r2_hidden(k4_tarski(sK1(sK0,k10_relat_1(sK0,k2_relat_1(sK0))),X0),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f151,plain,
    ( ~ r2_hidden(sK2(sK0,k10_relat_1(sK0,k2_relat_1(sK0))),k2_relat_1(sK0))
    | ~ spl9_2
    | ~ spl9_5 ),
    inference(resolution,[],[f86,f64])).

fof(f64,plain,
    ( r2_hidden(k4_tarski(sK1(sK0,k10_relat_1(sK0,k2_relat_1(sK0))),sK2(sK0,k10_relat_1(sK0,k2_relat_1(sK0)))),sK0)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f86,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK1(sK0,k10_relat_1(sK0,k2_relat_1(sK0))),X0),sK0)
        | ~ r2_hidden(X0,k2_relat_1(sK0)) )
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f85])).

fof(f119,plain,
    ( spl9_8
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f108,f62,f112])).

fof(f108,plain,
    ( r2_hidden(sK2(sK0,k10_relat_1(sK0,k2_relat_1(sK0))),k2_relat_1(sK0))
    | ~ spl9_2 ),
    inference(resolution,[],[f64,f42])).

fof(f42,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK6(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f17,f20,f19,f18])).

% (24069)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK4(X0,X1)),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

% (24061)Refutation not found, incomplete strategy% (24061)------------------------------
% (24061)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK4(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

% (24061)Termination reason: Refutation not found, incomplete strategy

% (24061)Memory used [KB]: 6140
fof(f20,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

% (24061)Time elapsed: 0.069 s
% (24061)------------------------------
% (24061)------------------------------
fof(f17,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f92,plain,(
    spl9_4 ),
    inference(avatar_contradiction_clause,[],[f91])).

fof(f91,plain,
    ( $false
    | spl9_4 ),
    inference(resolution,[],[f83,f26])).

fof(f83,plain,
    ( ~ v1_relat_1(sK0)
    | spl9_4 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl9_4
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f87,plain,
    ( ~ spl9_4
    | spl9_5
    | spl9_1 ),
    inference(avatar_split_clause,[],[f79,f58,f85,f81])).

fof(f79,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK0))
        | ~ r2_hidden(k4_tarski(sK1(sK0,k10_relat_1(sK0,k2_relat_1(sK0))),X0),sK0)
        | ~ v1_relat_1(sK0) )
    | spl9_1 ),
    inference(duplicate_literal_removal,[],[f78])).

fof(f78,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK0))
        | ~ r2_hidden(k4_tarski(sK1(sK0,k10_relat_1(sK0,k2_relat_1(sK0))),X0),sK0)
        | ~ r2_hidden(X0,k2_relat_1(sK0))
        | ~ v1_relat_1(sK0) )
    | spl9_1 ),
    inference(resolution,[],[f59,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ r2_hidden(X3,k2_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f59,plain,
    ( ~ r2_hidden(sK1(sK0,k10_relat_1(sK0,k2_relat_1(sK0))),k10_relat_1(sK0,k2_relat_1(sK0)))
    | spl9_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f69,plain,
    ( ~ spl9_1
    | spl9_3 ),
    inference(avatar_split_clause,[],[f56,f67,f58])).

fof(f56,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(sK1(sK0,k10_relat_1(sK0,k2_relat_1(sK0))),X0),sK0)
      | ~ r2_hidden(sK1(sK0,k10_relat_1(sK0,k2_relat_1(sK0))),k10_relat_1(sK0,k2_relat_1(sK0))) ) ),
    inference(resolution,[],[f45,f46])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( sQ8_eqProxy(k1_relat_1(X0),X1)
      | ~ r2_hidden(k4_tarski(sK1(X0,X1),X3),X0)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(equality_proxy_replacement,[],[f31,f44])).

fof(f44,plain,(
    ! [X1,X0] :
      ( sQ8_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ8_eqProxy])])).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( k1_relat_1(X0) = X1
      | ~ r2_hidden(k4_tarski(sK1(X0,X1),X3),X0)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK1(X0,X1),X3),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f11,f14,f13,f12])).

fof(f12,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK1(X0,X1),X3),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK1(X0,X1),X4),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK1(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
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
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
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
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f45,plain,(
    ~ sQ8_eqProxy(k1_relat_1(sK0),k10_relat_1(sK0,k2_relat_1(sK0))) ),
    inference(equality_proxy_replacement,[],[f27,f44])).

fof(f27,plain,(
    k1_relat_1(sK0) != k10_relat_1(sK0,k2_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f65,plain,
    ( spl9_1
    | spl9_2 ),
    inference(avatar_split_clause,[],[f55,f62,f58])).

fof(f55,plain,
    ( r2_hidden(k4_tarski(sK1(sK0,k10_relat_1(sK0,k2_relat_1(sK0))),sK2(sK0,k10_relat_1(sK0,k2_relat_1(sK0)))),sK0)
    | r2_hidden(sK1(sK0,k10_relat_1(sK0,k2_relat_1(sK0))),k10_relat_1(sK0,k2_relat_1(sK0))) ),
    inference(resolution,[],[f45,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( sQ8_eqProxy(k1_relat_1(X0),X1)
      | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
      | r2_hidden(sK1(X0,X1),X1) ) ),
    inference(equality_proxy_replacement,[],[f30,f44])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
      | r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:36:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.41  % (24074)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.19/0.47  % (24076)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.19/0.48  % (24068)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.19/0.49  % (24073)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.49  % (24073)Refutation found. Thanks to Tanya!
% 0.19/0.49  % SZS status Theorem for theBenchmark
% 0.19/0.49  % SZS output start Proof for theBenchmark
% 0.19/0.49  fof(f193,plain,(
% 0.19/0.49    $false),
% 0.19/0.49    inference(avatar_sat_refutation,[],[f65,f69,f87,f92,f119,f156,f192])).
% 0.19/0.49  fof(f192,plain,(
% 0.19/0.49    ~spl9_1 | ~spl9_3),
% 0.19/0.49    inference(avatar_contradiction_clause,[],[f188])).
% 0.19/0.49  fof(f188,plain,(
% 0.19/0.49    $false | (~spl9_1 | ~spl9_3)),
% 0.19/0.49    inference(resolution,[],[f166,f60])).
% 0.19/0.49  fof(f60,plain,(
% 0.19/0.49    r2_hidden(sK1(sK0,k10_relat_1(sK0,k2_relat_1(sK0))),k10_relat_1(sK0,k2_relat_1(sK0))) | ~spl9_1),
% 0.19/0.49    inference(avatar_component_clause,[],[f58])).
% 0.19/0.49  fof(f58,plain,(
% 0.19/0.49    spl9_1 <=> r2_hidden(sK1(sK0,k10_relat_1(sK0,k2_relat_1(sK0))),k10_relat_1(sK0,k2_relat_1(sK0)))),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.19/0.49  % (24072)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.19/0.49  % (24072)Refutation not found, incomplete strategy% (24072)------------------------------
% 0.19/0.49  % (24072)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (24072)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.49  
% 0.19/0.49  % (24072)Memory used [KB]: 10618
% 0.19/0.49  % (24072)Time elapsed: 0.084 s
% 0.19/0.49  % (24072)------------------------------
% 0.19/0.49  % (24072)------------------------------
% 0.19/0.49  % (24065)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.19/0.49  % (24064)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.50  % (24067)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.19/0.50  % (24062)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.50  % (24063)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.19/0.50  % (24066)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.19/0.50  % (24062)Refutation not found, incomplete strategy% (24062)------------------------------
% 0.19/0.50  % (24062)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (24075)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.19/0.50  % (24062)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (24062)Memory used [KB]: 10490
% 0.19/0.50  % (24062)Time elapsed: 0.091 s
% 0.19/0.50  % (24062)------------------------------
% 0.19/0.50  % (24062)------------------------------
% 0.19/0.50  % (24079)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.19/0.50  % (24075)Refutation not found, incomplete strategy% (24075)------------------------------
% 0.19/0.50  % (24075)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (24075)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (24075)Memory used [KB]: 10618
% 0.19/0.50  % (24075)Time elapsed: 0.051 s
% 0.19/0.50  % (24075)------------------------------
% 0.19/0.50  % (24075)------------------------------
% 0.19/0.51  % (24061)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.19/0.51  fof(f166,plain,(
% 0.19/0.51    ( ! [X0] : (~r2_hidden(sK1(sK0,k10_relat_1(sK0,k2_relat_1(sK0))),k10_relat_1(sK0,X0))) ) | ~spl9_3),
% 0.19/0.51    inference(resolution,[],[f68,f52])).
% 0.19/0.51  fof(f52,plain,(
% 0.19/0.51    ( ! [X2,X3] : (r2_hidden(k4_tarski(X2,sK7(X2,X3,sK0)),sK0) | ~r2_hidden(X2,k10_relat_1(sK0,X3))) )),
% 0.19/0.51    inference(resolution,[],[f26,f37])).
% 0.19/0.51  fof(f37,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,sK7(X0,X1,X2)),X2) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f25])).
% 0.19/0.51  fof(f25,plain,(
% 0.19/0.51    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK7(X0,X1,X2)),X2) & r2_hidden(sK7(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.19/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f23,f24])).
% 0.19/0.51  fof(f24,plain,(
% 0.19/0.51    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK7(X0,X1,X2)),X2) & r2_hidden(sK7(X0,X1,X2),k2_relat_1(X2))))),
% 0.19/0.51    introduced(choice_axiom,[])).
% 0.19/0.51  fof(f23,plain,(
% 0.19/0.51    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.19/0.51    inference(rectify,[],[f22])).
% 0.19/0.51  fof(f22,plain,(
% 0.19/0.51    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.19/0.51    inference(nnf_transformation,[],[f7])).
% 0.19/0.51  fof(f7,plain,(
% 0.19/0.51    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.19/0.51    inference(ennf_transformation,[],[f3])).
% 0.19/0.51  fof(f3,axiom,(
% 0.19/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).
% 0.19/0.51  fof(f26,plain,(
% 0.19/0.51    v1_relat_1(sK0)),
% 0.19/0.51    inference(cnf_transformation,[],[f9])).
% 0.19/0.51  fof(f9,plain,(
% 0.19/0.51    k1_relat_1(sK0) != k10_relat_1(sK0,k2_relat_1(sK0)) & v1_relat_1(sK0)),
% 0.19/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f8])).
% 0.19/0.51  fof(f8,plain,(
% 0.19/0.51    ? [X0] : (k1_relat_1(X0) != k10_relat_1(X0,k2_relat_1(X0)) & v1_relat_1(X0)) => (k1_relat_1(sK0) != k10_relat_1(sK0,k2_relat_1(sK0)) & v1_relat_1(sK0))),
% 0.19/0.51    introduced(choice_axiom,[])).
% 0.19/0.51  fof(f6,plain,(
% 0.19/0.51    ? [X0] : (k1_relat_1(X0) != k10_relat_1(X0,k2_relat_1(X0)) & v1_relat_1(X0))),
% 0.19/0.51    inference(ennf_transformation,[],[f5])).
% 0.19/0.51  fof(f5,negated_conjecture,(
% 0.19/0.51    ~! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 0.19/0.51    inference(negated_conjecture,[],[f4])).
% 0.19/0.51  fof(f4,conjecture,(
% 0.19/0.51    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 0.19/0.51  fof(f68,plain,(
% 0.19/0.51    ( ! [X0] : (~r2_hidden(k4_tarski(sK1(sK0,k10_relat_1(sK0,k2_relat_1(sK0))),X0),sK0)) ) | ~spl9_3),
% 0.19/0.51    inference(avatar_component_clause,[],[f67])).
% 0.19/0.51  fof(f67,plain,(
% 0.19/0.51    spl9_3 <=> ! [X0] : ~r2_hidden(k4_tarski(sK1(sK0,k10_relat_1(sK0,k2_relat_1(sK0))),X0),sK0)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.19/0.51  fof(f156,plain,(
% 0.19/0.51    ~spl9_8 | ~spl9_2 | ~spl9_5),
% 0.19/0.51    inference(avatar_split_clause,[],[f151,f85,f62,f112])).
% 0.19/0.51  fof(f112,plain,(
% 0.19/0.51    spl9_8 <=> r2_hidden(sK2(sK0,k10_relat_1(sK0,k2_relat_1(sK0))),k2_relat_1(sK0))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 0.19/0.51  fof(f62,plain,(
% 0.19/0.51    spl9_2 <=> r2_hidden(k4_tarski(sK1(sK0,k10_relat_1(sK0,k2_relat_1(sK0))),sK2(sK0,k10_relat_1(sK0,k2_relat_1(sK0)))),sK0)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.19/0.51  fof(f85,plain,(
% 0.19/0.51    spl9_5 <=> ! [X0] : (~r2_hidden(X0,k2_relat_1(sK0)) | ~r2_hidden(k4_tarski(sK1(sK0,k10_relat_1(sK0,k2_relat_1(sK0))),X0),sK0))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 0.19/0.51  fof(f151,plain,(
% 0.19/0.51    ~r2_hidden(sK2(sK0,k10_relat_1(sK0,k2_relat_1(sK0))),k2_relat_1(sK0)) | (~spl9_2 | ~spl9_5)),
% 0.19/0.51    inference(resolution,[],[f86,f64])).
% 0.19/0.51  fof(f64,plain,(
% 0.19/0.51    r2_hidden(k4_tarski(sK1(sK0,k10_relat_1(sK0,k2_relat_1(sK0))),sK2(sK0,k10_relat_1(sK0,k2_relat_1(sK0)))),sK0) | ~spl9_2),
% 0.19/0.51    inference(avatar_component_clause,[],[f62])).
% 0.19/0.51  fof(f86,plain,(
% 0.19/0.51    ( ! [X0] : (~r2_hidden(k4_tarski(sK1(sK0,k10_relat_1(sK0,k2_relat_1(sK0))),X0),sK0) | ~r2_hidden(X0,k2_relat_1(sK0))) ) | ~spl9_5),
% 0.19/0.51    inference(avatar_component_clause,[],[f85])).
% 0.19/0.51  fof(f119,plain,(
% 0.19/0.51    spl9_8 | ~spl9_2),
% 0.19/0.51    inference(avatar_split_clause,[],[f108,f62,f112])).
% 0.19/0.51  fof(f108,plain,(
% 0.19/0.51    r2_hidden(sK2(sK0,k10_relat_1(sK0,k2_relat_1(sK0))),k2_relat_1(sK0)) | ~spl9_2),
% 0.19/0.51    inference(resolution,[],[f64,f42])).
% 0.19/0.51  fof(f42,plain,(
% 0.19/0.51    ( ! [X6,X0,X5] : (r2_hidden(X5,k2_relat_1(X0)) | ~r2_hidden(k4_tarski(X6,X5),X0)) )),
% 0.19/0.51    inference(equality_resolution,[],[f33])).
% 0.19/0.51  fof(f33,plain,(
% 0.19/0.51    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 0.19/0.51    inference(cnf_transformation,[],[f21])).
% 0.19/0.51  fof(f21,plain,(
% 0.19/0.51    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.19/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f17,f20,f19,f18])).
% 0.19/0.51  % (24069)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.19/0.51  fof(f18,plain,(
% 0.19/0.51    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK4(X0,X1)),X0) | r2_hidden(sK4(X0,X1),X1))))),
% 0.19/0.51    introduced(choice_axiom,[])).
% 0.19/0.51  % (24061)Refutation not found, incomplete strategy% (24061)------------------------------
% 0.19/0.51  % (24061)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  fof(f19,plain,(
% 0.19/0.51    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK4(X0,X1)),X0) => r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0))),
% 0.19/0.51    introduced(choice_axiom,[])).
% 0.19/0.51  % (24061)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (24061)Memory used [KB]: 6140
% 0.19/0.51  fof(f20,plain,(
% 0.19/0.51    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK6(X0,X5),X5),X0))),
% 0.19/0.51    introduced(choice_axiom,[])).
% 0.19/0.51  % (24061)Time elapsed: 0.069 s
% 0.19/0.51  % (24061)------------------------------
% 0.19/0.51  % (24061)------------------------------
% 0.19/0.51  fof(f17,plain,(
% 0.19/0.51    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.19/0.51    inference(rectify,[],[f16])).
% 0.19/0.51  fof(f16,plain,(
% 0.19/0.51    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 0.19/0.51    inference(nnf_transformation,[],[f2])).
% 0.19/0.51  fof(f2,axiom,(
% 0.19/0.51    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 0.19/0.51  fof(f92,plain,(
% 0.19/0.51    spl9_4),
% 0.19/0.51    inference(avatar_contradiction_clause,[],[f91])).
% 0.19/0.51  fof(f91,plain,(
% 0.19/0.51    $false | spl9_4),
% 0.19/0.51    inference(resolution,[],[f83,f26])).
% 0.19/0.51  fof(f83,plain,(
% 0.19/0.51    ~v1_relat_1(sK0) | spl9_4),
% 0.19/0.51    inference(avatar_component_clause,[],[f81])).
% 0.19/0.51  fof(f81,plain,(
% 0.19/0.51    spl9_4 <=> v1_relat_1(sK0)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.19/0.51  fof(f87,plain,(
% 0.19/0.51    ~spl9_4 | spl9_5 | spl9_1),
% 0.19/0.51    inference(avatar_split_clause,[],[f79,f58,f85,f81])).
% 0.19/0.51  fof(f79,plain,(
% 0.19/0.51    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK0)) | ~r2_hidden(k4_tarski(sK1(sK0,k10_relat_1(sK0,k2_relat_1(sK0))),X0),sK0) | ~v1_relat_1(sK0)) ) | spl9_1),
% 0.19/0.51    inference(duplicate_literal_removal,[],[f78])).
% 0.19/0.51  fof(f78,plain,(
% 0.19/0.51    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK0)) | ~r2_hidden(k4_tarski(sK1(sK0,k10_relat_1(sK0,k2_relat_1(sK0))),X0),sK0) | ~r2_hidden(X0,k2_relat_1(sK0)) | ~v1_relat_1(sK0)) ) | spl9_1),
% 0.19/0.51    inference(resolution,[],[f59,f39])).
% 0.19/0.51  fof(f39,plain,(
% 0.19/0.51    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k10_relat_1(X2,X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f25])).
% 0.19/0.51  fof(f59,plain,(
% 0.19/0.51    ~r2_hidden(sK1(sK0,k10_relat_1(sK0,k2_relat_1(sK0))),k10_relat_1(sK0,k2_relat_1(sK0))) | spl9_1),
% 0.19/0.51    inference(avatar_component_clause,[],[f58])).
% 0.19/0.51  fof(f69,plain,(
% 0.19/0.51    ~spl9_1 | spl9_3),
% 0.19/0.51    inference(avatar_split_clause,[],[f56,f67,f58])).
% 0.19/0.51  fof(f56,plain,(
% 0.19/0.51    ( ! [X0] : (~r2_hidden(k4_tarski(sK1(sK0,k10_relat_1(sK0,k2_relat_1(sK0))),X0),sK0) | ~r2_hidden(sK1(sK0,k10_relat_1(sK0,k2_relat_1(sK0))),k10_relat_1(sK0,k2_relat_1(sK0)))) )),
% 0.19/0.51    inference(resolution,[],[f45,f46])).
% 0.19/0.51  fof(f46,plain,(
% 0.19/0.51    ( ! [X0,X3,X1] : (sQ8_eqProxy(k1_relat_1(X0),X1) | ~r2_hidden(k4_tarski(sK1(X0,X1),X3),X0) | ~r2_hidden(sK1(X0,X1),X1)) )),
% 0.19/0.51    inference(equality_proxy_replacement,[],[f31,f44])).
% 0.19/0.51  fof(f44,plain,(
% 0.19/0.51    ! [X1,X0] : (sQ8_eqProxy(X0,X1) <=> X0 = X1)),
% 0.19/0.51    introduced(equality_proxy_definition,[new_symbols(naming,[sQ8_eqProxy])])).
% 0.19/0.51  fof(f31,plain,(
% 0.19/0.51    ( ! [X0,X3,X1] : (k1_relat_1(X0) = X1 | ~r2_hidden(k4_tarski(sK1(X0,X1),X3),X0) | ~r2_hidden(sK1(X0,X1),X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f15])).
% 0.19/0.51  fof(f15,plain,(
% 0.19/0.51    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK1(X0,X1),X3),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.19/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f11,f14,f13,f12])).
% 0.19/0.51  fof(f12,plain,(
% 0.19/0.51    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK1(X0,X1),X3),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK1(X0,X1),X4),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 0.19/0.51    introduced(choice_axiom,[])).
% 0.19/0.51  fof(f13,plain,(
% 0.19/0.51    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK1(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0))),
% 0.19/0.51    introduced(choice_axiom,[])).
% 0.19/0.51  fof(f14,plain,(
% 0.19/0.51    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0))),
% 0.19/0.51    introduced(choice_axiom,[])).
% 0.19/0.51  fof(f11,plain,(
% 0.19/0.51    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.19/0.51    inference(rectify,[],[f10])).
% 0.19/0.51  fof(f10,plain,(
% 0.19/0.51    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 0.19/0.51    inference(nnf_transformation,[],[f1])).
% 0.19/0.51  fof(f1,axiom,(
% 0.19/0.51    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 0.19/0.51  fof(f45,plain,(
% 0.19/0.51    ~sQ8_eqProxy(k1_relat_1(sK0),k10_relat_1(sK0,k2_relat_1(sK0)))),
% 0.19/0.51    inference(equality_proxy_replacement,[],[f27,f44])).
% 0.19/0.51  fof(f27,plain,(
% 0.19/0.51    k1_relat_1(sK0) != k10_relat_1(sK0,k2_relat_1(sK0))),
% 0.19/0.51    inference(cnf_transformation,[],[f9])).
% 0.19/0.51  fof(f65,plain,(
% 0.19/0.51    spl9_1 | spl9_2),
% 0.19/0.51    inference(avatar_split_clause,[],[f55,f62,f58])).
% 0.19/0.51  fof(f55,plain,(
% 0.19/0.51    r2_hidden(k4_tarski(sK1(sK0,k10_relat_1(sK0,k2_relat_1(sK0))),sK2(sK0,k10_relat_1(sK0,k2_relat_1(sK0)))),sK0) | r2_hidden(sK1(sK0,k10_relat_1(sK0,k2_relat_1(sK0))),k10_relat_1(sK0,k2_relat_1(sK0)))),
% 0.19/0.51    inference(resolution,[],[f45,f47])).
% 0.19/0.51  fof(f47,plain,(
% 0.19/0.51    ( ! [X0,X1] : (sQ8_eqProxy(k1_relat_1(X0),X1) | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1)) )),
% 0.19/0.51    inference(equality_proxy_replacement,[],[f30,f44])).
% 0.19/0.51  fof(f30,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k1_relat_1(X0) = X1 | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f15])).
% 0.19/0.51  % SZS output end Proof for theBenchmark
% 0.19/0.51  % (24073)------------------------------
% 0.19/0.51  % (24073)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (24073)Termination reason: Refutation
% 0.19/0.51  
% 0.19/0.51  % (24073)Memory used [KB]: 6140
% 0.19/0.51  % (24073)Time elapsed: 0.087 s
% 0.19/0.51  % (24073)------------------------------
% 0.19/0.51  % (24073)------------------------------
% 0.19/0.51  % (24060)Success in time 0.155 s
%------------------------------------------------------------------------------
