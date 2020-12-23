%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:39 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 135 expanded)
%              Number of leaves         :   16 (  48 expanded)
%              Depth                    :   11
%              Number of atoms          :  269 ( 670 expanded)
%              Number of equality atoms :  100 ( 256 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f773,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f100,f101,f102,f142,f458,f462,f544,f770,f771,f772])).

fof(f772,plain,
    ( sK1 != sK3(k1_enumset1(sK0,sK0,sK1),sK2)
    | ~ r2_hidden(sK1,sK2)
    | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f771,plain,
    ( sK0 != sK3(k1_enumset1(sK0,sK0,sK1),sK2)
    | ~ r2_hidden(sK0,sK2)
    | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f770,plain,
    ( spl6_36
    | spl6_37
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f756,f144,f767,f763])).

fof(f763,plain,
    ( spl6_36
  <=> sK0 = sK3(k1_enumset1(sK0,sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f767,plain,
    ( spl6_37
  <=> sK1 = sK3(k1_enumset1(sK0,sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f144,plain,
    ( spl6_7
  <=> r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2),k1_enumset1(sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f756,plain,
    ( sK1 = sK3(k1_enumset1(sK0,sK0,sK1),sK2)
    | sK0 = sK3(k1_enumset1(sK0,sK0,sK1),sK2)
    | ~ spl6_7 ),
    inference(duplicate_literal_removal,[],[f749])).

fof(f749,plain,
    ( sK1 = sK3(k1_enumset1(sK0,sK0,sK1),sK2)
    | sK0 = sK3(k1_enumset1(sK0,sK0,sK1),sK2)
    | sK0 = sK3(k1_enumset1(sK0,sK0,sK1),sK2)
    | ~ spl6_7 ),
    inference(resolution,[],[f146,f87])).

fof(f87,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k1_enumset1(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK5(X0,X1,X2,X3) != X2
              & sK5(X0,X1,X2,X3) != X1
              & sK5(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK5(X0,X1,X2,X3),X3) )
          & ( sK5(X0,X1,X2,X3) = X2
            | sK5(X0,X1,X2,X3) = X1
            | sK5(X0,X1,X2,X3) = X0
            | r2_hidden(sK5(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f39,f40])).

fof(f40,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK5(X0,X1,X2,X3) != X2
            & sK5(X0,X1,X2,X3) != X1
            & sK5(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK5(X0,X1,X2,X3),X3) )
        & ( sK5(X0,X1,X2,X3) = X2
          | sK5(X0,X1,X2,X3) = X1
          | sK5(X0,X1,X2,X3) = X0
          | r2_hidden(sK5(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f146,plain,
    ( r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2),k1_enumset1(sK0,sK0,sK1))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f144])).

fof(f544,plain,
    ( spl6_7
    | spl6_1 ),
    inference(avatar_split_clause,[],[f534,f89,f144])).

fof(f89,plain,
    ( spl6_1
  <=> r1_tarski(k1_enumset1(sK0,sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f534,plain,
    ( r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2),k1_enumset1(sK0,sK0,sK1))
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f91,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
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

fof(f91,plain,
    ( ~ r1_tarski(k1_enumset1(sK0,sK0,sK1),sK2)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f89])).

fof(f462,plain,
    ( spl6_3
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f436,f89,f97])).

fof(f97,plain,
    ( spl6_3
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f436,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl6_1 ),
    inference(unit_resulting_resolution,[],[f82,f90,f51])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f90,plain,
    ( r1_tarski(k1_enumset1(sK0,sK0,sK1),sK2)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f89])).

fof(f82,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k1_enumset1(X0,X1,X5)) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f458,plain,
    ( spl6_2
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f439,f89,f93])).

fof(f93,plain,
    ( spl6_2
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f439,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl6_1 ),
    inference(unit_resulting_resolution,[],[f86,f90,f51])).

fof(f86,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k1_enumset1(X5,X1,X2)) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f142,plain,
    ( ~ spl6_6
    | spl6_1 ),
    inference(avatar_split_clause,[],[f129,f89,f139])).

fof(f139,plain,
    ( spl6_6
  <=> r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f129,plain,
    ( ~ r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2),sK2)
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f91,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f102,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f73,f93,f89])).

fof(f73,plain,
    ( r2_hidden(sK0,sK2)
    | r1_tarski(k1_enumset1(sK0,sK0,sK1),sK2) ),
    inference(definition_unfolding,[],[f42,f46])).

fof(f46,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f42,plain,
    ( r2_hidden(sK0,sK2)
    | r1_tarski(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f25])).

% (16446)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% (16444)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% (16452)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% (16459)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% (16450)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% (16451)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
fof(f25,plain,
    ( ( ~ r2_hidden(sK1,sK2)
      | ~ r2_hidden(sK0,sK2)
      | ~ r1_tarski(k2_tarski(sK0,sK1),sK2) )
    & ( ( r2_hidden(sK1,sK2)
        & r2_hidden(sK0,sK2) )
      | r1_tarski(k2_tarski(sK0,sK1),sK2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(X1,X2)
          | ~ r2_hidden(X0,X2)
          | ~ r1_tarski(k2_tarski(X0,X1),X2) )
        & ( ( r2_hidden(X1,X2)
            & r2_hidden(X0,X2) )
          | r1_tarski(k2_tarski(X0,X1),X2) ) )
   => ( ( ~ r2_hidden(sK1,sK2)
        | ~ r2_hidden(sK0,sK2)
        | ~ r1_tarski(k2_tarski(sK0,sK1),sK2) )
      & ( ( r2_hidden(sK1,sK2)
          & r2_hidden(sK0,sK2) )
        | r1_tarski(k2_tarski(sK0,sK1),sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | ~ r1_tarski(k2_tarski(X0,X1),X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | ~ r1_tarski(k2_tarski(X0,X1),X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <~> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_tarski(X0,X1),X2)
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f101,plain,
    ( spl6_1
    | spl6_3 ),
    inference(avatar_split_clause,[],[f72,f97,f89])).

fof(f72,plain,
    ( r2_hidden(sK1,sK2)
    | r1_tarski(k1_enumset1(sK0,sK0,sK1),sK2) ),
    inference(definition_unfolding,[],[f43,f46])).

fof(f43,plain,
    ( r2_hidden(sK1,sK2)
    | r1_tarski(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f100,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f71,f97,f93,f89])).

fof(f71,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK0,sK2)
    | ~ r1_tarski(k1_enumset1(sK0,sK0,sK1),sK2) ),
    inference(definition_unfolding,[],[f44,f46])).

fof(f44,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK0,sK2)
    | ~ r1_tarski(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:13:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (16443)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.47  % (16449)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.49  % (16465)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.50  % (16457)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.50  % (16440)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.50  % (16469)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.50  % (16461)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.51  % (16453)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.51  % (16442)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (16445)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (16462)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.51  % (16465)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f773,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f100,f101,f102,f142,f458,f462,f544,f770,f771,f772])).
% 0.20/0.51  fof(f772,plain,(
% 0.20/0.51    sK1 != sK3(k1_enumset1(sK0,sK0,sK1),sK2) | ~r2_hidden(sK1,sK2) | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2),sK2)),
% 0.20/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.51  fof(f771,plain,(
% 0.20/0.51    sK0 != sK3(k1_enumset1(sK0,sK0,sK1),sK2) | ~r2_hidden(sK0,sK2) | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2),sK2)),
% 0.20/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.51  fof(f770,plain,(
% 0.20/0.51    spl6_36 | spl6_37 | ~spl6_7),
% 0.20/0.51    inference(avatar_split_clause,[],[f756,f144,f767,f763])).
% 0.20/0.51  fof(f763,plain,(
% 0.20/0.51    spl6_36 <=> sK0 = sK3(k1_enumset1(sK0,sK0,sK1),sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).
% 0.20/0.51  fof(f767,plain,(
% 0.20/0.51    spl6_37 <=> sK1 = sK3(k1_enumset1(sK0,sK0,sK1),sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).
% 0.20/0.51  fof(f144,plain,(
% 0.20/0.51    spl6_7 <=> r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2),k1_enumset1(sK0,sK0,sK1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.20/0.51  fof(f756,plain,(
% 0.20/0.51    sK1 = sK3(k1_enumset1(sK0,sK0,sK1),sK2) | sK0 = sK3(k1_enumset1(sK0,sK0,sK1),sK2) | ~spl6_7),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f749])).
% 0.20/0.51  fof(f749,plain,(
% 0.20/0.51    sK1 = sK3(k1_enumset1(sK0,sK0,sK1),sK2) | sK0 = sK3(k1_enumset1(sK0,sK0,sK1),sK2) | sK0 = sK3(k1_enumset1(sK0,sK0,sK1),sK2) | ~spl6_7),
% 0.20/0.51    inference(resolution,[],[f146,f87])).
% 0.20/0.51  fof(f87,plain,(
% 0.20/0.51    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k1_enumset1(X0,X1,X2))) )),
% 0.20/0.51    inference(equality_resolution,[],[f63])).
% 0.20/0.51  fof(f63,plain,(
% 0.20/0.51    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.20/0.51    inference(cnf_transformation,[],[f41])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK5(X0,X1,X2,X3) != X2 & sK5(X0,X1,X2,X3) != X1 & sK5(X0,X1,X2,X3) != X0) | ~r2_hidden(sK5(X0,X1,X2,X3),X3)) & (sK5(X0,X1,X2,X3) = X2 | sK5(X0,X1,X2,X3) = X1 | sK5(X0,X1,X2,X3) = X0 | r2_hidden(sK5(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f39,f40])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK5(X0,X1,X2,X3) != X2 & sK5(X0,X1,X2,X3) != X1 & sK5(X0,X1,X2,X3) != X0) | ~r2_hidden(sK5(X0,X1,X2,X3),X3)) & (sK5(X0,X1,X2,X3) = X2 | sK5(X0,X1,X2,X3) = X1 | sK5(X0,X1,X2,X3) = X0 | r2_hidden(sK5(X0,X1,X2,X3),X3))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.20/0.51    inference(rectify,[],[f38])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.20/0.51    inference(flattening,[],[f37])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.20/0.51    inference(nnf_transformation,[],[f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 0.20/0.51  fof(f146,plain,(
% 0.20/0.51    r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2),k1_enumset1(sK0,sK0,sK1)) | ~spl6_7),
% 0.20/0.51    inference(avatar_component_clause,[],[f144])).
% 0.20/0.51  fof(f544,plain,(
% 0.20/0.51    spl6_7 | spl6_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f534,f89,f144])).
% 0.20/0.51  fof(f89,plain,(
% 0.20/0.51    spl6_1 <=> r1_tarski(k1_enumset1(sK0,sK0,sK1),sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.51  fof(f534,plain,(
% 0.20/0.51    r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2),k1_enumset1(sK0,sK0,sK1)) | spl6_1),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f91,f52])).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f31])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.51    inference(rectify,[],[f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.51    inference(nnf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.51  fof(f91,plain,(
% 0.20/0.51    ~r1_tarski(k1_enumset1(sK0,sK0,sK1),sK2) | spl6_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f89])).
% 0.20/0.51  fof(f462,plain,(
% 0.20/0.51    spl6_3 | ~spl6_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f436,f89,f97])).
% 0.20/0.51  fof(f97,plain,(
% 0.20/0.51    spl6_3 <=> r2_hidden(sK1,sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.20/0.51  fof(f436,plain,(
% 0.20/0.51    r2_hidden(sK1,sK2) | ~spl6_1),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f82,f90,f51])).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f31])).
% 0.20/0.51  fof(f90,plain,(
% 0.20/0.51    r1_tarski(k1_enumset1(sK0,sK0,sK1),sK2) | ~spl6_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f89])).
% 0.20/0.51  fof(f82,plain,(
% 0.20/0.51    ( ! [X0,X5,X1] : (r2_hidden(X5,k1_enumset1(X0,X1,X5))) )),
% 0.20/0.51    inference(equality_resolution,[],[f81])).
% 0.20/0.51  fof(f81,plain,(
% 0.20/0.51    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k1_enumset1(X0,X1,X5) != X3) )),
% 0.20/0.51    inference(equality_resolution,[],[f66])).
% 0.20/0.51  fof(f66,plain,(
% 0.20/0.51    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 0.20/0.51    inference(cnf_transformation,[],[f41])).
% 0.20/0.51  fof(f458,plain,(
% 0.20/0.51    spl6_2 | ~spl6_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f439,f89,f93])).
% 0.20/0.51  fof(f93,plain,(
% 0.20/0.51    spl6_2 <=> r2_hidden(sK0,sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.51  fof(f439,plain,(
% 0.20/0.51    r2_hidden(sK0,sK2) | ~spl6_1),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f86,f90,f51])).
% 0.20/0.51  fof(f86,plain,(
% 0.20/0.51    ( ! [X2,X5,X1] : (r2_hidden(X5,k1_enumset1(X5,X1,X2))) )),
% 0.20/0.51    inference(equality_resolution,[],[f85])).
% 0.20/0.51  fof(f85,plain,(
% 0.20/0.51    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k1_enumset1(X5,X1,X2) != X3) )),
% 0.20/0.51    inference(equality_resolution,[],[f64])).
% 0.20/0.51  fof(f64,plain,(
% 0.20/0.51    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 0.20/0.51    inference(cnf_transformation,[],[f41])).
% 0.20/0.51  fof(f142,plain,(
% 0.20/0.51    ~spl6_6 | spl6_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f129,f89,f139])).
% 0.20/0.51  fof(f139,plain,(
% 0.20/0.51    spl6_6 <=> r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2),sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.20/0.51  fof(f129,plain,(
% 0.20/0.51    ~r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2),sK2) | spl6_1),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f91,f53])).
% 0.20/0.51  fof(f53,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK3(X0,X1),X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f31])).
% 0.20/0.51  fof(f102,plain,(
% 0.20/0.51    spl6_1 | spl6_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f73,f93,f89])).
% 0.20/0.51  fof(f73,plain,(
% 0.20/0.51    r2_hidden(sK0,sK2) | r1_tarski(k1_enumset1(sK0,sK0,sK1),sK2)),
% 0.20/0.51    inference(definition_unfolding,[],[f42,f46])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    r2_hidden(sK0,sK2) | r1_tarski(k2_tarski(sK0,sK1),sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f25])).
% 0.20/0.51  % (16446)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (16444)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (16452)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (16459)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.53  % (16450)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.53  % (16451)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    (~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | ~r1_tarski(k2_tarski(sK0,sK1),sK2)) & ((r2_hidden(sK1,sK2) & r2_hidden(sK0,sK2)) | r1_tarski(k2_tarski(sK0,sK1),sK2))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f24])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ? [X0,X1,X2] : ((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | r1_tarski(k2_tarski(X0,X1),X2))) => ((~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | ~r1_tarski(k2_tarski(sK0,sK1),sK2)) & ((r2_hidden(sK1,sK2) & r2_hidden(sK0,sK2)) | r1_tarski(k2_tarski(sK0,sK1),sK2)))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    ? [X0,X1,X2] : ((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.20/0.53    inference(flattening,[],[f22])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ? [X0,X1,X2] : (((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.20/0.53    inference(nnf_transformation,[],[f14])).
% 0.20/0.53  fof(f14,plain,(
% 0.20/0.53    ? [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <~> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.20/0.53    inference(ennf_transformation,[],[f13])).
% 0.20/0.53  fof(f13,negated_conjecture,(
% 0.20/0.53    ~! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.20/0.53    inference(negated_conjecture,[],[f12])).
% 0.20/0.53  fof(f12,conjecture,(
% 0.20/0.53    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.20/0.53  fof(f101,plain,(
% 0.20/0.53    spl6_1 | spl6_3),
% 0.20/0.53    inference(avatar_split_clause,[],[f72,f97,f89])).
% 0.20/0.53  fof(f72,plain,(
% 0.20/0.53    r2_hidden(sK1,sK2) | r1_tarski(k1_enumset1(sK0,sK0,sK1),sK2)),
% 0.20/0.53    inference(definition_unfolding,[],[f43,f46])).
% 0.20/0.53  fof(f43,plain,(
% 0.20/0.53    r2_hidden(sK1,sK2) | r1_tarski(k2_tarski(sK0,sK1),sK2)),
% 0.20/0.53    inference(cnf_transformation,[],[f25])).
% 0.20/0.53  fof(f100,plain,(
% 0.20/0.53    ~spl6_1 | ~spl6_2 | ~spl6_3),
% 0.20/0.53    inference(avatar_split_clause,[],[f71,f97,f93,f89])).
% 0.20/0.53  fof(f71,plain,(
% 0.20/0.53    ~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | ~r1_tarski(k1_enumset1(sK0,sK0,sK1),sK2)),
% 0.20/0.53    inference(definition_unfolding,[],[f44,f46])).
% 0.20/0.53  fof(f44,plain,(
% 0.20/0.53    ~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | ~r1_tarski(k2_tarski(sK0,sK1),sK2)),
% 0.20/0.53    inference(cnf_transformation,[],[f25])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (16465)------------------------------
% 0.20/0.53  % (16465)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (16465)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (16465)Memory used [KB]: 6524
% 0.20/0.53  % (16465)Time elapsed: 0.130 s
% 0.20/0.53  % (16465)------------------------------
% 0.20/0.53  % (16465)------------------------------
% 0.20/0.54  % (16439)Success in time 0.176 s
%------------------------------------------------------------------------------
