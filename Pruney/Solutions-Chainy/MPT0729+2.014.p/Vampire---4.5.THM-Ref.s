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
% DateTime   : Thu Dec  3 12:55:12 EST 2020

% Result     : Theorem 1.23s
% Output     : Refutation 1.35s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 231 expanded)
%              Number of leaves         :   17 (  75 expanded)
%              Depth                    :   12
%              Number of atoms          :  308 ( 688 expanded)
%              Number of equality atoms :  157 ( 430 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f199,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f122,f135,f154,f155,f197])).

fof(f197,plain,(
    ~ spl4_1 ),
    inference(avatar_contradiction_clause,[],[f187])).

fof(f187,plain,
    ( $false
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f28,f177])).

fof(f177,plain,
    ( sK0 = sK1
    | ~ spl4_1 ),
    inference(duplicate_literal_removal,[],[f175])).

fof(f175,plain,
    ( sK0 = sK1
    | sK0 = sK1
    | sK0 = sK1
    | sK0 = sK1
    | ~ spl4_1 ),
    inference(resolution,[],[f84,f75])).

fof(f75,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( ~ r2_hidden(X6,k2_enumset1(X0,X1,X2,X3))
      | X2 = X6
      | X1 = X6
      | X0 = X6
      | X3 = X6 ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( X3 = X6
      | X2 = X6
      | X1 = X6
      | X0 = X6
      | ~ r2_hidden(X6,X4)
      | k2_enumset1(X0,X1,X2,X3) != X4 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_enumset1(X0,X1,X2,X3) = X4
        | ( ( ( sK3(X0,X1,X2,X3,X4) != X3
              & sK3(X0,X1,X2,X3,X4) != X2
              & sK3(X0,X1,X2,X3,X4) != X1
              & sK3(X0,X1,X2,X3,X4) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2,X3,X4),X4) )
          & ( sK3(X0,X1,X2,X3,X4) = X3
            | sK3(X0,X1,X2,X3,X4) = X2
            | sK3(X0,X1,X2,X3,X4) = X1
            | sK3(X0,X1,X2,X3,X4) = X0
            | r2_hidden(sK3(X0,X1,X2,X3,X4),X4) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X4)
              | ( X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 ) )
            & ( X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | ~ r2_hidden(X6,X4) ) )
        | k2_enumset1(X0,X1,X2,X3) != X4 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f25])).

% (5974)Refutation not found, incomplete strategy% (5974)------------------------------
% (5974)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f25,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( ( ( X3 != X5
              & X2 != X5
              & X1 != X5
              & X0 != X5 )
            | ~ r2_hidden(X5,X4) )
          & ( X3 = X5
            | X2 = X5
            | X1 = X5
            | X0 = X5
            | r2_hidden(X5,X4) ) )
     => ( ( ( sK3(X0,X1,X2,X3,X4) != X3
            & sK3(X0,X1,X2,X3,X4) != X2
            & sK3(X0,X1,X2,X3,X4) != X1
            & sK3(X0,X1,X2,X3,X4) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2,X3,X4),X4) )
        & ( sK3(X0,X1,X2,X3,X4) = X3
          | sK3(X0,X1,X2,X3,X4) = X2
          | sK3(X0,X1,X2,X3,X4) = X1
          | sK3(X0,X1,X2,X3,X4) = X0
          | r2_hidden(sK3(X0,X1,X2,X3,X4),X4) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_enumset1(X0,X1,X2,X3) = X4
        | ? [X5] :
            ( ( ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 )
              | ~ r2_hidden(X5,X4) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X4)
              | ( X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 ) )
            & ( X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | ~ r2_hidden(X6,X4) ) )
        | k2_enumset1(X0,X1,X2,X3) != X4 ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_enumset1(X0,X1,X2,X3) = X4
        | ? [X5] :
            ( ( ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 )
              | ~ r2_hidden(X5,X4) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X4)
              | ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X4) ) )
        | k2_enumset1(X0,X1,X2,X3) != X4 ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_enumset1(X0,X1,X2,X3) = X4
        | ? [X5] :
            ( ( ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 )
              | ~ r2_hidden(X5,X4) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X4)
              | ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X4) ) )
        | k2_enumset1(X0,X1,X2,X3) != X4 ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ( X3 = X5
            | X2 = X5
            | X1 = X5
            | X0 = X5 ) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X3 != X5
              & X2 != X5
              & X1 != X5
              & X0 != X5 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_enumset1)).

fof(f84,plain,
    ( r2_hidden(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f83])).

% (5980)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
fof(f83,plain,
    ( spl4_1
  <=> r2_hidden(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f28,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( sK0 != sK1
    & k1_ordinal1(sK0) = k1_ordinal1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f15])).

fof(f15,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_ordinal1(X0) = k1_ordinal1(X1) )
   => ( sK0 != sK1
      & k1_ordinal1(sK0) = k1_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_ordinal1(X0) = k1_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

% (5985)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_ordinal1(X0) = k1_ordinal1(X1)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( k1_ordinal1(X0) = k1_ordinal1(X1)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_ordinal1)).

fof(f155,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f142,f86,f83])).

fof(f86,plain,
    ( spl4_2
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f142,plain,
    ( r2_hidden(sK1,sK0)
    | r2_hidden(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(resolution,[],[f76,f66])).

fof(f66,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_tarski(k2_enumset1(X0,X0,X0,X1)))
      | r2_hidden(X4,X0)
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_tarski(k2_enumset1(X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f36,f53])).

fof(f53,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f32,f52])).

fof(f52,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f33,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f33,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & ~ r2_hidden(sK2(X0,X1,X2),X0) )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( r2_hidden(sK2(X0,X1,X2),X1)
            | r2_hidden(sK2(X0,X1,X2),X0)
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f20])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & ~ r2_hidden(sK2(X0,X1,X2),X0) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( r2_hidden(sK2(X0,X1,X2),X1)
          | r2_hidden(sK2(X0,X1,X2),X0)
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f76,plain,(
    r2_hidden(sK1,k3_tarski(k2_enumset1(sK0,sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK0)))) ),
    inference(superposition,[],[f57,f56])).

fof(f56,plain,(
    k3_tarski(k2_enumset1(sK0,sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK0))) = k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f27,f55,f55])).

fof(f55,plain,(
    ! [X0] : k1_ordinal1(X0) = k3_tarski(k2_enumset1(X0,X0,X0,k2_enumset1(X0,X0,X0,X0))) ),
    inference(definition_unfolding,[],[f31,f53,f54])).

fof(f54,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f30,f52])).

fof(f30,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f31,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f27,plain,(
    k1_ordinal1(sK0) = k1_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f57,plain,(
    ! [X0] : r2_hidden(X0,k3_tarski(k2_enumset1(X0,X0,X0,k2_enumset1(X0,X0,X0,X0)))) ),
    inference(definition_unfolding,[],[f29,f55])).

fof(f29,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

fof(f154,plain,
    ( ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f153])).

fof(f153,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f121,f97])).

fof(f97,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ spl4_2 ),
    inference(resolution,[],[f87,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f87,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f86])).

fof(f121,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl4_4
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f135,plain,(
    ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f126])).

fof(f126,plain,
    ( $false
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f28,f125])).

% (5985)Refutation not found, incomplete strategy% (5985)------------------------------
% (5985)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (5985)Termination reason: Refutation not found, incomplete strategy

% (5985)Memory used [KB]: 10618
% (5985)Time elapsed: 0.130 s
% (5985)------------------------------
% (5985)------------------------------
fof(f125,plain,
    ( sK0 = sK1
    | ~ spl4_3 ),
    inference(duplicate_literal_removal,[],[f123])).

fof(f123,plain,
    ( sK0 = sK1
    | sK0 = sK1
    | sK0 = sK1
    | sK0 = sK1
    | ~ spl4_3 ),
    inference(resolution,[],[f118,f75])).

fof(f118,plain,
    ( r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl4_3
  <=> r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f122,plain,
    ( spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f108,f120,f117])).

fof(f108,plain,
    ( r2_hidden(sK0,sK1)
    | r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(resolution,[],[f77,f57])).

fof(f77,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_tarski(k2_enumset1(sK0,sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK0))))
      | r2_hidden(X0,sK1)
      | r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1)) ) ),
    inference(superposition,[],[f66,f56])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:43:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.50  % (5976)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (5977)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (5978)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.23/0.51  % (6001)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.23/0.52  % (5993)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.23/0.52  % (5976)Refutation found. Thanks to Tanya!
% 1.23/0.52  % SZS status Theorem for theBenchmark
% 1.23/0.52  % (5986)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.23/0.52  % (5975)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.23/0.52  % (5984)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.23/0.52  % (5974)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.23/0.52  % SZS output start Proof for theBenchmark
% 1.23/0.53  fof(f199,plain,(
% 1.23/0.53    $false),
% 1.23/0.53    inference(avatar_sat_refutation,[],[f122,f135,f154,f155,f197])).
% 1.23/0.53  fof(f197,plain,(
% 1.23/0.53    ~spl4_1),
% 1.23/0.53    inference(avatar_contradiction_clause,[],[f187])).
% 1.23/0.53  fof(f187,plain,(
% 1.23/0.53    $false | ~spl4_1),
% 1.23/0.53    inference(subsumption_resolution,[],[f28,f177])).
% 1.23/0.53  fof(f177,plain,(
% 1.23/0.53    sK0 = sK1 | ~spl4_1),
% 1.23/0.53    inference(duplicate_literal_removal,[],[f175])).
% 1.23/0.53  fof(f175,plain,(
% 1.23/0.53    sK0 = sK1 | sK0 = sK1 | sK0 = sK1 | sK0 = sK1 | ~spl4_1),
% 1.23/0.53    inference(resolution,[],[f84,f75])).
% 1.23/0.53  fof(f75,plain,(
% 1.23/0.53    ( ! [X6,X2,X0,X3,X1] : (~r2_hidden(X6,k2_enumset1(X0,X1,X2,X3)) | X2 = X6 | X1 = X6 | X0 = X6 | X3 = X6) )),
% 1.23/0.53    inference(equality_resolution,[],[f42])).
% 1.23/0.53  fof(f42,plain,(
% 1.23/0.53    ( ! [X6,X4,X2,X0,X3,X1] : (X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | ~r2_hidden(X6,X4) | k2_enumset1(X0,X1,X2,X3) != X4) )),
% 1.23/0.53    inference(cnf_transformation,[],[f26])).
% 1.23/0.53  fof(f26,plain,(
% 1.23/0.53    ! [X0,X1,X2,X3,X4] : ((k2_enumset1(X0,X1,X2,X3) = X4 | (((sK3(X0,X1,X2,X3,X4) != X3 & sK3(X0,X1,X2,X3,X4) != X2 & sK3(X0,X1,X2,X3,X4) != X1 & sK3(X0,X1,X2,X3,X4) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3,X4),X4)) & (sK3(X0,X1,X2,X3,X4) = X3 | sK3(X0,X1,X2,X3,X4) = X2 | sK3(X0,X1,X2,X3,X4) = X1 | sK3(X0,X1,X2,X3,X4) = X0 | r2_hidden(sK3(X0,X1,X2,X3,X4),X4)))) & (! [X6] : ((r2_hidden(X6,X4) | (X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)) & (X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | ~r2_hidden(X6,X4))) | k2_enumset1(X0,X1,X2,X3) != X4))),
% 1.23/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f25])).
% 1.23/0.53  % (5974)Refutation not found, incomplete strategy% (5974)------------------------------
% 1.23/0.53  % (5974)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.53  fof(f25,plain,(
% 1.23/0.53    ! [X4,X3,X2,X1,X0] : (? [X5] : (((X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5) | ~r2_hidden(X5,X4)) & (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5 | r2_hidden(X5,X4))) => (((sK3(X0,X1,X2,X3,X4) != X3 & sK3(X0,X1,X2,X3,X4) != X2 & sK3(X0,X1,X2,X3,X4) != X1 & sK3(X0,X1,X2,X3,X4) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3,X4),X4)) & (sK3(X0,X1,X2,X3,X4) = X3 | sK3(X0,X1,X2,X3,X4) = X2 | sK3(X0,X1,X2,X3,X4) = X1 | sK3(X0,X1,X2,X3,X4) = X0 | r2_hidden(sK3(X0,X1,X2,X3,X4),X4))))),
% 1.23/0.53    introduced(choice_axiom,[])).
% 1.23/0.53  fof(f24,plain,(
% 1.23/0.53    ! [X0,X1,X2,X3,X4] : ((k2_enumset1(X0,X1,X2,X3) = X4 | ? [X5] : (((X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5) | ~r2_hidden(X5,X4)) & (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5 | r2_hidden(X5,X4)))) & (! [X6] : ((r2_hidden(X6,X4) | (X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)) & (X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | ~r2_hidden(X6,X4))) | k2_enumset1(X0,X1,X2,X3) != X4))),
% 1.23/0.53    inference(rectify,[],[f23])).
% 1.23/0.53  fof(f23,plain,(
% 1.23/0.53    ! [X0,X1,X2,X3,X4] : ((k2_enumset1(X0,X1,X2,X3) = X4 | ? [X5] : (((X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5) | ~r2_hidden(X5,X4)) & (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5 | r2_hidden(X5,X4)))) & (! [X5] : ((r2_hidden(X5,X4) | (X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)) & (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X4))) | k2_enumset1(X0,X1,X2,X3) != X4))),
% 1.23/0.53    inference(flattening,[],[f22])).
% 1.23/0.53  fof(f22,plain,(
% 1.23/0.53    ! [X0,X1,X2,X3,X4] : ((k2_enumset1(X0,X1,X2,X3) = X4 | ? [X5] : (((X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5) | ~r2_hidden(X5,X4)) & ((X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5) | r2_hidden(X5,X4)))) & (! [X5] : ((r2_hidden(X5,X4) | (X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)) & ((X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5) | ~r2_hidden(X5,X4))) | k2_enumset1(X0,X1,X2,X3) != X4))),
% 1.23/0.53    inference(nnf_transformation,[],[f14])).
% 1.23/0.53  fof(f14,plain,(
% 1.23/0.53    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> ! [X5] : (r2_hidden(X5,X4) <=> (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5)))),
% 1.23/0.53    inference(ennf_transformation,[],[f7])).
% 1.23/0.53  fof(f7,axiom,(
% 1.23/0.53    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> ! [X5] : (r2_hidden(X5,X4) <=> ~(X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)))),
% 1.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_enumset1)).
% 1.23/0.53  fof(f84,plain,(
% 1.23/0.53    r2_hidden(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl4_1),
% 1.23/0.53    inference(avatar_component_clause,[],[f83])).
% 1.35/0.53  % (5980)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.35/0.53  fof(f83,plain,(
% 1.35/0.53    spl4_1 <=> r2_hidden(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.35/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.35/0.53  fof(f28,plain,(
% 1.35/0.53    sK0 != sK1),
% 1.35/0.53    inference(cnf_transformation,[],[f16])).
% 1.35/0.53  fof(f16,plain,(
% 1.35/0.53    sK0 != sK1 & k1_ordinal1(sK0) = k1_ordinal1(sK1)),
% 1.35/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f15])).
% 1.35/0.53  fof(f15,plain,(
% 1.35/0.53    ? [X0,X1] : (X0 != X1 & k1_ordinal1(X0) = k1_ordinal1(X1)) => (sK0 != sK1 & k1_ordinal1(sK0) = k1_ordinal1(sK1))),
% 1.35/0.53    introduced(choice_axiom,[])).
% 1.35/0.53  fof(f12,plain,(
% 1.35/0.53    ? [X0,X1] : (X0 != X1 & k1_ordinal1(X0) = k1_ordinal1(X1))),
% 1.35/0.53    inference(ennf_transformation,[],[f11])).
% 1.35/0.53  % (5985)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.35/0.53  fof(f11,negated_conjecture,(
% 1.35/0.53    ~! [X0,X1] : (k1_ordinal1(X0) = k1_ordinal1(X1) => X0 = X1)),
% 1.35/0.53    inference(negated_conjecture,[],[f10])).
% 1.35/0.53  fof(f10,conjecture,(
% 1.35/0.53    ! [X0,X1] : (k1_ordinal1(X0) = k1_ordinal1(X1) => X0 = X1)),
% 1.35/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_ordinal1)).
% 1.35/0.53  fof(f155,plain,(
% 1.35/0.53    spl4_1 | spl4_2),
% 1.35/0.53    inference(avatar_split_clause,[],[f142,f86,f83])).
% 1.35/0.53  fof(f86,plain,(
% 1.35/0.53    spl4_2 <=> r2_hidden(sK1,sK0)),
% 1.35/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.35/0.53  fof(f142,plain,(
% 1.35/0.53    r2_hidden(sK1,sK0) | r2_hidden(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.35/0.53    inference(resolution,[],[f76,f66])).
% 1.35/0.53  fof(f66,plain,(
% 1.35/0.53    ( ! [X4,X0,X1] : (~r2_hidden(X4,k3_tarski(k2_enumset1(X0,X0,X0,X1))) | r2_hidden(X4,X0) | r2_hidden(X4,X1)) )),
% 1.35/0.53    inference(equality_resolution,[],[f63])).
% 1.35/0.53  fof(f63,plain,(
% 1.35/0.53    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_tarski(k2_enumset1(X0,X0,X0,X1)) != X2) )),
% 1.35/0.53    inference(definition_unfolding,[],[f36,f53])).
% 1.35/0.53  fof(f53,plain,(
% 1.35/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 1.35/0.53    inference(definition_unfolding,[],[f32,f52])).
% 1.35/0.53  fof(f52,plain,(
% 1.35/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.35/0.53    inference(definition_unfolding,[],[f33,f35])).
% 1.35/0.53  fof(f35,plain,(
% 1.35/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.35/0.53    inference(cnf_transformation,[],[f5])).
% 1.35/0.53  fof(f5,axiom,(
% 1.35/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.35/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.35/0.53  fof(f33,plain,(
% 1.35/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.35/0.53    inference(cnf_transformation,[],[f4])).
% 1.35/0.53  fof(f4,axiom,(
% 1.35/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.35/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.35/0.53  fof(f32,plain,(
% 1.35/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.35/0.53    inference(cnf_transformation,[],[f6])).
% 1.35/0.53  fof(f6,axiom,(
% 1.35/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.35/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.35/0.53  fof(f36,plain,(
% 1.35/0.53    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.35/0.53    inference(cnf_transformation,[],[f21])).
% 1.35/0.53  fof(f21,plain,(
% 1.35/0.53    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK2(X0,X1,X2),X1) & ~r2_hidden(sK2(X0,X1,X2),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.35/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f20])).
% 1.35/0.53  fof(f20,plain,(
% 1.35/0.53    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK2(X0,X1,X2),X1) & ~r2_hidden(sK2(X0,X1,X2),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 1.35/0.53    introduced(choice_axiom,[])).
% 1.35/0.53  fof(f19,plain,(
% 1.35/0.53    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.35/0.53    inference(rectify,[],[f18])).
% 1.35/0.53  fof(f18,plain,(
% 1.35/0.53    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.35/0.53    inference(flattening,[],[f17])).
% 1.35/0.53  fof(f17,plain,(
% 1.35/0.53    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.35/0.53    inference(nnf_transformation,[],[f2])).
% 1.35/0.53  fof(f2,axiom,(
% 1.35/0.53    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.35/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 1.35/0.53  fof(f76,plain,(
% 1.35/0.53    r2_hidden(sK1,k3_tarski(k2_enumset1(sK0,sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK0))))),
% 1.35/0.53    inference(superposition,[],[f57,f56])).
% 1.35/0.53  fof(f56,plain,(
% 1.35/0.53    k3_tarski(k2_enumset1(sK0,sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK0))) = k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK1,sK1,sK1,sK1)))),
% 1.35/0.53    inference(definition_unfolding,[],[f27,f55,f55])).
% 1.35/0.53  fof(f55,plain,(
% 1.35/0.53    ( ! [X0] : (k1_ordinal1(X0) = k3_tarski(k2_enumset1(X0,X0,X0,k2_enumset1(X0,X0,X0,X0)))) )),
% 1.35/0.53    inference(definition_unfolding,[],[f31,f53,f54])).
% 1.35/0.53  fof(f54,plain,(
% 1.35/0.53    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.35/0.53    inference(definition_unfolding,[],[f30,f52])).
% 1.35/0.53  fof(f30,plain,(
% 1.35/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.35/0.53    inference(cnf_transformation,[],[f3])).
% 1.35/0.53  fof(f3,axiom,(
% 1.35/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.35/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.35/0.53  fof(f31,plain,(
% 1.35/0.53    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 1.35/0.53    inference(cnf_transformation,[],[f8])).
% 1.35/0.53  fof(f8,axiom,(
% 1.35/0.53    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 1.35/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).
% 1.35/0.53  fof(f27,plain,(
% 1.35/0.53    k1_ordinal1(sK0) = k1_ordinal1(sK1)),
% 1.35/0.53    inference(cnf_transformation,[],[f16])).
% 1.35/0.53  fof(f57,plain,(
% 1.35/0.53    ( ! [X0] : (r2_hidden(X0,k3_tarski(k2_enumset1(X0,X0,X0,k2_enumset1(X0,X0,X0,X0))))) )),
% 1.35/0.53    inference(definition_unfolding,[],[f29,f55])).
% 1.35/0.53  fof(f29,plain,(
% 1.35/0.53    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 1.35/0.53    inference(cnf_transformation,[],[f9])).
% 1.35/0.53  fof(f9,axiom,(
% 1.35/0.53    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 1.35/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).
% 1.35/0.53  fof(f154,plain,(
% 1.35/0.53    ~spl4_2 | ~spl4_4),
% 1.35/0.53    inference(avatar_contradiction_clause,[],[f153])).
% 1.35/0.53  fof(f153,plain,(
% 1.35/0.53    $false | (~spl4_2 | ~spl4_4)),
% 1.35/0.53    inference(subsumption_resolution,[],[f121,f97])).
% 1.35/0.53  fof(f97,plain,(
% 1.35/0.53    ~r2_hidden(sK0,sK1) | ~spl4_2),
% 1.35/0.53    inference(resolution,[],[f87,f34])).
% 1.35/0.53  fof(f34,plain,(
% 1.35/0.53    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.35/0.53    inference(cnf_transformation,[],[f13])).
% 1.35/0.53  fof(f13,plain,(
% 1.35/0.53    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 1.35/0.53    inference(ennf_transformation,[],[f1])).
% 1.35/0.53  fof(f1,axiom,(
% 1.35/0.53    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 1.35/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 1.35/0.53  fof(f87,plain,(
% 1.35/0.53    r2_hidden(sK1,sK0) | ~spl4_2),
% 1.35/0.53    inference(avatar_component_clause,[],[f86])).
% 1.35/0.53  fof(f121,plain,(
% 1.35/0.53    r2_hidden(sK0,sK1) | ~spl4_4),
% 1.35/0.53    inference(avatar_component_clause,[],[f120])).
% 1.35/0.53  fof(f120,plain,(
% 1.35/0.53    spl4_4 <=> r2_hidden(sK0,sK1)),
% 1.35/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.35/0.53  fof(f135,plain,(
% 1.35/0.53    ~spl4_3),
% 1.35/0.53    inference(avatar_contradiction_clause,[],[f126])).
% 1.35/0.53  fof(f126,plain,(
% 1.35/0.53    $false | ~spl4_3),
% 1.35/0.53    inference(subsumption_resolution,[],[f28,f125])).
% 1.35/0.53  % (5985)Refutation not found, incomplete strategy% (5985)------------------------------
% 1.35/0.53  % (5985)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.53  % (5985)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.53  
% 1.35/0.53  % (5985)Memory used [KB]: 10618
% 1.35/0.53  % (5985)Time elapsed: 0.130 s
% 1.35/0.53  % (5985)------------------------------
% 1.35/0.53  % (5985)------------------------------
% 1.35/0.53  fof(f125,plain,(
% 1.35/0.53    sK0 = sK1 | ~spl4_3),
% 1.35/0.53    inference(duplicate_literal_removal,[],[f123])).
% 1.35/0.53  fof(f123,plain,(
% 1.35/0.53    sK0 = sK1 | sK0 = sK1 | sK0 = sK1 | sK0 = sK1 | ~spl4_3),
% 1.35/0.53    inference(resolution,[],[f118,f75])).
% 1.35/0.53  fof(f118,plain,(
% 1.35/0.53    r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl4_3),
% 1.35/0.53    inference(avatar_component_clause,[],[f117])).
% 1.35/0.53  fof(f117,plain,(
% 1.35/0.53    spl4_3 <=> r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.35/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.35/0.53  fof(f122,plain,(
% 1.35/0.53    spl4_3 | spl4_4),
% 1.35/0.53    inference(avatar_split_clause,[],[f108,f120,f117])).
% 1.35/0.53  fof(f108,plain,(
% 1.35/0.53    r2_hidden(sK0,sK1) | r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.35/0.53    inference(resolution,[],[f77,f57])).
% 1.35/0.53  fof(f77,plain,(
% 1.35/0.53    ( ! [X0] : (~r2_hidden(X0,k3_tarski(k2_enumset1(sK0,sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK0)))) | r2_hidden(X0,sK1) | r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1))) )),
% 1.35/0.53    inference(superposition,[],[f66,f56])).
% 1.35/0.53  % SZS output end Proof for theBenchmark
% 1.35/0.53  % (5976)------------------------------
% 1.35/0.53  % (5976)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.53  % (5976)Termination reason: Refutation
% 1.35/0.53  
% 1.35/0.53  % (5976)Memory used [KB]: 10746
% 1.35/0.53  % (5976)Time elapsed: 0.109 s
% 1.35/0.53  % (5976)------------------------------
% 1.35/0.53  % (5976)------------------------------
% 1.35/0.53  % (5971)Success in time 0.175 s
%------------------------------------------------------------------------------
