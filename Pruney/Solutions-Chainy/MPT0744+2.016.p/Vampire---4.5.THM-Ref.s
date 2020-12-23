%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:31 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 213 expanded)
%              Number of leaves         :   28 (  79 expanded)
%              Depth                    :   11
%              Number of atoms          :  496 ( 848 expanded)
%              Number of equality atoms :  141 ( 175 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f289,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f102,f107,f116,f117,f183,f189,f198,f207,f215,f224,f256,f267,f278,f287,f288])).

fof(f288,plain,
    ( sK0 != sK1
    | r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK1,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f287,plain,
    ( ~ spl4_3
    | spl4_8
    | spl4_10 ),
    inference(avatar_contradiction_clause,[],[f286])).

fof(f286,plain,
    ( $false
    | ~ spl4_3
    | spl4_8
    | spl4_10 ),
    inference(unit_resulting_resolution,[],[f197,f110,f205,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_xboole_0(X1,k2_enumset1(X1,X1,X1,X1)))
      | r2_hidden(X0,X1)
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f64,f77])).

fof(f77,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k2_enumset1(X0,X0,X0,X0)) ),
    inference(definition_unfolding,[],[f68,f76])).

fof(f76,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f73,f75])).

fof(f75,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f74,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f74,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f73,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f68,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f64,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

fof(f205,plain,
    ( sK0 != sK1
    | spl4_10 ),
    inference(avatar_component_clause,[],[f204])).

fof(f204,plain,
    ( spl4_10
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f110,plain,
    ( r2_hidden(sK0,k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl4_3
  <=> r2_hidden(sK0,k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f197,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f195])).

fof(f195,plain,
    ( spl4_8
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f278,plain,
    ( ~ spl4_6
    | ~ spl4_8 ),
    inference(avatar_contradiction_clause,[],[f275])).

fof(f275,plain,
    ( $false
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f182,f196,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f196,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f195])).

fof(f182,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f180])).

fof(f180,plain,
    ( spl4_6
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f267,plain,(
    spl4_14 ),
    inference(avatar_contradiction_clause,[],[f257])).

fof(f257,plain,
    ( $false
    | spl4_14 ),
    inference(unit_resulting_resolution,[],[f84,f255])).

fof(f255,plain,
    ( ~ r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))
    | spl4_14 ),
    inference(avatar_component_clause,[],[f253])).

fof(f253,plain,
    ( spl4_14
  <=> r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f84,plain,(
    ! [X6,X2,X0,X1] : r2_hidden(X6,k2_enumset1(X0,X1,X2,X6)) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X6,X4,X2,X0,X1] :
      ( r2_hidden(X6,X4)
      | k2_enumset1(X0,X1,X2,X6) != X4 ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r2_hidden(X6,X4)
      | X3 != X6
      | k2_enumset1(X0,X1,X2,X3) != X4 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_enumset1(X0,X1,X2,X3) = X4
        | ( ( ( sK2(X0,X1,X2,X3,X4) != X3
              & sK2(X0,X1,X2,X3,X4) != X2
              & sK2(X0,X1,X2,X3,X4) != X1
              & sK2(X0,X1,X2,X3,X4) != X0 )
            | ~ r2_hidden(sK2(X0,X1,X2,X3,X4),X4) )
          & ( sK2(X0,X1,X2,X3,X4) = X3
            | sK2(X0,X1,X2,X3,X4) = X2
            | sK2(X0,X1,X2,X3,X4) = X1
            | sK2(X0,X1,X2,X3,X4) = X0
            | r2_hidden(sK2(X0,X1,X2,X3,X4),X4) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).

fof(f30,plain,(
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
     => ( ( ( sK2(X0,X1,X2,X3,X4) != X3
            & sK2(X0,X1,X2,X3,X4) != X2
            & sK2(X0,X1,X2,X3,X4) != X1
            & sK2(X0,X1,X2,X3,X4) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2,X3,X4),X4) )
        & ( sK2(X0,X1,X2,X3,X4) = X3
          | sK2(X0,X1,X2,X3,X4) = X2
          | sK2(X0,X1,X2,X3,X4) = X1
          | sK2(X0,X1,X2,X3,X4) = X0
          | r2_hidden(sK2(X0,X1,X2,X3,X4),X4) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
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

fof(f256,plain,
    ( ~ spl4_14
    | ~ spl4_10
    | spl4_11 ),
    inference(avatar_split_clause,[],[f234,f212,f204,f253])).

fof(f212,plain,
    ( spl4_11
  <=> r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f234,plain,
    ( ~ r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl4_10
    | spl4_11 ),
    inference(superposition,[],[f214,f206])).

fof(f206,plain,
    ( sK0 = sK1
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f204])).

fof(f214,plain,
    ( ~ r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK1))
    | spl4_11 ),
    inference(avatar_component_clause,[],[f212])).

fof(f224,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | spl4_8
    | spl4_9 ),
    inference(avatar_contradiction_clause,[],[f219])).

fof(f219,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | spl4_8
    | spl4_9 ),
    inference(unit_resulting_resolution,[],[f101,f106,f197,f202,f178])).

fof(f178,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r2_hidden(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f177])).

fof(f177,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r1_tarski(X1,X0)
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1) ) ),
    inference(resolution,[],[f47,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(X0,X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | r2_hidden(X1,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f202,plain,
    ( ~ r1_tarski(sK1,sK0)
    | spl4_9 ),
    inference(avatar_component_clause,[],[f200])).

fof(f200,plain,
    ( spl4_9
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f106,plain,
    ( v3_ordinal1(sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl4_2
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f101,plain,
    ( v3_ordinal1(sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl4_1
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f215,plain,
    ( ~ spl4_11
    | spl4_3 ),
    inference(avatar_split_clause,[],[f193,f109,f212])).

fof(f193,plain,
    ( ~ r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK1))
    | spl4_3 ),
    inference(resolution,[],[f111,f92])).

fof(f92,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & ~ r2_hidden(sK3(X0,X1,X2),X0) )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( r2_hidden(sK3(X0,X1,X2),X1)
            | r2_hidden(sK3(X0,X1,X2),X0)
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f34,f35])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & ~ r2_hidden(sK3(X0,X1,X2),X0) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( r2_hidden(sK3(X0,X1,X2),X1)
          | r2_hidden(sK3(X0,X1,X2),X0)
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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

fof(f111,plain,
    ( ~ r2_hidden(sK0,k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f109])).

fof(f207,plain,
    ( ~ spl4_9
    | spl4_10
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f191,f186,f204,f200])).

fof(f186,plain,
    ( spl4_7
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f191,plain,
    ( sK0 = sK1
    | ~ r1_tarski(sK1,sK0)
    | ~ spl4_7 ),
    inference(resolution,[],[f188,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f188,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f186])).

fof(f198,plain,
    ( ~ spl4_8
    | spl4_3 ),
    inference(avatar_split_clause,[],[f192,f109,f195])).

fof(f192,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl4_3 ),
    inference(resolution,[],[f111,f93])).

fof(f93,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f189,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | spl4_7
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f184,f113,f186,f104,f99])).

fof(f113,plain,
    ( spl4_4
  <=> r1_ordinal1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f184,plain,
    ( r1_tarski(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | ~ spl4_4 ),
    inference(resolution,[],[f114,f45])).

fof(f114,plain,
    ( r1_ordinal1(sK0,sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f113])).

fof(f183,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | spl4_6
    | spl4_4 ),
    inference(avatar_split_clause,[],[f176,f113,f180,f104,f99])).

fof(f176,plain,
    ( r2_hidden(sK1,sK0)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | spl4_4 ),
    inference(resolution,[],[f47,f115])).

fof(f115,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f113])).

fof(f117,plain,
    ( spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f79,f113,f109])).

fof(f79,plain,
    ( r1_ordinal1(sK0,sK1)
    | r2_hidden(sK0,k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f43,f77])).

fof(f43,plain,
    ( r1_ordinal1(sK0,sK1)
    | r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ( ~ r1_ordinal1(sK0,sK1)
      | ~ r2_hidden(sK0,k1_ordinal1(sK1)) )
    & ( r1_ordinal1(sK0,sK1)
      | r2_hidden(sK0,k1_ordinal1(sK1)) )
    & v3_ordinal1(sK1)
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f24,f23])).

fof(f23,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_ordinal1(X0,X1)
              | ~ r2_hidden(X0,k1_ordinal1(X1)) )
            & ( r1_ordinal1(X0,X1)
              | r2_hidden(X0,k1_ordinal1(X1)) )
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ( ~ r1_ordinal1(sK0,X1)
            | ~ r2_hidden(sK0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(sK0,X1)
            | r2_hidden(sK0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X1] :
        ( ( ~ r1_ordinal1(sK0,X1)
          | ~ r2_hidden(sK0,k1_ordinal1(X1)) )
        & ( r1_ordinal1(sK0,X1)
          | r2_hidden(sK0,k1_ordinal1(X1)) )
        & v3_ordinal1(X1) )
   => ( ( ~ r1_ordinal1(sK0,sK1)
        | ~ r2_hidden(sK0,k1_ordinal1(sK1)) )
      & ( r1_ordinal1(sK0,sK1)
        | r2_hidden(sK0,k1_ordinal1(sK1)) )
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <~> r1_ordinal1(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,k1_ordinal1(X1))
            <=> r1_ordinal1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).

fof(f116,plain,
    ( ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f78,f113,f109])).

fof(f78,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ r2_hidden(sK0,k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f44,f77])).

fof(f44,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f107,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f42,f104])).

fof(f42,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f102,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f41,f99])).

fof(f41,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:44:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (22232)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.50  % (22255)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.51  % (22255)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (22233)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (22248)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.52  % (22248)Refutation not found, incomplete strategy% (22248)------------------------------
% 0.21/0.52  % (22248)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (22248)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (22248)Memory used [KB]: 10618
% 0.21/0.52  % (22248)Time elapsed: 0.101 s
% 0.21/0.52  % (22248)------------------------------
% 0.21/0.52  % (22248)------------------------------
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f289,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f102,f107,f116,f117,f183,f189,f198,f207,f215,f224,f256,f267,f278,f287,f288])).
% 0.21/0.53  fof(f288,plain,(
% 0.21/0.53    sK0 != sK1 | r2_hidden(sK0,sK1) | ~r2_hidden(sK1,sK0)),
% 0.21/0.53    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.53  fof(f287,plain,(
% 0.21/0.53    ~spl4_3 | spl4_8 | spl4_10),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f286])).
% 0.21/0.53  fof(f286,plain,(
% 0.21/0.53    $false | (~spl4_3 | spl4_8 | spl4_10)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f197,f110,f205,f82])).
% 0.21/0.53  fof(f82,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(X0,k2_xboole_0(X1,k2_enumset1(X1,X1,X1,X1))) | r2_hidden(X0,X1) | X0 = X1) )),
% 0.21/0.53    inference(definition_unfolding,[],[f64,f77])).
% 0.21/0.53  fof(f77,plain,(
% 0.21/0.53    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k2_enumset1(X0,X0,X0,X0))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f68,f76])).
% 0.21/0.53  fof(f76,plain,(
% 0.21/0.53    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f73,f75])).
% 0.21/0.53  fof(f75,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f74,f72])).
% 0.21/0.53  fof(f72,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.53  fof(f73,plain,(
% 0.21/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 0.21/0.53    inference(flattening,[],[f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 0.21/0.53    inference(nnf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).
% 0.21/0.53  fof(f205,plain,(
% 0.21/0.53    sK0 != sK1 | spl4_10),
% 0.21/0.53    inference(avatar_component_clause,[],[f204])).
% 0.21/0.53  fof(f204,plain,(
% 0.21/0.53    spl4_10 <=> sK0 = sK1),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.53  fof(f110,plain,(
% 0.21/0.53    r2_hidden(sK0,k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1))) | ~spl4_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f109])).
% 0.21/0.53  fof(f109,plain,(
% 0.21/0.53    spl4_3 <=> r2_hidden(sK0,k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.53  fof(f197,plain,(
% 0.21/0.53    ~r2_hidden(sK0,sK1) | spl4_8),
% 0.21/0.53    inference(avatar_component_clause,[],[f195])).
% 0.21/0.53  fof(f195,plain,(
% 0.21/0.53    spl4_8 <=> r2_hidden(sK0,sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.53  fof(f278,plain,(
% 0.21/0.53    ~spl4_6 | ~spl4_8),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f275])).
% 0.21/0.53  fof(f275,plain,(
% 0.21/0.53    $false | (~spl4_6 | ~spl4_8)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f182,f196,f67])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 0.21/0.53  fof(f196,plain,(
% 0.21/0.53    r2_hidden(sK0,sK1) | ~spl4_8),
% 0.21/0.53    inference(avatar_component_clause,[],[f195])).
% 0.21/0.53  fof(f182,plain,(
% 0.21/0.53    r2_hidden(sK1,sK0) | ~spl4_6),
% 0.21/0.53    inference(avatar_component_clause,[],[f180])).
% 0.21/0.53  fof(f180,plain,(
% 0.21/0.53    spl4_6 <=> r2_hidden(sK1,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.53  fof(f267,plain,(
% 0.21/0.53    spl4_14),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f257])).
% 0.21/0.53  fof(f257,plain,(
% 0.21/0.53    $false | spl4_14),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f84,f255])).
% 0.21/0.53  fof(f255,plain,(
% 0.21/0.53    ~r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) | spl4_14),
% 0.21/0.53    inference(avatar_component_clause,[],[f253])).
% 0.21/0.53  fof(f253,plain,(
% 0.21/0.53    spl4_14 <=> r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    ( ! [X6,X2,X0,X1] : (r2_hidden(X6,k2_enumset1(X0,X1,X2,X6))) )),
% 0.21/0.53    inference(equality_resolution,[],[f83])).
% 0.21/0.53  fof(f83,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X1] : (r2_hidden(X6,X4) | k2_enumset1(X0,X1,X2,X6) != X4) )),
% 0.21/0.53    inference(equality_resolution,[],[f52])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X3,X1] : (r2_hidden(X6,X4) | X3 != X6 | k2_enumset1(X0,X1,X2,X3) != X4) )),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4] : ((k2_enumset1(X0,X1,X2,X3) = X4 | (((sK2(X0,X1,X2,X3,X4) != X3 & sK2(X0,X1,X2,X3,X4) != X2 & sK2(X0,X1,X2,X3,X4) != X1 & sK2(X0,X1,X2,X3,X4) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3,X4),X4)) & (sK2(X0,X1,X2,X3,X4) = X3 | sK2(X0,X1,X2,X3,X4) = X2 | sK2(X0,X1,X2,X3,X4) = X1 | sK2(X0,X1,X2,X3,X4) = X0 | r2_hidden(sK2(X0,X1,X2,X3,X4),X4)))) & (! [X6] : ((r2_hidden(X6,X4) | (X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)) & (X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | ~r2_hidden(X6,X4))) | k2_enumset1(X0,X1,X2,X3) != X4))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X4,X3,X2,X1,X0] : (? [X5] : (((X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5) | ~r2_hidden(X5,X4)) & (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5 | r2_hidden(X5,X4))) => (((sK2(X0,X1,X2,X3,X4) != X3 & sK2(X0,X1,X2,X3,X4) != X2 & sK2(X0,X1,X2,X3,X4) != X1 & sK2(X0,X1,X2,X3,X4) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3,X4),X4)) & (sK2(X0,X1,X2,X3,X4) = X3 | sK2(X0,X1,X2,X3,X4) = X2 | sK2(X0,X1,X2,X3,X4) = X1 | sK2(X0,X1,X2,X3,X4) = X0 | r2_hidden(sK2(X0,X1,X2,X3,X4),X4))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4] : ((k2_enumset1(X0,X1,X2,X3) = X4 | ? [X5] : (((X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5) | ~r2_hidden(X5,X4)) & (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5 | r2_hidden(X5,X4)))) & (! [X6] : ((r2_hidden(X6,X4) | (X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)) & (X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | ~r2_hidden(X6,X4))) | k2_enumset1(X0,X1,X2,X3) != X4))),
% 0.21/0.53    inference(rectify,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4] : ((k2_enumset1(X0,X1,X2,X3) = X4 | ? [X5] : (((X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5) | ~r2_hidden(X5,X4)) & (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5 | r2_hidden(X5,X4)))) & (! [X5] : ((r2_hidden(X5,X4) | (X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)) & (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X4))) | k2_enumset1(X0,X1,X2,X3) != X4))),
% 0.21/0.53    inference(flattening,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4] : ((k2_enumset1(X0,X1,X2,X3) = X4 | ? [X5] : (((X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5) | ~r2_hidden(X5,X4)) & ((X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5) | r2_hidden(X5,X4)))) & (! [X5] : ((r2_hidden(X5,X4) | (X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)) & ((X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5) | ~r2_hidden(X5,X4))) | k2_enumset1(X0,X1,X2,X3) != X4))),
% 0.21/0.53    inference(nnf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> ! [X5] : (r2_hidden(X5,X4) <=> (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5)))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> ! [X5] : (r2_hidden(X5,X4) <=> ~(X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_enumset1)).
% 0.21/0.53  fof(f256,plain,(
% 0.21/0.53    ~spl4_14 | ~spl4_10 | spl4_11),
% 0.21/0.53    inference(avatar_split_clause,[],[f234,f212,f204,f253])).
% 0.21/0.53  fof(f212,plain,(
% 0.21/0.53    spl4_11 <=> r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.53  fof(f234,plain,(
% 0.21/0.53    ~r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) | (~spl4_10 | spl4_11)),
% 0.21/0.53    inference(superposition,[],[f214,f206])).
% 0.21/0.53  fof(f206,plain,(
% 0.21/0.53    sK0 = sK1 | ~spl4_10),
% 0.21/0.53    inference(avatar_component_clause,[],[f204])).
% 0.21/0.53  fof(f214,plain,(
% 0.21/0.53    ~r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | spl4_11),
% 0.21/0.53    inference(avatar_component_clause,[],[f212])).
% 0.21/0.53  fof(f224,plain,(
% 0.21/0.53    ~spl4_1 | ~spl4_2 | spl4_8 | spl4_9),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f219])).
% 0.21/0.53  fof(f219,plain,(
% 0.21/0.53    $false | (~spl4_1 | ~spl4_2 | spl4_8 | spl4_9)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f101,f106,f197,f202,f178])).
% 0.21/0.53  fof(f178,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(X1,X0) | ~v3_ordinal1(X0) | ~v3_ordinal1(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f177])).
% 0.21/0.53  fof(f177,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~v3_ordinal1(X0) | ~v3_ordinal1(X1) | r1_tarski(X1,X0) | ~v3_ordinal1(X0) | ~v3_ordinal1(X1)) )),
% 0.21/0.53    inference(resolution,[],[f47,f45])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_ordinal1(X0,X1) | r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.21/0.53    inference(flattening,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | r2_hidden(X1,X0) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.53    inference(flattening,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,axiom,(
% 0.21/0.53    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).
% 0.21/0.53  fof(f202,plain,(
% 0.21/0.53    ~r1_tarski(sK1,sK0) | spl4_9),
% 0.21/0.53    inference(avatar_component_clause,[],[f200])).
% 0.21/0.53  fof(f200,plain,(
% 0.21/0.53    spl4_9 <=> r1_tarski(sK1,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.53  fof(f106,plain,(
% 0.21/0.53    v3_ordinal1(sK1) | ~spl4_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f104])).
% 0.21/0.53  fof(f104,plain,(
% 0.21/0.53    spl4_2 <=> v3_ordinal1(sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.53  fof(f101,plain,(
% 0.21/0.53    v3_ordinal1(sK0) | ~spl4_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f99])).
% 0.21/0.53  fof(f99,plain,(
% 0.21/0.53    spl4_1 <=> v3_ordinal1(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.53  fof(f215,plain,(
% 0.21/0.53    ~spl4_11 | spl4_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f193,f109,f212])).
% 0.21/0.53  fof(f193,plain,(
% 0.21/0.53    ~r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | spl4_3),
% 0.21/0.53    inference(resolution,[],[f111,f92])).
% 0.21/0.53  fof(f92,plain,(
% 0.21/0.53    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 0.21/0.53    inference(equality_resolution,[],[f60])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 0.21/0.53    inference(cnf_transformation,[],[f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK3(X0,X1,X2),X1) & ~r2_hidden(sK3(X0,X1,X2),X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f34,f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK3(X0,X1,X2),X1) & ~r2_hidden(sK3(X0,X1,X2),X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.53    inference(rectify,[],[f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.53    inference(flattening,[],[f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.53    inference(nnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.21/0.53  fof(f111,plain,(
% 0.21/0.53    ~r2_hidden(sK0,k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1))) | spl4_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f109])).
% 0.21/0.53  fof(f207,plain,(
% 0.21/0.53    ~spl4_9 | spl4_10 | ~spl4_7),
% 0.21/0.53    inference(avatar_split_clause,[],[f191,f186,f204,f200])).
% 0.21/0.53  fof(f186,plain,(
% 0.21/0.53    spl4_7 <=> r1_tarski(sK0,sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.53  fof(f191,plain,(
% 0.21/0.53    sK0 = sK1 | ~r1_tarski(sK1,sK0) | ~spl4_7),
% 0.21/0.53    inference(resolution,[],[f188,f71])).
% 0.21/0.53  fof(f71,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.53    inference(flattening,[],[f39])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.53    inference(nnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.53  fof(f188,plain,(
% 0.21/0.53    r1_tarski(sK0,sK1) | ~spl4_7),
% 0.21/0.53    inference(avatar_component_clause,[],[f186])).
% 0.21/0.53  fof(f198,plain,(
% 0.21/0.53    ~spl4_8 | spl4_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f192,f109,f195])).
% 0.21/0.53  fof(f192,plain,(
% 0.21/0.53    ~r2_hidden(sK0,sK1) | spl4_3),
% 0.21/0.53    inference(resolution,[],[f111,f93])).
% 0.21/0.53  fof(f93,plain,(
% 0.21/0.53    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 0.21/0.53    inference(equality_resolution,[],[f59])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 0.21/0.53    inference(cnf_transformation,[],[f36])).
% 0.21/0.53  fof(f189,plain,(
% 0.21/0.53    ~spl4_1 | ~spl4_2 | spl4_7 | ~spl4_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f184,f113,f186,f104,f99])).
% 0.21/0.53  fof(f113,plain,(
% 0.21/0.53    spl4_4 <=> r1_ordinal1(sK0,sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.53  fof(f184,plain,(
% 0.21/0.53    r1_tarski(sK0,sK1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | ~spl4_4),
% 0.21/0.53    inference(resolution,[],[f114,f45])).
% 0.21/0.53  fof(f114,plain,(
% 0.21/0.53    r1_ordinal1(sK0,sK1) | ~spl4_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f113])).
% 0.21/0.53  fof(f183,plain,(
% 0.21/0.53    ~spl4_1 | ~spl4_2 | spl4_6 | spl4_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f176,f113,f180,f104,f99])).
% 0.21/0.53  fof(f176,plain,(
% 0.21/0.53    r2_hidden(sK1,sK0) | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | spl4_4),
% 0.21/0.53    inference(resolution,[],[f47,f115])).
% 0.21/0.53  fof(f115,plain,(
% 0.21/0.53    ~r1_ordinal1(sK0,sK1) | spl4_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f113])).
% 0.21/0.53  fof(f117,plain,(
% 0.21/0.53    spl4_3 | spl4_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f79,f113,f109])).
% 0.21/0.53  fof(f79,plain,(
% 0.21/0.53    r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)))),
% 0.21/0.53    inference(definition_unfolding,[],[f43,f77])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k1_ordinal1(sK1))),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ((~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k1_ordinal1(sK1))) & (r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k1_ordinal1(sK1))) & v3_ordinal1(sK1)) & v3_ordinal1(sK0)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f24,f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(sK0,X1) | ~r2_hidden(sK0,k1_ordinal1(X1))) & (r1_ordinal1(sK0,X1) | r2_hidden(sK0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(sK0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ? [X1] : ((~r1_ordinal1(sK0,X1) | ~r2_hidden(sK0,k1_ordinal1(X1))) & (r1_ordinal1(sK0,X1) | r2_hidden(sK0,k1_ordinal1(X1))) & v3_ordinal1(X1)) => ((~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k1_ordinal1(sK1))) & (r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k1_ordinal1(sK1))) & v3_ordinal1(sK1))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.53    inference(flattening,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1)))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <~> r1_ordinal1(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,negated_conjecture,(
% 0.21/0.53    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 0.21/0.53    inference(negated_conjecture,[],[f12])).
% 0.21/0.53  fof(f12,conjecture,(
% 0.21/0.53    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).
% 0.21/0.53  fof(f116,plain,(
% 0.21/0.53    ~spl4_3 | ~spl4_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f78,f113,f109])).
% 0.21/0.53  fof(f78,plain,(
% 0.21/0.53    ~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)))),
% 0.21/0.53    inference(definition_unfolding,[],[f44,f77])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k1_ordinal1(sK1))),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f107,plain,(
% 0.21/0.53    spl4_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f42,f104])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    v3_ordinal1(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f102,plain,(
% 0.21/0.53    spl4_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f41,f99])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    v3_ordinal1(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (22255)------------------------------
% 0.21/0.53  % (22255)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (22255)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (22255)Memory used [KB]: 10874
% 0.21/0.53  % (22255)Time elapsed: 0.102 s
% 0.21/0.53  % (22255)------------------------------
% 0.21/0.53  % (22255)------------------------------
% 0.21/0.54  % (22231)Success in time 0.173 s
%------------------------------------------------------------------------------
