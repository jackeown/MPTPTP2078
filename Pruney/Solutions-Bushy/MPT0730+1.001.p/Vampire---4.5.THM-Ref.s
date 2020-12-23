%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0730+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:33 EST 2020

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 125 expanded)
%              Number of leaves         :   12 (  38 expanded)
%              Depth                    :   11
%              Number of atoms          :  266 ( 589 expanded)
%              Number of equality atoms :   57 ( 123 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f92,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f64,f65,f75,f87,f91])).

fof(f91,plain,
    ( spl5_3
    | ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f90])).

fof(f90,plain,
    ( $false
    | spl5_3
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f89,f62])).

fof(f62,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl5_4
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f89,plain,
    ( ~ r2_hidden(sK1,sK2)
    | spl5_3 ),
    inference(resolution,[],[f59,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f32,f45])).

fof(f45,plain,(
    ! [X0,X1] : sP0(X1,X0,k2_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f3,f7])).

fof(f7,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f32,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ( ~ r2_hidden(sK4(X0,X1,X2),X0)
              & ~ r2_hidden(sK4(X0,X1,X2),X1) )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( r2_hidden(sK4(X0,X1,X2),X0)
            | r2_hidden(sK4(X0,X1,X2),X1)
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X0)
                & ~ r2_hidden(X4,X1) ) )
            & ( r2_hidden(X4,X0)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f20])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X3,X1) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X0)
            | r2_hidden(X3,X1)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK4(X0,X1,X2),X0)
            & ~ r2_hidden(sK4(X0,X1,X2),X1) )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( r2_hidden(sK4(X0,X1,X2),X0)
          | r2_hidden(sK4(X0,X1,X2),X1)
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X3,X1) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X0)
              | r2_hidden(X3,X1)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X0)
                & ~ r2_hidden(X4,X1) ) )
            & ( r2_hidden(X4,X0)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f59,plain,
    ( ~ r2_hidden(sK1,k2_xboole_0(sK2,k1_tarski(sK2)))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl5_3
  <=> r2_hidden(sK1,k2_xboole_0(sK2,k1_tarski(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f87,plain,
    ( spl5_2
    | ~ spl5_3
    | spl5_4 ),
    inference(avatar_contradiction_clause,[],[f86])).

fof(f86,plain,
    ( $false
    | spl5_2
    | ~ spl5_3
    | spl5_4 ),
    inference(subsumption_resolution,[],[f85,f77])).

fof(f77,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK2))
    | spl5_2 ),
    inference(extensionality_resolution,[],[f44,f54])).

fof(f54,plain,
    ( sK1 != sK2
    | spl5_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl5_2
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f44,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f15])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f85,plain,
    ( r2_hidden(sK1,k1_tarski(sK2))
    | ~ spl5_3
    | spl5_4 ),
    inference(subsumption_resolution,[],[f84,f63])).

fof(f63,plain,
    ( ~ r2_hidden(sK1,sK2)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f61])).

fof(f84,plain,
    ( r2_hidden(sK1,sK2)
    | r2_hidden(sK1,k1_tarski(sK2))
    | ~ spl5_3 ),
    inference(resolution,[],[f80,f58])).

fof(f58,plain,
    ( r2_hidden(sK1,k2_xboole_0(sK2,k1_tarski(sK2)))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f57])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | r2_hidden(X0,X2) ) ),
    inference(resolution,[],[f31,f45])).

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f75,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f74])).

fof(f74,plain,
    ( $false
    | spl5_1 ),
    inference(subsumption_resolution,[],[f73,f43])).

fof(f43,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f73,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK1))
    | spl5_1 ),
    inference(resolution,[],[f71,f50])).

fof(f50,plain,
    ( ~ r2_hidden(sK1,k2_xboole_0(sK1,k1_tarski(sK1)))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl5_1
  <=> r2_hidden(sK1,k2_xboole_0(sK1,k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X2,X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f33,f45])).

fof(f33,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X0)
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f65,plain,
    ( spl5_3
    | spl5_4
    | spl5_2 ),
    inference(avatar_split_clause,[],[f41,f52,f61,f57])).

fof(f41,plain,
    ( sK1 = sK2
    | r2_hidden(sK1,sK2)
    | r2_hidden(sK1,k2_xboole_0(sK2,k1_tarski(sK2))) ),
    inference(definition_unfolding,[],[f23,f26])).

fof(f26,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f23,plain,
    ( sK1 = sK2
    | r2_hidden(sK1,sK2)
    | r2_hidden(sK1,k1_ordinal1(sK2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ( ( sK1 != sK2
        & ~ r2_hidden(sK1,sK2) )
      | ~ r2_hidden(sK1,k1_ordinal1(sK2)) )
    & ( sK1 = sK2
      | r2_hidden(sK1,sK2)
      | r2_hidden(sK1,k1_ordinal1(sK2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f10,f11])).

fof(f11,plain,
    ( ? [X0,X1] :
        ( ( ( X0 != X1
            & ~ r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_ordinal1(X1)) )
        & ( X0 = X1
          | r2_hidden(X0,X1)
          | r2_hidden(X0,k1_ordinal1(X1)) ) )
   => ( ( ( sK1 != sK2
          & ~ r2_hidden(sK1,sK2) )
        | ~ r2_hidden(sK1,k1_ordinal1(sK2)) )
      & ( sK1 = sK2
        | r2_hidden(sK1,sK2)
        | r2_hidden(sK1,k1_ordinal1(sK2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ( ( X0 != X1
          & ~ r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k1_ordinal1(X1)) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ( ( X0 != X1
          & ~ r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k1_ordinal1(X1)) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <~> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,k1_ordinal1(X1))
      <=> ( X0 = X1
          | r2_hidden(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

fof(f64,plain,
    ( ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f40,f61,f57])).

fof(f40,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK1,k2_xboole_0(sK2,k1_tarski(sK2))) ),
    inference(definition_unfolding,[],[f24,f26])).

fof(f24,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK1,k1_ordinal1(sK2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f55,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f46,f52,f48])).

fof(f46,plain,
    ( sK1 != sK2
    | ~ r2_hidden(sK1,k2_xboole_0(sK1,k1_tarski(sK1))) ),
    inference(inner_rewriting,[],[f39])).

fof(f39,plain,
    ( sK1 != sK2
    | ~ r2_hidden(sK1,k2_xboole_0(sK2,k1_tarski(sK2))) ),
    inference(definition_unfolding,[],[f25,f26])).

fof(f25,plain,
    ( sK1 != sK2
    | ~ r2_hidden(sK1,k1_ordinal1(sK2)) ),
    inference(cnf_transformation,[],[f12])).

%------------------------------------------------------------------------------
