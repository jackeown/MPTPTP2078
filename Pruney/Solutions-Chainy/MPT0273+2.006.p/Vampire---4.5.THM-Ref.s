%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:18 EST 2020

% Result     : Theorem 11.46s
% Output     : Refutation 11.46s
% Verified   : 
% Statistics : Number of formulae       :  171 ( 736 expanded)
%              Number of leaves         :   27 ( 220 expanded)
%              Depth                    :   16
%              Number of atoms          :  609 (2837 expanded)
%              Number of equality atoms :  229 (1438 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9669,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f242,f303,f361,f386,f446,f449,f703,f1288,f1391,f2727,f2944,f9667,f9668])).

fof(f9668,plain,
    ( sK0 != sK1
    | r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK0,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f9667,plain,
    ( ~ spl5_3
    | spl5_5
    | spl5_6 ),
    inference(avatar_contradiction_clause,[],[f9666])).

fof(f9666,plain,
    ( $false
    | ~ spl5_3
    | spl5_5
    | spl5_6 ),
    inference(subsumption_resolution,[],[f9665,f117])).

fof(f117,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f116])).

fof(f116,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k3_enumset1(X0,X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f106])).

fof(f106,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f79,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f58,f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f58,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f79,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK4(X0,X1,X2,X3) != X2
              & sK4(X0,X1,X2,X3) != X1
              & sK4(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
          & ( sK4(X0,X1,X2,X3) = X2
            | sK4(X0,X1,X2,X3) = X1
            | sK4(X0,X1,X2,X3) = X0
            | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f43,f44])).

fof(f44,plain,(
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
     => ( ( ( sK4(X0,X1,X2,X3) != X2
            & sK4(X0,X1,X2,X3) != X1
            & sK4(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
        & ( sK4(X0,X1,X2,X3) = X2
          | sK4(X0,X1,X2,X3) = X1
          | sK4(X0,X1,X2,X3) = X0
          | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
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
    inference(rectify,[],[f42])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f9665,plain,
    ( ~ r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK1))
    | ~ spl5_3
    | spl5_5
    | spl5_6 ),
    inference(subsumption_resolution,[],[f9651,f702])).

fof(f702,plain,
    ( ~ r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | spl5_6 ),
    inference(avatar_component_clause,[],[f700])).

fof(f700,plain,
    ( spl5_6
  <=> r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f9651,plain,
    ( r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | ~ r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK1))
    | ~ spl5_3
    | spl5_5 ),
    inference(resolution,[],[f1581,f3214])).

fof(f3214,plain,
    ( ! [X0] : ~ r2_hidden(sK1,k3_xboole_0(sK2,X0))
    | spl5_5 ),
    inference(unit_resulting_resolution,[],[f385,f177])).

fof(f177,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
      | r2_hidden(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f170])).

fof(f170,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k3_xboole_0(X1,X2))
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f73,f115])).

fof(f115,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f64,f53])).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f64,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f37,f38])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f385,plain,
    ( ~ r2_hidden(sK1,sK2)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f383])).

fof(f383,plain,
    ( spl5_5
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f1581,plain,
    ( ! [X1] :
        ( r2_hidden(X1,k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))
        | r2_hidden(X1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
        | ~ r2_hidden(X1,k3_enumset1(sK0,sK0,sK0,sK0,sK1)) )
    | ~ spl5_3 ),
    inference(superposition,[],[f72,f301])).

fof(f301,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f300])).

fof(f300,plain,
    ( spl5_3
  <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f2944,plain,
    ( ~ spl5_3
    | ~ spl5_10 ),
    inference(avatar_contradiction_clause,[],[f2898])).

fof(f2898,plain,
    ( $false
    | ~ spl5_3
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f117,f133,f2824,f73])).

fof(f2824,plain,
    ( ! [X2] : ~ r2_hidden(X2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | ~ spl5_3
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f2821,f1585])).

fof(f1585,plain,
    ( ! [X3] :
        ( r2_hidden(X3,k3_enumset1(sK0,sK0,sK0,sK0,sK1))
        | ~ r2_hidden(X3,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) )
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f1583,f1584])).

fof(f1584,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))
        | ~ r2_hidden(X2,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) )
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f1582,f230])).

fof(f230,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_hidden(X6,k3_xboole_0(X8,X7))
      | r2_hidden(X6,X7) ) ),
    inference(subsumption_resolution,[],[f229,f177])).

fof(f229,plain,(
    ! [X6,X8,X7] :
      ( r2_hidden(X6,X7)
      | ~ r2_hidden(X6,X8)
      | ~ r2_hidden(X6,k3_xboole_0(X8,X7)) ) ),
    inference(duplicate_literal_removal,[],[f223])).

fof(f223,plain,(
    ! [X6,X8,X7] :
      ( r2_hidden(X6,X7)
      | ~ r2_hidden(X6,X8)
      | ~ r2_hidden(X6,X8)
      | ~ r2_hidden(X6,k3_xboole_0(X8,X7)) ) ),
    inference(resolution,[],[f113,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f113,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f66,f53])).

fof(f66,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f1582,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
        | ~ r2_hidden(X2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))
        | ~ r2_hidden(X2,k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) )
    | ~ spl5_3 ),
    inference(superposition,[],[f71,f301])).

fof(f1583,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
        | r2_hidden(X3,k3_enumset1(sK0,sK0,sK0,sK0,sK1))
        | r2_hidden(X3,k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) )
    | ~ spl5_3 ),
    inference(superposition,[],[f70,f301])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f2821,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))
        | ~ r2_hidden(X2,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) )
    | ~ spl5_3
    | ~ spl5_10 ),
    inference(backward_demodulation,[],[f1584,f2805])).

fof(f2805,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))
    | ~ spl5_10 ),
    inference(superposition,[],[f2726,f51])).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f2726,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f2724])).

fof(f2724,plain,
    ( spl5_10
  <=> k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f133,plain,(
    ! [X6,X7] : ~ r2_hidden(X7,k5_xboole_0(X6,X6)) ),
    inference(subsumption_resolution,[],[f132,f70])).

fof(f132,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X7,k5_xboole_0(X6,X6))
      | ~ r2_hidden(X7,X6) ) ),
    inference(superposition,[],[f114,f123])).

fof(f123,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(unit_resulting_resolution,[],[f110,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f110,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f114,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f99])).

fof(f99,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f65,f53])).

fof(f65,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f2727,plain,
    ( spl5_10
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f1567,f383,f239,f2724])).

fof(f239,plain,
    ( spl5_2
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f1567,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f240,f384,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | k3_enumset1(X0,X0,X0,X0,X2) = k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X2),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f63,f85,f85])).

fof(f85,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f52,f84])).

fof(f52,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
     => k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_zfmisc_1)).

fof(f384,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f383])).

fof(f240,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f239])).

fof(f1391,plain,
    ( spl5_2
    | spl5_3
    | ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f1390])).

fof(f1390,plain,
    ( $false
    | spl5_2
    | spl5_3
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f1389,f321])).

fof(f321,plain,(
    ! [X2,X0,X1] : k3_enumset1(X0,X0,X0,X0,X0) = k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X2,X0)) ),
    inference(unit_resulting_resolution,[],[f117,f112])).

fof(f112,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X2,X1)
      | k3_enumset1(X2,X2,X2,X2,X2) = k3_xboole_0(k3_enumset1(X2,X2,X2,X2,X2),X1) ) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( k3_enumset1(X0,X0,X0,X0,X0) = k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X2),X1)
      | X0 != X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f61,f86,f85])).

fof(f86,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f50,f85])).

fof(f50,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | X0 != X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ( X0 != X2
        & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ( X0 != X2
        & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,X1)
     => ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
        | ( X0 != X2
          & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_zfmisc_1)).

fof(f1389,plain,
    ( ! [X0,X1] : k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) != k3_xboole_0(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(X0,X0,X0,X1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
    | spl5_2
    | spl5_3
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f1301,f1019])).

fof(f1019,plain,
    ( ! [X0,X1] : k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(X0,X0,X0,X1,sK0),sK2))
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f251,f112])).

fof(f251,plain,
    ( ! [X0,X1] : r2_hidden(sK0,k5_xboole_0(k3_enumset1(X0,X0,X0,X1,sK0),sK2))
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f117,f241,f72])).

fof(f241,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f239])).

fof(f1301,plain,
    ( ! [X0,X1] : k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) != k3_xboole_0(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK2))),k3_enumset1(X0,X0,X0,X1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK2))))
    | spl5_3
    | ~ spl5_4 ),
    inference(backward_demodulation,[],[f607,f359])).

fof(f359,plain,
    ( sK0 = sK1
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f358])).

fof(f358,plain,
    ( spl5_4
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f607,plain,
    ( ! [X0,X1] : k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) != k3_xboole_0(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))),k3_enumset1(X0,X0,X0,X1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))))
    | spl5_3 ),
    inference(forward_demodulation,[],[f583,f191])).

fof(f191,plain,(
    ! [X6,X7] : k5_xboole_0(X6,k3_xboole_0(X7,X6)) = k3_xboole_0(X6,k5_xboole_0(X6,X7)) ),
    inference(forward_demodulation,[],[f180,f51])).

fof(f180,plain,(
    ! [X6,X7] : k3_xboole_0(k5_xboole_0(X6,X7),X6) = k5_xboole_0(X6,k3_xboole_0(X7,X6)) ),
    inference(superposition,[],[f59,f123])).

fof(f59,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f583,plain,
    ( ! [X0,X1] : k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) != k3_xboole_0(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))),k3_enumset1(X0,X0,X0,X1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))))
    | spl5_3 ),
    inference(unit_resulting_resolution,[],[f302,f117,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( k3_enumset1(X0,X0,X0,X0,X0) != k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f74,f86,f85])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(X1,X2)
      | k1_tarski(X0) != k3_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( X0 = X1
      | ~ r2_hidden(X1,X2)
      | k1_tarski(X0) != k3_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ~ ( X0 != X1
        & r2_hidden(X1,X2)
        & k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_zfmisc_1)).

fof(f302,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f300])).

fof(f1288,plain,
    ( spl5_2
    | spl5_3
    | ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f1287])).

fof(f1287,plain,
    ( $false
    | spl5_2
    | spl5_3
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f1272,f321])).

fof(f1272,plain,
    ( ! [X0,X1] : k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) != k3_xboole_0(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(X0,X0,X0,X1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
    | spl5_2
    | spl5_3
    | ~ spl5_5 ),
    inference(backward_demodulation,[],[f607,f1255])).

fof(f1255,plain,
    ( ! [X0] : k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,X0,sK1),sK2))
    | spl5_2
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f253,f451,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(X2,X1)
      | k3_enumset1(X0,X0,X0,X0,X0) = k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X2),X1) ) ),
    inference(definition_unfolding,[],[f60,f86,f85])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f451,plain,
    ( ! [X0,X1] : ~ r2_hidden(sK1,k5_xboole_0(k3_enumset1(X0,X0,X0,X1,sK1),sK2))
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f117,f384,f71])).

fof(f253,plain,
    ( ! [X0,X1] : r2_hidden(sK0,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,X0,X1),sK2))
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f121,f241,f72])).

fof(f121,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k3_enumset1(X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f120])).

fof(f120,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k3_enumset1(X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f108])).

fof(f108,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f77,f84])).

fof(f77,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f703,plain,
    ( ~ spl5_6
    | spl5_4 ),
    inference(avatar_split_clause,[],[f368,f358,f700])).

fof(f368,plain,
    ( ~ r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | spl5_4 ),
    inference(unit_resulting_resolution,[],[f360,f360,f360,f122])).

fof(f122,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X2))
      | X1 = X5
      | X0 = X5
      | X2 = X5 ) ),
    inference(equality_resolution,[],[f109])).

fof(f109,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f76,f84])).

fof(f76,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f360,plain,
    ( sK0 != sK1
    | spl5_4 ),
    inference(avatar_component_clause,[],[f358])).

fof(f449,plain,
    ( ~ spl5_1
    | spl5_3 ),
    inference(avatar_contradiction_clause,[],[f448])).

fof(f448,plain,
    ( $false
    | ~ spl5_1
    | spl5_3 ),
    inference(subsumption_resolution,[],[f447,f302])).

fof(f447,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))
    | ~ spl5_1 ),
    inference(forward_demodulation,[],[f237,f51])).

fof(f237,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f235])).

fof(f235,plain,
    ( spl5_1
  <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f446,plain,
    ( spl5_1
    | spl5_5
    | spl5_4 ),
    inference(avatar_split_clause,[],[f89,f358,f383,f235])).

fof(f89,plain,
    ( sK0 = sK1
    | r2_hidden(sK1,sK2)
    | k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f47,f86,f53,f85])).

fof(f47,plain,
    ( sK0 = sK1
    | r2_hidden(sK1,sK2)
    | k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ( ( sK0 != sK1
        & ~ r2_hidden(sK1,sK2) )
      | r2_hidden(sK0,sK2)
      | k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) )
    & ( ( ( sK0 = sK1
          | r2_hidden(sK1,sK2) )
        & ~ r2_hidden(sK0,sK2) )
      | k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f31])).

fof(f31,plain,
    ( ? [X0,X1,X2] :
        ( ( ( X0 != X1
            & ~ r2_hidden(X1,X2) )
          | r2_hidden(X0,X2)
          | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) )
        & ( ( ( X0 = X1
              | r2_hidden(X1,X2) )
            & ~ r2_hidden(X0,X2) )
          | k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) ) )
   => ( ( ( sK0 != sK1
          & ~ r2_hidden(sK1,sK2) )
        | r2_hidden(sK0,sK2)
        | k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) )
      & ( ( ( sK0 = sK1
            | r2_hidden(sK1,sK2) )
          & ~ r2_hidden(sK0,sK2) )
        | k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ? [X0,X1,X2] :
      ( ( ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2)
        | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( ( ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2)
        | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <~> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
      <=> ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_zfmisc_1)).

fof(f386,plain,
    ( ~ spl5_1
    | spl5_2
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f88,f383,f239,f235])).

fof(f88,plain,
    ( ~ r2_hidden(sK1,sK2)
    | r2_hidden(sK0,sK2)
    | k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f48,f86,f53,f85])).

fof(f48,plain,
    ( ~ r2_hidden(sK1,sK2)
    | r2_hidden(sK0,sK2)
    | k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f361,plain,
    ( ~ spl5_1
    | spl5_2
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f87,f358,f239,f235])).

fof(f87,plain,
    ( sK0 != sK1
    | r2_hidden(sK0,sK2)
    | k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f49,f86,f53,f85])).

fof(f49,plain,
    ( sK0 != sK1
    | r2_hidden(sK0,sK2)
    | k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f303,plain,
    ( ~ spl5_3
    | spl5_1 ),
    inference(avatar_split_clause,[],[f243,f235,f300])).

fof(f243,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))
    | spl5_1 ),
    inference(forward_demodulation,[],[f236,f51])).

fof(f236,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f235])).

fof(f242,plain,
    ( spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f90,f239,f235])).

fof(f90,plain,
    ( ~ r2_hidden(sK0,sK2)
    | k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f46,f86,f53,f85])).

fof(f46,plain,
    ( ~ r2_hidden(sK0,sK2)
    | k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:16:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (12277)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.49  % (12269)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.51  % (12272)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.51  % (12270)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.30/0.52  % (12260)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.30/0.53  % (12285)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.30/0.53  % (12280)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.30/0.53  % (12282)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.30/0.53  % (12264)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.30/0.53  % (12274)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.30/0.53  % (12262)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.30/0.53  % (12263)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.30/0.53  % (12289)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.30/0.53  % (12261)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.43/0.54  % (12265)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.43/0.54  % (12271)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.43/0.54  % (12284)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.43/0.54  % (12266)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.43/0.54  % (12268)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.43/0.54  % (12275)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.43/0.54  % (12288)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.43/0.54  % (12283)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.43/0.54  % (12286)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.43/0.54  % (12281)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.43/0.55  % (12287)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.43/0.55  % (12276)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.43/0.55  % (12276)Refutation not found, incomplete strategy% (12276)------------------------------
% 1.43/0.55  % (12276)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.55  % (12276)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.55  
% 1.43/0.55  % (12276)Memory used [KB]: 10618
% 1.43/0.55  % (12276)Time elapsed: 0.144 s
% 1.43/0.55  % (12276)------------------------------
% 1.43/0.55  % (12276)------------------------------
% 1.43/0.55  % (12267)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.43/0.55  % (12279)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.43/0.55  % (12278)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.43/0.55  % (12273)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 2.56/0.70  % (12263)Refutation not found, incomplete strategy% (12263)------------------------------
% 2.56/0.70  % (12263)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.56/0.70  % (12263)Termination reason: Refutation not found, incomplete strategy
% 2.56/0.70  
% 2.56/0.70  % (12263)Memory used [KB]: 6268
% 2.56/0.70  % (12263)Time elapsed: 0.270 s
% 2.56/0.70  % (12263)------------------------------
% 2.56/0.70  % (12263)------------------------------
% 2.56/0.74  % (12290)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 3.44/0.81  % (12262)Time limit reached!
% 3.44/0.81  % (12262)------------------------------
% 3.44/0.81  % (12262)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.44/0.81  % (12262)Termination reason: Time limit
% 3.44/0.81  
% 3.44/0.81  % (12262)Memory used [KB]: 6524
% 3.44/0.81  % (12262)Time elapsed: 0.406 s
% 3.44/0.81  % (12262)------------------------------
% 3.44/0.81  % (12262)------------------------------
% 3.44/0.82  % (12284)Time limit reached!
% 3.44/0.82  % (12284)------------------------------
% 3.44/0.82  % (12284)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.44/0.82  % (12284)Termination reason: Time limit
% 3.44/0.82  % (12284)Termination phase: Saturation
% 3.44/0.82  
% 3.44/0.82  % (12284)Memory used [KB]: 12920
% 3.44/0.82  % (12284)Time elapsed: 0.400 s
% 3.44/0.82  % (12284)------------------------------
% 3.44/0.82  % (12284)------------------------------
% 3.61/0.85  % (12291)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 3.61/0.92  % (12289)Time limit reached!
% 3.61/0.92  % (12289)------------------------------
% 3.61/0.92  % (12289)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.61/0.92  % (12289)Termination reason: Time limit
% 3.61/0.92  
% 3.61/0.92  % (12289)Memory used [KB]: 3837
% 3.61/0.92  % (12289)Time elapsed: 0.516 s
% 3.61/0.92  % (12289)------------------------------
% 3.61/0.92  % (12289)------------------------------
% 4.27/0.94  % (12292)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 4.27/0.94  % (12266)Time limit reached!
% 4.27/0.94  % (12266)------------------------------
% 4.27/0.94  % (12266)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.27/0.94  % (12266)Termination reason: Time limit
% 4.27/0.94  
% 4.27/0.94  % (12266)Memory used [KB]: 15607
% 4.27/0.94  % (12266)Time elapsed: 0.501 s
% 4.27/0.94  % (12266)------------------------------
% 4.27/0.94  % (12266)------------------------------
% 4.27/0.97  % (12293)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 4.27/0.97  % (12274)Time limit reached!
% 4.27/0.97  % (12274)------------------------------
% 4.27/0.97  % (12274)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.27/0.97  % (12274)Termination reason: Time limit
% 4.27/0.97  
% 4.27/0.97  % (12274)Memory used [KB]: 3709
% 4.27/0.97  % (12274)Time elapsed: 0.529 s
% 4.27/0.97  % (12274)------------------------------
% 4.27/0.97  % (12274)------------------------------
% 4.71/1.00  % (12267)Time limit reached!
% 4.71/1.00  % (12267)------------------------------
% 4.71/1.00  % (12267)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.71/1.00  % (12267)Termination reason: Time limit
% 4.71/1.00  % (12267)Termination phase: Saturation
% 4.71/1.00  
% 4.71/1.00  % (12267)Memory used [KB]: 5245
% 4.71/1.00  % (12267)Time elapsed: 0.600 s
% 4.71/1.00  % (12267)------------------------------
% 4.71/1.00  % (12267)------------------------------
% 4.71/1.06  % (12294)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 5.12/1.06  % (12294)Refutation not found, incomplete strategy% (12294)------------------------------
% 5.12/1.06  % (12294)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.12/1.07  % (12294)Termination reason: Refutation not found, incomplete strategy
% 5.12/1.07  
% 5.12/1.07  % (12294)Memory used [KB]: 10746
% 5.12/1.07  % (12294)Time elapsed: 0.114 s
% 5.12/1.07  % (12294)------------------------------
% 5.12/1.07  % (12294)------------------------------
% 5.12/1.08  % (12295)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 5.66/1.11  % (12296)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 5.95/1.12  % (12297)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 6.16/1.22  % (12261)Time limit reached!
% 6.16/1.22  % (12261)------------------------------
% 6.16/1.22  % (12261)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.78/1.23  % (12261)Termination reason: Time limit
% 6.78/1.23  
% 6.78/1.23  % (12261)Memory used [KB]: 3326
% 6.78/1.23  % (12261)Time elapsed: 0.818 s
% 6.78/1.23  % (12261)------------------------------
% 6.78/1.23  % (12261)------------------------------
% 6.78/1.24  % (12298)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 7.87/1.38  % (12299)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 8.17/1.43  % (12272)Time limit reached!
% 8.17/1.43  % (12272)------------------------------
% 8.17/1.43  % (12272)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.17/1.43  % (12272)Termination reason: Time limit
% 8.17/1.43  
% 8.17/1.43  % (12272)Memory used [KB]: 12920
% 8.17/1.43  % (12272)Time elapsed: 1.027 s
% 8.17/1.43  % (12272)------------------------------
% 8.17/1.43  % (12272)------------------------------
% 8.17/1.44  % (12287)Time limit reached!
% 8.17/1.44  % (12287)------------------------------
% 8.17/1.44  % (12287)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.17/1.44  % (12287)Termination reason: Time limit
% 8.17/1.44  
% 8.17/1.44  % (12287)Memory used [KB]: 9850
% 8.17/1.44  % (12287)Time elapsed: 1.030 s
% 8.17/1.44  % (12287)------------------------------
% 8.17/1.44  % (12287)------------------------------
% 8.94/1.58  % (12301)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 9.33/1.61  % (12300)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 9.33/1.63  % (12296)Time limit reached!
% 9.33/1.63  % (12296)------------------------------
% 9.33/1.63  % (12296)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.33/1.63  % (12296)Termination reason: Time limit
% 9.33/1.63  
% 9.33/1.63  % (12296)Memory used [KB]: 16630
% 9.33/1.63  % (12296)Time elapsed: 0.636 s
% 9.33/1.63  % (12296)------------------------------
% 9.33/1.63  % (12296)------------------------------
% 9.33/1.66  % (12260)Time limit reached!
% 9.33/1.66  % (12260)------------------------------
% 9.33/1.66  % (12260)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.33/1.66  % (12260)Termination reason: Time limit
% 9.33/1.66  % (12260)Termination phase: Saturation
% 9.33/1.66  
% 9.33/1.66  % (12260)Memory used [KB]: 10490
% 9.33/1.66  % (12260)Time elapsed: 1.214 s
% 9.33/1.66  % (12260)------------------------------
% 9.33/1.66  % (12260)------------------------------
% 10.44/1.69  % (12292)Time limit reached!
% 10.44/1.69  % (12292)------------------------------
% 10.44/1.69  % (12292)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.44/1.70  % (12292)Termination reason: Time limit
% 10.44/1.70  
% 10.44/1.70  % (12292)Memory used [KB]: 11129
% 10.44/1.70  % (12292)Time elapsed: 0.803 s
% 10.44/1.70  % (12292)------------------------------
% 10.44/1.70  % (12292)------------------------------
% 10.44/1.72  % (12265)Time limit reached!
% 10.44/1.72  % (12265)------------------------------
% 10.44/1.72  % (12265)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.44/1.72  % (12265)Termination reason: Time limit
% 10.44/1.72  
% 10.44/1.72  % (12265)Memory used [KB]: 9210
% 10.44/1.72  % (12265)Time elapsed: 1.315 s
% 10.44/1.72  % (12265)------------------------------
% 10.44/1.72  % (12265)------------------------------
% 10.92/1.79  % (12303)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 10.92/1.80  % (12303)Refutation not found, incomplete strategy% (12303)------------------------------
% 10.92/1.80  % (12303)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.92/1.80  % (12303)Termination reason: Refutation not found, incomplete strategy
% 10.92/1.80  
% 10.92/1.80  % (12303)Memory used [KB]: 10746
% 10.92/1.80  % (12303)Time elapsed: 0.098 s
% 10.92/1.80  % (12303)------------------------------
% 10.92/1.80  % (12303)------------------------------
% 10.92/1.81  % (12302)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 11.46/1.82  % (12280)Refutation found. Thanks to Tanya!
% 11.46/1.82  % SZS status Theorem for theBenchmark
% 11.46/1.82  % SZS output start Proof for theBenchmark
% 11.46/1.82  fof(f9669,plain,(
% 11.46/1.82    $false),
% 11.46/1.82    inference(avatar_sat_refutation,[],[f242,f303,f361,f386,f446,f449,f703,f1288,f1391,f2727,f2944,f9667,f9668])).
% 11.46/1.82  fof(f9668,plain,(
% 11.46/1.82    sK0 != sK1 | r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2)),
% 11.46/1.82    introduced(theory_tautology_sat_conflict,[])).
% 11.46/1.82  fof(f9667,plain,(
% 11.46/1.82    ~spl5_3 | spl5_5 | spl5_6),
% 11.46/1.82    inference(avatar_contradiction_clause,[],[f9666])).
% 11.46/1.82  fof(f9666,plain,(
% 11.46/1.82    $false | (~spl5_3 | spl5_5 | spl5_6)),
% 11.46/1.82    inference(subsumption_resolution,[],[f9665,f117])).
% 11.46/1.82  fof(f117,plain,(
% 11.46/1.82    ( ! [X0,X5,X1] : (r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X5))) )),
% 11.46/1.82    inference(equality_resolution,[],[f116])).
% 11.46/1.82  fof(f116,plain,(
% 11.46/1.82    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k3_enumset1(X0,X0,X0,X1,X5) != X3) )),
% 11.46/1.82    inference(equality_resolution,[],[f106])).
% 11.46/1.82  fof(f106,plain,(
% 11.46/1.82    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 11.46/1.82    inference(definition_unfolding,[],[f79,f84])).
% 11.46/1.82  fof(f84,plain,(
% 11.46/1.82    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 11.46/1.82    inference(definition_unfolding,[],[f58,f75])).
% 11.46/1.82  fof(f75,plain,(
% 11.46/1.82    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 11.46/1.82    inference(cnf_transformation,[],[f12])).
% 11.46/1.82  fof(f12,axiom,(
% 11.46/1.82    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 11.46/1.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 11.46/1.82  fof(f58,plain,(
% 11.46/1.82    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 11.46/1.82    inference(cnf_transformation,[],[f11])).
% 11.46/1.82  fof(f11,axiom,(
% 11.46/1.82    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 11.46/1.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 11.46/1.82  fof(f79,plain,(
% 11.46/1.82    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 11.46/1.82    inference(cnf_transformation,[],[f45])).
% 11.46/1.82  fof(f45,plain,(
% 11.46/1.82    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 11.46/1.82    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f43,f44])).
% 11.46/1.82  fof(f44,plain,(
% 11.46/1.82    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3))))),
% 11.46/1.82    introduced(choice_axiom,[])).
% 11.46/1.82  fof(f43,plain,(
% 11.46/1.82    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 11.46/1.82    inference(rectify,[],[f42])).
% 11.46/1.82  fof(f42,plain,(
% 11.46/1.82    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 11.46/1.82    inference(flattening,[],[f41])).
% 11.46/1.82  fof(f41,plain,(
% 11.46/1.82    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 11.46/1.82    inference(nnf_transformation,[],[f28])).
% 11.46/1.82  fof(f28,plain,(
% 11.46/1.82    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 11.46/1.82    inference(ennf_transformation,[],[f8])).
% 11.46/1.82  fof(f8,axiom,(
% 11.46/1.82    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 11.46/1.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 11.46/1.82  fof(f9665,plain,(
% 11.46/1.82    ~r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK1)) | (~spl5_3 | spl5_5 | spl5_6)),
% 11.46/1.82    inference(subsumption_resolution,[],[f9651,f702])).
% 11.46/1.82  fof(f702,plain,(
% 11.46/1.82    ~r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | spl5_6),
% 11.46/1.82    inference(avatar_component_clause,[],[f700])).
% 11.46/1.82  fof(f700,plain,(
% 11.46/1.82    spl5_6 <=> r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 11.46/1.82    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 11.46/1.82  fof(f9651,plain,(
% 11.46/1.82    r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK1)) | (~spl5_3 | spl5_5)),
% 11.46/1.82    inference(resolution,[],[f1581,f3214])).
% 11.46/1.82  fof(f3214,plain,(
% 11.46/1.82    ( ! [X0] : (~r2_hidden(sK1,k3_xboole_0(sK2,X0))) ) | spl5_5),
% 11.46/1.82    inference(unit_resulting_resolution,[],[f385,f177])).
% 11.46/1.82  fof(f177,plain,(
% 11.46/1.82    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_xboole_0(X1,X2)) | r2_hidden(X0,X1)) )),
% 11.46/1.82    inference(duplicate_literal_removal,[],[f170])).
% 11.46/1.82  fof(f170,plain,(
% 11.46/1.82    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,k3_xboole_0(X1,X2)) | r2_hidden(X0,X1)) )),
% 11.46/1.82    inference(resolution,[],[f73,f115])).
% 11.46/1.82  fof(f115,plain,(
% 11.46/1.82    ( ! [X4,X0,X1] : (~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X4,X0)) )),
% 11.46/1.82    inference(equality_resolution,[],[f100])).
% 11.46/1.82  fof(f100,plain,(
% 11.46/1.82    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 11.46/1.82    inference(definition_unfolding,[],[f64,f53])).
% 11.46/1.82  fof(f53,plain,(
% 11.46/1.82    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 11.46/1.82    inference(cnf_transformation,[],[f5])).
% 11.46/1.82  fof(f5,axiom,(
% 11.46/1.82    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 11.46/1.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 11.46/1.82  fof(f64,plain,(
% 11.46/1.82    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 11.46/1.82    inference(cnf_transformation,[],[f39])).
% 11.46/1.82  fof(f39,plain,(
% 11.46/1.82    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 11.46/1.82    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f37,f38])).
% 11.46/1.82  fof(f38,plain,(
% 11.46/1.82    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 11.46/1.82    introduced(choice_axiom,[])).
% 11.46/1.82  fof(f37,plain,(
% 11.46/1.82    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 11.46/1.82    inference(rectify,[],[f36])).
% 11.46/1.82  fof(f36,plain,(
% 11.46/1.82    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 11.46/1.82    inference(flattening,[],[f35])).
% 11.46/1.82  fof(f35,plain,(
% 11.46/1.82    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 11.46/1.82    inference(nnf_transformation,[],[f2])).
% 11.46/1.82  fof(f2,axiom,(
% 11.46/1.82    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 11.46/1.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 11.46/1.82  fof(f73,plain,(
% 11.46/1.82    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 11.46/1.82    inference(cnf_transformation,[],[f40])).
% 11.46/1.82  fof(f40,plain,(
% 11.46/1.82    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 11.46/1.82    inference(nnf_transformation,[],[f26])).
% 11.46/1.82  fof(f26,plain,(
% 11.46/1.82    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 11.46/1.82    inference(ennf_transformation,[],[f3])).
% 11.46/1.82  fof(f3,axiom,(
% 11.46/1.82    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 11.46/1.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).
% 11.46/1.82  fof(f385,plain,(
% 11.46/1.82    ~r2_hidden(sK1,sK2) | spl5_5),
% 11.46/1.82    inference(avatar_component_clause,[],[f383])).
% 11.46/1.82  fof(f383,plain,(
% 11.46/1.82    spl5_5 <=> r2_hidden(sK1,sK2)),
% 11.46/1.82    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 11.46/1.82  fof(f1581,plain,(
% 11.46/1.82    ( ! [X1] : (r2_hidden(X1,k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) | r2_hidden(X1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(X1,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) ) | ~spl5_3),
% 11.46/1.82    inference(superposition,[],[f72,f301])).
% 11.46/1.82  fof(f301,plain,(
% 11.46/1.82    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) | ~spl5_3),
% 11.46/1.82    inference(avatar_component_clause,[],[f300])).
% 11.46/1.82  fof(f300,plain,(
% 11.46/1.82    spl5_3 <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))),
% 11.46/1.82    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 11.46/1.82  fof(f72,plain,(
% 11.46/1.82    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) )),
% 11.46/1.82    inference(cnf_transformation,[],[f40])).
% 11.46/1.82  fof(f2944,plain,(
% 11.46/1.82    ~spl5_3 | ~spl5_10),
% 11.46/1.82    inference(avatar_contradiction_clause,[],[f2898])).
% 11.46/1.82  fof(f2898,plain,(
% 11.46/1.82    $false | (~spl5_3 | ~spl5_10)),
% 11.46/1.82    inference(unit_resulting_resolution,[],[f117,f133,f2824,f73])).
% 11.46/1.82  fof(f2824,plain,(
% 11.46/1.82    ( ! [X2] : (~r2_hidden(X2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ) | (~spl5_3 | ~spl5_10)),
% 11.46/1.82    inference(subsumption_resolution,[],[f2821,f1585])).
% 11.46/1.82  fof(f1585,plain,(
% 11.46/1.82    ( ! [X3] : (r2_hidden(X3,k3_enumset1(sK0,sK0,sK0,sK0,sK1)) | ~r2_hidden(X3,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ) | ~spl5_3),
% 11.46/1.82    inference(subsumption_resolution,[],[f1583,f1584])).
% 11.46/1.82  fof(f1584,plain,(
% 11.46/1.82    ( ! [X2] : (~r2_hidden(X2,k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) | ~r2_hidden(X2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ) | ~spl5_3),
% 11.46/1.82    inference(subsumption_resolution,[],[f1582,f230])).
% 11.46/1.82  fof(f230,plain,(
% 11.46/1.82    ( ! [X6,X8,X7] : (~r2_hidden(X6,k3_xboole_0(X8,X7)) | r2_hidden(X6,X7)) )),
% 11.46/1.82    inference(subsumption_resolution,[],[f229,f177])).
% 11.46/1.82  fof(f229,plain,(
% 11.46/1.82    ( ! [X6,X8,X7] : (r2_hidden(X6,X7) | ~r2_hidden(X6,X8) | ~r2_hidden(X6,k3_xboole_0(X8,X7))) )),
% 11.46/1.82    inference(duplicate_literal_removal,[],[f223])).
% 11.46/1.82  fof(f223,plain,(
% 11.46/1.82    ( ! [X6,X8,X7] : (r2_hidden(X6,X7) | ~r2_hidden(X6,X8) | ~r2_hidden(X6,X8) | ~r2_hidden(X6,k3_xboole_0(X8,X7))) )),
% 11.46/1.82    inference(resolution,[],[f113,f71])).
% 11.46/1.82  fof(f71,plain,(
% 11.46/1.82    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 11.46/1.82    inference(cnf_transformation,[],[f40])).
% 11.46/1.82  fof(f113,plain,(
% 11.46/1.82    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 11.46/1.82    inference(equality_resolution,[],[f98])).
% 11.46/1.82  fof(f98,plain,(
% 11.46/1.82    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 11.46/1.82    inference(definition_unfolding,[],[f66,f53])).
% 11.46/1.82  fof(f66,plain,(
% 11.46/1.82    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 11.46/1.82    inference(cnf_transformation,[],[f39])).
% 11.46/1.82  fof(f1582,plain,(
% 11.46/1.82    ( ! [X2] : (~r2_hidden(X2,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(X2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)) | ~r2_hidden(X2,k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))) ) | ~spl5_3),
% 11.46/1.82    inference(superposition,[],[f71,f301])).
% 11.46/1.82  fof(f1583,plain,(
% 11.46/1.82    ( ! [X3] : (~r2_hidden(X3,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | r2_hidden(X3,k3_enumset1(sK0,sK0,sK0,sK0,sK1)) | r2_hidden(X3,k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))) ) | ~spl5_3),
% 11.46/1.82    inference(superposition,[],[f70,f301])).
% 11.46/1.82  fof(f70,plain,(
% 11.46/1.82    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | r2_hidden(X0,X2)) )),
% 11.46/1.82    inference(cnf_transformation,[],[f40])).
% 11.46/1.82  fof(f2821,plain,(
% 11.46/1.82    ( ! [X2] : (~r2_hidden(X2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)) | ~r2_hidden(X2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ) | (~spl5_3 | ~spl5_10)),
% 11.46/1.82    inference(backward_demodulation,[],[f1584,f2805])).
% 11.46/1.82  fof(f2805,plain,(
% 11.46/1.82    k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)) | ~spl5_10),
% 11.46/1.82    inference(superposition,[],[f2726,f51])).
% 11.46/1.82  fof(f51,plain,(
% 11.46/1.82    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 11.46/1.82    inference(cnf_transformation,[],[f1])).
% 11.46/1.82  fof(f1,axiom,(
% 11.46/1.82    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 11.46/1.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 11.46/1.82  fof(f2726,plain,(
% 11.46/1.82    k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2) | ~spl5_10),
% 11.46/1.82    inference(avatar_component_clause,[],[f2724])).
% 11.46/1.82  fof(f2724,plain,(
% 11.46/1.82    spl5_10 <=> k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)),
% 11.46/1.82    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 11.46/1.82  fof(f133,plain,(
% 11.46/1.82    ( ! [X6,X7] : (~r2_hidden(X7,k5_xboole_0(X6,X6))) )),
% 11.46/1.82    inference(subsumption_resolution,[],[f132,f70])).
% 11.46/1.82  fof(f132,plain,(
% 11.46/1.82    ( ! [X6,X7] : (~r2_hidden(X7,k5_xboole_0(X6,X6)) | ~r2_hidden(X7,X6)) )),
% 11.46/1.82    inference(superposition,[],[f114,f123])).
% 11.46/1.82  fof(f123,plain,(
% 11.46/1.82    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 11.46/1.82    inference(unit_resulting_resolution,[],[f110,f54])).
% 11.46/1.82  fof(f54,plain,(
% 11.46/1.82    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 11.46/1.82    inference(cnf_transformation,[],[f20])).
% 11.46/1.82  fof(f20,plain,(
% 11.46/1.82    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 11.46/1.82    inference(ennf_transformation,[],[f7])).
% 11.46/1.82  fof(f7,axiom,(
% 11.46/1.82    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 11.46/1.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 11.46/1.82  fof(f110,plain,(
% 11.46/1.82    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.46/1.82    inference(equality_resolution,[],[f56])).
% 11.46/1.82  fof(f56,plain,(
% 11.46/1.82    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 11.46/1.82    inference(cnf_transformation,[],[f34])).
% 11.46/1.82  fof(f34,plain,(
% 11.46/1.82    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.46/1.82    inference(flattening,[],[f33])).
% 11.46/1.82  fof(f33,plain,(
% 11.46/1.82    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.46/1.82    inference(nnf_transformation,[],[f4])).
% 11.46/1.82  fof(f4,axiom,(
% 11.46/1.82    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.46/1.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 11.46/1.82  fof(f114,plain,(
% 11.46/1.82    ( ! [X4,X0,X1] : (~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | ~r2_hidden(X4,X1)) )),
% 11.46/1.82    inference(equality_resolution,[],[f99])).
% 11.46/1.82  fof(f99,plain,(
% 11.46/1.82    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 11.46/1.82    inference(definition_unfolding,[],[f65,f53])).
% 11.46/1.82  fof(f65,plain,(
% 11.46/1.82    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 11.46/1.82    inference(cnf_transformation,[],[f39])).
% 11.46/1.82  fof(f2727,plain,(
% 11.46/1.82    spl5_10 | ~spl5_2 | ~spl5_5),
% 11.46/1.82    inference(avatar_split_clause,[],[f1567,f383,f239,f2724])).
% 11.46/1.82  fof(f239,plain,(
% 11.46/1.82    spl5_2 <=> r2_hidden(sK0,sK2)),
% 11.46/1.82    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 11.46/1.82  fof(f1567,plain,(
% 11.46/1.82    k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2) | (~spl5_2 | ~spl5_5)),
% 11.46/1.82    inference(unit_resulting_resolution,[],[f240,f384,f94])).
% 11.46/1.82  fof(f94,plain,(
% 11.46/1.82    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | k3_enumset1(X0,X0,X0,X0,X2) = k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X2),X1) | ~r2_hidden(X0,X1)) )),
% 11.46/1.82    inference(definition_unfolding,[],[f63,f85,f85])).
% 11.46/1.82  fof(f85,plain,(
% 11.46/1.82    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 11.46/1.82    inference(definition_unfolding,[],[f52,f84])).
% 11.46/1.82  fof(f52,plain,(
% 11.46/1.82    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 11.46/1.82    inference(cnf_transformation,[],[f10])).
% 11.46/1.82  fof(f10,axiom,(
% 11.46/1.82    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 11.46/1.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 11.46/1.82  fof(f63,plain,(
% 11.46/1.82    ( ! [X2,X0,X1] : (k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)) )),
% 11.46/1.82    inference(cnf_transformation,[],[f25])).
% 11.46/1.82  fof(f25,plain,(
% 11.46/1.82    ! [X0,X1,X2] : (k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1))),
% 11.46/1.82    inference(flattening,[],[f24])).
% 11.46/1.82  fof(f24,plain,(
% 11.46/1.82    ! [X0,X1,X2] : (k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) | (~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)))),
% 11.46/1.82    inference(ennf_transformation,[],[f13])).
% 11.46/1.82  fof(f13,axiom,(
% 11.46/1.82    ! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1))),
% 11.46/1.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_zfmisc_1)).
% 11.46/1.82  fof(f384,plain,(
% 11.46/1.82    r2_hidden(sK1,sK2) | ~spl5_5),
% 11.46/1.82    inference(avatar_component_clause,[],[f383])).
% 11.46/1.82  fof(f240,plain,(
% 11.46/1.82    r2_hidden(sK0,sK2) | ~spl5_2),
% 11.46/1.82    inference(avatar_component_clause,[],[f239])).
% 11.46/1.82  fof(f1391,plain,(
% 11.46/1.82    spl5_2 | spl5_3 | ~spl5_4),
% 11.46/1.82    inference(avatar_contradiction_clause,[],[f1390])).
% 11.46/1.82  fof(f1390,plain,(
% 11.46/1.82    $false | (spl5_2 | spl5_3 | ~spl5_4)),
% 11.46/1.82    inference(subsumption_resolution,[],[f1389,f321])).
% 11.46/1.82  fof(f321,plain,(
% 11.46/1.82    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X0,X0) = k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X2,X0))) )),
% 11.46/1.82    inference(unit_resulting_resolution,[],[f117,f112])).
% 11.46/1.82  fof(f112,plain,(
% 11.46/1.82    ( ! [X2,X1] : (~r2_hidden(X2,X1) | k3_enumset1(X2,X2,X2,X2,X2) = k3_xboole_0(k3_enumset1(X2,X2,X2,X2,X2),X1)) )),
% 11.46/1.82    inference(equality_resolution,[],[f91])).
% 11.46/1.82  fof(f91,plain,(
% 11.46/1.82    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X0,X0) = k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X2),X1) | X0 != X2 | ~r2_hidden(X0,X1)) )),
% 11.46/1.82    inference(definition_unfolding,[],[f61,f86,f85])).
% 11.46/1.82  fof(f86,plain,(
% 11.46/1.82    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 11.46/1.82    inference(definition_unfolding,[],[f50,f85])).
% 11.46/1.82  fof(f50,plain,(
% 11.46/1.82    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 11.46/1.82    inference(cnf_transformation,[],[f9])).
% 11.46/1.82  fof(f9,axiom,(
% 11.46/1.82    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 11.46/1.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 11.46/1.82  fof(f61,plain,(
% 11.46/1.82    ( ! [X2,X0,X1] : (k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | X0 != X2 | ~r2_hidden(X0,X1)) )),
% 11.46/1.82    inference(cnf_transformation,[],[f22])).
% 11.46/1.82  fof(f22,plain,(
% 11.46/1.82    ! [X0,X1,X2] : (k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | (X0 != X2 & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 11.46/1.82    inference(flattening,[],[f21])).
% 11.46/1.82  fof(f21,plain,(
% 11.46/1.82    ! [X0,X1,X2] : ((k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | (X0 != X2 & r2_hidden(X2,X1))) | ~r2_hidden(X0,X1))),
% 11.46/1.82    inference(ennf_transformation,[],[f15])).
% 11.46/1.82  fof(f15,axiom,(
% 11.46/1.82    ! [X0,X1,X2] : (r2_hidden(X0,X1) => (k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | (X0 != X2 & r2_hidden(X2,X1))))),
% 11.46/1.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_zfmisc_1)).
% 11.46/1.82  fof(f1389,plain,(
% 11.46/1.82    ( ! [X0,X1] : (k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) != k3_xboole_0(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(X0,X0,X0,X1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) ) | (spl5_2 | spl5_3 | ~spl5_4)),
% 11.46/1.82    inference(forward_demodulation,[],[f1301,f1019])).
% 11.46/1.82  fof(f1019,plain,(
% 11.46/1.82    ( ! [X0,X1] : (k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(X0,X0,X0,X1,sK0),sK2))) ) | spl5_2),
% 11.46/1.82    inference(unit_resulting_resolution,[],[f251,f112])).
% 11.46/1.82  fof(f251,plain,(
% 11.46/1.82    ( ! [X0,X1] : (r2_hidden(sK0,k5_xboole_0(k3_enumset1(X0,X0,X0,X1,sK0),sK2))) ) | spl5_2),
% 11.46/1.82    inference(unit_resulting_resolution,[],[f117,f241,f72])).
% 11.46/1.82  fof(f241,plain,(
% 11.46/1.82    ~r2_hidden(sK0,sK2) | spl5_2),
% 11.46/1.82    inference(avatar_component_clause,[],[f239])).
% 11.46/1.82  fof(f1301,plain,(
% 11.46/1.82    ( ! [X0,X1] : (k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) != k3_xboole_0(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK2))),k3_enumset1(X0,X0,X0,X1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK2))))) ) | (spl5_3 | ~spl5_4)),
% 11.46/1.82    inference(backward_demodulation,[],[f607,f359])).
% 11.46/1.82  fof(f359,plain,(
% 11.46/1.82    sK0 = sK1 | ~spl5_4),
% 11.46/1.82    inference(avatar_component_clause,[],[f358])).
% 11.46/1.82  fof(f358,plain,(
% 11.46/1.82    spl5_4 <=> sK0 = sK1),
% 11.46/1.82    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 11.46/1.82  fof(f607,plain,(
% 11.46/1.82    ( ! [X0,X1] : (k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) != k3_xboole_0(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))),k3_enumset1(X0,X0,X0,X1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))))) ) | spl5_3),
% 11.46/1.82    inference(forward_demodulation,[],[f583,f191])).
% 11.46/1.82  fof(f191,plain,(
% 11.46/1.82    ( ! [X6,X7] : (k5_xboole_0(X6,k3_xboole_0(X7,X6)) = k3_xboole_0(X6,k5_xboole_0(X6,X7))) )),
% 11.46/1.82    inference(forward_demodulation,[],[f180,f51])).
% 11.46/1.82  fof(f180,plain,(
% 11.46/1.82    ( ! [X6,X7] : (k3_xboole_0(k5_xboole_0(X6,X7),X6) = k5_xboole_0(X6,k3_xboole_0(X7,X6))) )),
% 11.46/1.82    inference(superposition,[],[f59,f123])).
% 11.46/1.82  fof(f59,plain,(
% 11.46/1.82    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 11.46/1.82    inference(cnf_transformation,[],[f6])).
% 11.46/1.82  fof(f6,axiom,(
% 11.46/1.82    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 11.46/1.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).
% 11.46/1.82  fof(f583,plain,(
% 11.46/1.82    ( ! [X0,X1] : (k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) != k3_xboole_0(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))),k3_enumset1(X0,X0,X0,X1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))))) ) | spl5_3),
% 11.46/1.82    inference(unit_resulting_resolution,[],[f302,f117,f101])).
% 11.46/1.82  fof(f101,plain,(
% 11.46/1.82    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X0,X0) != k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | X0 = X1) )),
% 11.46/1.82    inference(definition_unfolding,[],[f74,f86,f85])).
% 11.46/1.82  fof(f74,plain,(
% 11.46/1.82    ( ! [X2,X0,X1] : (X0 = X1 | ~r2_hidden(X1,X2) | k1_tarski(X0) != k3_xboole_0(k2_tarski(X0,X1),X2)) )),
% 11.46/1.82    inference(cnf_transformation,[],[f27])).
% 11.46/1.82  fof(f27,plain,(
% 11.46/1.82    ! [X0,X1,X2] : (X0 = X1 | ~r2_hidden(X1,X2) | k1_tarski(X0) != k3_xboole_0(k2_tarski(X0,X1),X2))),
% 11.46/1.82    inference(ennf_transformation,[],[f14])).
% 11.46/1.82  fof(f14,axiom,(
% 11.46/1.82    ! [X0,X1,X2] : ~(X0 != X1 & r2_hidden(X1,X2) & k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X1),X2))),
% 11.46/1.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_zfmisc_1)).
% 11.46/1.82  fof(f302,plain,(
% 11.46/1.82    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) | spl5_3),
% 11.46/1.82    inference(avatar_component_clause,[],[f300])).
% 11.46/1.82  fof(f1288,plain,(
% 11.46/1.82    spl5_2 | spl5_3 | ~spl5_5),
% 11.46/1.82    inference(avatar_contradiction_clause,[],[f1287])).
% 11.46/1.82  fof(f1287,plain,(
% 11.46/1.82    $false | (spl5_2 | spl5_3 | ~spl5_5)),
% 11.46/1.82    inference(subsumption_resolution,[],[f1272,f321])).
% 11.46/1.82  fof(f1272,plain,(
% 11.46/1.82    ( ! [X0,X1] : (k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) != k3_xboole_0(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(X0,X0,X0,X1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) ) | (spl5_2 | spl5_3 | ~spl5_5)),
% 11.46/1.82    inference(backward_demodulation,[],[f607,f1255])).
% 11.46/1.82  fof(f1255,plain,(
% 11.46/1.82    ( ! [X0] : (k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,X0,sK1),sK2))) ) | (spl5_2 | ~spl5_5)),
% 11.46/1.82    inference(unit_resulting_resolution,[],[f253,f451,f92])).
% 11.46/1.82  fof(f92,plain,(
% 11.46/1.82    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | r2_hidden(X2,X1) | k3_enumset1(X0,X0,X0,X0,X0) = k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X2),X1)) )),
% 11.46/1.82    inference(definition_unfolding,[],[f60,f86,f85])).
% 11.46/1.82  fof(f60,plain,(
% 11.46/1.82    ( ! [X2,X0,X1] : (k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | ~r2_hidden(X0,X1)) )),
% 11.46/1.82    inference(cnf_transformation,[],[f22])).
% 11.46/1.82  fof(f451,plain,(
% 11.46/1.82    ( ! [X0,X1] : (~r2_hidden(sK1,k5_xboole_0(k3_enumset1(X0,X0,X0,X1,sK1),sK2))) ) | ~spl5_5),
% 11.46/1.82    inference(unit_resulting_resolution,[],[f117,f384,f71])).
% 11.46/1.82  fof(f253,plain,(
% 11.46/1.82    ( ! [X0,X1] : (r2_hidden(sK0,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,X0,X1),sK2))) ) | spl5_2),
% 11.46/1.82    inference(unit_resulting_resolution,[],[f121,f241,f72])).
% 11.46/1.82  fof(f121,plain,(
% 11.46/1.82    ( ! [X2,X5,X1] : (r2_hidden(X5,k3_enumset1(X5,X5,X5,X1,X2))) )),
% 11.46/1.82    inference(equality_resolution,[],[f120])).
% 11.46/1.82  fof(f120,plain,(
% 11.46/1.82    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k3_enumset1(X5,X5,X5,X1,X2) != X3) )),
% 11.46/1.82    inference(equality_resolution,[],[f108])).
% 11.46/1.82  fof(f108,plain,(
% 11.46/1.82    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 11.46/1.82    inference(definition_unfolding,[],[f77,f84])).
% 11.46/1.82  fof(f77,plain,(
% 11.46/1.82    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 11.46/1.82    inference(cnf_transformation,[],[f45])).
% 11.46/1.82  fof(f703,plain,(
% 11.46/1.82    ~spl5_6 | spl5_4),
% 11.46/1.82    inference(avatar_split_clause,[],[f368,f358,f700])).
% 11.46/1.82  fof(f368,plain,(
% 11.46/1.82    ~r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | spl5_4),
% 11.46/1.82    inference(unit_resulting_resolution,[],[f360,f360,f360,f122])).
% 11.46/1.82  fof(f122,plain,(
% 11.46/1.82    ( ! [X2,X0,X5,X1] : (~r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X2)) | X1 = X5 | X0 = X5 | X2 = X5) )),
% 11.46/1.82    inference(equality_resolution,[],[f109])).
% 11.46/1.82  fof(f109,plain,(
% 11.46/1.82    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 11.46/1.82    inference(definition_unfolding,[],[f76,f84])).
% 11.46/1.82  fof(f76,plain,(
% 11.46/1.82    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 11.46/1.82    inference(cnf_transformation,[],[f45])).
% 11.46/1.82  fof(f360,plain,(
% 11.46/1.82    sK0 != sK1 | spl5_4),
% 11.46/1.82    inference(avatar_component_clause,[],[f358])).
% 11.46/1.82  fof(f449,plain,(
% 11.46/1.82    ~spl5_1 | spl5_3),
% 11.46/1.82    inference(avatar_contradiction_clause,[],[f448])).
% 11.46/1.82  fof(f448,plain,(
% 11.46/1.82    $false | (~spl5_1 | spl5_3)),
% 11.46/1.82    inference(subsumption_resolution,[],[f447,f302])).
% 11.46/1.82  fof(f447,plain,(
% 11.46/1.82    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) | ~spl5_1),
% 11.46/1.82    inference(forward_demodulation,[],[f237,f51])).
% 11.46/1.82  fof(f237,plain,(
% 11.46/1.82    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)) | ~spl5_1),
% 11.46/1.82    inference(avatar_component_clause,[],[f235])).
% 11.46/1.82  fof(f235,plain,(
% 11.46/1.82    spl5_1 <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))),
% 11.46/1.82    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 11.46/1.82  fof(f446,plain,(
% 11.46/1.82    spl5_1 | spl5_5 | spl5_4),
% 11.46/1.82    inference(avatar_split_clause,[],[f89,f358,f383,f235])).
% 11.46/1.82  fof(f89,plain,(
% 11.46/1.82    sK0 = sK1 | r2_hidden(sK1,sK2) | k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))),
% 11.46/1.82    inference(definition_unfolding,[],[f47,f86,f53,f85])).
% 11.46/1.82  fof(f47,plain,(
% 11.46/1.82    sK0 = sK1 | r2_hidden(sK1,sK2) | k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 11.46/1.82    inference(cnf_transformation,[],[f32])).
% 11.46/1.82  fof(f32,plain,(
% 11.46/1.82    ((sK0 != sK1 & ~r2_hidden(sK1,sK2)) | r2_hidden(sK0,sK2) | k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)) & (((sK0 = sK1 | r2_hidden(sK1,sK2)) & ~r2_hidden(sK0,sK2)) | k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 11.46/1.82    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f31])).
% 11.46/1.82  fof(f31,plain,(
% 11.46/1.82    ? [X0,X1,X2] : (((X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2))) => (((sK0 != sK1 & ~r2_hidden(sK1,sK2)) | r2_hidden(sK0,sK2) | k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)) & (((sK0 = sK1 | r2_hidden(sK1,sK2)) & ~r2_hidden(sK0,sK2)) | k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)))),
% 11.46/1.82    introduced(choice_axiom,[])).
% 11.46/1.82  fof(f30,plain,(
% 11.46/1.82    ? [X0,X1,X2] : (((X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 11.46/1.82    inference(flattening,[],[f29])).
% 11.46/1.82  fof(f29,plain,(
% 11.46/1.82    ? [X0,X1,X2] : ((((X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2)) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 11.46/1.82    inference(nnf_transformation,[],[f19])).
% 11.46/1.82  fof(f19,plain,(
% 11.46/1.82    ? [X0,X1,X2] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) <~> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 11.46/1.82    inference(ennf_transformation,[],[f18])).
% 11.46/1.82  fof(f18,negated_conjecture,(
% 11.46/1.82    ~! [X0,X1,X2] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 11.46/1.82    inference(negated_conjecture,[],[f17])).
% 11.46/1.82  fof(f17,conjecture,(
% 11.46/1.82    ! [X0,X1,X2] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 11.46/1.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_zfmisc_1)).
% 11.46/1.82  fof(f386,plain,(
% 11.46/1.82    ~spl5_1 | spl5_2 | ~spl5_5),
% 11.46/1.82    inference(avatar_split_clause,[],[f88,f383,f239,f235])).
% 11.46/1.82  fof(f88,plain,(
% 11.46/1.82    ~r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2) | k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))),
% 11.46/1.82    inference(definition_unfolding,[],[f48,f86,f53,f85])).
% 11.46/1.82  fof(f48,plain,(
% 11.46/1.82    ~r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2) | k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 11.46/1.82    inference(cnf_transformation,[],[f32])).
% 11.46/1.82  fof(f361,plain,(
% 11.46/1.82    ~spl5_1 | spl5_2 | ~spl5_4),
% 11.46/1.82    inference(avatar_split_clause,[],[f87,f358,f239,f235])).
% 11.46/1.82  fof(f87,plain,(
% 11.46/1.82    sK0 != sK1 | r2_hidden(sK0,sK2) | k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))),
% 11.46/1.82    inference(definition_unfolding,[],[f49,f86,f53,f85])).
% 11.46/1.82  fof(f49,plain,(
% 11.46/1.82    sK0 != sK1 | r2_hidden(sK0,sK2) | k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 11.46/1.82    inference(cnf_transformation,[],[f32])).
% 11.46/1.82  fof(f303,plain,(
% 11.46/1.82    ~spl5_3 | spl5_1),
% 11.46/1.82    inference(avatar_split_clause,[],[f243,f235,f300])).
% 11.46/1.82  fof(f243,plain,(
% 11.46/1.82    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) | spl5_1),
% 11.46/1.82    inference(forward_demodulation,[],[f236,f51])).
% 11.46/1.82  fof(f236,plain,(
% 11.46/1.82    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)) | spl5_1),
% 11.46/1.82    inference(avatar_component_clause,[],[f235])).
% 11.46/1.82  fof(f242,plain,(
% 11.46/1.82    spl5_1 | ~spl5_2),
% 11.46/1.82    inference(avatar_split_clause,[],[f90,f239,f235])).
% 11.46/1.82  fof(f90,plain,(
% 11.46/1.82    ~r2_hidden(sK0,sK2) | k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))),
% 11.46/1.82    inference(definition_unfolding,[],[f46,f86,f53,f85])).
% 11.46/1.82  fof(f46,plain,(
% 11.46/1.82    ~r2_hidden(sK0,sK2) | k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 11.46/1.82    inference(cnf_transformation,[],[f32])).
% 11.46/1.82  % SZS output end Proof for theBenchmark
% 11.46/1.82  % (12280)------------------------------
% 11.46/1.82  % (12280)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.46/1.82  % (12280)Termination reason: Refutation
% 11.46/1.82  
% 11.46/1.82  % (12280)Memory used [KB]: 22131
% 11.46/1.82  % (12280)Time elapsed: 1.406 s
% 11.46/1.82  % (12280)------------------------------
% 11.46/1.82  % (12280)------------------------------
% 11.46/1.85  % (12259)Success in time 1.476 s
%------------------------------------------------------------------------------
