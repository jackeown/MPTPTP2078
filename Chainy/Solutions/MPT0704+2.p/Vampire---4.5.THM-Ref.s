%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0704+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:45 EST 2020

% Result     : Theorem 3.00s
% Output     : Refutation 3.82s
% Verified   : 
% Statistics : Number of formulae       :  270 ( 798 expanded)
%              Number of leaves         :   63 ( 278 expanded)
%              Depth                    :   11
%              Number of atoms          :  830 (3006 expanded)
%              Number of equality atoms :  132 ( 278 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3297,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2590,f2595,f2599,f2603,f2609,f2622,f2628,f2633,f2641,f2642,f2646,f2654,f2662,f2672,f2673,f2674,f2675,f2684,f2685,f2686,f2819,f2953,f2963,f2965,f2967,f2969,f2973,f3020,f3029,f3055,f3060,f3066,f3071,f3182,f3187,f3192,f3197,f3296])).

fof(f3296,plain,
    ( spl101_1
    | spl101_19 ),
    inference(avatar_contradiction_clause,[],[f3295])).

fof(f3295,plain,
    ( $false
    | spl101_1
    | spl101_19 ),
    inference(global_subsumption,[],[f1755,f1754,f2586,f3293])).

fof(f3293,plain,
    ( v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl101_19 ),
    inference(resolution,[],[f3019,f1794])).

fof(f1794,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),k2_relat_1(X0))
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1507])).

fof(f1507,plain,(
    ! [X0] :
      ( ( ( ! [X1] :
              ( k10_relat_1(X0,k1_tarski(X1)) = k1_tarski(sK5(X0,X1))
              | ~ r2_hidden(X1,k2_relat_1(X0)) )
          | ~ v2_funct_1(X0) )
        & ( v2_funct_1(X0)
          | ( ! [X4] : k1_tarski(X4) != k10_relat_1(X0,k1_tarski(sK6(X0)))
            & r2_hidden(sK6(X0),k2_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f1504,f1506,f1505])).

fof(f1505,plain,(
    ! [X1,X0] :
      ( ? [X2] : k1_tarski(X2) = k10_relat_1(X0,k1_tarski(X1))
     => k10_relat_1(X0,k1_tarski(X1)) = k1_tarski(sK5(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f1506,plain,(
    ! [X0] :
      ( ? [X3] :
          ( ! [X4] : k1_tarski(X4) != k10_relat_1(X0,k1_tarski(X3))
          & r2_hidden(X3,k2_relat_1(X0)) )
     => ( ! [X4] : k1_tarski(X4) != k10_relat_1(X0,k1_tarski(sK6(X0)))
        & r2_hidden(sK6(X0),k2_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f1504,plain,(
    ! [X0] :
      ( ( ( ! [X1] :
              ( ? [X2] : k1_tarski(X2) = k10_relat_1(X0,k1_tarski(X1))
              | ~ r2_hidden(X1,k2_relat_1(X0)) )
          | ~ v2_funct_1(X0) )
        & ( v2_funct_1(X0)
          | ? [X3] :
              ( ! [X4] : k1_tarski(X4) != k10_relat_1(X0,k1_tarski(X3))
              & r2_hidden(X3,k2_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f1503])).

fof(f1503,plain,(
    ! [X0] :
      ( ( ( ! [X1] :
              ( ? [X2] : k1_tarski(X2) = k10_relat_1(X0,k1_tarski(X1))
              | ~ r2_hidden(X1,k2_relat_1(X0)) )
          | ~ v2_funct_1(X0) )
        & ( v2_funct_1(X0)
          | ? [X1] :
              ( ! [X2] : k1_tarski(X2) != k10_relat_1(X0,k1_tarski(X1))
              & r2_hidden(X1,k2_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1070])).

fof(f1070,plain,(
    ! [X0] :
      ( ( ! [X1] :
            ( ? [X2] : k1_tarski(X2) = k10_relat_1(X0,k1_tarski(X1))
            | ~ r2_hidden(X1,k2_relat_1(X0)) )
      <=> v2_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1069])).

fof(f1069,plain,(
    ! [X0] :
      ( ( ! [X1] :
            ( ? [X2] : k1_tarski(X2) = k10_relat_1(X0,k1_tarski(X1))
            | ~ r2_hidden(X1,k2_relat_1(X0)) )
      <=> v2_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f945])).

fof(f945,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ! [X1] :
            ~ ( ! [X2] : k1_tarski(X2) != k10_relat_1(X0,k1_tarski(X1))
              & r2_hidden(X1,k2_relat_1(X0)) )
      <=> v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_funct_1)).

fof(f3019,plain,
    ( ~ r2_hidden(sK6(sK0),k2_relat_1(sK0))
    | spl101_19 ),
    inference(avatar_component_clause,[],[f3018])).

fof(f3018,plain,
    ( spl101_19
  <=> r2_hidden(sK6(sK0),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_19])])).

fof(f2586,plain,
    ( ~ v2_funct_1(sK0)
    | spl101_1 ),
    inference(avatar_component_clause,[],[f2585])).

fof(f2585,plain,
    ( spl101_1
  <=> v2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_1])])).

fof(f1754,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f1492])).

fof(f1492,plain,
    ( ( ! [X2] : ~ r1_tarski(k10_relat_1(sK0,k1_tarski(sK1)),k1_tarski(X2))
      | ~ v2_funct_1(sK0) )
    & ( ! [X3] : r1_tarski(k10_relat_1(sK0,k1_tarski(X3)),k1_tarski(sK2(X3)))
      | v2_funct_1(sK0) )
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f1488,f1491,f1490,f1489])).

fof(f1489,plain,
    ( ? [X0] :
        ( ( ? [X1] :
            ! [X2] : ~ r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2))
          | ~ v2_funct_1(X0) )
        & ( ! [X3] :
            ? [X4] : r1_tarski(k10_relat_1(X0,k1_tarski(X3)),k1_tarski(X4))
          | v2_funct_1(X0) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( ? [X1] :
          ! [X2] : ~ r1_tarski(k10_relat_1(sK0,k1_tarski(X1)),k1_tarski(X2))
        | ~ v2_funct_1(sK0) )
      & ( ! [X3] :
          ? [X4] : r1_tarski(k10_relat_1(sK0,k1_tarski(X3)),k1_tarski(X4))
        | v2_funct_1(sK0) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f1490,plain,
    ( ? [X1] :
      ! [X2] : ~ r1_tarski(k10_relat_1(sK0,k1_tarski(X1)),k1_tarski(X2))
   => ! [X2] : ~ r1_tarski(k10_relat_1(sK0,k1_tarski(sK1)),k1_tarski(X2)) ),
    introduced(choice_axiom,[])).

fof(f1491,plain,(
    ! [X3] :
      ( ? [X4] : r1_tarski(k10_relat_1(sK0,k1_tarski(X3)),k1_tarski(X4))
     => r1_tarski(k10_relat_1(sK0,k1_tarski(X3)),k1_tarski(sK2(X3))) ) ),
    introduced(choice_axiom,[])).

fof(f1488,plain,(
    ? [X0] :
      ( ( ? [X1] :
          ! [X2] : ~ r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2))
        | ~ v2_funct_1(X0) )
      & ( ! [X3] :
          ? [X4] : r1_tarski(k10_relat_1(X0,k1_tarski(X3)),k1_tarski(X4))
        | v2_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(rectify,[],[f1487])).

fof(f1487,plain,(
    ? [X0] :
      ( ( ? [X1] :
          ! [X2] : ~ r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2))
        | ~ v2_funct_1(X0) )
      & ( ! [X1] :
          ? [X2] : r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2))
        | v2_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f1486])).

fof(f1486,plain,(
    ? [X0] :
      ( ( ? [X1] :
          ! [X2] : ~ r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2))
        | ~ v2_funct_1(X0) )
      & ( ! [X1] :
          ? [X2] : r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2))
        | v2_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1025])).

fof(f1025,plain,(
    ? [X0] :
      ( ( v2_funct_1(X0)
      <~> ! [X1] :
          ? [X2] : r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2)) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f1024])).

fof(f1024,plain,(
    ? [X0] :
      ( ( v2_funct_1(X0)
      <~> ! [X1] :
          ? [X2] : r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2)) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f962])).

fof(f962,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
        <=> ! [X1] :
            ? [X2] : r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2)) ) ) ),
    inference(negated_conjecture,[],[f961])).

fof(f961,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1] :
          ? [X2] : r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_funct_1)).

fof(f1755,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f1492])).

fof(f3197,plain,
    ( spl101_26
    | spl101_30
    | ~ spl101_3 ),
    inference(avatar_split_clause,[],[f3193,f2593,f3195,f3177])).

fof(f3177,plain,
    ( spl101_26
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_26])])).

fof(f3195,plain,
    ( spl101_30
  <=> ! [X5] :
        ( ~ r1_xboole_0(k2_relat_1(sK0),k1_tarski(X5))
        | r2_hidden(sK60(k1_xboole_0),k1_tarski(sK2(X5))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_30])])).

fof(f2593,plain,
    ( spl101_3
  <=> ! [X3] : r1_tarski(k10_relat_1(sK0,k1_tarski(X3)),k1_tarski(sK2(X3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_3])])).

fof(f3193,plain,
    ( ! [X5] :
        ( ~ r1_xboole_0(k2_relat_1(sK0),k1_tarski(X5))
        | v1_relat_1(k1_xboole_0)
        | r2_hidden(sK60(k1_xboole_0),k1_tarski(sK2(X5))) )
    | ~ spl101_3 ),
    inference(global_subsumption,[],[f1754,f3174])).

fof(f3174,plain,
    ( ! [X5] :
        ( r2_hidden(sK60(k1_xboole_0),k1_tarski(sK2(X5)))
        | v1_relat_1(k1_xboole_0)
        | ~ r1_xboole_0(k2_relat_1(sK0),k1_tarski(X5))
        | ~ v1_relat_1(sK0) )
    | ~ spl101_3 ),
    inference(superposition,[],[f2744,f1784])).

fof(f1784,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k10_relat_1(X1,X0)
      | ~ r1_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1499])).

fof(f1499,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k10_relat_1(X1,X0)
          | ~ r1_xboole_0(k2_relat_1(X1),X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 != k10_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f1058])).

fof(f1058,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f775])).

fof(f775,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

fof(f2744,plain,
    ( ! [X137] :
        ( r2_hidden(sK60(k10_relat_1(sK0,k1_tarski(X137))),k1_tarski(sK2(X137)))
        | v1_relat_1(k10_relat_1(sK0,k1_tarski(X137))) )
    | ~ spl101_3 ),
    inference(resolution,[],[f2690,f2046])).

fof(f2046,plain,(
    ! [X0] :
      ( r2_hidden(sK60(X0),X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1625])).

fof(f1625,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ( ! [X2,X3] : k4_tarski(X2,X3) != sK60(X0)
          & r2_hidden(sK60(X0),X0) ) )
      & ( ! [X4] :
            ( k4_tarski(sK61(X4),sK62(X4)) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK60,sK61,sK62])],[f1622,f1624,f1623])).

fof(f1623,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK60(X0)
        & r2_hidden(sK60(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1624,plain,(
    ! [X4] :
      ( ? [X5,X6] : k4_tarski(X5,X6) = X4
     => k4_tarski(sK61(X4),sK62(X4)) = X4 ) ),
    introduced(choice_axiom,[])).

fof(f1622,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X4] :
            ( ? [X5,X6] : k4_tarski(X5,X6) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(rectify,[],[f1621])).

fof(f1621,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( ? [X2,X3] : k4_tarski(X2,X3) = X1
            | ~ r2_hidden(X1,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(nnf_transformation,[],[f1195])).

fof(f1195,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f653])).

fof(f653,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(f2690,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,k10_relat_1(sK0,k1_tarski(X3)))
        | r2_hidden(X2,k1_tarski(sK2(X3))) )
    | ~ spl101_3 ),
    inference(resolution,[],[f2594,f2071])).

fof(f2071,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f1652])).

fof(f1652,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK76(X0,X1),X1)
          & r2_hidden(sK76(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK76])],[f1650,f1651])).

fof(f1651,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK76(X0,X1),X1)
        & r2_hidden(sK76(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1650,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f1649])).

fof(f1649,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1203])).

fof(f1203,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f2594,plain,
    ( ! [X3] : r1_tarski(k10_relat_1(sK0,k1_tarski(X3)),k1_tarski(sK2(X3)))
    | ~ spl101_3 ),
    inference(avatar_component_clause,[],[f2593])).

fof(f3192,plain,
    ( spl101_26
    | spl101_29
    | ~ spl101_3 ),
    inference(avatar_split_clause,[],[f3188,f2593,f3190,f3177])).

fof(f3190,plain,
    ( spl101_29
  <=> ! [X4] :
        ( r2_hidden(sK60(k1_xboole_0),k1_tarski(sK2(sK4(X4,sK0))))
        | r1_tarski(X4,k2_relat_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_29])])).

fof(f3188,plain,
    ( ! [X4] :
        ( r2_hidden(sK60(k1_xboole_0),k1_tarski(sK2(sK4(X4,sK0))))
        | v1_relat_1(k1_xboole_0)
        | r1_tarski(X4,k2_relat_1(sK0)) )
    | ~ spl101_3 ),
    inference(global_subsumption,[],[f1754,f3173])).

fof(f3173,plain,
    ( ! [X4] :
        ( r2_hidden(sK60(k1_xboole_0),k1_tarski(sK2(sK4(X4,sK0))))
        | v1_relat_1(k1_xboole_0)
        | r1_tarski(X4,k2_relat_1(sK0))
        | ~ v1_relat_1(sK0) )
    | ~ spl101_3 ),
    inference(superposition,[],[f2744,f1788])).

fof(f1788,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(sK4(X0,X1)))
      | r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1502])).

fof(f1502,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_relat_1(X1))
      | ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(sK4(X0,X1)))
        & r2_hidden(sK4(X0,X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f1061,f1501])).

fof(f1501,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X2))
          & r2_hidden(X2,X0) )
     => ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(sK4(X0,X1)))
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1061,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_relat_1(X1))
      | ? [X2] :
          ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X2))
          & r2_hidden(X2,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1060])).

fof(f1060,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_relat_1(X1))
      | ? [X2] :
          ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X2))
          & r2_hidden(X2,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f944])).

fof(f944,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( ! [X2] :
            ~ ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X2))
              & r2_hidden(X2,X0) )
       => r1_tarski(X0,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_funct_1)).

fof(f3187,plain,
    ( spl101_26
    | spl101_28
    | ~ spl101_3 ),
    inference(avatar_split_clause,[],[f3183,f2593,f3185,f3177])).

fof(f3185,plain,
    ( spl101_28
  <=> ! [X3] :
        ( r2_hidden(X3,k2_relat_1(sK0))
        | r2_hidden(sK60(k1_xboole_0),k1_tarski(sK2(X3))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_28])])).

fof(f3183,plain,
    ( ! [X3] :
        ( r2_hidden(X3,k2_relat_1(sK0))
        | r2_hidden(sK60(k1_xboole_0),k1_tarski(sK2(X3)))
        | v1_relat_1(k1_xboole_0) )
    | ~ spl101_3 ),
    inference(global_subsumption,[],[f1754,f3172])).

fof(f3172,plain,
    ( ! [X3] :
        ( r2_hidden(sK60(k1_xboole_0),k1_tarski(sK2(X3)))
        | v1_relat_1(k1_xboole_0)
        | r2_hidden(X3,k2_relat_1(sK0))
        | ~ v1_relat_1(sK0) )
    | ~ spl101_3 ),
    inference(superposition,[],[f2744,f1786])).

fof(f1786,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))
      | r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1500])).

fof(f1500,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,k2_relat_1(X1))
          | k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0)) )
        & ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
          | ~ r2_hidden(X0,k2_relat_1(X1)) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f1059])).

fof(f1059,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k2_relat_1(X1))
      <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f943])).

fof(f943,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k2_relat_1(X1))
      <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).

fof(f3182,plain,
    ( spl101_26
    | spl101_27
    | ~ spl101_3
    | ~ spl101_17 ),
    inference(avatar_split_clause,[],[f3170,f2817,f2593,f3180,f3177])).

fof(f3180,plain,
    ( spl101_27
  <=> r2_hidden(sK60(k1_xboole_0),k1_tarski(sK2(sK6(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_27])])).

fof(f2817,plain,
    ( spl101_17
  <=> k1_xboole_0 = k10_relat_1(sK0,k1_tarski(sK6(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_17])])).

fof(f3170,plain,
    ( r2_hidden(sK60(k1_xboole_0),k1_tarski(sK2(sK6(sK0))))
    | v1_relat_1(k1_xboole_0)
    | ~ spl101_3
    | ~ spl101_17 ),
    inference(superposition,[],[f2744,f2818])).

fof(f2818,plain,
    ( k1_xboole_0 = k10_relat_1(sK0,k1_tarski(sK6(sK0)))
    | ~ spl101_17 ),
    inference(avatar_component_clause,[],[f2817])).

fof(f3071,plain,
    ( spl101_25
    | ~ spl101_17 ),
    inference(avatar_split_clause,[],[f3067,f2817,f3069])).

fof(f3069,plain,
    ( spl101_25
  <=> r1_xboole_0(k2_relat_1(sK0),k1_tarski(sK6(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_25])])).

fof(f3067,plain,
    ( r1_xboole_0(k2_relat_1(sK0),k1_tarski(sK6(sK0)))
    | ~ spl101_17 ),
    inference(global_subsumption,[],[f1754,f3012])).

fof(f3012,plain,
    ( r1_xboole_0(k2_relat_1(sK0),k1_tarski(sK6(sK0)))
    | ~ v1_relat_1(sK0)
    | ~ spl101_17 ),
    inference(trivial_inequality_removal,[],[f3006])).

fof(f3006,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k2_relat_1(sK0),k1_tarski(sK6(sK0)))
    | ~ v1_relat_1(sK0)
    | ~ spl101_17 ),
    inference(superposition,[],[f1783,f2818])).

fof(f1783,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | r1_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1499])).

fof(f3066,plain,
    ( spl101_24
    | ~ spl101_21
    | ~ spl101_17 ),
    inference(avatar_split_clause,[],[f3062,f2817,f3027,f3064])).

fof(f3064,plain,
    ( spl101_24
  <=> k1_xboole_0 = k1_tarski(sK6(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_24])])).

fof(f3027,plain,
    ( spl101_21
  <=> r1_tarski(k1_tarski(sK6(sK0)),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_21])])).

fof(f3062,plain,
    ( ~ r1_tarski(k1_tarski(sK6(sK0)),k2_relat_1(sK0))
    | k1_xboole_0 = k1_tarski(sK6(sK0))
    | ~ spl101_17 ),
    inference(global_subsumption,[],[f1754,f3013])).

fof(f3013,plain,
    ( ~ r1_tarski(k1_tarski(sK6(sK0)),k2_relat_1(sK0))
    | k1_xboole_0 = k1_tarski(sK6(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl101_17 ),
    inference(trivial_inequality_removal,[],[f3005])).

fof(f3005,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_tarski(k1_tarski(sK6(sK0)),k2_relat_1(sK0))
    | k1_xboole_0 = k1_tarski(sK6(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl101_17 ),
    inference(superposition,[],[f1782,f2818])).

fof(f1782,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1057])).

fof(f1057,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1056])).

fof(f1056,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f776])).

fof(f776,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k10_relat_1(X1,X0)
          & r1_tarski(X0,k2_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_relat_1)).

fof(f3060,plain,
    ( spl101_23
    | ~ spl101_17 ),
    inference(avatar_split_clause,[],[f3056,f2817,f3058])).

fof(f3058,plain,
    ( spl101_23
  <=> r1_tarski(k9_relat_1(sK0,k1_xboole_0),k1_tarski(sK6(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_23])])).

fof(f3056,plain,
    ( r1_tarski(k9_relat_1(sK0,k1_xboole_0),k1_tarski(sK6(sK0)))
    | ~ spl101_17 ),
    inference(global_subsumption,[],[f1755,f1754,f3002])).

fof(f3002,plain,
    ( r1_tarski(k9_relat_1(sK0,k1_xboole_0),k1_tarski(sK6(sK0)))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl101_17 ),
    inference(superposition,[],[f1779,f2818])).

fof(f1779,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1052])).

fof(f1052,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1051])).

fof(f1051,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f946])).

fof(f946,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(f3055,plain,
    ( ~ spl101_21
    | spl101_22
    | ~ spl101_17 ),
    inference(avatar_split_clause,[],[f3051,f2817,f3053,f3027])).

fof(f3053,plain,
    ( spl101_22
  <=> k1_tarski(sK6(sK0)) = k9_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_22])])).

fof(f3051,plain,
    ( k1_tarski(sK6(sK0)) = k9_relat_1(sK0,k1_xboole_0)
    | ~ r1_tarski(k1_tarski(sK6(sK0)),k2_relat_1(sK0))
    | ~ spl101_17 ),
    inference(global_subsumption,[],[f1755,f1754,f3001])).

fof(f3001,plain,
    ( k1_tarski(sK6(sK0)) = k9_relat_1(sK0,k1_xboole_0)
    | ~ r1_tarski(k1_tarski(sK6(sK0)),k2_relat_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl101_17 ),
    inference(superposition,[],[f1776,f2818])).

fof(f1776,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1046])).

fof(f1046,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1045])).

fof(f1045,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f948])).

fof(f948,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(f3029,plain,
    ( spl101_20
    | ~ spl101_21
    | ~ spl101_17 ),
    inference(avatar_split_clause,[],[f3022,f2817,f3027,f3024])).

fof(f3024,plain,
    ( spl101_20
  <=> ! [X6] :
        ( ~ r1_tarski(k1_xboole_0,k10_relat_1(sK0,X6))
        | r1_tarski(k1_tarski(sK6(sK0)),X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_20])])).

fof(f3022,plain,
    ( ! [X6] :
        ( ~ r1_tarski(k1_tarski(sK6(sK0)),k2_relat_1(sK0))
        | ~ r1_tarski(k1_xboole_0,k10_relat_1(sK0,X6))
        | r1_tarski(k1_tarski(sK6(sK0)),X6) )
    | ~ spl101_17 ),
    inference(global_subsumption,[],[f1755,f1754,f2986])).

fof(f2986,plain,
    ( ! [X6] :
        ( ~ r1_tarski(k1_xboole_0,k10_relat_1(sK0,X6))
        | ~ r1_tarski(k1_tarski(sK6(sK0)),k2_relat_1(sK0))
        | r1_tarski(k1_tarski(sK6(sK0)),X6)
        | ~ v1_funct_1(sK0)
        | ~ v1_relat_1(sK0) )
    | ~ spl101_17 ),
    inference(superposition,[],[f1762,f2818])).

fof(f1762,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,k2_relat_1(X2))
      | r1_tarski(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1029])).

fof(f1029,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k2_relat_1(X2))
      | ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1028])).

fof(f1028,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k2_relat_1(X2))
      | ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f960])).

fof(f960,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(X0,k2_relat_1(X2))
          & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).

fof(f3020,plain,
    ( ~ spl101_19
    | ~ spl101_17 ),
    inference(avatar_split_clause,[],[f3016,f2817,f3018])).

fof(f3016,plain,
    ( ~ r2_hidden(sK6(sK0),k2_relat_1(sK0))
    | ~ spl101_17 ),
    inference(global_subsumption,[],[f1754,f3014])).

fof(f3014,plain,
    ( ~ r2_hidden(sK6(sK0),k2_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl101_17 ),
    inference(trivial_inequality_removal,[],[f2984])).

fof(f2984,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r2_hidden(sK6(sK0),k2_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl101_17 ),
    inference(superposition,[],[f1785,f2818])).

fof(f1785,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1500])).

fof(f2973,plain,(
    ~ spl101_16 ),
    inference(avatar_contradiction_clause,[],[f2972])).

fof(f2972,plain,
    ( $false
    | ~ spl101_16 ),
    inference(equality_resolution,[],[f2815])).

fof(f2815,plain,
    ( ! [X7] : k1_tarski(X7) != k1_tarski(sK2(sK6(sK0)))
    | ~ spl101_16 ),
    inference(avatar_component_clause,[],[f2814])).

fof(f2814,plain,
    ( spl101_16
  <=> ! [X7] : k1_tarski(X7) != k1_tarski(sK2(sK6(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_16])])).

fof(f2969,plain,
    ( spl101_7
    | spl101_15 ),
    inference(avatar_contradiction_clause,[],[f2968])).

fof(f2968,plain,
    ( $false
    | spl101_7
    | spl101_15 ),
    inference(global_subsumption,[],[f2618,f2957])).

fof(f2957,plain,
    ( r2_hidden(sK1,k2_relat_1(sK0))
    | spl101_15 ),
    inference(resolution,[],[f2661,f2221])).

fof(f2221,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1348])).

fof(f1348,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f414])).

fof(f414,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_zfmisc_1)).

fof(f2661,plain,
    ( ~ r1_xboole_0(k1_tarski(sK1),k2_relat_1(sK0))
    | spl101_15 ),
    inference(avatar_component_clause,[],[f2660])).

fof(f2660,plain,
    ( spl101_15
  <=> r1_xboole_0(k1_tarski(sK1),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_15])])).

fof(f2618,plain,
    ( ~ r2_hidden(sK1,k2_relat_1(sK0))
    | spl101_7 ),
    inference(avatar_component_clause,[],[f2617])).

fof(f2617,plain,
    ( spl101_7
  <=> r2_hidden(sK1,k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_7])])).

fof(f2967,plain,
    ( spl101_7
    | spl101_15 ),
    inference(avatar_contradiction_clause,[],[f2966])).

fof(f2966,plain,
    ( $false
    | spl101_7
    | spl101_15 ),
    inference(global_subsumption,[],[f2618,f2957])).

fof(f2965,plain,
    ( spl101_7
    | spl101_15 ),
    inference(avatar_contradiction_clause,[],[f2964])).

fof(f2964,plain,
    ( $false
    | spl101_7
    | spl101_15 ),
    inference(global_subsumption,[],[f2618,f2957])).

fof(f2963,plain,
    ( spl101_7
    | spl101_15 ),
    inference(avatar_contradiction_clause,[],[f2962])).

fof(f2962,plain,
    ( $false
    | spl101_7
    | spl101_15 ),
    inference(global_subsumption,[],[f2618,f2956])).

fof(f2956,plain,
    ( r2_hidden(sK1,k2_relat_1(sK0))
    | spl101_15 ),
    inference(resolution,[],[f2661,f2222])).

fof(f2222,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1349])).

fof(f1349,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f306])).

fof(f306,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f2953,plain,
    ( ~ spl101_18
    | spl101_13 ),
    inference(avatar_split_clause,[],[f2949,f2649,f2951])).

fof(f2951,plain,
    ( spl101_18
  <=> k1_xboole_0 = k2_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_18])])).

fof(f2649,plain,
    ( spl101_13
  <=> k1_xboole_0 = k1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_13])])).

fof(f2949,plain,
    ( k1_xboole_0 != k2_relat_1(sK0)
    | spl101_13 ),
    inference(global_subsumption,[],[f1754,f2948])).

fof(f2948,plain,
    ( k1_xboole_0 != k2_relat_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl101_13 ),
    inference(trivial_inequality_removal,[],[f2947])).

fof(f2947,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 != k2_relat_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl101_13 ),
    inference(superposition,[],[f2650,f1901])).

fof(f1901,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1552])).

fof(f1552,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1129])).

fof(f1129,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f860])).

fof(f860,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(f2650,plain,
    ( k1_xboole_0 != k1_relat_1(sK0)
    | spl101_13 ),
    inference(avatar_component_clause,[],[f2649])).

fof(f2819,plain,
    ( spl101_16
    | spl101_17
    | spl101_1
    | ~ spl101_3 ),
    inference(avatar_split_clause,[],[f2812,f2593,f2585,f2817,f2814])).

fof(f2812,plain,
    ( ! [X7] :
        ( k1_xboole_0 = k10_relat_1(sK0,k1_tarski(sK6(sK0)))
        | k1_tarski(X7) != k1_tarski(sK2(sK6(sK0))) )
    | spl101_1
    | ~ spl101_3 ),
    inference(global_subsumption,[],[f1755,f1754,f2586,f2781])).

fof(f2781,plain,
    ( ! [X7] :
        ( k1_tarski(X7) != k1_tarski(sK2(sK6(sK0)))
        | v2_funct_1(sK0)
        | ~ v1_funct_1(sK0)
        | ~ v1_relat_1(sK0)
        | k1_xboole_0 = k10_relat_1(sK0,k1_tarski(sK6(sK0))) )
    | ~ spl101_3 ),
    inference(superposition,[],[f1795,f2688])).

fof(f2688,plain,
    ( ! [X0] :
        ( k10_relat_1(sK0,k1_tarski(X0)) = k1_tarski(sK2(X0))
        | k1_xboole_0 = k10_relat_1(sK0,k1_tarski(X0)) )
    | ~ spl101_3 ),
    inference(resolution,[],[f2594,f1828])).

fof(f1828,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f1525])).

fof(f1525,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f1524])).

fof(f1524,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f313])).

fof(f313,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f1795,plain,(
    ! [X4,X0] :
      ( k1_tarski(X4) != k10_relat_1(X0,k1_tarski(sK6(X0)))
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1507])).

fof(f2686,plain,(
    ~ spl101_9 ),
    inference(avatar_contradiction_clause,[],[f2677])).

fof(f2677,plain,
    ( $false
    | ~ spl101_9 ),
    inference(resolution,[],[f2627,f2503])).

fof(f2503,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k1_tarski(X1)) ),
    inference(equality_resolution,[],[f1829])).

fof(f1829,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f1525])).

fof(f2627,plain,
    ( ! [X1] : ~ r1_tarski(k1_xboole_0,k1_tarski(X1))
    | ~ spl101_9 ),
    inference(avatar_component_clause,[],[f2626])).

fof(f2626,plain,
    ( spl101_9
  <=> ! [X1] : ~ r1_tarski(k1_xboole_0,k1_tarski(X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_9])])).

fof(f2685,plain,(
    ~ spl101_9 ),
    inference(avatar_contradiction_clause,[],[f2678])).

fof(f2678,plain,
    ( $false
    | ~ spl101_9 ),
    inference(resolution,[],[f2627,f2501])).

fof(f2501,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k1_tarski(X1)) ),
    inference(equality_resolution,[],[f1826])).

fof(f1826,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f1523])).

fof(f1523,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f1522])).

fof(f1522,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f397])).

fof(f397,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_zfmisc_1)).

fof(f2684,plain,(
    ~ spl101_9 ),
    inference(avatar_contradiction_clause,[],[f2679])).

fof(f2679,plain,
    ( $false
    | ~ spl101_9 ),
    inference(resolution,[],[f2627,f2180])).

fof(f2180,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f2675,plain,(
    ~ spl101_8 ),
    inference(avatar_contradiction_clause,[],[f2663])).

fof(f2663,plain,
    ( $false
    | ~ spl101_8 ),
    inference(resolution,[],[f2621,f2502])).

fof(f2502,plain,(
    ! [X1] : r1_tarski(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f1830])).

fof(f1830,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_tarski(X1) != X0 ) ),
    inference(cnf_transformation,[],[f1525])).

fof(f2621,plain,
    ( ! [X0] : ~ r1_tarski(k1_tarski(sK5(sK0,sK1)),k1_tarski(X0))
    | ~ spl101_8 ),
    inference(avatar_component_clause,[],[f2620])).

fof(f2620,plain,
    ( spl101_8
  <=> ! [X0] : ~ r1_tarski(k1_tarski(sK5(sK0,sK1)),k1_tarski(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_8])])).

fof(f2674,plain,(
    ~ spl101_8 ),
    inference(avatar_contradiction_clause,[],[f2664])).

fof(f2664,plain,
    ( $false
    | ~ spl101_8 ),
    inference(resolution,[],[f2621,f2500])).

fof(f2500,plain,(
    ! [X1] : r1_tarski(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f1827])).

fof(f1827,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_tarski(X1) != X0 ) ),
    inference(cnf_transformation,[],[f1523])).

fof(f2673,plain,(
    ~ spl101_8 ),
    inference(avatar_contradiction_clause,[],[f2667])).

fof(f2667,plain,
    ( $false
    | ~ spl101_8 ),
    inference(resolution,[],[f2621,f2496])).

fof(f2496,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f1759])).

fof(f1759,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1494])).

fof(f1494,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f1493])).

fof(f1493,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f2672,plain,(
    ~ spl101_8 ),
    inference(avatar_contradiction_clause,[],[f2668])).

fof(f2668,plain,
    ( $false
    | ~ spl101_8 ),
    inference(resolution,[],[f2621,f2495])).

fof(f2495,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f1760])).

fof(f1760,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1494])).

fof(f2662,plain,
    ( ~ spl101_15
    | spl101_10 ),
    inference(avatar_split_clause,[],[f2655,f2631,f2660])).

fof(f2631,plain,
    ( spl101_10
  <=> r1_xboole_0(k2_relat_1(sK0),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_10])])).

fof(f2655,plain,
    ( ~ r1_xboole_0(k1_tarski(sK1),k2_relat_1(sK0))
    | spl101_10 ),
    inference(resolution,[],[f2632,f2220])).

fof(f2220,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1347])).

fof(f1347,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f2632,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK0),k1_tarski(sK1))
    | spl101_10 ),
    inference(avatar_component_clause,[],[f2631])).

fof(f2654,plain,
    ( ~ spl101_13
    | spl101_14
    | ~ spl101_7 ),
    inference(avatar_split_clause,[],[f2647,f2617,f2652,f2649])).

fof(f2652,plain,
    ( spl101_14
  <=> r2_hidden(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_14])])).

fof(f2647,plain,
    ( r2_hidden(sK1,k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(sK0)
    | ~ spl101_7 ),
    inference(global_subsumption,[],[f1754,f2637])).

fof(f2637,plain,
    ( r2_hidden(sK1,k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl101_7 ),
    inference(superposition,[],[f2624,f1900])).

fof(f1900,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1552])).

fof(f2624,plain,
    ( r2_hidden(sK1,k2_relat_1(sK0))
    | ~ spl101_7 ),
    inference(avatar_component_clause,[],[f2617])).

fof(f2646,plain,
    ( ~ spl101_12
    | ~ spl101_7 ),
    inference(avatar_split_clause,[],[f2636,f2617,f2644])).

fof(f2644,plain,
    ( spl101_12
  <=> r2_hidden(k2_relat_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_12])])).

fof(f2636,plain,
    ( ~ r2_hidden(k2_relat_1(sK0),sK1)
    | ~ spl101_7 ),
    inference(resolution,[],[f2624,f2076])).

fof(f2076,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1205])).

fof(f1205,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f2642,plain,
    ( ~ spl101_11
    | ~ spl101_7 ),
    inference(avatar_split_clause,[],[f2635,f2617,f2639])).

fof(f2639,plain,
    ( spl101_11
  <=> v1_xboole_0(k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_11])])).

fof(f2635,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK0))
    | ~ spl101_7 ),
    inference(resolution,[],[f2624,f2246])).

fof(f2246,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f1363])).

fof(f1363,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f148])).

fof(f148,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f2641,plain,
    ( ~ spl101_11
    | ~ spl101_7 ),
    inference(avatar_split_clause,[],[f2634,f2617,f2639])).

fof(f2634,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK0))
    | ~ spl101_7 ),
    inference(resolution,[],[f2624,f2263])).

fof(f2263,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1690])).

fof(f1690,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK89(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK89])],[f1688,f1689])).

fof(f1689,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK89(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1688,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f1687])).

fof(f1687,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f2633,plain,
    ( spl101_9
    | ~ spl101_10
    | ~ spl101_2 ),
    inference(avatar_split_clause,[],[f2629,f2588,f2631,f2626])).

fof(f2588,plain,
    ( spl101_2
  <=> ! [X2] : ~ r1_tarski(k10_relat_1(sK0,k1_tarski(sK1)),k1_tarski(X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_2])])).

fof(f2629,plain,
    ( ! [X2] :
        ( ~ r1_xboole_0(k2_relat_1(sK0),k1_tarski(sK1))
        | ~ r1_tarski(k1_xboole_0,k1_tarski(X2)) )
    | ~ spl101_2 ),
    inference(global_subsumption,[],[f1754,f2613])).

fof(f2613,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k1_xboole_0,k1_tarski(X2))
        | ~ r1_xboole_0(k2_relat_1(sK0),k1_tarski(sK1))
        | ~ v1_relat_1(sK0) )
    | ~ spl101_2 ),
    inference(superposition,[],[f2589,f1784])).

fof(f2589,plain,
    ( ! [X2] : ~ r1_tarski(k10_relat_1(sK0,k1_tarski(sK1)),k1_tarski(X2))
    | ~ spl101_2 ),
    inference(avatar_component_clause,[],[f2588])).

fof(f2628,plain,
    ( spl101_7
    | spl101_9
    | ~ spl101_2 ),
    inference(avatar_split_clause,[],[f2623,f2588,f2626,f2617])).

fof(f2623,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k1_xboole_0,k1_tarski(X1))
        | r2_hidden(sK1,k2_relat_1(sK0)) )
    | ~ spl101_2 ),
    inference(global_subsumption,[],[f1754,f2612])).

fof(f2612,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k1_xboole_0,k1_tarski(X1))
        | r2_hidden(sK1,k2_relat_1(sK0))
        | ~ v1_relat_1(sK0) )
    | ~ spl101_2 ),
    inference(superposition,[],[f2589,f1786])).

fof(f2622,plain,
    ( ~ spl101_7
    | spl101_8
    | ~ spl101_1
    | ~ spl101_2 ),
    inference(avatar_split_clause,[],[f2615,f2588,f2585,f2620,f2617])).

fof(f2615,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_tarski(sK5(sK0,sK1)),k1_tarski(X0))
        | ~ r2_hidden(sK1,k2_relat_1(sK0)) )
    | ~ spl101_1
    | ~ spl101_2 ),
    inference(global_subsumption,[],[f1755,f1754,f2591,f2611])).

fof(f2611,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_tarski(sK5(sK0,sK1)),k1_tarski(X0))
        | ~ r2_hidden(sK1,k2_relat_1(sK0))
        | ~ v2_funct_1(sK0)
        | ~ v1_funct_1(sK0)
        | ~ v1_relat_1(sK0) )
    | ~ spl101_2 ),
    inference(superposition,[],[f2589,f1796])).

fof(f1796,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X0,k1_tarski(X1)) = k1_tarski(sK5(X0,X1))
      | ~ r2_hidden(X1,k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1507])).

fof(f2591,plain,
    ( v2_funct_1(sK0)
    | ~ spl101_1 ),
    inference(avatar_component_clause,[],[f2585])).

fof(f2609,plain,
    ( ~ spl101_6
    | spl101_1 ),
    inference(avatar_split_clause,[],[f2605,f2585,f2607])).

fof(f2607,plain,
    ( spl101_6
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_6])])).

fof(f2605,plain,
    ( ~ v1_xboole_0(sK0)
    | spl101_1 ),
    inference(global_subsumption,[],[f1755,f1754,f2604])).

fof(f2604,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_xboole_0(sK0)
    | spl101_1 ),
    inference(resolution,[],[f2586,f1870])).

fof(f1870,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1111])).

fof(f1111,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f1110])).

fof(f1110,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f890])).

fof(f890,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0)
        & v1_xboole_0(X0) )
     => ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_1)).

fof(f2603,plain,(
    spl101_5 ),
    inference(avatar_split_clause,[],[f1754,f2601])).

fof(f2601,plain,
    ( spl101_5
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_5])])).

fof(f2599,plain,(
    spl101_4 ),
    inference(avatar_split_clause,[],[f1755,f2597])).

fof(f2597,plain,
    ( spl101_4
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_4])])).

fof(f2595,plain,
    ( spl101_1
    | spl101_3 ),
    inference(avatar_split_clause,[],[f1756,f2593,f2585])).

fof(f1756,plain,(
    ! [X3] :
      ( r1_tarski(k10_relat_1(sK0,k1_tarski(X3)),k1_tarski(sK2(X3)))
      | v2_funct_1(sK0) ) ),
    inference(cnf_transformation,[],[f1492])).

fof(f2590,plain,
    ( ~ spl101_1
    | spl101_2 ),
    inference(avatar_split_clause,[],[f1757,f2588,f2585])).

fof(f1757,plain,(
    ! [X2] :
      ( ~ r1_tarski(k10_relat_1(sK0,k1_tarski(sK1)),k1_tarski(X2))
      | ~ v2_funct_1(sK0) ) ),
    inference(cnf_transformation,[],[f1492])).
%------------------------------------------------------------------------------
