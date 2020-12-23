%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0764+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:48 EST 2020

% Result     : Theorem 1.92s
% Output     : Refutation 2.44s
% Verified   : 
% Statistics : Number of formulae       :  189 ( 563 expanded)
%              Number of leaves         :   59 ( 222 expanded)
%              Depth                    :   12
%              Number of atoms          :  899 (2903 expanded)
%              Number of equality atoms :  123 ( 359 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2704,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2332,f2336,f2340,f2344,f2354,f2358,f2413,f2414,f2421,f2425,f2429,f2430,f2437,f2441,f2445,f2452,f2456,f2460,f2464,f2468,f2681,f2694,f2700,f2703])).

fof(f2703,plain,(
    ~ spl70_25 ),
    inference(avatar_contradiction_clause,[],[f2702])).

fof(f2702,plain,
    ( $false
    | ~ spl70_25 ),
    inference(global_subsumption,[],[f1693,f1692,f1691,f2701])).

fof(f2701,plain,
    ( ~ r1_tarski(sK1,k3_relat_1(sK0))
    | ~ v2_wellord1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl70_25 ),
    inference(resolution,[],[f2680,f1792])).

fof(f1792,plain,(
    ! [X0] :
      ( r2_wellord1(X0,k3_relat_1(X0))
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1562])).

fof(f1562,plain,(
    ! [X0] :
      ( ( ( r2_wellord1(X0,k3_relat_1(X0))
          | ~ v2_wellord1(X0) )
        & ( v2_wellord1(X0)
          | ~ r2_wellord1(X0,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1197])).

fof(f1197,plain,(
    ! [X0] :
      ( ( r2_wellord1(X0,k3_relat_1(X0))
      <=> v2_wellord1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1145])).

fof(f1145,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( r2_wellord1(X0,k3_relat_1(X0))
      <=> v2_wellord1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord1)).

fof(f2680,plain,
    ( ! [X0] :
        ( ~ r2_wellord1(sK0,X0)
        | ~ r1_tarski(sK1,X0) )
    | ~ spl70_25 ),
    inference(avatar_component_clause,[],[f2679])).

fof(f2679,plain,
    ( spl70_25
  <=> ! [X0] :
        ( ~ r2_wellord1(sK0,X0)
        | ~ r1_tarski(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl70_25])])).

fof(f1691,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f1498])).

fof(f1498,plain,
    ( ! [X2] :
        ( ( ~ r2_hidden(k4_tarski(X2,sK2(X2)),sK0)
          & r2_hidden(sK2(X2),sK1) )
        | ~ r2_hidden(X2,sK1) )
    & k1_xboole_0 != sK1
    & r1_tarski(sK1,k3_relat_1(sK0))
    & v2_wellord1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f1153,f1497,f1496,f1495])).

fof(f1495,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ! [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(k4_tarski(X2,X3),X0)
                    & r2_hidden(X3,X1) )
                | ~ r2_hidden(X2,X1) )
            & k1_xboole_0 != X1
            & r1_tarski(X1,k3_relat_1(X0)) )
        & v2_wellord1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k4_tarski(X2,X3),sK0)
                  & r2_hidden(X3,X1) )
              | ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1
          & r1_tarski(X1,k3_relat_1(sK0)) )
      & v2_wellord1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f1496,plain,
    ( ? [X1] :
        ( ! [X2] :
            ( ? [X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),sK0)
                & r2_hidden(X3,X1) )
            | ~ r2_hidden(X2,X1) )
        & k1_xboole_0 != X1
        & r1_tarski(X1,k3_relat_1(sK0)) )
   => ( ! [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(k4_tarski(X2,X3),sK0)
              & r2_hidden(X3,sK1) )
          | ~ r2_hidden(X2,sK1) )
      & k1_xboole_0 != sK1
      & r1_tarski(sK1,k3_relat_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f1497,plain,(
    ! [X2] :
      ( ? [X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),sK0)
          & r2_hidden(X3,sK1) )
     => ( ~ r2_hidden(k4_tarski(X2,sK2(X2)),sK0)
        & r2_hidden(sK2(X2),sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f1153,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k4_tarski(X2,X3),X0)
                  & r2_hidden(X3,X1) )
              | ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1
          & r1_tarski(X1,k3_relat_1(X0)) )
      & v2_wellord1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f1152])).

fof(f1152,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k4_tarski(X2,X3),X0)
                  & r2_hidden(X3,X1) )
              | ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1
          & r1_tarski(X1,k3_relat_1(X0)) )
      & v2_wellord1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1142])).

fof(f1142,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( v2_wellord1(X0)
         => ! [X1] :
              ~ ( ! [X2] :
                    ~ ( ! [X3] :
                          ( r2_hidden(X3,X1)
                         => r2_hidden(k4_tarski(X2,X3),X0) )
                      & r2_hidden(X2,X1) )
                & k1_xboole_0 != X1
                & r1_tarski(X1,k3_relat_1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f1141])).

fof(f1141,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ~ ( ! [X2] :
                  ~ ( ! [X3] :
                        ( r2_hidden(X3,X1)
                       => r2_hidden(k4_tarski(X2,X3),X0) )
                    & r2_hidden(X2,X1) )
              & k1_xboole_0 != X1
              & r1_tarski(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_wellord1)).

fof(f1692,plain,(
    v2_wellord1(sK0) ),
    inference(cnf_transformation,[],[f1498])).

fof(f1693,plain,(
    r1_tarski(sK1,k3_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f1498])).

fof(f2700,plain,(
    spl70_24 ),
    inference(avatar_contradiction_clause,[],[f2699])).

fof(f2699,plain,
    ( $false
    | spl70_24 ),
    inference(global_subsumption,[],[f1693,f1692,f1691,f2698])).

fof(f2698,plain,
    ( ~ r1_tarski(sK1,k3_relat_1(sK0))
    | ~ v2_wellord1(sK0)
    | ~ v1_relat_1(sK0)
    | spl70_24 ),
    inference(resolution,[],[f2697,f1792])).

fof(f2697,plain,
    ( ! [X0] :
        ( ~ r2_wellord1(sK0,X0)
        | ~ r1_tarski(sK1,X0) )
    | spl70_24 ),
    inference(global_subsumption,[],[f1694,f1691,f2696])).

fof(f2696,plain,
    ( ! [X0] :
        ( k1_xboole_0 = sK1
        | ~ r1_tarski(sK1,X0)
        | ~ r2_wellord1(sK0,X0)
        | ~ v1_relat_1(sK0) )
    | spl70_24 ),
    inference(resolution,[],[f2677,f2095])).

fof(f2095,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK58(X1,X2),X2)
      | k1_xboole_0 = X2
      | ~ r1_tarski(X2,X0)
      | ~ r2_wellord1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1646])).

fof(f1646,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ! [X4] :
                ( r2_hidden(k4_tarski(sK58(X1,X2),X4),X1)
                | ~ r2_hidden(X4,X2) )
            & r2_hidden(sK58(X1,X2),X2) )
          | k1_xboole_0 = X2
          | ~ r1_tarski(X2,X0) )
      | ~ r2_wellord1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK58])],[f1395,f1645])).

fof(f1645,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( ! [X4] :
              ( r2_hidden(k4_tarski(X3,X4),X1)
              | ~ r2_hidden(X4,X2) )
          & r2_hidden(X3,X2) )
     => ( ! [X4] :
            ( r2_hidden(k4_tarski(sK58(X1,X2),X4),X1)
            | ~ r2_hidden(X4,X2) )
        & r2_hidden(sK58(X1,X2),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f1395,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ? [X3] :
              ( ! [X4] :
                  ( r2_hidden(k4_tarski(X3,X4),X1)
                  | ~ r2_hidden(X4,X2) )
              & r2_hidden(X3,X2) )
          | k1_xboole_0 = X2
          | ~ r1_tarski(X2,X0) )
      | ~ r2_wellord1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1394])).

fof(f1394,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ? [X3] :
              ( ! [X4] :
                  ( r2_hidden(k4_tarski(X3,X4),X1)
                  | ~ r2_hidden(X4,X2) )
              & r2_hidden(X3,X2) )
          | k1_xboole_0 = X2
          | ~ r1_tarski(X2,X0) )
      | ~ r2_wellord1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1146])).

fof(f1146,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_wellord1(X1,X0)
       => ! [X2] :
            ~ ( ! [X3] :
                  ~ ( ! [X4] :
                        ( r2_hidden(X4,X2)
                       => r2_hidden(k4_tarski(X3,X4),X1) )
                    & r2_hidden(X3,X2) )
              & k1_xboole_0 != X2
              & r1_tarski(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_wellord1)).

fof(f2677,plain,
    ( ~ r2_hidden(sK58(sK0,sK1),sK1)
    | spl70_24 ),
    inference(avatar_component_clause,[],[f2676])).

fof(f2676,plain,
    ( spl70_24
  <=> r2_hidden(sK58(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl70_24])])).

fof(f1694,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f1498])).

fof(f2694,plain,
    ( ~ spl70_26
    | spl70_27
    | spl70_28
    | ~ spl70_29
    | ~ spl70_2 ),
    inference(avatar_split_clause,[],[f2672,f2334,f2692,f2689,f2686,f2683])).

fof(f2683,plain,
    ( spl70_26
  <=> r2_hidden(sK2(sK58(sK0,k3_relat_1(sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl70_26])])).

fof(f2686,plain,
    ( spl70_27
  <=> k1_xboole_0 = k3_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl70_27])])).

fof(f2689,plain,
    ( spl70_28
  <=> ! [X21] :
        ( ~ r1_tarski(k3_relat_1(sK0),X21)
        | ~ r2_wellord1(sK0,X21) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl70_28])])).

fof(f2692,plain,
    ( spl70_29
  <=> r2_hidden(sK58(sK0,k3_relat_1(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl70_29])])).

fof(f2334,plain,
    ( spl70_2
  <=> r1_tarski(sK1,k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl70_2])])).

fof(f2672,plain,
    ( ! [X21] :
        ( ~ r2_hidden(sK58(sK0,k3_relat_1(sK0)),sK1)
        | ~ r1_tarski(k3_relat_1(sK0),X21)
        | ~ r2_wellord1(sK0,X21)
        | k1_xboole_0 = k3_relat_1(sK0)
        | ~ r2_hidden(sK2(sK58(sK0,k3_relat_1(sK0))),sK1) )
    | ~ spl70_2 ),
    inference(resolution,[],[f2368,f2346])).

fof(f2346,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k3_relat_1(sK0))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl70_2 ),
    inference(resolution,[],[f2335,f1759])).

fof(f1759,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f1551])).

fof(f1551,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK32(X0,X1),X1)
          & r2_hidden(sK32(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK32])],[f1549,f1550])).

fof(f1550,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK32(X0,X1),X1)
        & r2_hidden(sK32(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1549,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f1548])).

fof(f1548,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1178])).

fof(f1178,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f2335,plain,
    ( r1_tarski(sK1,k3_relat_1(sK0))
    | ~ spl70_2 ),
    inference(avatar_component_clause,[],[f2334])).

fof(f2368,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(sK58(sK0,X0)),X0)
      | ~ r2_hidden(sK58(sK0,X0),sK1)
      | ~ r1_tarski(X0,X1)
      | ~ r2_wellord1(sK0,X1)
      | k1_xboole_0 = X0 ) ),
    inference(global_subsumption,[],[f1691,f2366])).

fof(f2366,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK58(sK0,X0),sK1)
      | ~ r2_hidden(sK2(sK58(sK0,X0)),X0)
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1)
      | ~ r2_wellord1(sK0,X1)
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f1696,f2096])).

fof(f2096,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK58(X1,X2),X4),X1)
      | ~ r2_hidden(X4,X2)
      | k1_xboole_0 = X2
      | ~ r1_tarski(X2,X0)
      | ~ r2_wellord1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1646])).

fof(f1696,plain,(
    ! [X2] :
      ( ~ r2_hidden(k4_tarski(X2,sK2(X2)),sK0)
      | ~ r2_hidden(X2,sK1) ) ),
    inference(cnf_transformation,[],[f1498])).

fof(f2681,plain,
    ( ~ spl70_24
    | spl70_25 ),
    inference(avatar_split_clause,[],[f2674,f2679,f2676])).

fof(f2674,plain,(
    ! [X0] :
      ( ~ r2_wellord1(sK0,X0)
      | ~ r2_hidden(sK58(sK0,sK1),sK1)
      | ~ r1_tarski(sK1,X0) ) ),
    inference(global_subsumption,[],[f1694,f2673])).

fof(f2673,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK58(sK0,sK1),sK1)
      | ~ r1_tarski(sK1,X0)
      | ~ r2_wellord1(sK0,X0)
      | k1_xboole_0 = sK1 ) ),
    inference(duplicate_literal_removal,[],[f2664])).

fof(f2664,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK58(sK0,sK1),sK1)
      | ~ r1_tarski(sK1,X0)
      | ~ r2_wellord1(sK0,X0)
      | k1_xboole_0 = sK1
      | ~ r2_hidden(sK58(sK0,sK1),sK1) ) ),
    inference(resolution,[],[f2368,f1695])).

fof(f1695,plain,(
    ! [X2] :
      ( r2_hidden(sK2(X2),sK1)
      | ~ r2_hidden(X2,sK1) ) ),
    inference(cnf_transformation,[],[f1498])).

fof(f2468,plain,
    ( ~ spl70_14
    | spl70_23
    | ~ spl70_2 ),
    inference(avatar_split_clause,[],[f2393,f2334,f2466,f2432])).

fof(f2432,plain,
    ( spl70_14
  <=> v1_relat_1(k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl70_14])])).

fof(f2466,plain,
    ( spl70_23
  <=> ! [X53,X52,X54] :
        ( ~ r2_hidden(k4_tarski(sK23(X52,X53,k3_relat_1(sK0)),sK24(X52,X53,k3_relat_1(sK0))),sK1)
        | ~ v1_relat_1(X52)
        | ~ v1_relat_1(X53)
        | k3_relat_1(sK0) = k5_relat_1(X52,X53)
        | ~ r2_hidden(k4_tarski(sK23(X52,X53,k3_relat_1(sK0)),X54),X52)
        | ~ r2_hidden(k4_tarski(X54,sK24(X52,X53,k3_relat_1(sK0))),X53) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl70_23])])).

fof(f2393,plain,
    ( ! [X54,X52,X53] :
        ( ~ r2_hidden(k4_tarski(sK23(X52,X53,k3_relat_1(sK0)),sK24(X52,X53,k3_relat_1(sK0))),sK1)
        | ~ r2_hidden(k4_tarski(X54,sK24(X52,X53,k3_relat_1(sK0))),X53)
        | ~ r2_hidden(k4_tarski(sK23(X52,X53,k3_relat_1(sK0)),X54),X52)
        | k3_relat_1(sK0) = k5_relat_1(X52,X53)
        | ~ v1_relat_1(k3_relat_1(sK0))
        | ~ v1_relat_1(X53)
        | ~ v1_relat_1(X52) )
    | ~ spl70_2 ),
    inference(resolution,[],[f2346,f1746])).

fof(f1746,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(sK23(X0,X1,X2),sK24(X0,X1,X2)),X2)
      | ~ r2_hidden(k4_tarski(X5,sK24(X0,X1,X2)),X1)
      | ~ r2_hidden(k4_tarski(sK23(X0,X1,X2),X5),X0)
      | k5_relat_1(X0,X1) = X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1539])).

fof(f1539,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ( ( ! [X5] :
                          ( ~ r2_hidden(k4_tarski(X5,sK24(X0,X1,X2)),X1)
                          | ~ r2_hidden(k4_tarski(sK23(X0,X1,X2),X5),X0) )
                      | ~ r2_hidden(k4_tarski(sK23(X0,X1,X2),sK24(X0,X1,X2)),X2) )
                    & ( ( r2_hidden(k4_tarski(sK25(X0,X1,X2),sK24(X0,X1,X2)),X1)
                        & r2_hidden(k4_tarski(sK23(X0,X1,X2),sK25(X0,X1,X2)),X0) )
                      | r2_hidden(k4_tarski(sK23(X0,X1,X2),sK24(X0,X1,X2)),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ( r2_hidden(k4_tarski(sK26(X0,X1,X7,X8),X8),X1)
                          & r2_hidden(k4_tarski(X7,sK26(X0,X1,X7,X8)),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK23,sK24,sK25,sK26])],[f1535,f1538,f1537,f1536])).

fof(f1536,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                | ~ r2_hidden(k4_tarski(X3,X5),X0) )
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ? [X6] :
                ( r2_hidden(k4_tarski(X6,X4),X1)
                & r2_hidden(k4_tarski(X3,X6),X0) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ! [X5] :
              ( ~ r2_hidden(k4_tarski(X5,sK24(X0,X1,X2)),X1)
              | ~ r2_hidden(k4_tarski(sK23(X0,X1,X2),X5),X0) )
          | ~ r2_hidden(k4_tarski(sK23(X0,X1,X2),sK24(X0,X1,X2)),X2) )
        & ( ? [X6] :
              ( r2_hidden(k4_tarski(X6,sK24(X0,X1,X2)),X1)
              & r2_hidden(k4_tarski(sK23(X0,X1,X2),X6),X0) )
          | r2_hidden(k4_tarski(sK23(X0,X1,X2),sK24(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1537,plain,(
    ! [X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,sK24(X0,X1,X2)),X1)
          & r2_hidden(k4_tarski(sK23(X0,X1,X2),X6),X0) )
     => ( r2_hidden(k4_tarski(sK25(X0,X1,X2),sK24(X0,X1,X2)),X1)
        & r2_hidden(k4_tarski(sK23(X0,X1,X2),sK25(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1538,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X1)
          & r2_hidden(k4_tarski(X7,X10),X0) )
     => ( r2_hidden(k4_tarski(sK26(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK26(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1535,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ? [X3,X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                      & ( ? [X6] :
                            ( r2_hidden(k4_tarski(X6,X4),X1)
                            & r2_hidden(k4_tarski(X3,X6),X0) )
                        | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ? [X10] :
                            ( r2_hidden(k4_tarski(X10,X8),X1)
                            & r2_hidden(k4_tarski(X7,X10),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f1534])).

fof(f1534,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ? [X3,X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                      & ( ? [X5] :
                            ( r2_hidden(k4_tarski(X5,X4),X1)
                            & r2_hidden(k4_tarski(X3,X5),X0) )
                        | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
                & ( ! [X3,X4] :
                      ( ( r2_hidden(k4_tarski(X3,X4),X2)
                        | ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) ) )
                      & ( ? [X5] :
                            ( r2_hidden(k4_tarski(X5,X4),X1)
                            & r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1168])).

fof(f1168,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f660])).

fof(f660,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).

fof(f2464,plain,
    ( ~ spl70_14
    | spl70_22
    | ~ spl70_2 ),
    inference(avatar_split_clause,[],[f2392,f2334,f2462,f2432])).

fof(f2462,plain,
    ( spl70_22
  <=> ! [X51,X50] :
        ( ~ r2_hidden(k4_tarski(sK19(X50,X51,k3_relat_1(sK0)),sK20(X50,X51,k3_relat_1(sK0))),sK1)
        | ~ v1_relat_1(X50)
        | k3_relat_1(sK0) = k7_relat_1(X50,X51)
        | ~ r2_hidden(sK19(X50,X51,k3_relat_1(sK0)),X51)
        | ~ r2_hidden(k4_tarski(sK19(X50,X51,k3_relat_1(sK0)),sK20(X50,X51,k3_relat_1(sK0))),X50) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl70_22])])).

fof(f2392,plain,
    ( ! [X50,X51] :
        ( ~ r2_hidden(k4_tarski(sK19(X50,X51,k3_relat_1(sK0)),sK20(X50,X51,k3_relat_1(sK0))),sK1)
        | ~ r2_hidden(k4_tarski(sK19(X50,X51,k3_relat_1(sK0)),sK20(X50,X51,k3_relat_1(sK0))),X50)
        | ~ r2_hidden(sK19(X50,X51,k3_relat_1(sK0)),X51)
        | k3_relat_1(sK0) = k7_relat_1(X50,X51)
        | ~ v1_relat_1(k3_relat_1(sK0))
        | ~ v1_relat_1(X50) )
    | ~ spl70_2 ),
    inference(resolution,[],[f2346,f1737])).

fof(f1737,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK19(X0,X1,X2),sK20(X0,X1,X2)),X2)
      | ~ r2_hidden(k4_tarski(sK19(X0,X1,X2),sK20(X0,X1,X2)),X0)
      | ~ r2_hidden(sK19(X0,X1,X2),X1)
      | k7_relat_1(X0,X1) = X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1529])).

fof(f1529,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK19(X0,X1,X2),sK20(X0,X1,X2)),X0)
                  | ~ r2_hidden(sK19(X0,X1,X2),X1)
                  | ~ r2_hidden(k4_tarski(sK19(X0,X1,X2),sK20(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK19(X0,X1,X2),sK20(X0,X1,X2)),X0)
                    & r2_hidden(sK19(X0,X1,X2),X1) )
                  | r2_hidden(k4_tarski(sK19(X0,X1,X2),sK20(X0,X1,X2)),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK19,sK20])],[f1527,f1528])).

fof(f1528,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK19(X0,X1,X2),sK20(X0,X1,X2)),X0)
          | ~ r2_hidden(sK19(X0,X1,X2),X1)
          | ~ r2_hidden(k4_tarski(sK19(X0,X1,X2),sK20(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK19(X0,X1,X2),sK20(X0,X1,X2)),X0)
            & r2_hidden(sK19(X0,X1,X2),X1) )
          | r2_hidden(k4_tarski(sK19(X0,X1,X2),sK20(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1527,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f1526])).

fof(f1526,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1525])).

fof(f1525,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1166])).

fof(f1166,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f645])).

fof(f645,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( v1_relat_1(X2)
         => ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_relat_1)).

fof(f2460,plain,
    ( ~ spl70_14
    | spl70_21
    | ~ spl70_2 ),
    inference(avatar_split_clause,[],[f2389,f2334,f2458,f2432])).

fof(f2458,plain,
    ( spl70_21
  <=> ! [X44,X45] :
        ( ~ r2_hidden(k4_tarski(X44,X45),sK1)
        | r2_hidden(X45,k3_relat_1(k3_relat_1(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl70_21])])).

fof(f2389,plain,
    ( ! [X45,X44] :
        ( ~ r2_hidden(k4_tarski(X44,X45),sK1)
        | r2_hidden(X45,k3_relat_1(k3_relat_1(sK0)))
        | ~ v1_relat_1(k3_relat_1(sK0)) )
    | ~ spl70_2 ),
    inference(resolution,[],[f2346,f1783])).

fof(f1783,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X1,k3_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1191])).

fof(f1191,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1190])).

fof(f1190,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f833])).

fof(f833,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relat_1)).

fof(f2456,plain,
    ( ~ spl70_14
    | spl70_20
    | ~ spl70_2 ),
    inference(avatar_split_clause,[],[f2388,f2334,f2454,f2432])).

fof(f2454,plain,
    ( spl70_20
  <=> ! [X42,X43] :
        ( ~ r2_hidden(k4_tarski(X42,X43),sK1)
        | r2_hidden(X42,k3_relat_1(k3_relat_1(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl70_20])])).

fof(f2388,plain,
    ( ! [X43,X42] :
        ( ~ r2_hidden(k4_tarski(X42,X43),sK1)
        | r2_hidden(X42,k3_relat_1(k3_relat_1(sK0)))
        | ~ v1_relat_1(k3_relat_1(sK0)) )
    | ~ spl70_2 ),
    inference(resolution,[],[f2346,f1782])).

fof(f1782,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X0,k3_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1191])).

fof(f2452,plain,
    ( ~ spl70_18
    | spl70_19
    | ~ spl70_2 ),
    inference(avatar_split_clause,[],[f2387,f2334,f2450,f2447])).

fof(f2447,plain,
    ( spl70_18
  <=> v1_funct_1(k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl70_18])])).

fof(f2450,plain,
    ( spl70_19
  <=> ! [X40,X41,X39] :
        ( ~ r2_hidden(k4_tarski(X39,X40),sK1)
        | ~ r2_hidden(k4_tarski(X39,X41),k3_relat_1(sK0))
        | X40 = X41 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl70_19])])).

fof(f2387,plain,
    ( ! [X39,X41,X40] :
        ( ~ r2_hidden(k4_tarski(X39,X40),sK1)
        | X40 = X41
        | ~ r2_hidden(k4_tarski(X39,X41),k3_relat_1(sK0))
        | ~ v1_funct_1(k3_relat_1(sK0)) )
    | ~ spl70_2 ),
    inference(resolution,[],[f2346,f1728])).

fof(f1728,plain,(
    ! [X6,X4,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X6),X0)
      | X5 = X6
      | ~ r2_hidden(k4_tarski(X4,X5),X0)
      | ~ v1_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f1524])).

fof(f1524,plain,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        | ( sK17(X0) != sK18(X0)
          & r2_hidden(k4_tarski(sK16(X0),sK18(X0)),X0)
          & r2_hidden(k4_tarski(sK16(X0),sK17(X0)),X0) ) )
      & ( ! [X4,X5,X6] :
            ( X5 = X6
            | ~ r2_hidden(k4_tarski(X4,X6),X0)
            | ~ r2_hidden(k4_tarski(X4,X5),X0) )
        | ~ v1_funct_1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK16,sK17,sK18])],[f1522,f1523])).

fof(f1523,plain,(
    ! [X0] :
      ( ? [X1,X2,X3] :
          ( X2 != X3
          & r2_hidden(k4_tarski(X1,X3),X0)
          & r2_hidden(k4_tarski(X1,X2),X0) )
     => ( sK17(X0) != sK18(X0)
        & r2_hidden(k4_tarski(sK16(X0),sK18(X0)),X0)
        & r2_hidden(k4_tarski(sK16(X0),sK17(X0)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1522,plain,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        | ? [X1,X2,X3] :
            ( X2 != X3
            & r2_hidden(k4_tarski(X1,X3),X0)
            & r2_hidden(k4_tarski(X1,X2),X0) ) )
      & ( ! [X4,X5,X6] :
            ( X5 = X6
            | ~ r2_hidden(k4_tarski(X4,X6),X0)
            | ~ r2_hidden(k4_tarski(X4,X5),X0) )
        | ~ v1_funct_1(X0) ) ) ),
    inference(rectify,[],[f1521])).

fof(f1521,plain,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        | ? [X1,X2,X3] :
            ( X2 != X3
            & r2_hidden(k4_tarski(X1,X3),X0)
            & r2_hidden(k4_tarski(X1,X2),X0) ) )
      & ( ! [X1,X2,X3] :
            ( X2 = X3
            | ~ r2_hidden(k4_tarski(X1,X3),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) )
        | ~ v1_funct_1(X0) ) ) ),
    inference(nnf_transformation,[],[f1165])).

fof(f1165,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
    <=> ! [X1,X2,X3] :
          ( X2 = X3
          | ~ r2_hidden(k4_tarski(X1,X3),X0)
          | ~ r2_hidden(k4_tarski(X1,X2),X0) ) ) ),
    inference(flattening,[],[f1164])).

fof(f1164,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
    <=> ! [X1,X2,X3] :
          ( X2 = X3
          | ~ r2_hidden(k4_tarski(X1,X3),X0)
          | ~ r2_hidden(k4_tarski(X1,X2),X0) ) ) ),
    inference(ennf_transformation,[],[f1061])).

fof(f1061,axiom,(
    ! [X0] :
      ( v1_funct_1(X0)
    <=> ! [X1,X2,X3] :
          ( ( r2_hidden(k4_tarski(X1,X3),X0)
            & r2_hidden(k4_tarski(X1,X2),X0) )
         => X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_1)).

fof(f2445,plain,
    ( ~ spl70_14
    | spl70_17
    | ~ spl70_2 ),
    inference(avatar_split_clause,[],[f2386,f2334,f2443,f2432])).

fof(f2443,plain,
    ( spl70_17
  <=> ! [X38,X37] :
        ( ~ r2_hidden(k4_tarski(X37,X38),sK1)
        | r2_hidden(X38,k2_relat_1(k3_relat_1(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl70_17])])).

fof(f2386,plain,
    ( ! [X37,X38] :
        ( ~ r2_hidden(k4_tarski(X37,X38),sK1)
        | r2_hidden(X38,k2_relat_1(k3_relat_1(sK0)))
        | ~ v1_relat_1(k3_relat_1(sK0)) )
    | ~ spl70_2 ),
    inference(resolution,[],[f2346,f1705])).

fof(f1705,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X1,k2_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1160])).

fof(f1160,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1159])).

fof(f1159,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f814])).

fof(f814,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

fof(f2441,plain,
    ( ~ spl70_14
    | spl70_16
    | ~ spl70_2 ),
    inference(avatar_split_clause,[],[f2385,f2334,f2439,f2432])).

fof(f2439,plain,
    ( spl70_16
  <=> ! [X36,X35] :
        ( ~ r2_hidden(k4_tarski(X35,X36),sK1)
        | r2_hidden(X35,k1_relat_1(k3_relat_1(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl70_16])])).

fof(f2385,plain,
    ( ! [X35,X36] :
        ( ~ r2_hidden(k4_tarski(X35,X36),sK1)
        | r2_hidden(X35,k1_relat_1(k3_relat_1(sK0)))
        | ~ v1_relat_1(k3_relat_1(sK0)) )
    | ~ spl70_2 ),
    inference(resolution,[],[f2346,f1704])).

fof(f1704,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1160])).

fof(f2437,plain,
    ( ~ spl70_14
    | spl70_15
    | ~ spl70_2 ),
    inference(avatar_split_clause,[],[f2384,f2334,f2435,f2432])).

fof(f2435,plain,
    ( spl70_15
  <=> ! [X34] :
        ( ~ r2_hidden(k4_tarski(sK27(X34,k3_relat_1(sK0)),sK28(X34,k3_relat_1(sK0))),sK1)
        | ~ v1_relat_1(X34)
        | ~ r2_hidden(k4_tarski(sK27(X34,k3_relat_1(sK0)),sK28(X34,k3_relat_1(sK0))),X34)
        | k3_relat_1(sK0) = X34 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl70_15])])).

fof(f2384,plain,
    ( ! [X34] :
        ( ~ r2_hidden(k4_tarski(sK27(X34,k3_relat_1(sK0)),sK28(X34,k3_relat_1(sK0))),sK1)
        | k3_relat_1(sK0) = X34
        | ~ r2_hidden(k4_tarski(sK27(X34,k3_relat_1(sK0)),sK28(X34,k3_relat_1(sK0))),X34)
        | ~ v1_relat_1(k3_relat_1(sK0))
        | ~ v1_relat_1(X34) )
    | ~ spl70_2 ),
    inference(resolution,[],[f2346,f1750])).

fof(f1750,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK27(X0,X1),sK28(X0,X1)),X1)
      | X0 = X1
      | ~ r2_hidden(k4_tarski(sK27(X0,X1),sK28(X0,X1)),X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1543])).

fof(f1543,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( X0 = X1
              | ( ( ~ r2_hidden(k4_tarski(sK27(X0,X1),sK28(X0,X1)),X1)
                  | ~ r2_hidden(k4_tarski(sK27(X0,X1),sK28(X0,X1)),X0) )
                & ( r2_hidden(k4_tarski(sK27(X0,X1),sK28(X0,X1)),X1)
                  | r2_hidden(k4_tarski(sK27(X0,X1),sK28(X0,X1)),X0) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) )
                  & ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X4,X5),X0) ) )
              | X0 != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK27,sK28])],[f1541,f1542])).

fof(f1542,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r2_hidden(k4_tarski(X2,X3),X1)
            | ~ r2_hidden(k4_tarski(X2,X3),X0) )
          & ( r2_hidden(k4_tarski(X2,X3),X1)
            | r2_hidden(k4_tarski(X2,X3),X0) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK27(X0,X1),sK28(X0,X1)),X1)
          | ~ r2_hidden(k4_tarski(sK27(X0,X1),sK28(X0,X1)),X0) )
        & ( r2_hidden(k4_tarski(sK27(X0,X1),sK28(X0,X1)),X1)
          | r2_hidden(k4_tarski(sK27(X0,X1),sK28(X0,X1)),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1541,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( X0 = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X2,X3),X0) )
                  & ( r2_hidden(k4_tarski(X2,X3),X1)
                    | r2_hidden(k4_tarski(X2,X3),X0) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) )
                  & ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X4,X5),X0) ) )
              | X0 != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f1540])).

fof(f1540,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( X0 = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X2,X3),X0) )
                  & ( r2_hidden(k4_tarski(X2,X3),X1)
                    | r2_hidden(k4_tarski(X2,X3),X0) ) ) )
            & ( ! [X2,X3] :
                  ( ( r2_hidden(k4_tarski(X2,X3),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
              | X0 != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1169])).

fof(f1169,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( X0 = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X0)
              <=> r2_hidden(k4_tarski(X2,X3),X1) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f654])).

fof(f654,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( X0 = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X0)
              <=> r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_relat_1)).

fof(f2430,plain,
    ( spl70_13
    | spl70_12
    | ~ spl70_2 ),
    inference(avatar_split_clause,[],[f2382,f2334,f2423,f2427])).

fof(f2427,plain,
    ( spl70_13
  <=> ! [X27,X26] : sK11(k3_relat_1(sK0)) != k4_tarski(X26,X27) ),
    introduced(avatar_definition,[new_symbols(naming,[spl70_13])])).

fof(f2423,plain,
    ( spl70_12
  <=> ! [X22,X23,X24] :
        ( ~ r2_hidden(k4_tarski(sK9(X22,k3_relat_1(sK0)),sK10(X22,k3_relat_1(sK0))),sK1)
        | k4_tarski(X23,X24) != sK12(X22)
        | ~ r2_hidden(k4_tarski(sK9(X22,k3_relat_1(sK0)),sK10(X22,k3_relat_1(sK0))),X22)
        | k3_relat_1(sK0) = X22 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl70_12])])).

fof(f2382,plain,
    ( ! [X30,X28,X31,X29,X32] :
        ( ~ r2_hidden(k4_tarski(sK9(X28,k3_relat_1(sK0)),sK10(X28,k3_relat_1(sK0))),sK1)
        | k3_relat_1(sK0) = X28
        | ~ r2_hidden(k4_tarski(sK9(X28,k3_relat_1(sK0)),sK10(X28,k3_relat_1(sK0))),X28)
        | sK11(k3_relat_1(sK0)) != k4_tarski(X29,X30)
        | k4_tarski(X31,X32) != sK12(X28) )
    | ~ spl70_2 ),
    inference(resolution,[],[f2346,f1721])).

fof(f1721,plain,(
    ! [X6,X0,X8,X5,X1,X9] :
      ( ~ r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X1)
      | X0 = X1
      | ~ r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0)
      | k4_tarski(X5,X6) != sK11(X1)
      | k4_tarski(X8,X9) != sK12(X0) ) ),
    inference(cnf_transformation,[],[f1515])).

fof(f1515,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X1)
          | ~ r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0) )
        & ( r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X1)
          | r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0) ) )
      | ( ! [X5,X6] : k4_tarski(X5,X6) != sK11(X1)
        & r2_hidden(sK11(X1),X1) )
      | ( ! [X8,X9] : k4_tarski(X8,X9) != sK12(X0)
        & r2_hidden(sK12(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11,sK12])],[f1511,f1514,f1513,f1512])).

fof(f1512,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r2_hidden(k4_tarski(X2,X3),X1)
            | ~ r2_hidden(k4_tarski(X2,X3),X0) )
          & ( r2_hidden(k4_tarski(X2,X3),X1)
            | r2_hidden(k4_tarski(X2,X3),X0) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X1)
          | ~ r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0) )
        & ( r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X1)
          | r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1513,plain,(
    ! [X1] :
      ( ? [X4] :
          ( ! [X5,X6] : k4_tarski(X5,X6) != X4
          & r2_hidden(X4,X1) )
     => ( ! [X6,X5] : k4_tarski(X5,X6) != sK11(X1)
        & r2_hidden(sK11(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f1514,plain,(
    ! [X0] :
      ( ? [X7] :
          ( ! [X8,X9] : k4_tarski(X8,X9) != X7
          & r2_hidden(X7,X0) )
     => ( ! [X9,X8] : k4_tarski(X8,X9) != sK12(X0)
        & r2_hidden(sK12(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1511,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2,X3] :
          ( ( ~ r2_hidden(k4_tarski(X2,X3),X1)
            | ~ r2_hidden(k4_tarski(X2,X3),X0) )
          & ( r2_hidden(k4_tarski(X2,X3),X1)
            | r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ? [X4] :
          ( ! [X5,X6] : k4_tarski(X5,X6) != X4
          & r2_hidden(X4,X1) )
      | ? [X7] :
          ( ! [X8,X9] : k4_tarski(X8,X9) != X7
          & r2_hidden(X7,X0) ) ) ),
    inference(nnf_transformation,[],[f1162])).

fof(f1162,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2,X3] :
          ( r2_hidden(k4_tarski(X2,X3),X0)
        <~> r2_hidden(k4_tarski(X2,X3),X1) )
      | ? [X4] :
          ( ! [X5,X6] : k4_tarski(X5,X6) != X4
          & r2_hidden(X4,X1) )
      | ? [X7] :
          ( ! [X8,X9] : k4_tarski(X8,X9) != X7
          & r2_hidden(X7,X0) ) ) ),
    inference(flattening,[],[f1161])).

fof(f1161,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2,X3] :
          ( r2_hidden(k4_tarski(X2,X3),X0)
        <~> r2_hidden(k4_tarski(X2,X3),X1) )
      | ? [X4] :
          ( ! [X5,X6] : k4_tarski(X5,X6) != X4
          & r2_hidden(X4,X1) )
      | ? [X7] :
          ( ! [X8,X9] : k4_tarski(X8,X9) != X7
          & r2_hidden(X7,X0) ) ) ),
    inference(ennf_transformation,[],[f1147])).

fof(f1147,plain,(
    ! [X0,X1] :
      ( ( ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X0)
          <=> r2_hidden(k4_tarski(X2,X3),X1) )
        & ! [X4] :
            ~ ( ! [X5,X6] : k4_tarski(X5,X6) != X4
              & r2_hidden(X4,X1) )
        & ! [X7] :
            ~ ( ! [X8,X9] : k4_tarski(X8,X9) != X7
              & r2_hidden(X7,X0) ) )
     => X0 = X1 ) ),
    inference(rectify,[],[f299])).

fof(f299,axiom,(
    ! [X0,X1] :
      ( ( ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X0)
          <=> r2_hidden(k4_tarski(X2,X3),X1) )
        & ! [X2] :
            ~ ( ! [X3,X4] : k4_tarski(X3,X4) != X2
              & r2_hidden(X2,X1) )
        & ! [X2] :
            ~ ( ! [X3,X4] : k4_tarski(X3,X4) != X2
              & r2_hidden(X2,X0) ) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l131_zfmisc_1)).

fof(f2429,plain,
    ( spl70_13
    | spl70_11
    | ~ spl70_2 ),
    inference(avatar_split_clause,[],[f2381,f2334,f2419,f2427])).

fof(f2419,plain,
    ( spl70_11
  <=> ! [X21] :
        ( ~ r2_hidden(k4_tarski(sK9(X21,k3_relat_1(sK0)),sK10(X21,k3_relat_1(sK0))),sK1)
        | r2_hidden(sK12(X21),X21)
        | ~ r2_hidden(k4_tarski(sK9(X21,k3_relat_1(sK0)),sK10(X21,k3_relat_1(sK0))),X21)
        | k3_relat_1(sK0) = X21 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl70_11])])).

fof(f2381,plain,
    ( ! [X26,X27,X25] :
        ( ~ r2_hidden(k4_tarski(sK9(X25,k3_relat_1(sK0)),sK10(X25,k3_relat_1(sK0))),sK1)
        | k3_relat_1(sK0) = X25
        | ~ r2_hidden(k4_tarski(sK9(X25,k3_relat_1(sK0)),sK10(X25,k3_relat_1(sK0))),X25)
        | sK11(k3_relat_1(sK0)) != k4_tarski(X26,X27)
        | r2_hidden(sK12(X25),X25) )
    | ~ spl70_2 ),
    inference(resolution,[],[f2346,f1720])).

fof(f1720,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X1)
      | X0 = X1
      | ~ r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0)
      | k4_tarski(X5,X6) != sK11(X1)
      | r2_hidden(sK12(X0),X0) ) ),
    inference(cnf_transformation,[],[f1515])).

fof(f2425,plain,
    ( spl70_10
    | spl70_12
    | ~ spl70_2 ),
    inference(avatar_split_clause,[],[f2380,f2334,f2423,f2416])).

fof(f2416,plain,
    ( spl70_10
  <=> r2_hidden(sK11(k3_relat_1(sK0)),k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl70_10])])).

fof(f2380,plain,
    ( ! [X24,X23,X22] :
        ( ~ r2_hidden(k4_tarski(sK9(X22,k3_relat_1(sK0)),sK10(X22,k3_relat_1(sK0))),sK1)
        | k3_relat_1(sK0) = X22
        | ~ r2_hidden(k4_tarski(sK9(X22,k3_relat_1(sK0)),sK10(X22,k3_relat_1(sK0))),X22)
        | r2_hidden(sK11(k3_relat_1(sK0)),k3_relat_1(sK0))
        | k4_tarski(X23,X24) != sK12(X22) )
    | ~ spl70_2 ),
    inference(resolution,[],[f2346,f1719])).

fof(f1719,plain,(
    ! [X0,X8,X1,X9] :
      ( ~ r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X1)
      | X0 = X1
      | ~ r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0)
      | r2_hidden(sK11(X1),X1)
      | k4_tarski(X8,X9) != sK12(X0) ) ),
    inference(cnf_transformation,[],[f1515])).

fof(f2421,plain,
    ( spl70_10
    | spl70_11
    | ~ spl70_2 ),
    inference(avatar_split_clause,[],[f2379,f2334,f2419,f2416])).

fof(f2379,plain,
    ( ! [X21] :
        ( ~ r2_hidden(k4_tarski(sK9(X21,k3_relat_1(sK0)),sK10(X21,k3_relat_1(sK0))),sK1)
        | k3_relat_1(sK0) = X21
        | ~ r2_hidden(k4_tarski(sK9(X21,k3_relat_1(sK0)),sK10(X21,k3_relat_1(sK0))),X21)
        | r2_hidden(sK11(k3_relat_1(sK0)),k3_relat_1(sK0))
        | r2_hidden(sK12(X21),X21) )
    | ~ spl70_2 ),
    inference(resolution,[],[f2346,f1718])).

fof(f1718,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X1)
      | X0 = X1
      | ~ r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0)
      | r2_hidden(sK11(X1),X1)
      | r2_hidden(sK12(X0),X0) ) ),
    inference(cnf_transformation,[],[f1515])).

fof(f2414,plain,
    ( ~ spl70_8
    | spl70_9
    | ~ spl70_2 ),
    inference(avatar_split_clause,[],[f2376,f2334,f2411,f2408])).

fof(f2408,plain,
    ( spl70_8
  <=> v1_xboole_0(k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl70_8])])).

fof(f2411,plain,
    ( spl70_9
  <=> ! [X15] : ~ r2_hidden(X15,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl70_9])])).

fof(f2376,plain,
    ( ! [X16] :
        ( ~ r2_hidden(X16,sK1)
        | ~ v1_xboole_0(k3_relat_1(sK0)) )
    | ~ spl70_2 ),
    inference(resolution,[],[f2346,f1944])).

fof(f1944,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1621])).

fof(f1621,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK50(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK50])],[f1619,f1620])).

fof(f1620,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK50(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1619,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f1618])).

fof(f1618,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f2413,plain,
    ( ~ spl70_8
    | spl70_9
    | ~ spl70_2 ),
    inference(avatar_split_clause,[],[f2375,f2334,f2411,f2408])).

fof(f2375,plain,
    ( ! [X15] :
        ( ~ r2_hidden(X15,sK1)
        | ~ v1_xboole_0(k3_relat_1(sK0)) )
    | ~ spl70_2 ),
    inference(resolution,[],[f2346,f1929])).

fof(f1929,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f1254])).

fof(f1254,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f148])).

fof(f148,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(f2358,plain,
    ( ~ spl70_7
    | ~ spl70_2 ),
    inference(avatar_split_clause,[],[f2347,f2334,f2356])).

fof(f2356,plain,
    ( spl70_7
  <=> r2_hidden(k3_relat_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl70_7])])).

fof(f2347,plain,
    ( ~ r2_hidden(k3_relat_1(sK0),sK1)
    | ~ spl70_2 ),
    inference(resolution,[],[f2335,f1758])).

fof(f1758,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1177])).

fof(f1177,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1125])).

fof(f1125,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f2354,plain,
    ( ~ spl70_5
    | spl70_6
    | ~ spl70_2 ),
    inference(avatar_split_clause,[],[f2345,f2334,f2352,f2349])).

fof(f2349,plain,
    ( spl70_5
  <=> r1_tarski(k3_relat_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl70_5])])).

fof(f2352,plain,
    ( spl70_6
  <=> k3_relat_1(sK0) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl70_6])])).

fof(f2345,plain,
    ( k3_relat_1(sK0) = sK1
    | ~ r1_tarski(k3_relat_1(sK0),sK1)
    | ~ spl70_2 ),
    inference(resolution,[],[f2335,f1781])).

fof(f1781,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1561])).

fof(f1561,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f1560])).

fof(f1560,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f2344,plain,(
    spl70_4 ),
    inference(avatar_split_clause,[],[f1691,f2342])).

fof(f2342,plain,
    ( spl70_4
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl70_4])])).

fof(f2340,plain,(
    spl70_3 ),
    inference(avatar_split_clause,[],[f1692,f2338])).

fof(f2338,plain,
    ( spl70_3
  <=> v2_wellord1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl70_3])])).

fof(f2336,plain,(
    spl70_2 ),
    inference(avatar_split_clause,[],[f1693,f2334])).

fof(f2332,plain,(
    ~ spl70_1 ),
    inference(avatar_split_clause,[],[f1694,f2330])).

fof(f2330,plain,
    ( spl70_1
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl70_1])])).
%------------------------------------------------------------------------------
