%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : xboole_0__t2_xboole_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:18 EDT 2019

% Result     : Theorem 14.54s
% Output     : Refutation 14.54s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 297 expanded)
%              Number of leaves         :   25 ( 102 expanded)
%              Depth                    :   10
%              Number of atoms          :  458 (1503 expanded)
%              Number of equality atoms :   33 ( 112 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5678,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2762,f2778,f2780,f2796,f2813,f2880,f2954,f2963,f2964,f2981,f5325,f5326,f5666,f5667,f5668,f5677])).

fof(f5677,plain,
    ( ~ spl8_24
    | spl8_35 ),
    inference(avatar_contradiction_clause,[],[f5670])).

fof(f5670,plain,
    ( $false
    | ~ spl8_24
    | ~ spl8_35 ),
    inference(resolution,[],[f2990,f2761])).

fof(f2761,plain,
    ( ~ r2_hidden(sK5(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))),sK4)
    | ~ spl8_35 ),
    inference(avatar_component_clause,[],[f2760])).

fof(f2760,plain,
    ( spl8_35
  <=> ~ r2_hidden(sK5(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).

fof(f2990,plain,
    ( r2_hidden(sK5(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))),sK4)
    | ~ spl8_24 ),
    inference(resolution,[],[f2728,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k4_xboole_0(X1,X2))
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f52,f70])).

fof(f70,plain,(
    ! [X0,X1] : sP0(X1,X0,k4_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f7,f18])).

fof(f18,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_0__t2_xboole_0.p',d5_xboole_0)).

fof(f52,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( r2_hidden(sK6(X0,X1,X2),X0)
            | ~ r2_hidden(sK6(X0,X1,X2),X1)
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK6(X0,X1,X2),X0)
              & r2_hidden(sK6(X0,X1,X2),X1) )
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f30,f31])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK6(X0,X1,X2),X0)
          | ~ r2_hidden(sK6(X0,X1,X2),X1)
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK6(X0,X1,X2),X0)
            & r2_hidden(sK6(X0,X1,X2),X1) )
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X0)
                & r2_hidden(X3,X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f2728,plain,
    ( r2_hidden(sK5(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))),k4_xboole_0(sK4,sK3))
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f2727])).

fof(f2727,plain,
    ( spl8_24
  <=> r2_hidden(sK5(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))),k4_xboole_0(sK4,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f5668,plain,
    ( spl8_32
    | ~ spl8_5
    | spl8_35 ),
    inference(avatar_split_clause,[],[f5333,f2760,f150,f2754])).

fof(f2754,plain,
    ( spl8_32
  <=> r2_hidden(sK5(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f150,plain,
    ( spl8_5
  <=> ~ r2_hidden(sK5(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f5333,plain,
    ( ~ r2_hidden(sK5(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))),sK2)
    | r2_hidden(sK5(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))),sK3)
    | ~ spl8_35 ),
    inference(resolution,[],[f2761,f42])).

fof(f42,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK4)
      | ~ r2_hidden(X3,sK2)
      | r2_hidden(X3,sK3) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( k5_xboole_0(sK3,sK4) != sK2
    & ! [X3] :
        ( ( ~ r2_hidden(X3,sK2)
          | ( ( ~ r2_hidden(X3,sK4)
              | ~ r2_hidden(X3,sK3) )
            & ( r2_hidden(X3,sK4)
              | r2_hidden(X3,sK3) ) ) )
        & ( ( ( r2_hidden(X3,sK3)
              | ~ r2_hidden(X3,sK4) )
            & ( r2_hidden(X3,sK4)
              | ~ r2_hidden(X3,sK3) ) )
          | r2_hidden(X3,sK2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f22,f23])).

fof(f23,plain,
    ( ? [X0,X1,X2] :
        ( k5_xboole_0(X1,X2) != X0
        & ! [X3] :
            ( ( ~ r2_hidden(X3,X0)
              | ( ( ~ r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,X1) )
                & ( r2_hidden(X3,X2)
                  | r2_hidden(X3,X1) ) ) )
            & ( ( ( r2_hidden(X3,X1)
                  | ~ r2_hidden(X3,X2) )
                & ( r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,X1) ) )
              | r2_hidden(X3,X0) ) ) )
   => ( k5_xboole_0(sK3,sK4) != sK2
      & ! [X3] :
          ( ( ~ r2_hidden(X3,sK2)
            | ( ( ~ r2_hidden(X3,sK4)
                | ~ r2_hidden(X3,sK3) )
              & ( r2_hidden(X3,sK4)
                | r2_hidden(X3,sK3) ) ) )
          & ( ( ( r2_hidden(X3,sK3)
                | ~ r2_hidden(X3,sK4) )
              & ( r2_hidden(X3,sK4)
                | ~ r2_hidden(X3,sK3) ) )
            | r2_hidden(X3,sK2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( k5_xboole_0(X1,X2) != X0
      & ! [X3] :
          ( ( ~ r2_hidden(X3,X0)
            | ( ( ~ r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) )
              & ( r2_hidden(X3,X2)
                | r2_hidden(X3,X1) ) ) )
          & ( ( ( r2_hidden(X3,X1)
                | ~ r2_hidden(X3,X2) )
              & ( r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) ) )
            | r2_hidden(X3,X0) ) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( k5_xboole_0(X1,X2) != X0
      & ! [X3] :
          ( ~ r2_hidden(X3,X0)
        <=> ( r2_hidden(X3,X1)
          <=> r2_hidden(X3,X2) ) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ! [X3] :
            ( ~ r2_hidden(X3,X0)
          <=> ( r2_hidden(X3,X1)
            <=> r2_hidden(X3,X2) ) )
       => k5_xboole_0(X1,X2) = X0 ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r2_hidden(X3,X0)
        <=> ( r2_hidden(X3,X1)
          <=> r2_hidden(X3,X2) ) )
     => k5_xboole_0(X1,X2) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_0__t2_xboole_0.p',t2_xboole_0)).

fof(f5667,plain,
    ( spl8_4
    | ~ spl8_33
    | spl8_35 ),
    inference(avatar_split_clause,[],[f5334,f2760,f2751,f147])).

fof(f147,plain,
    ( spl8_4
  <=> r2_hidden(sK5(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f2751,plain,
    ( spl8_33
  <=> ~ r2_hidden(sK5(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).

fof(f5334,plain,
    ( ~ r2_hidden(sK5(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))),sK3)
    | r2_hidden(sK5(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))),sK2)
    | ~ spl8_35 ),
    inference(resolution,[],[f2761,f40])).

fof(f40,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK4)
      | ~ r2_hidden(X3,sK3)
      | r2_hidden(X3,sK2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f5666,plain,
    ( spl8_7
    | ~ spl8_26 ),
    inference(avatar_contradiction_clause,[],[f5656])).

fof(f5656,plain,
    ( $false
    | ~ spl8_7
    | ~ spl8_26 ),
    inference(resolution,[],[f5646,f157])).

fof(f157,plain,
    ( ~ r2_hidden(sK5(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))),k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3)))
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl8_7
  <=> ~ r2_hidden(sK5(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))),k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f5646,plain,
    ( ! [X1] : r2_hidden(sK5(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))),k2_xboole_0(k4_xboole_0(sK3,sK4),X1))
    | ~ spl8_26 ),
    inference(resolution,[],[f5354,f81])).

fof(f81,plain,(
    ! [X2,X1] : sP1(X2,X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f71,f46])).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/xboole_0__t2_xboole_0.p',commutativity_k2_xboole_0)).

fof(f71,plain,(
    ! [X0,X1] : sP1(X1,X0,k2_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X0,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ~ sP1(X1,X0,X2) )
      & ( sP1(X1,X0,X2)
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> sP1(X1,X0,X2) ) ),
    inference(definition_folding,[],[f6,f20])).

fof(f20,plain,(
    ! [X1,X0,X2] :
      ( sP1(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_0__t2_xboole_0.p',d3_xboole_0)).

fof(f5354,plain,
    ( ! [X0,X1] :
        ( ~ sP1(k4_xboole_0(sK3,sK4),X1,X0)
        | r2_hidden(sK5(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))),X0) )
    | ~ spl8_26 ),
    inference(resolution,[],[f2734,f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X0)
      | r2_hidden(X4,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ( ~ r2_hidden(sK7(X0,X1,X2),X0)
              & ~ r2_hidden(sK7(X0,X1,X2),X1) )
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( r2_hidden(sK7(X0,X1,X2),X0)
            | r2_hidden(sK7(X0,X1,X2),X1)
            | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X0)
                & ~ r2_hidden(X4,X1) ) )
            & ( r2_hidden(X4,X0)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f36,f37])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X3,X1) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X0)
            | r2_hidden(X3,X1)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK7(X0,X1,X2),X0)
            & ~ r2_hidden(sK7(X0,X1,X2),X1) )
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( r2_hidden(sK7(X0,X1,X2),X0)
          | r2_hidden(sK7(X0,X1,X2),X1)
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
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
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X1,X0,X2] :
      ( ( sP1(X1,X0,X2)
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
        | ~ sP1(X1,X0,X2) ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X1,X0,X2] :
      ( ( sP1(X1,X0,X2)
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
        | ~ sP1(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f2734,plain,
    ( r2_hidden(sK5(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))),k4_xboole_0(sK3,sK4))
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f2733])).

fof(f2733,plain,
    ( spl8_26
  <=> r2_hidden(sK5(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))),k4_xboole_0(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f5326,plain,
    ( ~ spl8_33
    | ~ spl8_35
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f2985,f147,f2760,f2751])).

fof(f2985,plain,
    ( ~ r2_hidden(sK5(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))),sK4)
    | ~ r2_hidden(sK5(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))),sK3)
    | ~ spl8_4 ),
    inference(resolution,[],[f148,f43])).

fof(f43,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK2)
      | ~ r2_hidden(X3,sK4)
      | ~ r2_hidden(X3,sK3) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f148,plain,
    ( r2_hidden(sK5(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))),sK2)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f147])).

fof(f5325,plain,
    ( spl8_7
    | ~ spl8_24 ),
    inference(avatar_contradiction_clause,[],[f5315])).

fof(f5315,plain,
    ( $false
    | ~ spl8_7
    | ~ spl8_24 ),
    inference(resolution,[],[f5312,f157])).

fof(f5312,plain,
    ( ! [X0] : r2_hidden(sK5(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))),k2_xboole_0(X0,k4_xboole_0(sK4,sK3)))
    | ~ spl8_24 ),
    inference(resolution,[],[f2991,f71])).

fof(f2991,plain,
    ( ! [X0,X1] :
        ( ~ sP1(k4_xboole_0(sK4,sK3),X1,X0)
        | r2_hidden(sK5(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))),X0) )
    | ~ spl8_24 ),
    inference(resolution,[],[f2728,f62])).

fof(f2981,plain,
    ( spl8_4
    | ~ spl8_35
    | spl8_33 ),
    inference(avatar_split_clause,[],[f2980,f2751,f2760,f147])).

fof(f2980,plain,
    ( ~ r2_hidden(sK5(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))),sK4)
    | r2_hidden(sK5(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))),sK2)
    | ~ spl8_33 ),
    inference(resolution,[],[f2752,f41])).

fof(f41,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK3)
      | ~ r2_hidden(X3,sK4)
      | r2_hidden(X3,sK2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2752,plain,
    ( ~ r2_hidden(sK5(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))),sK3)
    | ~ spl8_33 ),
    inference(avatar_component_clause,[],[f2751])).

fof(f2964,plain,
    ( spl8_24
    | spl8_26
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f2956,f153,f2733,f2727])).

fof(f153,plain,
    ( spl8_6
  <=> r2_hidden(sK5(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))),k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f2956,plain,
    ( r2_hidden(sK5(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))),k4_xboole_0(sK3,sK4))
    | r2_hidden(sK5(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))),k4_xboole_0(sK4,sK3))
    | ~ spl8_6 ),
    inference(resolution,[],[f154,f197])).

fof(f197,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | r2_hidden(X0,X2) ) ),
    inference(resolution,[],[f60,f71])).

fof(f60,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f154,plain,
    ( r2_hidden(sK5(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))),k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3)))
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f153])).

fof(f2963,plain,
    ( ~ spl8_26
    | ~ spl8_34 ),
    inference(avatar_contradiction_clause,[],[f2960])).

fof(f2960,plain,
    ( $false
    | ~ spl8_26
    | ~ spl8_34 ),
    inference(resolution,[],[f2766,f2758])).

fof(f2758,plain,
    ( r2_hidden(sK5(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))),sK4)
    | ~ spl8_34 ),
    inference(avatar_component_clause,[],[f2757])).

fof(f2757,plain,
    ( spl8_34
  <=> r2_hidden(sK5(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).

fof(f2766,plain,
    ( ~ r2_hidden(sK5(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))),sK4)
    | ~ spl8_26 ),
    inference(resolution,[],[f2734,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k4_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X2) ) ),
    inference(resolution,[],[f53,f70])).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f2954,plain,
    ( ~ spl8_24
    | ~ spl8_32 ),
    inference(avatar_contradiction_clause,[],[f2952])).

fof(f2952,plain,
    ( $false
    | ~ spl8_24
    | ~ spl8_32 ),
    inference(resolution,[],[f2947,f2755])).

fof(f2755,plain,
    ( r2_hidden(sK5(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))),sK3)
    | ~ spl8_32 ),
    inference(avatar_component_clause,[],[f2754])).

fof(f2947,plain,
    ( ~ r2_hidden(sK5(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))),sK3)
    | ~ spl8_24 ),
    inference(resolution,[],[f2728,f91])).

fof(f2880,plain,(
    ~ spl8_8 ),
    inference(avatar_contradiction_clause,[],[f2879])).

fof(f2879,plain,
    ( $false
    | ~ spl8_8 ),
    inference(trivial_inequality_removal,[],[f2875])).

fof(f2875,plain,
    ( sK2 != sK2
    | ~ spl8_8 ),
    inference(superposition,[],[f68,f165])).

fof(f165,plain,
    ( k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3)) = sK2
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl8_8
  <=> k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3)) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f68,plain,(
    k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3)) != sK2 ),
    inference(definition_unfolding,[],[f44,f48])).

fof(f48,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/xboole_0__t2_xboole_0.p',d6_xboole_0)).

fof(f44,plain,(
    k5_xboole_0(sK3,sK4) != sK2 ),
    inference(cnf_transformation,[],[f24])).

fof(f2813,plain,
    ( spl8_4
    | spl8_8
    | spl8_7 ),
    inference(avatar_split_clause,[],[f2788,f156,f164,f147])).

fof(f2788,plain,
    ( k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3)) = sK2
    | r2_hidden(sK5(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))),sK2)
    | ~ spl8_7 ),
    inference(resolution,[],[f157,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | X0 = X1
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK5(X0,X1),X1)
          | ~ r2_hidden(sK5(X0,X1),X0) )
        & ( r2_hidden(sK5(X0,X1),X1)
          | r2_hidden(sK5(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f25,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK5(X0,X1),X1)
          | ~ r2_hidden(sK5(X0,X1),X0) )
        & ( r2_hidden(sK5(X0,X1),X1)
          | r2_hidden(sK5(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_0__t2_xboole_0.p',t2_tarski)).

fof(f2796,plain,
    ( spl8_34
    | ~ spl8_33
    | spl8_27 ),
    inference(avatar_split_clause,[],[f2795,f2730,f2751,f2757])).

fof(f2730,plain,
    ( spl8_27
  <=> ~ r2_hidden(sK5(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))),k4_xboole_0(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f2795,plain,
    ( ~ r2_hidden(sK5(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))),sK3)
    | r2_hidden(sK5(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))),sK4)
    | ~ spl8_27 ),
    inference(resolution,[],[f2731,f176])).

fof(f176,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k4_xboole_0(X2,X1))
      | ~ r2_hidden(X0,X2)
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f54,f70])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f2731,plain,
    ( ~ r2_hidden(sK5(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))),k4_xboole_0(sK3,sK4))
    | ~ spl8_27 ),
    inference(avatar_component_clause,[],[f2730])).

fof(f2780,plain,
    ( ~ spl8_5
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f467,f156,f150])).

fof(f467,plain,
    ( ~ r2_hidden(sK5(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))),k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3)))
    | ~ r2_hidden(sK5(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))),sK2) ),
    inference(extensionality_resolution,[],[f51,f68])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | X0 = X1
      | ~ r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2778,plain,
    ( ~ spl8_26
    | spl8_33 ),
    inference(avatar_contradiction_clause,[],[f2771])).

fof(f2771,plain,
    ( $false
    | ~ spl8_26
    | ~ spl8_33 ),
    inference(resolution,[],[f2767,f2752])).

fof(f2767,plain,
    ( r2_hidden(sK5(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))),sK3)
    | ~ spl8_26 ),
    inference(resolution,[],[f2734,f90])).

fof(f2762,plain,
    ( spl8_32
    | ~ spl8_35
    | spl8_25 ),
    inference(avatar_split_clause,[],[f2749,f2724,f2760,f2754])).

fof(f2724,plain,
    ( spl8_25
  <=> ~ r2_hidden(sK5(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))),k4_xboole_0(sK4,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f2749,plain,
    ( ~ r2_hidden(sK5(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))),sK4)
    | r2_hidden(sK5(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))),sK3)
    | ~ spl8_25 ),
    inference(resolution,[],[f2725,f176])).

fof(f2725,plain,
    ( ~ r2_hidden(sK5(sK2,k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3))),k4_xboole_0(sK4,sK3))
    | ~ spl8_25 ),
    inference(avatar_component_clause,[],[f2724])).
%------------------------------------------------------------------------------
