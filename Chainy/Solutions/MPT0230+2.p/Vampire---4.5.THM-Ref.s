%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0230+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:18 EST 2020

% Result     : Theorem 1.47s
% Output     : Refutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :   51 (  69 expanded)
%              Number of leaves         :   11 (  22 expanded)
%              Depth                    :   11
%              Number of atoms          :  215 ( 267 expanded)
%              Number of equality atoms :   98 ( 127 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1482,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1474,f1477,f1481])).

fof(f1481,plain,(
    ~ spl32_8 ),
    inference(avatar_contradiction_clause,[],[f1480])).

fof(f1480,plain,
    ( $false
    | ~ spl32_8 ),
    inference(subsumption_resolution,[],[f1479,f1066])).

fof(f1066,plain,(
    ~ sQ31_eqProxy(sK4,sK5) ),
    inference(equality_proxy_replacement,[],[f570,f1049])).

fof(f1049,plain,(
    ! [X1,X0] :
      ( sQ31_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ31_eqProxy])])).

fof(f570,plain,(
    sK4 != sK5 ),
    inference(cnf_transformation,[],[f461])).

fof(f461,plain,
    ( sK4 != sK6
    & sK4 != sK5
    & r1_tarski(k1_tarski(sK4),k2_tarski(sK5,sK6)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f326,f460])).

fof(f460,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) )
   => ( sK4 != sK6
      & sK4 != sK5
      & r1_tarski(k1_tarski(sK4),k2_tarski(sK5,sK6)) ) ),
    introduced(choice_axiom,[])).

fof(f326,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & X0 != X1
      & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(ennf_transformation,[],[f315])).

fof(f315,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( X0 != X2
          & X0 != X1
          & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(negated_conjecture,[],[f314])).

fof(f314,conjecture,(
    ! [X0,X1,X2] :
      ~ ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

fof(f1479,plain,
    ( sQ31_eqProxy(sK4,sK5)
    | ~ spl32_8 ),
    inference(resolution,[],[f1473,f1304])).

fof(f1304,plain,(
    ! [X0,X1] :
      ( ~ sQ31_eqProxy(X0,X1)
      | sQ31_eqProxy(X1,X0) ) ),
    inference(equality_proxy_axiom,[],[f1049])).

fof(f1473,plain,
    ( sQ31_eqProxy(sK5,sK4)
    | ~ spl32_8 ),
    inference(avatar_component_clause,[],[f1471])).

fof(f1471,plain,
    ( spl32_8
  <=> sQ31_eqProxy(sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl32_8])])).

fof(f1477,plain,(
    ~ spl32_7 ),
    inference(avatar_contradiction_clause,[],[f1476])).

fof(f1476,plain,
    ( $false
    | ~ spl32_7 ),
    inference(subsumption_resolution,[],[f1475,f1065])).

fof(f1065,plain,(
    ~ sQ31_eqProxy(sK4,sK6) ),
    inference(equality_proxy_replacement,[],[f571,f1049])).

fof(f571,plain,(
    sK4 != sK6 ),
    inference(cnf_transformation,[],[f461])).

fof(f1475,plain,
    ( sQ31_eqProxy(sK4,sK6)
    | ~ spl32_7 ),
    inference(resolution,[],[f1469,f1304])).

fof(f1469,plain,
    ( sQ31_eqProxy(sK6,sK4)
    | ~ spl32_7 ),
    inference(avatar_component_clause,[],[f1467])).

fof(f1467,plain,
    ( spl32_7
  <=> sQ31_eqProxy(sK6,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl32_7])])).

fof(f1474,plain,
    ( spl32_7
    | spl32_8 ),
    inference(avatar_split_clause,[],[f1450,f1471,f1467])).

fof(f1450,plain,
    ( sQ31_eqProxy(sK5,sK4)
    | sQ31_eqProxy(sK6,sK4) ),
    inference(resolution,[],[f1334,f999])).

fof(f999,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f998])).

fof(f998,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f712])).

fof(f712,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f500])).

fof(f500,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK17(X0,X1) != X0
            | ~ r2_hidden(sK17(X0,X1),X1) )
          & ( sK17(X0,X1) = X0
            | r2_hidden(sK17(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK17])],[f498,f499])).

fof(f499,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK17(X0,X1) != X0
          | ~ r2_hidden(sK17(X0,X1),X1) )
        & ( sK17(X0,X1) = X0
          | r2_hidden(sK17(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f498,plain,(
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
    inference(rectify,[],[f497])).

fof(f497,plain,(
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
    inference(nnf_transformation,[],[f175])).

fof(f175,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f1334,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_tarski(sK4))
      | sQ31_eqProxy(sK5,X0)
      | sQ31_eqProxy(sK6,X0) ) ),
    inference(resolution,[],[f1318,f1215])).

fof(f1215,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_tarski(X0,X1))
      | sQ31_eqProxy(X0,X4)
      | sQ31_eqProxy(X1,X4) ) ),
    inference(equality_proxy_replacement,[],[f1010,f1049,f1049])).

fof(f1010,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_tarski(X0,X1)) ) ),
    inference(equality_resolution,[],[f827])).

fof(f827,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f523])).

fof(f523,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK22(X0,X1,X2) != X1
              & sK22(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK22(X0,X1,X2),X2) )
          & ( sK22(X0,X1,X2) = X1
            | sK22(X0,X1,X2) = X0
            | r2_hidden(sK22(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK22])],[f521,f522])).

fof(f522,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK22(X0,X1,X2) != X1
            & sK22(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK22(X0,X1,X2),X2) )
        & ( sK22(X0,X1,X2) = X1
          | sK22(X0,X1,X2) = X0
          | r2_hidden(sK22(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f521,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f520])).

fof(f520,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f519])).

fof(f519,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f176])).

fof(f176,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f1318,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_tarski(sK5,sK6))
      | ~ r2_hidden(X0,k1_tarski(sK4)) ) ),
    inference(resolution,[],[f569,f698])).

fof(f698,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f486])).

fof(f486,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK12(X0,X1),X1)
          & r2_hidden(sK12(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f484,f485])).

fof(f485,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK12(X0,X1),X1)
        & r2_hidden(sK12(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f484,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f483])).

fof(f483,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f363])).

fof(f363,plain,(
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

fof(f569,plain,(
    r1_tarski(k1_tarski(sK4),k2_tarski(sK5,sK6)) ),
    inference(cnf_transformation,[],[f461])).
%------------------------------------------------------------------------------
