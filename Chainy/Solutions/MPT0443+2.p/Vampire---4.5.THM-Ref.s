%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0443+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:30 EST 2020

% Result     : Theorem 37.80s
% Output     : Refutation 37.80s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 217 expanded)
%              Number of leaves         :   20 (  76 expanded)
%              Depth                    :   11
%              Number of atoms          :  322 (1055 expanded)
%              Number of equality atoms :   39 ( 138 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16735,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f4788,f16430,f16542,f16628,f16655,f16688,f16708,f16734])).

fof(f16734,plain,
    ( spl131_3
    | ~ spl131_17 ),
    inference(avatar_contradiction_clause,[],[f16728])).

fof(f16728,plain,
    ( $false
    | spl131_3
    | ~ spl131_17 ),
    inference(unit_resulting_resolution,[],[f2566,f4784,f16537,f3929])).

fof(f3929,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_tarski(k2_xboole_0(X6,X7),X5)
      | r2_hidden(X4,X5)
      | ~ r2_hidden(X4,X7) ) ),
    inference(resolution,[],[f1925,f2624])).

fof(f2624,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f2202])).

fof(f2202,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1400])).

fof(f1400,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK105(X0,X1,X2),X1)
              & ~ r2_hidden(sK105(X0,X1,X2),X0) )
            | ~ r2_hidden(sK105(X0,X1,X2),X2) )
          & ( r2_hidden(sK105(X0,X1,X2),X1)
            | r2_hidden(sK105(X0,X1,X2),X0)
            | r2_hidden(sK105(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK105])],[f1398,f1399])).

fof(f1399,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK105(X0,X1,X2),X1)
            & ~ r2_hidden(sK105(X0,X1,X2),X0) )
          | ~ r2_hidden(sK105(X0,X1,X2),X2) )
        & ( r2_hidden(sK105(X0,X1,X2),X1)
          | r2_hidden(sK105(X0,X1,X2),X0)
          | r2_hidden(sK105(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1398,plain,(
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
    inference(rectify,[],[f1397])).

fof(f1397,plain,(
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
    inference(flattening,[],[f1396])).

fof(f1396,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f1925,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1288])).

fof(f1288,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK60(X0,X1),X1)
          & r2_hidden(sK60(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK60])],[f1286,f1287])).

fof(f1287,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK60(X0,X1),X1)
        & r2_hidden(sK60(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1286,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f1285])).

fof(f1285,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f914])).

fof(f914,plain,(
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

fof(f16537,plain,
    ( r2_hidden(sK61(k2_xboole_0(sK3,sK4),k2_xboole_0(k2_relat_1(sK3),k2_relat_1(sK4))),k2_relat_1(sK4))
    | ~ spl131_17 ),
    inference(avatar_component_clause,[],[f16535])).

fof(f16535,plain,
    ( spl131_17
  <=> r2_hidden(sK61(k2_xboole_0(sK3,sK4),k2_xboole_0(k2_relat_1(sK3),k2_relat_1(sK4))),k2_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl131_17])])).

fof(f4784,plain,
    ( ~ r2_hidden(sK61(k2_xboole_0(sK3,sK4),k2_xboole_0(k2_relat_1(sK3),k2_relat_1(sK4))),k2_xboole_0(k2_relat_1(sK3),k2_relat_1(sK4)))
    | spl131_3 ),
    inference(avatar_component_clause,[],[f4782])).

fof(f4782,plain,
    ( spl131_3
  <=> r2_hidden(sK61(k2_xboole_0(sK3,sK4),k2_xboole_0(k2_relat_1(sK3),k2_relat_1(sK4))),k2_xboole_0(k2_relat_1(sK3),k2_relat_1(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl131_3])])).

fof(f2566,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f1903])).

fof(f1903,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1267])).

fof(f1267,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f1266])).

fof(f1266,plain,(
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

fof(f16708,plain,
    ( ~ spl131_4
    | ~ spl131_18 ),
    inference(avatar_contradiction_clause,[],[f16699])).

fof(f16699,plain,
    ( $false
    | ~ spl131_4
    | ~ spl131_18 ),
    inference(unit_resulting_resolution,[],[f2566,f16667,f16541,f3940])).

fof(f3940,plain,(
    ! [X37,X35,X36] :
      ( ~ r2_hidden(X36,k2_relat_1(X35))
      | ~ r1_tarski(X35,X37)
      | r2_hidden(k4_tarski(sK63(X35,X36),X36),X37) ) ),
    inference(resolution,[],[f1925,f2570])).

fof(f2570,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK63(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f1928])).

fof(f1928,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK63(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1294])).

fof(f1294,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK61(X0,X1)),X0)
            | ~ r2_hidden(sK61(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK62(X0,X1),sK61(X0,X1)),X0)
            | r2_hidden(sK61(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK63(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK61,sK62,sK63])],[f1290,f1293,f1292,f1291])).

fof(f1291,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK61(X0,X1)),X0)
          | ~ r2_hidden(sK61(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK61(X0,X1)),X0)
          | r2_hidden(sK61(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1292,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK61(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK62(X0,X1),sK61(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1293,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK63(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1290,plain,(
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
    inference(rectify,[],[f1289])).

fof(f1289,plain,(
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
    inference(nnf_transformation,[],[f642])).

fof(f642,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f16541,plain,
    ( r2_hidden(sK61(k2_xboole_0(sK3,sK4),k2_xboole_0(k2_relat_1(sK3),k2_relat_1(sK4))),k2_relat_1(sK3))
    | ~ spl131_18 ),
    inference(avatar_component_clause,[],[f16539])).

fof(f16539,plain,
    ( spl131_18
  <=> r2_hidden(sK61(k2_xboole_0(sK3,sK4),k2_xboole_0(k2_relat_1(sK3),k2_relat_1(sK4))),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl131_18])])).

fof(f16667,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,sK61(k2_xboole_0(sK3,sK4),k2_xboole_0(k2_relat_1(sK3),k2_relat_1(sK4)))),sK3)
    | ~ spl131_4 ),
    inference(resolution,[],[f4787,f2625])).

fof(f2625,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f2201])).

fof(f2201,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1400])).

fof(f4787,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,sK61(k2_xboole_0(sK3,sK4),k2_xboole_0(k2_relat_1(sK3),k2_relat_1(sK4)))),k2_xboole_0(sK3,sK4))
    | ~ spl131_4 ),
    inference(avatar_component_clause,[],[f4786])).

fof(f4786,plain,
    ( spl131_4
  <=> ! [X0] : ~ r2_hidden(k4_tarski(X0,sK61(k2_xboole_0(sK3,sK4),k2_xboole_0(k2_relat_1(sK3),k2_relat_1(sK4)))),k2_xboole_0(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl131_4])])).

fof(f16688,plain,
    ( ~ spl131_4
    | ~ spl131_17 ),
    inference(avatar_contradiction_clause,[],[f16687])).

fof(f16687,plain,
    ( $false
    | ~ spl131_4
    | ~ spl131_17 ),
    inference(subsumption_resolution,[],[f16683,f16537])).

fof(f16683,plain,
    ( ~ r2_hidden(sK61(k2_xboole_0(sK3,sK4),k2_xboole_0(k2_relat_1(sK3),k2_relat_1(sK4))),k2_relat_1(sK4))
    | ~ spl131_4 ),
    inference(resolution,[],[f16668,f2570])).

fof(f16668,plain,
    ( ! [X1] : ~ r2_hidden(k4_tarski(X1,sK61(k2_xboole_0(sK3,sK4),k2_xboole_0(k2_relat_1(sK3),k2_relat_1(sK4)))),sK4)
    | ~ spl131_4 ),
    inference(resolution,[],[f4787,f2624])).

fof(f16655,plain,
    ( spl131_3
    | ~ spl131_16 ),
    inference(avatar_contradiction_clause,[],[f16648])).

fof(f16648,plain,
    ( $false
    | spl131_3
    | ~ spl131_16 ),
    inference(unit_resulting_resolution,[],[f1624,f4784,f16429,f3936])).

fof(f3936,plain,(
    ! [X28,X26,X27,X25] :
      ( ~ r1_tarski(k2_relat_1(X27),X26)
      | r2_hidden(X25,X26)
      | ~ r2_hidden(k4_tarski(X28,X25),X27) ) ),
    inference(resolution,[],[f1925,f2569])).

fof(f2569,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f1929])).

fof(f1929,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1294])).

fof(f16429,plain,
    ( r2_hidden(k4_tarski(sK62(k2_xboole_0(sK3,sK4),k2_xboole_0(k2_relat_1(sK3),k2_relat_1(sK4))),sK61(k2_xboole_0(sK3,sK4),k2_xboole_0(k2_relat_1(sK3),k2_relat_1(sK4)))),sK3)
    | ~ spl131_16 ),
    inference(avatar_component_clause,[],[f16427])).

fof(f16427,plain,
    ( spl131_16
  <=> r2_hidden(k4_tarski(sK62(k2_xboole_0(sK3,sK4),k2_xboole_0(k2_relat_1(sK3),k2_relat_1(sK4))),sK61(k2_xboole_0(sK3,sK4),k2_xboole_0(k2_relat_1(sK3),k2_relat_1(sK4)))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl131_16])])).

fof(f1624,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f149])).

fof(f149,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f16628,plain,
    ( ~ spl131_15
    | spl131_17 ),
    inference(avatar_contradiction_clause,[],[f16622])).

fof(f16622,plain,
    ( $false
    | ~ spl131_15
    | spl131_17 ),
    inference(unit_resulting_resolution,[],[f2566,f16536,f16425,f3936])).

fof(f16425,plain,
    ( r2_hidden(k4_tarski(sK62(k2_xboole_0(sK3,sK4),k2_xboole_0(k2_relat_1(sK3),k2_relat_1(sK4))),sK61(k2_xboole_0(sK3,sK4),k2_xboole_0(k2_relat_1(sK3),k2_relat_1(sK4)))),sK4)
    | ~ spl131_15 ),
    inference(avatar_component_clause,[],[f16423])).

fof(f16423,plain,
    ( spl131_15
  <=> r2_hidden(k4_tarski(sK62(k2_xboole_0(sK3,sK4),k2_xboole_0(k2_relat_1(sK3),k2_relat_1(sK4))),sK61(k2_xboole_0(sK3,sK4),k2_xboole_0(k2_relat_1(sK3),k2_relat_1(sK4)))),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl131_15])])).

fof(f16536,plain,
    ( ~ r2_hidden(sK61(k2_xboole_0(sK3,sK4),k2_xboole_0(k2_relat_1(sK3),k2_relat_1(sK4))),k2_relat_1(sK4))
    | spl131_17 ),
    inference(avatar_component_clause,[],[f16535])).

fof(f16542,plain,
    ( spl131_17
    | spl131_18
    | ~ spl131_3 ),
    inference(avatar_split_clause,[],[f16433,f4782,f16539,f16535])).

fof(f16433,plain,
    ( r2_hidden(sK61(k2_xboole_0(sK3,sK4),k2_xboole_0(k2_relat_1(sK3),k2_relat_1(sK4))),k2_relat_1(sK3))
    | r2_hidden(sK61(k2_xboole_0(sK3,sK4),k2_xboole_0(k2_relat_1(sK3),k2_relat_1(sK4))),k2_relat_1(sK4))
    | ~ spl131_3 ),
    inference(resolution,[],[f4783,f2626])).

fof(f2626,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_xboole_0(X0,X1))
      | r2_hidden(X4,X0)
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f2200])).

fof(f2200,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1400])).

fof(f4783,plain,
    ( r2_hidden(sK61(k2_xboole_0(sK3,sK4),k2_xboole_0(k2_relat_1(sK3),k2_relat_1(sK4))),k2_xboole_0(k2_relat_1(sK3),k2_relat_1(sK4)))
    | ~ spl131_3 ),
    inference(avatar_component_clause,[],[f4782])).

fof(f16430,plain,
    ( spl131_15
    | spl131_16
    | spl131_3 ),
    inference(avatar_split_clause,[],[f5828,f4782,f16427,f16423])).

fof(f5828,plain,
    ( r2_hidden(k4_tarski(sK62(k2_xboole_0(sK3,sK4),k2_xboole_0(k2_relat_1(sK3),k2_relat_1(sK4))),sK61(k2_xboole_0(sK3,sK4),k2_xboole_0(k2_relat_1(sK3),k2_relat_1(sK4)))),sK3)
    | r2_hidden(k4_tarski(sK62(k2_xboole_0(sK3,sK4),k2_xboole_0(k2_relat_1(sK3),k2_relat_1(sK4))),sK61(k2_xboole_0(sK3,sK4),k2_xboole_0(k2_relat_1(sK3),k2_relat_1(sK4)))),sK4)
    | spl131_3 ),
    inference(resolution,[],[f5826,f2626])).

fof(f5826,plain,
    ( r2_hidden(k4_tarski(sK62(k2_xboole_0(sK3,sK4),k2_xboole_0(k2_relat_1(sK3),k2_relat_1(sK4))),sK61(k2_xboole_0(sK3,sK4),k2_xboole_0(k2_relat_1(sK3),k2_relat_1(sK4)))),k2_xboole_0(sK3,sK4))
    | spl131_3 ),
    inference(subsumption_resolution,[],[f3564,f4784])).

fof(f3564,plain,
    ( r2_hidden(k4_tarski(sK62(k2_xboole_0(sK3,sK4),k2_xboole_0(k2_relat_1(sK3),k2_relat_1(sK4))),sK61(k2_xboole_0(sK3,sK4),k2_xboole_0(k2_relat_1(sK3),k2_relat_1(sK4)))),k2_xboole_0(sK3,sK4))
    | r2_hidden(sK61(k2_xboole_0(sK3,sK4),k2_xboole_0(k2_relat_1(sK3),k2_relat_1(sK4))),k2_xboole_0(k2_relat_1(sK3),k2_relat_1(sK4))) ),
    inference(resolution,[],[f2975,f2759])).

fof(f2759,plain,(
    ~ sQ130_eqProxy(k2_relat_1(k2_xboole_0(sK3,sK4)),k2_xboole_0(k2_relat_1(sK3),k2_relat_1(sK4))) ),
    inference(equality_proxy_replacement,[],[f1502,f2741])).

fof(f2741,plain,(
    ! [X1,X0] :
      ( sQ130_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ130_eqProxy])])).

fof(f1502,plain,(
    k2_relat_1(k2_xboole_0(sK3,sK4)) != k2_xboole_0(k2_relat_1(sK3),k2_relat_1(sK4)) ),
    inference(cnf_transformation,[],[f1133])).

fof(f1133,plain,
    ( k2_relat_1(k2_xboole_0(sK3,sK4)) != k2_xboole_0(k2_relat_1(sK3),k2_relat_1(sK4))
    & v1_relat_1(sK4)
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f680,f1132,f1131])).

fof(f1131,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_relat_1(k2_xboole_0(X0,X1)) != k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k2_relat_1(k2_xboole_0(sK3,X1)) != k2_xboole_0(k2_relat_1(sK3),k2_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f1132,plain,
    ( ? [X1] :
        ( k2_relat_1(k2_xboole_0(sK3,X1)) != k2_xboole_0(k2_relat_1(sK3),k2_relat_1(X1))
        & v1_relat_1(X1) )
   => ( k2_relat_1(k2_xboole_0(sK3,sK4)) != k2_xboole_0(k2_relat_1(sK3),k2_relat_1(sK4))
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f680,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_relat_1(k2_xboole_0(X0,X1)) != k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f663])).

fof(f663,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) ) ) ),
    inference(negated_conjecture,[],[f662])).

fof(f662,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_relat_1)).

fof(f2975,plain,(
    ! [X0,X1] :
      ( sQ130_eqProxy(k2_relat_1(X0),X1)
      | r2_hidden(k4_tarski(sK62(X0,X1),sK61(X0,X1)),X0)
      | r2_hidden(sK61(X0,X1),X1) ) ),
    inference(equality_proxy_replacement,[],[f1930,f2741])).

fof(f1930,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK62(X0,X1),sK61(X0,X1)),X0)
      | r2_hidden(sK61(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f1294])).

fof(f4788,plain,
    ( ~ spl131_3
    | spl131_4 ),
    inference(avatar_split_clause,[],[f3563,f4786,f4782])).

fof(f3563,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(X0,sK61(k2_xboole_0(sK3,sK4),k2_xboole_0(k2_relat_1(sK3),k2_relat_1(sK4)))),k2_xboole_0(sK3,sK4))
      | ~ r2_hidden(sK61(k2_xboole_0(sK3,sK4),k2_xboole_0(k2_relat_1(sK3),k2_relat_1(sK4))),k2_xboole_0(k2_relat_1(sK3),k2_relat_1(sK4))) ) ),
    inference(resolution,[],[f2974,f2759])).

fof(f2974,plain,(
    ! [X0,X3,X1] :
      ( sQ130_eqProxy(k2_relat_1(X0),X1)
      | ~ r2_hidden(k4_tarski(X3,sK61(X0,X1)),X0)
      | ~ r2_hidden(sK61(X0,X1),X1) ) ),
    inference(equality_proxy_replacement,[],[f1931,f2741])).

fof(f1931,plain,(
    ! [X0,X3,X1] :
      ( k2_relat_1(X0) = X1
      | ~ r2_hidden(k4_tarski(X3,sK61(X0,X1)),X0)
      | ~ r2_hidden(sK61(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f1294])).
%------------------------------------------------------------------------------
