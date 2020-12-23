%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:26 EST 2020

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 271 expanded)
%              Number of leaves         :   25 (  90 expanded)
%              Depth                    :   12
%              Number of atoms          :  412 (1138 expanded)
%              Number of equality atoms :  109 ( 324 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f678,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f119,f128,f133,f467,f556,f561,f572,f588,f596,f647,f676])).

fof(f676,plain,
    ( ~ spl7_1
    | ~ spl7_7 ),
    inference(avatar_contradiction_clause,[],[f667])).

fof(f667,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_7 ),
    inference(unit_resulting_resolution,[],[f118,f551,f113])).

fof(f113,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK6(X0,X1,X2),X1)
            | ~ r2_hidden(sK6(X0,X1,X2),X0)
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK6(X0,X1,X2),X1)
              & r2_hidden(sK6(X0,X1,X2),X0) )
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f42,f43])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK6(X0,X1,X2),X1)
          | ~ r2_hidden(sK6(X0,X1,X2),X0)
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK6(X0,X1,X2),X1)
            & r2_hidden(sK6(X0,X1,X2),X0) )
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
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
    inference(rectify,[],[f41])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f551,plain,
    ( r2_hidden(sK0,k4_xboole_0(k2_tarski(sK0,sK2),sK1))
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f549])).

fof(f549,plain,
    ( spl7_7
  <=> r2_hidden(sK0,k4_xboole_0(k2_tarski(sK0,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f118,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl7_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f647,plain,
    ( spl7_6
    | spl7_10 ),
    inference(avatar_contradiction_clause,[],[f639])).

fof(f639,plain,
    ( $false
    | spl7_6
    | spl7_10 ),
    inference(unit_resulting_resolution,[],[f595,f466,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X0) = k4_xboole_0(k2_tarski(X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f63,f61,f61])).

fof(f61,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
        | r2_hidden(X0,X1) )
      & ( ~ r2_hidden(X0,X1)
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).

fof(f466,plain,
    ( k2_tarski(sK0,sK0) != k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),sK1))
    | spl7_6 ),
    inference(avatar_component_clause,[],[f464])).

fof(f464,plain,
    ( spl7_6
  <=> k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f595,plain,
    ( ~ r2_hidden(sK0,k4_xboole_0(k2_tarski(sK0,sK0),sK1))
    | spl7_10 ),
    inference(avatar_component_clause,[],[f593])).

fof(f593,plain,
    ( spl7_10
  <=> r2_hidden(sK0,k4_xboole_0(k2_tarski(sK0,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f596,plain,
    ( ~ spl7_10
    | ~ spl7_3
    | spl7_8 ),
    inference(avatar_split_clause,[],[f567,f553,f125,f593])).

fof(f125,plain,
    ( spl7_3
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f553,plain,
    ( spl7_8
  <=> r2_hidden(sK2,k4_xboole_0(k2_tarski(sK0,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f567,plain,
    ( ~ r2_hidden(sK0,k4_xboole_0(k2_tarski(sK0,sK0),sK1))
    | ~ spl7_3
    | spl7_8 ),
    inference(superposition,[],[f555,f127])).

fof(f127,plain,
    ( sK0 = sK2
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f125])).

fof(f555,plain,
    ( ~ r2_hidden(sK2,k4_xboole_0(k2_tarski(sK0,sK2),sK1))
    | spl7_8 ),
    inference(avatar_component_clause,[],[f553])).

fof(f588,plain,(
    spl7_9 ),
    inference(avatar_contradiction_clause,[],[f577])).

fof(f577,plain,
    ( $false
    | spl7_9 ),
    inference(unit_resulting_resolution,[],[f161,f164,f571,f205])).

fof(f205,plain,(
    ! [X19,X17,X18] :
      ( ~ r2_hidden(X19,k2_tarski(X17,X17))
      | ~ r2_hidden(X19,X18)
      | r2_hidden(X17,X18) ) ),
    inference(superposition,[],[f113,f96])).

fof(f571,plain,
    ( ~ r2_hidden(sK0,k2_tarski(sK0,sK0))
    | spl7_9 ),
    inference(avatar_component_clause,[],[f569])).

fof(f569,plain,
    ( spl7_9
  <=> r2_hidden(sK0,k2_tarski(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f164,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X1,X0)) ),
    inference(resolution,[],[f158,f161])).

fof(f158,plain,(
    ! [X8,X7,X9] :
      ( ~ r2_hidden(X9,k2_tarski(X8,X8))
      | r2_hidden(X9,k2_tarski(X7,X8)) ) ),
    inference(superposition,[],[f109,f84])).

fof(f84,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1)) ),
    inference(definition_unfolding,[],[f60,f61,f61])).

fof(f60,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f109,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
              & ~ r2_hidden(sK5(X0,X1,X2),X0) )
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( r2_hidden(sK5(X0,X1,X2),X1)
            | r2_hidden(sK5(X0,X1,X2),X0)
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f37,f38])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            & ~ r2_hidden(sK5(X0,X1,X2),X0) )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( r2_hidden(sK5(X0,X1,X2),X1)
          | r2_hidden(sK5(X0,X1,X2),X0)
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f161,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(resolution,[],[f157,f107])).

fof(f107,plain,(
    ! [X3] : r2_hidden(X3,k2_tarski(X3,X3)) ),
    inference(equality_resolution,[],[f106])).

fof(f106,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_tarski(X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f65,f61])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK4(X0,X1) != X0
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( sK4(X0,X1) = X0
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK4(X0,X1) != X0
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( sK4(X0,X1) = X0
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f157,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(X6,k2_tarski(X4,X4))
      | r2_hidden(X6,k2_tarski(X4,X5)) ) ),
    inference(superposition,[],[f110,f84])).

fof(f110,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f572,plain,
    ( ~ spl7_9
    | ~ spl7_3
    | spl7_5 ),
    inference(avatar_split_clause,[],[f564,f460,f125,f569])).

fof(f460,plain,
    ( spl7_5
  <=> r2_hidden(sK2,k2_tarski(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f564,plain,
    ( ~ r2_hidden(sK0,k2_tarski(sK0,sK0))
    | ~ spl7_3
    | spl7_5 ),
    inference(superposition,[],[f462,f127])).

fof(f462,plain,
    ( ~ r2_hidden(sK2,k2_tarski(sK0,sK0))
    | spl7_5 ),
    inference(avatar_component_clause,[],[f460])).

fof(f561,plain,
    ( spl7_2
    | spl7_8 ),
    inference(avatar_contradiction_clause,[],[f557])).

fof(f557,plain,
    ( $false
    | spl7_2
    | spl7_8 ),
    inference(unit_resulting_resolution,[],[f123,f164,f555,f112])).

fof(f112,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f123,plain,
    ( ~ r2_hidden(sK2,sK1)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl7_2
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f556,plain,
    ( spl7_7
    | ~ spl7_8
    | spl7_4 ),
    inference(avatar_split_clause,[],[f514,f130,f553,f549])).

fof(f130,plain,
    ( spl7_4
  <=> k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK2),k4_xboole_0(k2_tarski(sK0,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f514,plain,
    ( ~ r2_hidden(sK2,k4_xboole_0(k2_tarski(sK0,sK2),sK1))
    | r2_hidden(sK0,k4_xboole_0(k2_tarski(sK0,sK2),sK1))
    | spl7_4 ),
    inference(trivial_inequality_removal,[],[f495])).

fof(f495,plain,
    ( k2_tarski(sK0,sK0) != k2_tarski(sK0,sK0)
    | ~ r2_hidden(sK2,k4_xboole_0(k2_tarski(sK0,sK2),sK1))
    | r2_hidden(sK0,k4_xboole_0(k2_tarski(sK0,sK2),sK1))
    | spl7_4 ),
    inference(superposition,[],[f132,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f57,f61])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l38_zfmisc_1)).

fof(f132,plain,
    ( k2_tarski(sK0,sK0) != k4_xboole_0(k2_tarski(sK0,sK2),k4_xboole_0(k2_tarski(sK0,sK2),sK1))
    | spl7_4 ),
    inference(avatar_component_clause,[],[f130])).

fof(f467,plain,
    ( ~ spl7_5
    | ~ spl7_6
    | spl7_4 ),
    inference(avatar_split_clause,[],[f457,f130,f464,f460])).

fof(f457,plain,
    ( k2_tarski(sK0,sK0) != k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),sK1))
    | ~ r2_hidden(sK2,k2_tarski(sK0,sK0))
    | spl7_4 ),
    inference(superposition,[],[f132,f236])).

fof(f236,plain,(
    ! [X0,X1] :
      ( k2_tarski(X1,X1) = k2_tarski(X1,X0)
      | ~ r2_hidden(X0,k2_tarski(X1,X1)) ) ),
    inference(duplicate_literal_removal,[],[f226])).

fof(f226,plain,(
    ! [X0,X1] :
      ( k2_tarski(X1,X1) = k2_tarski(X1,X0)
      | ~ r2_hidden(X0,k2_tarski(X1,X1))
      | ~ r2_hidden(X0,k2_tarski(X1,X1)) ) ),
    inference(superposition,[],[f153,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) = X1
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) = X1
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) = X1
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
     => k2_xboole_0(k2_tarski(X0,X2),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_zfmisc_1)).

fof(f153,plain,(
    ! [X2,X3] : k2_xboole_0(k2_tarski(X3,X3),k2_tarski(X2,X2)) = k2_tarski(X2,X3) ),
    inference(superposition,[],[f84,f83])).

fof(f83,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f133,plain,(
    ~ spl7_4 ),
    inference(avatar_split_clause,[],[f85,f130])).

fof(f85,plain,(
    k2_tarski(sK0,sK0) != k4_xboole_0(k2_tarski(sK0,sK2),k4_xboole_0(k2_tarski(sK0,sK2),sK1)) ),
    inference(definition_unfolding,[],[f47,f61,f54])).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f47,plain,(
    k1_tarski(sK0) != k3_xboole_0(k2_tarski(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( k1_tarski(sK0) != k3_xboole_0(k2_tarski(sK0,sK2),sK1)
    & ( sK0 = sK2
      | ~ r2_hidden(sK2,sK1) )
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f21])).

fof(f21,plain,
    ( ? [X0,X1,X2] :
        ( k1_tarski(X0) != k3_xboole_0(k2_tarski(X0,X2),X1)
        & ( X0 = X2
          | ~ r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) )
   => ( k1_tarski(sK0) != k3_xboole_0(k2_tarski(sK0,sK2),sK1)
      & ( sK0 = sK2
        | ~ r2_hidden(sK2,sK1) )
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(X0) != k3_xboole_0(k2_tarski(X0,X2),X1)
      & ( X0 = X2
        | ~ r2_hidden(X2,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(X0) != k3_xboole_0(k2_tarski(X0,X2),X1)
      & ( X0 = X2
        | ~ r2_hidden(X2,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,X1)
       => ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
          | ( X0 != X2
            & r2_hidden(X2,X1) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,X1)
     => ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
        | ( X0 != X2
          & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_zfmisc_1)).

fof(f128,plain,
    ( ~ spl7_2
    | spl7_3 ),
    inference(avatar_split_clause,[],[f46,f125,f121])).

fof(f46,plain,
    ( sK0 = sK2
    | ~ r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f119,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f45,f116])).

fof(f45,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.08  % Command    : run_vampire %s %d
% 0.08/0.27  % Computer   : n003.cluster.edu
% 0.08/0.27  % Model      : x86_64 x86_64
% 0.08/0.27  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.08/0.27  % Memory     : 8042.1875MB
% 0.08/0.27  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.08/0.27  % CPULimit   : 60
% 0.08/0.27  % WCLimit    : 600
% 0.08/0.27  % DateTime   : Tue Dec  1 13:12:27 EST 2020
% 0.08/0.27  % CPUTime    : 
% 0.12/0.36  % (3326)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.12/0.37  % (3331)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.12/0.39  % (3328)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.12/0.40  % (3327)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.12/0.40  % (3349)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.12/0.40  % (3329)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.12/0.40  % (3350)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.12/0.40  % (3340)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.12/0.40  % (3341)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.12/0.40  % (3330)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.12/0.41  % (3337)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.12/0.41  % (3338)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.12/0.42  % (3334)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.12/0.42  % (3345)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.12/0.42  % (3335)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.12/0.42  % (3339)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.12/0.42  % (3344)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.12/0.42  % (3351)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.12/0.43  % (3346)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.12/0.43  % (3347)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.12/0.43  % (3355)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.12/0.43  % (3342)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.12/0.43  % (3336)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.12/0.43  % (3348)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.12/0.44  % (3342)Refutation not found, incomplete strategy% (3342)------------------------------
% 0.12/0.44  % (3342)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.12/0.44  % (3342)Termination reason: Refutation not found, incomplete strategy
% 0.12/0.44  
% 0.12/0.44  % (3342)Memory used [KB]: 10618
% 0.12/0.44  % (3342)Time elapsed: 0.111 s
% 0.12/0.44  % (3342)------------------------------
% 0.12/0.44  % (3342)------------------------------
% 0.12/0.44  % (3333)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.12/0.44  % (3352)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.12/0.44  % (3336)Refutation not found, incomplete strategy% (3336)------------------------------
% 0.12/0.44  % (3336)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.12/0.44  % (3336)Termination reason: Refutation not found, incomplete strategy
% 0.12/0.44  
% 0.12/0.44  % (3336)Memory used [KB]: 10746
% 0.12/0.44  % (3336)Time elapsed: 0.098 s
% 0.12/0.44  % (3336)------------------------------
% 0.12/0.44  % (3336)------------------------------
% 0.12/0.44  % (3332)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.12/0.45  % (3349)Refutation found. Thanks to Tanya!
% 0.12/0.45  % SZS status Theorem for theBenchmark
% 0.12/0.45  % SZS output start Proof for theBenchmark
% 0.12/0.45  fof(f678,plain,(
% 0.12/0.45    $false),
% 0.12/0.45    inference(avatar_sat_refutation,[],[f119,f128,f133,f467,f556,f561,f572,f588,f596,f647,f676])).
% 0.12/0.45  fof(f676,plain,(
% 0.12/0.45    ~spl7_1 | ~spl7_7),
% 0.12/0.45    inference(avatar_contradiction_clause,[],[f667])).
% 0.12/0.45  fof(f667,plain,(
% 0.12/0.45    $false | (~spl7_1 | ~spl7_7)),
% 0.12/0.45    inference(unit_resulting_resolution,[],[f118,f551,f113])).
% 0.12/0.45  fof(f113,plain,(
% 0.12/0.45    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 0.12/0.45    inference(equality_resolution,[],[f75])).
% 0.12/0.45  fof(f75,plain,(
% 0.12/0.45    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.12/0.45    inference(cnf_transformation,[],[f44])).
% 0.12/0.45  fof(f44,plain,(
% 0.12/0.45    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((~r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(sK6(X0,X1,X2),X0)) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.12/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f42,f43])).
% 0.12/0.45  fof(f43,plain,(
% 0.12/0.45    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((~r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(sK6(X0,X1,X2),X0)) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 0.12/0.45    introduced(choice_axiom,[])).
% 0.12/0.45  fof(f42,plain,(
% 0.12/0.45    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.12/0.45    inference(rectify,[],[f41])).
% 0.12/0.45  fof(f41,plain,(
% 0.12/0.45    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.12/0.45    inference(flattening,[],[f40])).
% 0.12/0.45  fof(f40,plain,(
% 0.12/0.45    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.12/0.45    inference(nnf_transformation,[],[f4])).
% 0.12/0.45  fof(f4,axiom,(
% 0.12/0.45    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.12/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.12/0.45  fof(f551,plain,(
% 0.12/0.45    r2_hidden(sK0,k4_xboole_0(k2_tarski(sK0,sK2),sK1)) | ~spl7_7),
% 0.12/0.45    inference(avatar_component_clause,[],[f549])).
% 0.12/0.45  fof(f549,plain,(
% 0.12/0.45    spl7_7 <=> r2_hidden(sK0,k4_xboole_0(k2_tarski(sK0,sK2),sK1))),
% 0.12/0.45    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.12/0.45  fof(f118,plain,(
% 0.12/0.45    r2_hidden(sK0,sK1) | ~spl7_1),
% 0.12/0.45    inference(avatar_component_clause,[],[f116])).
% 0.12/0.45  fof(f116,plain,(
% 0.12/0.45    spl7_1 <=> r2_hidden(sK0,sK1)),
% 0.12/0.45    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.12/0.45  fof(f647,plain,(
% 0.12/0.45    spl7_6 | spl7_10),
% 0.12/0.45    inference(avatar_contradiction_clause,[],[f639])).
% 0.12/0.45  fof(f639,plain,(
% 0.12/0.45    $false | (spl7_6 | spl7_10)),
% 0.12/0.45    inference(unit_resulting_resolution,[],[f595,f466,f96])).
% 0.12/0.45  fof(f96,plain,(
% 0.12/0.45    ( ! [X0,X1] : (k2_tarski(X0,X0) = k4_xboole_0(k2_tarski(X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.12/0.45    inference(definition_unfolding,[],[f63,f61,f61])).
% 0.12/0.45  fof(f61,plain,(
% 0.12/0.45    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.12/0.45    inference(cnf_transformation,[],[f11])).
% 0.12/0.45  fof(f11,axiom,(
% 0.12/0.45    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.12/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.12/0.45  fof(f63,plain,(
% 0.12/0.45    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.12/0.45    inference(cnf_transformation,[],[f30])).
% 0.12/0.45  fof(f30,plain,(
% 0.12/0.45    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) & (~r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)))),
% 0.12/0.45    inference(nnf_transformation,[],[f12])).
% 0.12/0.45  fof(f12,axiom,(
% 0.12/0.45    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 0.12/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).
% 0.12/0.45  fof(f466,plain,(
% 0.12/0.45    k2_tarski(sK0,sK0) != k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),sK1)) | spl7_6),
% 0.12/0.45    inference(avatar_component_clause,[],[f464])).
% 0.12/0.45  fof(f464,plain,(
% 0.12/0.45    spl7_6 <=> k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),sK1))),
% 0.12/0.45    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.12/0.45  fof(f595,plain,(
% 0.12/0.45    ~r2_hidden(sK0,k4_xboole_0(k2_tarski(sK0,sK0),sK1)) | spl7_10),
% 0.12/0.45    inference(avatar_component_clause,[],[f593])).
% 0.12/0.45  fof(f593,plain,(
% 0.12/0.45    spl7_10 <=> r2_hidden(sK0,k4_xboole_0(k2_tarski(sK0,sK0),sK1))),
% 0.12/0.45    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.12/0.45  fof(f596,plain,(
% 0.12/0.45    ~spl7_10 | ~spl7_3 | spl7_8),
% 0.12/0.45    inference(avatar_split_clause,[],[f567,f553,f125,f593])).
% 0.12/0.45  fof(f125,plain,(
% 0.12/0.45    spl7_3 <=> sK0 = sK2),
% 0.12/0.45    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.12/0.45  fof(f553,plain,(
% 0.12/0.45    spl7_8 <=> r2_hidden(sK2,k4_xboole_0(k2_tarski(sK0,sK2),sK1))),
% 0.12/0.45    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.12/0.45  fof(f567,plain,(
% 0.12/0.45    ~r2_hidden(sK0,k4_xboole_0(k2_tarski(sK0,sK0),sK1)) | (~spl7_3 | spl7_8)),
% 0.12/0.45    inference(superposition,[],[f555,f127])).
% 0.12/0.45  fof(f127,plain,(
% 0.12/0.45    sK0 = sK2 | ~spl7_3),
% 0.12/0.45    inference(avatar_component_clause,[],[f125])).
% 0.12/0.45  fof(f555,plain,(
% 0.12/0.45    ~r2_hidden(sK2,k4_xboole_0(k2_tarski(sK0,sK2),sK1)) | spl7_8),
% 0.12/0.45    inference(avatar_component_clause,[],[f553])).
% 0.12/0.45  fof(f588,plain,(
% 0.12/0.45    spl7_9),
% 0.12/0.45    inference(avatar_contradiction_clause,[],[f577])).
% 0.12/0.45  fof(f577,plain,(
% 0.12/0.45    $false | spl7_9),
% 0.12/0.45    inference(unit_resulting_resolution,[],[f161,f164,f571,f205])).
% 0.12/0.45  fof(f205,plain,(
% 0.12/0.45    ( ! [X19,X17,X18] : (~r2_hidden(X19,k2_tarski(X17,X17)) | ~r2_hidden(X19,X18) | r2_hidden(X17,X18)) )),
% 0.12/0.45    inference(superposition,[],[f113,f96])).
% 0.12/0.45  fof(f571,plain,(
% 0.12/0.45    ~r2_hidden(sK0,k2_tarski(sK0,sK0)) | spl7_9),
% 0.12/0.45    inference(avatar_component_clause,[],[f569])).
% 0.12/0.45  fof(f569,plain,(
% 0.12/0.45    spl7_9 <=> r2_hidden(sK0,k2_tarski(sK0,sK0))),
% 0.12/0.45    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.12/0.45  fof(f164,plain,(
% 0.12/0.45    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X1,X0))) )),
% 0.12/0.45    inference(resolution,[],[f158,f161])).
% 0.12/0.45  fof(f158,plain,(
% 0.12/0.45    ( ! [X8,X7,X9] : (~r2_hidden(X9,k2_tarski(X8,X8)) | r2_hidden(X9,k2_tarski(X7,X8))) )),
% 0.12/0.45    inference(superposition,[],[f109,f84])).
% 0.12/0.45  fof(f84,plain,(
% 0.12/0.45    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1))) )),
% 0.12/0.45    inference(definition_unfolding,[],[f60,f61,f61])).
% 0.12/0.45  fof(f60,plain,(
% 0.12/0.45    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.12/0.45    inference(cnf_transformation,[],[f10])).
% 0.12/0.45  fof(f10,axiom,(
% 0.12/0.45    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.12/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 0.12/0.45  fof(f109,plain,(
% 0.12/0.45    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 0.12/0.45    inference(equality_resolution,[],[f70])).
% 0.12/0.45  fof(f70,plain,(
% 0.12/0.45    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 0.12/0.45    inference(cnf_transformation,[],[f39])).
% 0.12/0.45  fof(f39,plain,(
% 0.12/0.45    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK5(X0,X1,X2),X1) & ~r2_hidden(sK5(X0,X1,X2),X0)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (r2_hidden(sK5(X0,X1,X2),X1) | r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.12/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f37,f38])).
% 0.12/0.45  fof(f38,plain,(
% 0.12/0.45    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK5(X0,X1,X2),X1) & ~r2_hidden(sK5(X0,X1,X2),X0)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (r2_hidden(sK5(X0,X1,X2),X1) | r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 0.12/0.45    introduced(choice_axiom,[])).
% 0.12/0.45  fof(f37,plain,(
% 0.12/0.45    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.12/0.45    inference(rectify,[],[f36])).
% 0.12/0.45  fof(f36,plain,(
% 0.12/0.45    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.12/0.45    inference(flattening,[],[f35])).
% 0.12/0.45  fof(f35,plain,(
% 0.12/0.45    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.12/0.45    inference(nnf_transformation,[],[f2])).
% 0.12/0.45  fof(f2,axiom,(
% 0.12/0.45    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.12/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.12/0.45  fof(f161,plain,(
% 0.12/0.45    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X0,X1))) )),
% 0.12/0.45    inference(resolution,[],[f157,f107])).
% 0.12/0.45  fof(f107,plain,(
% 0.12/0.45    ( ! [X3] : (r2_hidden(X3,k2_tarski(X3,X3))) )),
% 0.12/0.45    inference(equality_resolution,[],[f106])).
% 0.12/0.45  fof(f106,plain,(
% 0.12/0.45    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_tarski(X3,X3) != X1) )),
% 0.12/0.45    inference(equality_resolution,[],[f100])).
% 0.12/0.45  fof(f100,plain,(
% 0.12/0.45    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_tarski(X0,X0) != X1) )),
% 0.12/0.45    inference(definition_unfolding,[],[f65,f61])).
% 0.12/0.45  fof(f65,plain,(
% 0.12/0.45    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.12/0.45    inference(cnf_transformation,[],[f34])).
% 0.12/0.45  fof(f34,plain,(
% 0.12/0.45    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.12/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f33])).
% 0.12/0.45  fof(f33,plain,(
% 0.12/0.45    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1))))),
% 0.12/0.45    introduced(choice_axiom,[])).
% 0.12/0.45  fof(f32,plain,(
% 0.12/0.45    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.12/0.45    inference(rectify,[],[f31])).
% 0.12/0.45  fof(f31,plain,(
% 0.12/0.45    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.12/0.45    inference(nnf_transformation,[],[f9])).
% 0.12/0.45  fof(f9,axiom,(
% 0.12/0.45    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.12/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.12/0.45  fof(f157,plain,(
% 0.12/0.45    ( ! [X6,X4,X5] : (~r2_hidden(X6,k2_tarski(X4,X4)) | r2_hidden(X6,k2_tarski(X4,X5))) )),
% 0.12/0.45    inference(superposition,[],[f110,f84])).
% 0.12/0.45  fof(f110,plain,(
% 0.12/0.45    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 0.12/0.45    inference(equality_resolution,[],[f69])).
% 0.12/0.45  fof(f69,plain,(
% 0.12/0.45    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 0.12/0.45    inference(cnf_transformation,[],[f39])).
% 0.12/0.45  fof(f572,plain,(
% 0.12/0.45    ~spl7_9 | ~spl7_3 | spl7_5),
% 0.12/0.45    inference(avatar_split_clause,[],[f564,f460,f125,f569])).
% 0.12/0.45  fof(f460,plain,(
% 0.12/0.45    spl7_5 <=> r2_hidden(sK2,k2_tarski(sK0,sK0))),
% 0.12/0.45    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.12/0.45  fof(f564,plain,(
% 0.12/0.45    ~r2_hidden(sK0,k2_tarski(sK0,sK0)) | (~spl7_3 | spl7_5)),
% 0.12/0.45    inference(superposition,[],[f462,f127])).
% 0.12/0.45  fof(f462,plain,(
% 0.12/0.45    ~r2_hidden(sK2,k2_tarski(sK0,sK0)) | spl7_5),
% 0.12/0.45    inference(avatar_component_clause,[],[f460])).
% 0.12/0.45  fof(f561,plain,(
% 0.12/0.45    spl7_2 | spl7_8),
% 0.12/0.45    inference(avatar_contradiction_clause,[],[f557])).
% 0.12/0.45  fof(f557,plain,(
% 0.12/0.45    $false | (spl7_2 | spl7_8)),
% 0.12/0.45    inference(unit_resulting_resolution,[],[f123,f164,f555,f112])).
% 0.12/0.45  fof(f112,plain,(
% 0.12/0.45    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 0.12/0.45    inference(equality_resolution,[],[f76])).
% 0.12/0.45  fof(f76,plain,(
% 0.12/0.45    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 0.12/0.45    inference(cnf_transformation,[],[f44])).
% 0.12/0.45  fof(f123,plain,(
% 0.12/0.45    ~r2_hidden(sK2,sK1) | spl7_2),
% 0.12/0.45    inference(avatar_component_clause,[],[f121])).
% 0.12/0.45  fof(f121,plain,(
% 0.12/0.45    spl7_2 <=> r2_hidden(sK2,sK1)),
% 0.12/0.45    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.12/0.45  fof(f556,plain,(
% 0.12/0.45    spl7_7 | ~spl7_8 | spl7_4),
% 0.12/0.45    inference(avatar_split_clause,[],[f514,f130,f553,f549])).
% 0.12/0.45  fof(f130,plain,(
% 0.12/0.45    spl7_4 <=> k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK2),k4_xboole_0(k2_tarski(sK0,sK2),sK1))),
% 0.12/0.45    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.12/0.45  fof(f514,plain,(
% 0.12/0.45    ~r2_hidden(sK2,k4_xboole_0(k2_tarski(sK0,sK2),sK1)) | r2_hidden(sK0,k4_xboole_0(k2_tarski(sK0,sK2),sK1)) | spl7_4),
% 0.12/0.45    inference(trivial_inequality_removal,[],[f495])).
% 0.12/0.45  fof(f495,plain,(
% 0.12/0.45    k2_tarski(sK0,sK0) != k2_tarski(sK0,sK0) | ~r2_hidden(sK2,k4_xboole_0(k2_tarski(sK0,sK2),sK1)) | r2_hidden(sK0,k4_xboole_0(k2_tarski(sK0,sK2),sK1)) | spl7_4),
% 0.12/0.45    inference(superposition,[],[f132,f93])).
% 0.12/0.45  fof(f93,plain,(
% 0.12/0.45    ( ! [X2,X0,X1] : (k2_tarski(X0,X0) = k4_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 0.12/0.45    inference(definition_unfolding,[],[f57,f61])).
% 0.12/0.45  fof(f57,plain,(
% 0.12/0.45    ( ! [X2,X0,X1] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 0.12/0.45    inference(cnf_transformation,[],[f29])).
% 0.12/0.45  fof(f29,plain,(
% 0.12/0.45    ! [X0,X1,X2] : ((k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) | (X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2)) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 0.12/0.45    inference(flattening,[],[f28])).
% 0.12/0.45  fof(f28,plain,(
% 0.12/0.45    ! [X0,X1,X2] : ((k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) | ((X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2))) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 0.12/0.45    inference(nnf_transformation,[],[f13])).
% 0.12/0.45  fof(f13,axiom,(
% 0.12/0.45    ! [X0,X1,X2] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 0.12/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l38_zfmisc_1)).
% 0.12/0.45  fof(f132,plain,(
% 0.12/0.45    k2_tarski(sK0,sK0) != k4_xboole_0(k2_tarski(sK0,sK2),k4_xboole_0(k2_tarski(sK0,sK2),sK1)) | spl7_4),
% 0.12/0.45    inference(avatar_component_clause,[],[f130])).
% 0.12/0.45  fof(f467,plain,(
% 0.12/0.45    ~spl7_5 | ~spl7_6 | spl7_4),
% 0.12/0.45    inference(avatar_split_clause,[],[f457,f130,f464,f460])).
% 0.12/0.45  fof(f457,plain,(
% 0.12/0.45    k2_tarski(sK0,sK0) != k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),sK1)) | ~r2_hidden(sK2,k2_tarski(sK0,sK0)) | spl7_4),
% 0.12/0.45    inference(superposition,[],[f132,f236])).
% 0.12/0.45  fof(f236,plain,(
% 0.12/0.45    ( ! [X0,X1] : (k2_tarski(X1,X1) = k2_tarski(X1,X0) | ~r2_hidden(X0,k2_tarski(X1,X1))) )),
% 0.12/0.45    inference(duplicate_literal_removal,[],[f226])).
% 0.12/0.45  fof(f226,plain,(
% 0.12/0.45    ( ! [X0,X1] : (k2_tarski(X1,X1) = k2_tarski(X1,X0) | ~r2_hidden(X0,k2_tarski(X1,X1)) | ~r2_hidden(X0,k2_tarski(X1,X1))) )),
% 0.12/0.45    inference(superposition,[],[f153,f59])).
% 0.12/0.45  fof(f59,plain,(
% 0.12/0.45    ( ! [X2,X0,X1] : (k2_xboole_0(k2_tarski(X0,X2),X1) = X1 | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)) )),
% 0.12/0.45    inference(cnf_transformation,[],[f20])).
% 0.12/0.45  fof(f20,plain,(
% 0.12/0.45    ! [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) = X1 | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1))),
% 0.12/0.45    inference(flattening,[],[f19])).
% 0.12/0.45  fof(f19,plain,(
% 0.12/0.45    ! [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) = X1 | (~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)))),
% 0.12/0.45    inference(ennf_transformation,[],[f14])).
% 0.12/0.45  fof(f14,axiom,(
% 0.12/0.45    ! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_xboole_0(k2_tarski(X0,X2),X1) = X1)),
% 0.12/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_zfmisc_1)).
% 0.12/0.45  fof(f153,plain,(
% 0.12/0.45    ( ! [X2,X3] : (k2_xboole_0(k2_tarski(X3,X3),k2_tarski(X2,X2)) = k2_tarski(X2,X3)) )),
% 0.12/0.45    inference(superposition,[],[f84,f83])).
% 0.12/0.45  fof(f83,plain,(
% 0.12/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.12/0.45    inference(cnf_transformation,[],[f1])).
% 0.12/0.45  fof(f1,axiom,(
% 0.12/0.45    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.12/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.12/0.45  fof(f133,plain,(
% 0.12/0.45    ~spl7_4),
% 0.12/0.45    inference(avatar_split_clause,[],[f85,f130])).
% 0.12/0.45  fof(f85,plain,(
% 0.12/0.45    k2_tarski(sK0,sK0) != k4_xboole_0(k2_tarski(sK0,sK2),k4_xboole_0(k2_tarski(sK0,sK2),sK1))),
% 0.12/0.45    inference(definition_unfolding,[],[f47,f61,f54])).
% 0.12/0.45  fof(f54,plain,(
% 0.12/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.12/0.45    inference(cnf_transformation,[],[f7])).
% 0.12/0.45  fof(f7,axiom,(
% 0.12/0.45    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.12/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.12/0.45  fof(f47,plain,(
% 0.12/0.45    k1_tarski(sK0) != k3_xboole_0(k2_tarski(sK0,sK2),sK1)),
% 0.12/0.45    inference(cnf_transformation,[],[f22])).
% 0.12/0.45  fof(f22,plain,(
% 0.12/0.45    k1_tarski(sK0) != k3_xboole_0(k2_tarski(sK0,sK2),sK1) & (sK0 = sK2 | ~r2_hidden(sK2,sK1)) & r2_hidden(sK0,sK1)),
% 0.12/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f21])).
% 0.12/0.45  fof(f21,plain,(
% 0.12/0.45    ? [X0,X1,X2] : (k1_tarski(X0) != k3_xboole_0(k2_tarski(X0,X2),X1) & (X0 = X2 | ~r2_hidden(X2,X1)) & r2_hidden(X0,X1)) => (k1_tarski(sK0) != k3_xboole_0(k2_tarski(sK0,sK2),sK1) & (sK0 = sK2 | ~r2_hidden(sK2,sK1)) & r2_hidden(sK0,sK1))),
% 0.12/0.45    introduced(choice_axiom,[])).
% 0.12/0.45  fof(f18,plain,(
% 0.12/0.45    ? [X0,X1,X2] : (k1_tarski(X0) != k3_xboole_0(k2_tarski(X0,X2),X1) & (X0 = X2 | ~r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 0.12/0.45    inference(flattening,[],[f17])).
% 0.12/0.45  fof(f17,plain,(
% 0.12/0.45    ? [X0,X1,X2] : ((k1_tarski(X0) != k3_xboole_0(k2_tarski(X0,X2),X1) & (X0 = X2 | ~r2_hidden(X2,X1))) & r2_hidden(X0,X1))),
% 0.12/0.45    inference(ennf_transformation,[],[f16])).
% 0.12/0.45  fof(f16,negated_conjecture,(
% 0.12/0.45    ~! [X0,X1,X2] : (r2_hidden(X0,X1) => (k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | (X0 != X2 & r2_hidden(X2,X1))))),
% 0.12/0.45    inference(negated_conjecture,[],[f15])).
% 0.12/0.45  fof(f15,conjecture,(
% 0.12/0.45    ! [X0,X1,X2] : (r2_hidden(X0,X1) => (k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | (X0 != X2 & r2_hidden(X2,X1))))),
% 0.12/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_zfmisc_1)).
% 0.12/0.45  fof(f128,plain,(
% 0.12/0.45    ~spl7_2 | spl7_3),
% 0.12/0.45    inference(avatar_split_clause,[],[f46,f125,f121])).
% 0.12/0.45  fof(f46,plain,(
% 0.12/0.45    sK0 = sK2 | ~r2_hidden(sK2,sK1)),
% 0.12/0.45    inference(cnf_transformation,[],[f22])).
% 0.12/0.45  fof(f119,plain,(
% 0.12/0.45    spl7_1),
% 0.12/0.45    inference(avatar_split_clause,[],[f45,f116])).
% 0.12/0.45  fof(f45,plain,(
% 0.12/0.45    r2_hidden(sK0,sK1)),
% 0.12/0.45    inference(cnf_transformation,[],[f22])).
% 0.12/0.45  % SZS output end Proof for theBenchmark
% 0.12/0.45  % (3349)------------------------------
% 0.12/0.45  % (3349)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.12/0.45  % (3349)Termination reason: Refutation
% 0.12/0.45  
% 0.12/0.45  % (3349)Memory used [KB]: 11257
% 0.12/0.45  % (3349)Time elapsed: 0.127 s
% 0.12/0.45  % (3349)------------------------------
% 0.12/0.45  % (3349)------------------------------
% 0.12/0.45  % (3353)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.12/0.46  % (3354)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.12/0.46  % (3343)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.12/0.46  % (3354)Refutation not found, incomplete strategy% (3354)------------------------------
% 0.12/0.46  % (3354)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.12/0.46  % (3354)Termination reason: Refutation not found, incomplete strategy
% 0.12/0.46  
% 0.12/0.46  % (3354)Memory used [KB]: 10746
% 0.12/0.46  % (3354)Time elapsed: 0.139 s
% 0.12/0.46  % (3354)------------------------------
% 0.12/0.46  % (3354)------------------------------
% 0.12/0.47  % (3325)Success in time 0.186 s
%------------------------------------------------------------------------------
