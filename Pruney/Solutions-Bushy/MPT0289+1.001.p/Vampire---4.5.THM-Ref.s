%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0289+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:41 EST 2020

% Result     : Theorem 2.27s
% Output     : Refutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 242 expanded)
%              Number of leaves         :   17 (  97 expanded)
%              Depth                    :   11
%              Number of atoms          :  326 (1346 expanded)
%              Number of equality atoms :   33 ( 159 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1686,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f77,f81,f208,f1391,f1607,f1634,f1674,f1680,f1681,f1685])).

fof(f1685,plain,
    ( ~ spl8_10
    | spl8_1 ),
    inference(avatar_split_clause,[],[f101,f65,f205])).

fof(f205,plain,
    ( spl8_10
  <=> r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k3_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f65,plain,
    ( spl8_1
  <=> r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f101,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k3_tarski(sK1))
    | spl8_1 ),
    inference(resolution,[],[f66,f49])).

fof(f49,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK6(X0,X1,X2),X1)
              & ~ r2_hidden(sK6(X0,X1,X2),X0) )
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( r2_hidden(sK6(X0,X1,X2),X1)
            | r2_hidden(sK6(X0,X1,X2),X0)
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f25,f26])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK6(X0,X1,X2),X1)
            & ~ r2_hidden(sK6(X0,X1,X2),X0) )
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( r2_hidden(sK6(X0,X1,X2),X1)
          | r2_hidden(sK6(X0,X1,X2),X0)
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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

fof(f66,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f65])).

fof(f1681,plain,
    ( spl8_5
    | ~ spl8_3
    | spl8_6 ),
    inference(avatar_split_clause,[],[f906,f94,f74,f90])).

fof(f90,plain,
    ( spl8_5
  <=> r2_hidden(sK4(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f74,plain,
    ( spl8_3
  <=> r2_hidden(sK4(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f94,plain,
    ( spl8_6
  <=> r2_hidden(sK4(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f906,plain,
    ( r2_hidden(sK4(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),sK0)
    | ~ spl8_3
    | spl8_6 ),
    inference(resolution,[],[f119,f76])).

fof(f76,plain,
    ( r2_hidden(sK4(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k2_xboole_0(sK0,sK1))
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f74])).

fof(f119,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK4(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k2_xboole_0(X1,sK1))
        | r2_hidden(sK4(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),X1) )
    | spl8_6 ),
    inference(resolution,[],[f95,f51])).

fof(f51,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f95,plain,
    ( ~ r2_hidden(sK4(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),sK1)
    | spl8_6 ),
    inference(avatar_component_clause,[],[f94])).

fof(f1680,plain,
    ( ~ spl8_9
    | spl8_1 ),
    inference(avatar_split_clause,[],[f100,f65,f201])).

fof(f201,plain,
    ( spl8_9
  <=> r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k3_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f100,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k3_tarski(sK0))
    | spl8_1 ),
    inference(resolution,[],[f66,f50])).

fof(f50,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1674,plain,
    ( ~ spl8_2
    | ~ spl8_6
    | spl8_10 ),
    inference(avatar_split_clause,[],[f1667,f205,f94,f69])).

fof(f69,plain,
    ( spl8_2
  <=> r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),sK4(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f1667,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),sK4(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))))
    | ~ spl8_6
    | spl8_10 ),
    inference(resolution,[],[f96,f1425])).

fof(f1425,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),X0) )
    | spl8_10 ),
    inference(resolution,[],[f206,f46])).

fof(f46,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k3_tarski(X0))
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK3(X0,X1),X3) )
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( ( r2_hidden(sK4(X0,X1),X0)
              & r2_hidden(sK3(X0,X1),sK4(X0,X1)) )
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK5(X0,X5),X0)
                & r2_hidden(X5,sK5(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f18,f21,f20,f19])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X3) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( r2_hidden(X4,X0)
                & r2_hidden(X2,X4) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(sK3(X0,X1),X3) )
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK3(X0,X1),X4) )
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(sK3(X0,X1),X4) )
     => ( r2_hidden(sK4(X0,X1),X0)
        & r2_hidden(sK3(X0,X1),sK4(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK5(X0,X5),X0)
        & r2_hidden(X5,sK5(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X0)
                  & r2_hidden(X2,X4) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ? [X7] :
                  ( r2_hidden(X7,X0)
                  & r2_hidden(X5,X7) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) ) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

fof(f206,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k3_tarski(sK1))
    | spl8_10 ),
    inference(avatar_component_clause,[],[f205])).

fof(f96,plain,
    ( r2_hidden(sK4(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),sK1)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f94])).

fof(f1634,plain,
    ( ~ spl8_2
    | ~ spl8_5
    | spl8_9 ),
    inference(avatar_split_clause,[],[f401,f201,f90,f69])).

fof(f401,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),sK4(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))))
    | ~ spl8_5
    | spl8_9 ),
    inference(resolution,[],[f229,f92])).

fof(f92,plain,
    ( r2_hidden(sK4(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),sK0)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f90])).

fof(f229,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),X0) )
    | spl8_9 ),
    inference(resolution,[],[f202,f46])).

fof(f202,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k3_tarski(sK0))
    | spl8_9 ),
    inference(avatar_component_clause,[],[f201])).

fof(f1607,plain,
    ( ~ spl8_4
    | ~ spl8_9 ),
    inference(avatar_contradiction_clause,[],[f1602])).

fof(f1602,plain,
    ( $false
    | ~ spl8_4
    | ~ spl8_9 ),
    inference(resolution,[],[f1498,f1415])).

fof(f1415,plain,
    ( r2_hidden(sK5(sK0,sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),sK0)
    | ~ spl8_9 ),
    inference(resolution,[],[f203,f47])).

fof(f47,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK5(X0,X5),X0)
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK5(X0,X5),X0)
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f203,plain,
    ( r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k3_tarski(sK0))
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f201])).

fof(f1498,plain,
    ( ~ r2_hidden(sK5(sK0,sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),sK0)
    | ~ spl8_4
    | ~ spl8_9 ),
    inference(resolution,[],[f1413,f50])).

fof(f1413,plain,
    ( ~ r2_hidden(sK5(sK0,sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),k2_xboole_0(sK0,sK1))
    | ~ spl8_4
    | ~ spl8_9 ),
    inference(resolution,[],[f203,f219])).

fof(f219,plain,
    ( ! [X12] :
        ( ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k3_tarski(X12))
        | ~ r2_hidden(sK5(X12,sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),k2_xboole_0(sK0,sK1)) )
    | ~ spl8_4 ),
    inference(resolution,[],[f80,f48])).

fof(f48,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,sK5(X0,X5))
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,sK5(X0,X5))
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f80,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),X0)
        | ~ r2_hidden(X0,k2_xboole_0(sK0,sK1)) )
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl8_4
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k2_xboole_0(sK0,sK1))
        | ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f1391,plain,
    ( ~ spl8_4
    | ~ spl8_10 ),
    inference(avatar_contradiction_clause,[],[f1386])).

fof(f1386,plain,
    ( $false
    | ~ spl8_4
    | ~ spl8_10 ),
    inference(resolution,[],[f463,f234])).

fof(f234,plain,
    ( r2_hidden(sK5(sK1,sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),sK1)
    | ~ spl8_10 ),
    inference(resolution,[],[f207,f47])).

fof(f207,plain,
    ( r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k3_tarski(sK1))
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f205])).

fof(f463,plain,
    ( ~ r2_hidden(sK5(sK1,sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),sK1)
    | ~ spl8_4
    | ~ spl8_10 ),
    inference(resolution,[],[f316,f49])).

fof(f316,plain,
    ( ~ r2_hidden(sK5(sK1,sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),k2_xboole_0(sK0,sK1))
    | ~ spl8_4
    | ~ spl8_10 ),
    inference(resolution,[],[f219,f207])).

fof(f208,plain,
    ( spl8_9
    | spl8_10
    | ~ spl8_1 ),
    inference(avatar_split_clause,[],[f191,f65,f205,f201])).

fof(f191,plain,
    ( r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k3_tarski(sK1))
    | r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k3_tarski(sK0))
    | ~ spl8_1 ),
    inference(resolution,[],[f67,f51])).

fof(f67,plain,
    ( r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f65])).

fof(f81,plain,
    ( ~ spl8_1
    | spl8_4 ),
    inference(avatar_split_clause,[],[f63,f79,f65])).

fof(f63,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_xboole_0(sK0,sK1))
      | ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),X0)
      | ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))) ) ),
    inference(resolution,[],[f53,f54])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( sQ7_eqProxy(k3_tarski(X0),X1)
      | ~ r2_hidden(X3,X0)
      | ~ r2_hidden(sK3(X0,X1),X3)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(equality_proxy_replacement,[],[f39,f52])).

fof(f52,plain,(
    ! [X1,X0] :
      ( sQ7_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ7_eqProxy])])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( k3_tarski(X0) = X1
      | ~ r2_hidden(X3,X0)
      | ~ r2_hidden(sK3(X0,X1),X3)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f53,plain,(
    ~ sQ7_eqProxy(k3_tarski(k2_xboole_0(sK0,sK1)),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))) ),
    inference(equality_proxy_replacement,[],[f28,f52])).

fof(f28,plain,(
    k3_tarski(k2_xboole_0(sK0,sK1)) != k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    k3_tarski(k2_xboole_0(sK0,sK1)) != k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f11])).

fof(f11,plain,
    ( ? [X0,X1] : k3_tarski(k2_xboole_0(X0,X1)) != k2_xboole_0(k3_tarski(X0),k3_tarski(X1))
   => k3_tarski(k2_xboole_0(sK0,sK1)) != k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1)) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1] : k3_tarski(k2_xboole_0(X0,X1)) != k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_zfmisc_1)).

fof(f77,plain,
    ( spl8_1
    | spl8_3 ),
    inference(avatar_split_clause,[],[f62,f74,f65])).

fof(f62,plain,
    ( r2_hidden(sK4(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k2_xboole_0(sK0,sK1))
    | r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))) ),
    inference(resolution,[],[f53,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( sQ7_eqProxy(k3_tarski(X0),X1)
      | r2_hidden(sK4(X0,X1),X0)
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(equality_proxy_replacement,[],[f38,f52])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
      | r2_hidden(sK4(X0,X1),X0)
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f72,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f61,f69,f65])).

fof(f61,plain,
    ( r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),sK4(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))))
    | r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))) ),
    inference(resolution,[],[f53,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( sQ7_eqProxy(k3_tarski(X0),X1)
      | r2_hidden(sK3(X0,X1),sK4(X0,X1))
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(equality_proxy_replacement,[],[f37,f52])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
      | r2_hidden(sK3(X0,X1),sK4(X0,X1))
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f22])).

%------------------------------------------------------------------------------
