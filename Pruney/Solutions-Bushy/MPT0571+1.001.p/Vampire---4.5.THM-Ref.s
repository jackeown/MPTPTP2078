%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0571+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:14 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 336 expanded)
%              Number of leaves         :   23 ( 133 expanded)
%              Depth                    :   11
%              Number of atoms          :  409 (1785 expanded)
%              Number of equality atoms :   34 ( 217 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1332,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f88,f125,f208,f316,f329,f334,f349,f357,f395,f400,f860,f865,f895,f1247,f1331])).

fof(f1331,plain,
    ( ~ spl8_5
    | ~ spl8_35
    | ~ spl8_36 ),
    inference(avatar_contradiction_clause,[],[f1324])).

fof(f1324,plain,
    ( $false
    | ~ spl8_5
    | ~ spl8_35
    | ~ spl8_36 ),
    inference(resolution,[],[f899,f866])).

fof(f866,plain,
    ( ! [X0] : r2_hidden(sK5(sK2,sK0,sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),k2_xboole_0(sK0,X0))
    | ~ spl8_36 ),
    inference(resolution,[],[f864,f38])).

fof(f38,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f17,f18])).

fof(f18,plain,(
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

fof(f17,plain,(
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
    inference(rectify,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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

fof(f864,plain,
    ( r2_hidden(sK5(sK2,sK0,sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK0)
    | ~ spl8_36 ),
    inference(avatar_component_clause,[],[f862])).

fof(f862,plain,
    ( spl8_36
  <=> r2_hidden(sK5(sK2,sK0,sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).

fof(f899,plain,
    ( ~ r2_hidden(sK5(sK2,sK0,sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),k2_xboole_0(sK0,sK1))
    | ~ spl8_5
    | ~ spl8_35 ),
    inference(resolution,[],[f859,f85])).

fof(f85,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),X0),sK2)
        | ~ r2_hidden(X0,k2_xboole_0(sK0,sK1)) )
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl8_5
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k2_xboole_0(sK0,sK1))
        | ~ r2_hidden(k4_tarski(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),X0),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f859,plain,
    ( r2_hidden(k4_tarski(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),sK5(sK2,sK0,sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))))),sK2)
    | ~ spl8_35 ),
    inference(avatar_component_clause,[],[f857])).

fof(f857,plain,
    ( spl8_35
  <=> r2_hidden(k4_tarski(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),sK5(sK2,sK0,sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).

fof(f1247,plain,
    ( ~ spl8_5
    | ~ spl8_22
    | ~ spl8_23 ),
    inference(avatar_contradiction_clause,[],[f1240])).

fof(f1240,plain,
    ( $false
    | ~ spl8_5
    | ~ spl8_22
    | ~ spl8_23 ),
    inference(resolution,[],[f886,f497])).

fof(f497,plain,
    ( ! [X1] : r2_hidden(sK5(sK2,sK1,sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),k2_xboole_0(X1,sK1))
    | ~ spl8_23 ),
    inference(resolution,[],[f399,f37])).

fof(f37,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f399,plain,
    ( r2_hidden(sK5(sK2,sK1,sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK1)
    | ~ spl8_23 ),
    inference(avatar_component_clause,[],[f397])).

fof(f397,plain,
    ( spl8_23
  <=> r2_hidden(sK5(sK2,sK1,sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f886,plain,
    ( ~ r2_hidden(sK5(sK2,sK1,sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),k2_xboole_0(sK0,sK1))
    | ~ spl8_5
    | ~ spl8_22 ),
    inference(resolution,[],[f394,f85])).

fof(f394,plain,
    ( r2_hidden(k4_tarski(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),sK5(sK2,sK1,sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))))),sK2)
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f392])).

fof(f392,plain,
    ( spl8_22
  <=> r2_hidden(k4_tarski(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),sK5(sK2,sK1,sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f895,plain,
    ( ~ spl8_23
    | ~ spl8_14
    | ~ spl8_22 ),
    inference(avatar_split_clause,[],[f884,f392,f206,f397])).

fof(f206,plain,
    ( spl8_14
  <=> ! [X1] :
        ( ~ r2_hidden(X1,sK1)
        | ~ r2_hidden(k4_tarski(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),X1),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f884,plain,
    ( ~ r2_hidden(sK5(sK2,sK1,sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK1)
    | ~ spl8_14
    | ~ spl8_22 ),
    inference(resolution,[],[f394,f207])).

fof(f207,plain,
    ( ! [X1] :
        ( ~ r2_hidden(k4_tarski(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),X1),sK2)
        | ~ r2_hidden(X1,sK1) )
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f206])).

fof(f865,plain,
    ( ~ spl8_1
    | spl8_36
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f851,f342,f862,f66])).

fof(f66,plain,
    ( spl8_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f342,plain,
    ( spl8_19
  <=> r2_hidden(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f851,plain,
    ( r2_hidden(sK5(sK2,sK0,sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK0)
    | ~ v1_relat_1(sK2)
    | ~ spl8_19 ),
    inference(resolution,[],[f344,f35])).

fof(f35,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),X4),X0) )
                | ~ r2_hidden(sK3(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK4(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0) )
                | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ( r2_hidden(sK5(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(X6,sK5(X0,X1,X6)),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f10,f13,f12,f11])).

fof(f11,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r2_hidden(k4_tarski(X3,X4),X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X3,X5),X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),X4),X0) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(sK3(X0,X1,X2),X5),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(sK3(X0,X1,X2),X5),X0) )
     => ( r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X6,X8),X0) )
     => ( r2_hidden(sK5(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(X6,sK5(X0,X1,X6)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( r2_hidden(X5,X1)
                      & r2_hidden(k4_tarski(X3,X5),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ? [X8] :
                      ( r2_hidden(X8,X1)
                      & r2_hidden(k4_tarski(X6,X8),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X3,X4),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) ) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).

fof(f344,plain,
    ( r2_hidden(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK0))
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f342])).

fof(f860,plain,
    ( ~ spl8_1
    | spl8_35
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f850,f342,f857,f66])).

fof(f850,plain,
    ( r2_hidden(k4_tarski(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),sK5(sK2,sK0,sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))))),sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl8_19 ),
    inference(resolution,[],[f344,f36])).

fof(f36,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k4_tarski(X6,sK5(X0,X1,X6)),X0)
      | ~ r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(k4_tarski(X6,sK5(X0,X1,X6)),X0)
      | ~ r2_hidden(X6,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f400,plain,
    ( ~ spl8_1
    | spl8_23
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f386,f346,f397,f66])).

fof(f346,plain,
    ( spl8_20
  <=> r2_hidden(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f386,plain,
    ( r2_hidden(sK5(sK2,sK1,sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl8_20 ),
    inference(resolution,[],[f348,f35])).

fof(f348,plain,
    ( r2_hidden(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK1))
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f346])).

fof(f395,plain,
    ( ~ spl8_1
    | spl8_22
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f385,f346,f392,f66])).

fof(f385,plain,
    ( r2_hidden(k4_tarski(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),sK5(sK2,sK1,sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))))),sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl8_20 ),
    inference(resolution,[],[f348,f36])).

fof(f357,plain,
    ( ~ spl8_10
    | spl8_2
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f309,f74,f70,f122])).

fof(f122,plain,
    ( spl8_10
  <=> r2_hidden(sK4(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f70,plain,
    ( spl8_2
  <=> r2_hidden(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f74,plain,
    ( spl8_3
  <=> r2_hidden(k4_tarski(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),sK4(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f309,plain,
    ( ~ r2_hidden(sK4(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),sK1)
    | spl8_2
    | ~ spl8_3 ),
    inference(resolution,[],[f141,f130])).

fof(f130,plain,
    ( ~ r2_hidden(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK1))
    | spl8_2 ),
    inference(resolution,[],[f71,f37])).

fof(f71,plain,
    ( ~ r2_hidden(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))
    | spl8_2 ),
    inference(avatar_component_clause,[],[f70])).

fof(f141,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,X0))
        | ~ r2_hidden(sK4(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),X0) )
    | ~ spl8_3 ),
    inference(resolution,[],[f76,f51])).

fof(f51,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X6),sK2)
      | ~ r2_hidden(X6,X5)
      | r2_hidden(X4,k10_relat_1(sK2,X5)) ) ),
    inference(resolution,[],[f20,f34])).

fof(f34,plain,(
    ! [X6,X0,X7,X1] :
      ( r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f20,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,
    ( k10_relat_1(sK2,k2_xboole_0(sK0,sK1)) != k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f7])).

fof(f7,plain,
    ( ? [X0,X1,X2] :
        ( k10_relat_1(X2,k2_xboole_0(X0,X1)) != k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        & v1_relat_1(X2) )
   => ( k10_relat_1(sK2,k2_xboole_0(sK0,sK1)) != k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( k10_relat_1(X2,k2_xboole_0(X0,X1)) != k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_relat_1)).

fof(f76,plain,
    ( r2_hidden(k4_tarski(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),sK4(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK2)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f74])).

fof(f349,plain,
    ( spl8_19
    | spl8_20
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f336,f70,f346,f342])).

fof(f336,plain,
    ( r2_hidden(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK1))
    | r2_hidden(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK0))
    | ~ spl8_2 ),
    inference(resolution,[],[f72,f39])).

fof(f39,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f72,plain,
    ( r2_hidden(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f70])).

fof(f334,plain,
    ( spl8_2
    | spl8_3 ),
    inference(avatar_split_clause,[],[f139,f74,f70])).

fof(f139,plain,
    ( r2_hidden(k4_tarski(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),sK4(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK2)
    | r2_hidden(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))) ),
    inference(resolution,[],[f52,f41])).

fof(f41,plain,(
    ~ sQ7_eqProxy(k10_relat_1(sK2,k2_xboole_0(sK0,sK1)),k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))) ),
    inference(equality_proxy_replacement,[],[f21,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( sQ7_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ7_eqProxy])])).

fof(f21,plain,(
    k10_relat_1(sK2,k2_xboole_0(sK0,sK1)) != k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f52,plain,(
    ! [X8,X7] :
      ( sQ7_eqProxy(k10_relat_1(sK2,X7),X8)
      | r2_hidden(k4_tarski(sK3(sK2,X7,X8),sK4(sK2,X7,X8)),sK2)
      | r2_hidden(sK3(sK2,X7,X8),X8) ) ),
    inference(resolution,[],[f20,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( sQ7_eqProxy(k10_relat_1(X0,X1),X2)
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f25,f40])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f329,plain,
    ( ~ spl8_2
    | spl8_5 ),
    inference(avatar_split_clause,[],[f140,f84,f70])).

fof(f140,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_xboole_0(sK0,sK1))
      | ~ r2_hidden(k4_tarski(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),X0),sK2)
      | ~ r2_hidden(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))) ) ),
    inference(resolution,[],[f54,f41])).

fof(f54,plain,(
    ! [X12,X13,X11] :
      ( sQ7_eqProxy(k10_relat_1(sK2,X11),X12)
      | ~ r2_hidden(X13,X11)
      | ~ r2_hidden(k4_tarski(sK3(sK2,X11,X12),X13),sK2)
      | ~ r2_hidden(sK3(sK2,X11,X12),X12) ) ),
    inference(resolution,[],[f20,f42])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( sQ7_eqProxy(k10_relat_1(X0,X1),X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),X4),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f27,f40])).

fof(f27,plain,(
    ! [X4,X2,X0,X1] :
      ( k10_relat_1(X0,X1) = X2
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),X4),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f316,plain,
    ( ~ spl8_9
    | spl8_2
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f308,f74,f70,f118])).

fof(f118,plain,
    ( spl8_9
  <=> r2_hidden(sK4(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f308,plain,
    ( ~ r2_hidden(sK4(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),sK0)
    | spl8_2
    | ~ spl8_3 ),
    inference(resolution,[],[f141,f129])).

fof(f129,plain,
    ( ~ r2_hidden(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK0))
    | spl8_2 ),
    inference(resolution,[],[f71,f38])).

fof(f208,plain,
    ( ~ spl8_1
    | spl8_14
    | spl8_2 ),
    inference(avatar_split_clause,[],[f202,f70,f206,f66])).

fof(f202,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK1)
        | ~ r2_hidden(k4_tarski(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),X1),sK2)
        | ~ v1_relat_1(sK2) )
    | spl8_2 ),
    inference(resolution,[],[f130,f34])).

fof(f125,plain,
    ( spl8_9
    | spl8_10
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f112,f79,f122,f118])).

fof(f79,plain,
    ( spl8_4
  <=> r2_hidden(sK4(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f112,plain,
    ( r2_hidden(sK4(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),sK1)
    | r2_hidden(sK4(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),sK0)
    | ~ spl8_4 ),
    inference(resolution,[],[f81,f39])).

fof(f81,plain,
    ( r2_hidden(sK4(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k2_xboole_0(sK0,sK1))
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f79])).

fof(f88,plain,(
    spl8_1 ),
    inference(avatar_contradiction_clause,[],[f87])).

fof(f87,plain,
    ( $false
    | spl8_1 ),
    inference(resolution,[],[f68,f20])).

fof(f68,plain,
    ( ~ v1_relat_1(sK2)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f66])).

fof(f82,plain,
    ( ~ spl8_1
    | spl8_2
    | spl8_4 ),
    inference(avatar_split_clause,[],[f63,f79,f70,f66])).

fof(f63,plain,
    ( r2_hidden(sK4(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k2_xboole_0(sK0,sK1))
    | r2_hidden(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f41,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( sQ7_eqProxy(k10_relat_1(X0,X1),X2)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f26,f40])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

%------------------------------------------------------------------------------
