%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0405+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:28 EST 2020

% Result     : Theorem 40.63s
% Output     : Refutation 40.63s
% Verified   : 
% Statistics : Number of formulae       :   51 (  76 expanded)
%              Number of leaves         :   15 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :  199 ( 350 expanded)
%              Number of equality atoms :   38 (  67 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f60836,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1373,f1459,f6609,f60791,f60834])).

fof(f60834,plain,
    ( spl44_1
    | ~ spl44_42
    | ~ spl44_95 ),
    inference(avatar_contradiction_clause,[],[f60833])).

fof(f60833,plain,
    ( $false
    | spl44_1
    | ~ spl44_42
    | ~ spl44_95 ),
    inference(subsumption_resolution,[],[f60807,f6637])).

fof(f6637,plain,
    ( ~ r1_tarski(sK1(k4_setfam_1(sK0,sK0),sK0),sK6(sK0,sK0,sK1(k4_setfam_1(sK0,sK0),sK0)))
    | spl44_1
    | ~ spl44_42 ),
    inference(unit_resulting_resolution,[],[f1372,f6608,f910])).

fof(f910,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(sK1(X0,X1),X3)
      | r1_setfam_1(X0,X1)
      | ~ r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f774])).

fof(f774,plain,(
    ! [X0,X1] :
      ( ( r1_setfam_1(X0,X1)
        | ( ! [X3] :
              ( ~ r1_tarski(sK1(X0,X1),X3)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X4] :
            ( ( r1_tarski(X4,sK2(X1,X4))
              & r2_hidden(sK2(X1,X4),X1) )
            | ~ r2_hidden(X4,X0) )
        | ~ r1_setfam_1(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f771,f773,f772])).

fof(f772,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_tarski(X2,X3)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X0) )
     => ( ! [X3] :
            ( ~ r1_tarski(sK1(X0,X1),X3)
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f773,plain,(
    ! [X4,X1] :
      ( ? [X5] :
          ( r1_tarski(X4,X5)
          & r2_hidden(X5,X1) )
     => ( r1_tarski(X4,sK2(X1,X4))
        & r2_hidden(sK2(X1,X4),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f771,plain,(
    ! [X0,X1] :
      ( ( r1_setfam_1(X0,X1)
        | ? [X2] :
            ( ! [X3] :
                ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) )
      & ( ! [X4] :
            ( ? [X5] :
                ( r1_tarski(X4,X5)
                & r2_hidden(X5,X1) )
            | ~ r2_hidden(X4,X0) )
        | ~ r1_setfam_1(X0,X1) ) ) ),
    inference(rectify,[],[f770])).

fof(f770,plain,(
    ! [X0,X1] :
      ( ( r1_setfam_1(X0,X1)
        | ? [X2] :
            ( ! [X3] :
                ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( ? [X3] :
                ( r1_tarski(X2,X3)
                & r2_hidden(X3,X1) )
            | ~ r2_hidden(X2,X0) )
        | ~ r1_setfam_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f598])).

fof(f598,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ( ? [X3] :
              ( r1_tarski(X2,X3)
              & r2_hidden(X3,X1) )
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f547])).

fof(f547,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

fof(f6608,plain,
    ( r2_hidden(sK6(sK0,sK0,sK1(k4_setfam_1(sK0,sK0),sK0)),sK0)
    | ~ spl44_42 ),
    inference(avatar_component_clause,[],[f6606])).

fof(f6606,plain,
    ( spl44_42
  <=> r2_hidden(sK6(sK0,sK0,sK1(k4_setfam_1(sK0,sK0),sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_42])])).

fof(f1372,plain,
    ( ~ r1_setfam_1(k4_setfam_1(sK0,sK0),sK0)
    | spl44_1 ),
    inference(avatar_component_clause,[],[f1370])).

fof(f1370,plain,
    ( spl44_1
  <=> r1_setfam_1(k4_setfam_1(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_1])])).

fof(f60807,plain,
    ( r1_tarski(sK1(k4_setfam_1(sK0,sK0),sK0),sK6(sK0,sK0,sK1(k4_setfam_1(sK0,sK0),sK0)))
    | ~ spl44_95 ),
    inference(superposition,[],[f1204,f60790])).

fof(f60790,plain,
    ( sK1(k4_setfam_1(sK0,sK0),sK0) = k4_xboole_0(sK6(sK0,sK0,sK1(k4_setfam_1(sK0,sK0),sK0)),sK7(sK0,sK0,sK1(k4_setfam_1(sK0,sK0),sK0)))
    | ~ spl44_95 ),
    inference(avatar_component_clause,[],[f60788])).

fof(f60788,plain,
    ( spl44_95
  <=> sK1(k4_setfam_1(sK0,sK0),sK0) = k4_xboole_0(sK6(sK0,sK0,sK1(k4_setfam_1(sK0,sK0),sK0)),sK7(sK0,sK0,sK1(k4_setfam_1(sK0,sK0),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_95])])).

fof(f1204,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f96])).

fof(f96,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f60791,plain,
    ( spl44_95
    | ~ spl44_7 ),
    inference(avatar_split_clause,[],[f1465,f1456,f60788])).

fof(f1456,plain,
    ( spl44_7
  <=> r2_hidden(sK1(k4_setfam_1(sK0,sK0),sK0),k4_setfam_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_7])])).

fof(f1465,plain,
    ( sK1(k4_setfam_1(sK0,sK0),sK0) = k4_xboole_0(sK6(sK0,sK0,sK1(k4_setfam_1(sK0,sK0),sK0)),sK7(sK0,sK0,sK1(k4_setfam_1(sK0,sK0),sK0)))
    | ~ spl44_7 ),
    inference(unit_resulting_resolution,[],[f1458,f1351])).

fof(f1351,plain,(
    ! [X0,X8,X1] :
      ( ~ r2_hidden(X8,k4_setfam_1(X0,X1))
      | k4_xboole_0(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8 ) ),
    inference(backward_demodulation,[],[f1287,f1115])).

fof(f1115,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f493])).

fof(f493,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f1287,plain,(
    ! [X0,X8,X1] :
      ( k6_subset_1(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,k4_setfam_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f919])).

fof(f919,plain,(
    ! [X2,X0,X8,X1] :
      ( k6_subset_1(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,X2)
      | k4_setfam_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f780])).

fof(f780,plain,(
    ! [X0,X1,X2] :
      ( ( k4_setfam_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k6_subset_1(X4,X5) != sK3(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( sK3(X0,X1,X2) = k6_subset_1(sK4(X0,X1,X2),sK5(X0,X1,X2))
              & r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k6_subset_1(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k6_subset_1(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8
                & r2_hidden(sK7(X0,X1,X8),X1)
                & r2_hidden(sK6(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k4_setfam_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f776,f779,f778,f777])).

fof(f777,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4,X5] :
                ( k6_subset_1(X4,X5) != X3
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X6,X7] :
                ( k6_subset_1(X6,X7) = X3
                & r2_hidden(X7,X1)
                & r2_hidden(X6,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X5,X4] :
              ( k6_subset_1(X4,X5) != sK3(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k6_subset_1(X6,X7) = sK3(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f778,plain,(
    ! [X2,X1,X0] :
      ( ? [X7,X6] :
          ( k6_subset_1(X6,X7) = sK3(X0,X1,X2)
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( sK3(X0,X1,X2) = k6_subset_1(sK4(X0,X1,X2),sK5(X0,X1,X2))
        & r2_hidden(sK5(X0,X1,X2),X1)
        & r2_hidden(sK4(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f779,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k6_subset_1(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k6_subset_1(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8
        & r2_hidden(sK7(X0,X1,X8),X1)
        & r2_hidden(sK6(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f776,plain,(
    ! [X0,X1,X2] :
      ( ( k4_setfam_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k6_subset_1(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X6,X7] :
                  ( k6_subset_1(X6,X7) = X3
                  & r2_hidden(X7,X1)
                  & r2_hidden(X6,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k6_subset_1(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ? [X11,X12] :
                  ( k6_subset_1(X11,X12) = X8
                  & r2_hidden(X12,X1)
                  & r2_hidden(X11,X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k4_setfam_1(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f775])).

fof(f775,plain,(
    ! [X0,X1,X2] :
      ( ( k4_setfam_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k6_subset_1(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4,X5] :
                  ( k6_subset_1(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4,X5] :
                  ( k6_subset_1(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) ) )
            & ( ? [X4,X5] :
                  ( k6_subset_1(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_setfam_1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f551])).

fof(f551,axiom,(
    ! [X0,X1,X2] :
      ( k4_setfam_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k6_subset_1(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_setfam_1)).

fof(f1458,plain,
    ( r2_hidden(sK1(k4_setfam_1(sK0,sK0),sK0),k4_setfam_1(sK0,sK0))
    | ~ spl44_7 ),
    inference(avatar_component_clause,[],[f1456])).

fof(f6609,plain,
    ( spl44_42
    | ~ spl44_7 ),
    inference(avatar_split_clause,[],[f1466,f1456,f6606])).

fof(f1466,plain,
    ( r2_hidden(sK6(sK0,sK0,sK1(k4_setfam_1(sK0,sK0),sK0)),sK0)
    | ~ spl44_7 ),
    inference(unit_resulting_resolution,[],[f1458,f1289])).

fof(f1289,plain,(
    ! [X0,X8,X1] :
      ( ~ r2_hidden(X8,k4_setfam_1(X0,X1))
      | r2_hidden(sK6(X0,X1,X8),X0) ) ),
    inference(equality_resolution,[],[f917])).

fof(f917,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK6(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k4_setfam_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f780])).

fof(f1459,plain,
    ( spl44_7
    | spl44_1 ),
    inference(avatar_split_clause,[],[f1383,f1370,f1456])).

fof(f1383,plain,
    ( r2_hidden(sK1(k4_setfam_1(sK0,sK0),sK0),k4_setfam_1(sK0,sK0))
    | spl44_1 ),
    inference(unit_resulting_resolution,[],[f1372,f909])).

fof(f909,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f774])).

fof(f1373,plain,(
    ~ spl44_1 ),
    inference(avatar_split_clause,[],[f904,f1370])).

fof(f904,plain,(
    ~ r1_setfam_1(k4_setfam_1(sK0,sK0),sK0) ),
    inference(cnf_transformation,[],[f769])).

fof(f769,plain,(
    ~ r1_setfam_1(k4_setfam_1(sK0,sK0),sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f594,f768])).

fof(f768,plain,
    ( ? [X0] : ~ r1_setfam_1(k4_setfam_1(X0,X0),X0)
   => ~ r1_setfam_1(k4_setfam_1(sK0,sK0),sK0) ),
    introduced(choice_axiom,[])).

fof(f594,plain,(
    ? [X0] : ~ r1_setfam_1(k4_setfam_1(X0,X0),X0) ),
    inference(ennf_transformation,[],[f578])).

fof(f578,negated_conjecture,(
    ~ ! [X0] : r1_setfam_1(k4_setfam_1(X0,X0),X0) ),
    inference(negated_conjecture,[],[f577])).

fof(f577,conjecture,(
    ! [X0] : r1_setfam_1(k4_setfam_1(X0,X0),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_setfam_1)).
%------------------------------------------------------------------------------
