%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0558+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:12 EST 2020

% Result     : Theorem 3.21s
% Output     : Refutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 246 expanded)
%              Number of leaves         :   29 ( 110 expanded)
%              Depth                    :   10
%              Number of atoms          :  471 (1138 expanded)
%              Number of equality atoms :   43 ( 148 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6321,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f104,f108,f163,f249,f253,f286,f291,f429,f1430,f5082,f5829,f5843,f6320])).

fof(f6320,plain,
    ( ~ spl13_17
    | ~ spl13_23
    | ~ spl13_24 ),
    inference(avatar_contradiction_clause,[],[f6316])).

fof(f6316,plain,
    ( $false
    | ~ spl13_17
    | ~ spl13_23
    | ~ spl13_24 ),
    inference(resolution,[],[f1319,f1314])).

fof(f1314,plain,
    ( r2_hidden(sK5(sK0,sK1,sK10(k5_relat_1(sK0,sK1),k9_relat_1(sK1,k2_relat_1(sK0))),sK9(k5_relat_1(sK0,sK1),k9_relat_1(sK1,k2_relat_1(sK0)))),k2_relat_1(sK0))
    | ~ spl13_23 ),
    inference(resolution,[],[f285,f59])).

fof(f59,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK9(X0,X1)),X0)
            | ~ r2_hidden(sK9(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK10(X0,X1),sK9(X0,X1)),X0)
            | r2_hidden(sK9(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK11(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11])],[f28,f31,f30,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK9(X0,X1)),X0)
          | ~ r2_hidden(sK9(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK9(X0,X1)),X0)
          | r2_hidden(sK9(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK9(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK10(X0,X1),sK9(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK11(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f285,plain,
    ( r2_hidden(k4_tarski(sK10(k5_relat_1(sK0,sK1),k9_relat_1(sK1,k2_relat_1(sK0))),sK5(sK0,sK1,sK10(k5_relat_1(sK0,sK1),k9_relat_1(sK1,k2_relat_1(sK0))),sK9(k5_relat_1(sK0,sK1),k9_relat_1(sK1,k2_relat_1(sK0))))),sK0)
    | ~ spl13_23 ),
    inference(avatar_component_clause,[],[f283])).

fof(f283,plain,
    ( spl13_23
  <=> r2_hidden(k4_tarski(sK10(k5_relat_1(sK0,sK1),k9_relat_1(sK1,k2_relat_1(sK0))),sK5(sK0,sK1,sK10(k5_relat_1(sK0,sK1),k9_relat_1(sK1,k2_relat_1(sK0))),sK9(k5_relat_1(sK0,sK1),k9_relat_1(sK1,k2_relat_1(sK0))))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_23])])).

fof(f1319,plain,
    ( ~ r2_hidden(sK5(sK0,sK1,sK10(k5_relat_1(sK0,sK1),k9_relat_1(sK1,k2_relat_1(sK0))),sK9(k5_relat_1(sK0,sK1),k9_relat_1(sK1,k2_relat_1(sK0)))),k2_relat_1(sK0))
    | ~ spl13_17
    | ~ spl13_24 ),
    inference(resolution,[],[f290,f252])).

fof(f252,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK9(k5_relat_1(sK0,sK1),k9_relat_1(sK1,k2_relat_1(sK0)))),sK1)
        | ~ r2_hidden(X0,k2_relat_1(sK0)) )
    | ~ spl13_17 ),
    inference(avatar_component_clause,[],[f251])).

fof(f251,plain,
    ( spl13_17
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK0))
        | ~ r2_hidden(k4_tarski(X0,sK9(k5_relat_1(sK0,sK1),k9_relat_1(sK1,k2_relat_1(sK0)))),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_17])])).

fof(f290,plain,
    ( r2_hidden(k4_tarski(sK5(sK0,sK1,sK10(k5_relat_1(sK0,sK1),k9_relat_1(sK1,k2_relat_1(sK0))),sK9(k5_relat_1(sK0,sK1),k9_relat_1(sK1,k2_relat_1(sK0)))),sK9(k5_relat_1(sK0,sK1),k9_relat_1(sK1,k2_relat_1(sK0)))),sK1)
    | ~ spl13_24 ),
    inference(avatar_component_clause,[],[f288])).

fof(f288,plain,
    ( spl13_24
  <=> r2_hidden(k4_tarski(sK5(sK0,sK1,sK10(k5_relat_1(sK0,sK1),k9_relat_1(sK1,k2_relat_1(sK0))),sK9(k5_relat_1(sK0,sK1),k9_relat_1(sK1,k2_relat_1(sK0)))),sK9(k5_relat_1(sK0,sK1),k9_relat_1(sK1,k2_relat_1(sK0)))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_24])])).

fof(f5843,plain,
    ( ~ spl13_1
    | spl13_94 ),
    inference(avatar_split_clause,[],[f1483,f1377,f97])).

fof(f97,plain,
    ( spl13_1
  <=> r2_hidden(sK9(k5_relat_1(sK0,sK1),k9_relat_1(sK1,k2_relat_1(sK0))),k9_relat_1(sK1,k2_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).

fof(f1377,plain,
    ( spl13_94
  <=> r2_hidden(k4_tarski(sK8(sK1,k2_relat_1(sK0),sK9(k5_relat_1(sK0,sK1),k9_relat_1(sK1,k2_relat_1(sK0)))),sK9(k5_relat_1(sK0,sK1),k9_relat_1(sK1,k2_relat_1(sK0)))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_94])])).

fof(f1483,plain,
    ( ~ r2_hidden(sK9(k5_relat_1(sK0,sK1),k9_relat_1(sK1,k2_relat_1(sK0))),k9_relat_1(sK1,k2_relat_1(sK0)))
    | spl13_94 ),
    inference(resolution,[],[f1378,f93])).

fof(f93,plain,(
    ! [X28,X27] :
      ( r2_hidden(k4_tarski(sK8(sK1,X27,X28),X28),sK1)
      | ~ r2_hidden(X28,k9_relat_1(sK1,X27)) ) ),
    inference(resolution,[],[f34,f58])).

fof(f58,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k4_tarski(sK8(X0,X1,X6),X6),X0)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK8(X0,X1,X6),X6),X0)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(X4,sK6(X0,X1,X2)),X0) )
                | ~ r2_hidden(sK6(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK7(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK7(X0,X1,X2),sK6(X0,X1,X2)),X0) )
                | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X7,X6),X0) ) )
                & ( ( r2_hidden(sK8(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(sK8(X0,X1,X6),X6),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f22,f25,f24,f23])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r2_hidden(k4_tarski(X4,X3),X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X5,X3),X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r2_hidden(k4_tarski(X4,sK6(X0,X1,X2)),X0) )
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(X5,sK6(X0,X1,X2)),X0) )
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X5,sK6(X0,X1,X2)),X0) )
     => ( r2_hidden(sK7(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK7(X0,X1,X2),sK6(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X8,X6),X0) )
     => ( r2_hidden(sK8(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(sK8(X0,X1,X6),X6),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( r2_hidden(X5,X1)
                      & r2_hidden(k4_tarski(X5,X3),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X7,X6),X0) ) )
                & ( ? [X8] :
                      ( r2_hidden(X8,X1)
                      & r2_hidden(k4_tarski(X8,X6),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X4,X3),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) ) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_relat_1)).

fof(f34,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( k2_relat_1(k5_relat_1(sK0,sK1)) != k9_relat_1(sK1,k2_relat_1(sK0))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f13,f12])).

fof(f12,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_relat_1(k5_relat_1(X0,X1)) != k9_relat_1(X1,k2_relat_1(X0))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k2_relat_1(k5_relat_1(sK0,X1)) != k9_relat_1(X1,k2_relat_1(sK0))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X1] :
        ( k2_relat_1(k5_relat_1(sK0,X1)) != k9_relat_1(X1,k2_relat_1(sK0))
        & v1_relat_1(X1) )
   => ( k2_relat_1(k5_relat_1(sK0,sK1)) != k9_relat_1(sK1,k2_relat_1(sK0))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) != k9_relat_1(X1,k2_relat_1(X0))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

fof(f1378,plain,
    ( ~ r2_hidden(k4_tarski(sK8(sK1,k2_relat_1(sK0),sK9(k5_relat_1(sK0,sK1),k9_relat_1(sK1,k2_relat_1(sK0)))),sK9(k5_relat_1(sK0,sK1),k9_relat_1(sK1,k2_relat_1(sK0)))),sK1)
    | spl13_94 ),
    inference(avatar_component_clause,[],[f1377])).

fof(f5829,plain,
    ( ~ spl13_95
    | ~ spl13_94
    | ~ spl13_97 ),
    inference(avatar_split_clause,[],[f5827,f1428,f1377,f1382])).

fof(f1382,plain,
    ( spl13_95
  <=> r2_hidden(sK8(sK1,k2_relat_1(sK0),sK9(k5_relat_1(sK0,sK1),k9_relat_1(sK1,k2_relat_1(sK0)))),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_95])])).

fof(f1428,plain,
    ( spl13_97
  <=> ! [X1,X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK9(k5_relat_1(sK0,sK1),k9_relat_1(sK1,k2_relat_1(sK0)))),sK1)
        | ~ r2_hidden(k4_tarski(X1,X0),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_97])])).

fof(f5827,plain,
    ( ~ r2_hidden(sK8(sK1,k2_relat_1(sK0),sK9(k5_relat_1(sK0,sK1),k9_relat_1(sK1,k2_relat_1(sK0)))),k2_relat_1(sK0))
    | ~ spl13_94
    | ~ spl13_97 ),
    inference(resolution,[],[f5243,f60])).

fof(f60,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK11(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK11(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f5243,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,sK8(sK1,k2_relat_1(sK0),sK9(k5_relat_1(sK0,sK1),k9_relat_1(sK1,k2_relat_1(sK0))))),sK0)
    | ~ spl13_94
    | ~ spl13_97 ),
    inference(resolution,[],[f1379,f1429])).

fof(f1429,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,sK9(k5_relat_1(sK0,sK1),k9_relat_1(sK1,k2_relat_1(sK0)))),sK1)
        | ~ r2_hidden(k4_tarski(X1,X0),sK0) )
    | ~ spl13_97 ),
    inference(avatar_component_clause,[],[f1428])).

fof(f1379,plain,
    ( r2_hidden(k4_tarski(sK8(sK1,k2_relat_1(sK0),sK9(k5_relat_1(sK0,sK1),k9_relat_1(sK1,k2_relat_1(sK0)))),sK9(k5_relat_1(sK0,sK1),k9_relat_1(sK1,k2_relat_1(sK0)))),sK1)
    | ~ spl13_94 ),
    inference(avatar_component_clause,[],[f1377])).

fof(f5082,plain,
    ( ~ spl13_13
    | ~ spl13_1
    | spl13_95 ),
    inference(avatar_split_clause,[],[f1479,f1382,f97,f219])).

fof(f219,plain,
    ( spl13_13
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_13])])).

fof(f1479,plain,
    ( ~ r2_hidden(sK9(k5_relat_1(sK0,sK1),k9_relat_1(sK1,k2_relat_1(sK0))),k9_relat_1(sK1,k2_relat_1(sK0)))
    | ~ v1_relat_1(sK1)
    | spl13_95 ),
    inference(resolution,[],[f1383,f57])).

fof(f57,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK8(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK8(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1383,plain,
    ( ~ r2_hidden(sK8(sK1,k2_relat_1(sK0),sK9(k5_relat_1(sK0,sK1),k9_relat_1(sK1,k2_relat_1(sK0)))),k2_relat_1(sK0))
    | spl13_95 ),
    inference(avatar_component_clause,[],[f1382])).

fof(f1430,plain,
    ( ~ spl13_4
    | ~ spl13_13
    | ~ spl13_22
    | spl13_97
    | ~ spl13_3 ),
    inference(avatar_split_clause,[],[f1422,f106,f1428,f279,f219,f135])).

fof(f135,plain,
    ( spl13_4
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_4])])).

fof(f279,plain,
    ( spl13_22
  <=> v1_relat_1(k5_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_22])])).

fof(f106,plain,
    ( spl13_3
  <=> ! [X0] : ~ r2_hidden(k4_tarski(X0,sK9(k5_relat_1(sK0,sK1),k9_relat_1(sK1,k2_relat_1(sK0)))),k5_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_3])])).

fof(f1422,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,sK9(k5_relat_1(sK0,sK1),k9_relat_1(sK1,k2_relat_1(sK0)))),sK1)
        | ~ r2_hidden(k4_tarski(X1,X0),sK0)
        | ~ v1_relat_1(k5_relat_1(sK0,sK1))
        | ~ v1_relat_1(sK1)
        | ~ v1_relat_1(sK0) )
    | ~ spl13_3 ),
    inference(resolution,[],[f107,f53])).

fof(f53,plain,(
    ! [X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),X2)
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ( ( ! [X5] :
                          ( ~ r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X1)
                          | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0) )
                      | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) )
                    & ( ( r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X1)
                        & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK4(X0,X1,X2)),X0) )
                      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ( r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1)
                          & r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f16,f19,f18,f17])).

fof(f17,plain,(
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
              ( ~ r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X1)
              | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0) )
          | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) )
        & ( ? [X6] :
              ( r2_hidden(k4_tarski(X6,sK3(X0,X1,X2)),X1)
              & r2_hidden(k4_tarski(sK2(X0,X1,X2),X6),X0) )
          | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,sK3(X0,X1,X2)),X1)
          & r2_hidden(k4_tarski(sK2(X0,X1,X2),X6),X0) )
     => ( r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X1)
        & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK4(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X1)
          & r2_hidden(k4_tarski(X7,X10),X0) )
     => ( r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
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
    inference(rectify,[],[f15])).

fof(f15,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).

fof(f107,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,sK9(k5_relat_1(sK0,sK1),k9_relat_1(sK1,k2_relat_1(sK0)))),k5_relat_1(sK0,sK1))
    | ~ spl13_3 ),
    inference(avatar_component_clause,[],[f106])).

fof(f429,plain,(
    spl13_22 ),
    inference(avatar_contradiction_clause,[],[f427])).

fof(f427,plain,
    ( $false
    | spl13_22 ),
    inference(resolution,[],[f281,f111])).

fof(f111,plain,(
    v1_relat_1(k5_relat_1(sK0,sK1)) ),
    inference(resolution,[],[f72,f34])).

fof(f72,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k5_relat_1(sK0,X0)) ) ),
    inference(resolution,[],[f33,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f33,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f281,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | spl13_22 ),
    inference(avatar_component_clause,[],[f279])).

fof(f291,plain,
    ( ~ spl13_4
    | ~ spl13_13
    | ~ spl13_22
    | spl13_24
    | ~ spl13_2 ),
    inference(avatar_split_clause,[],[f272,f101,f288,f279,f219,f135])).

fof(f101,plain,
    ( spl13_2
  <=> r2_hidden(k4_tarski(sK10(k5_relat_1(sK0,sK1),k9_relat_1(sK1,k2_relat_1(sK0))),sK9(k5_relat_1(sK0,sK1),k9_relat_1(sK1,k2_relat_1(sK0)))),k5_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).

fof(f272,plain,
    ( r2_hidden(k4_tarski(sK5(sK0,sK1,sK10(k5_relat_1(sK0,sK1),k9_relat_1(sK1,k2_relat_1(sK0))),sK9(k5_relat_1(sK0,sK1),k9_relat_1(sK1,k2_relat_1(sK0)))),sK9(k5_relat_1(sK0,sK1),k9_relat_1(sK1,k2_relat_1(sK0)))),sK1)
    | ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl13_2 ),
    inference(resolution,[],[f103,f54])).

fof(f54,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f103,plain,
    ( r2_hidden(k4_tarski(sK10(k5_relat_1(sK0,sK1),k9_relat_1(sK1,k2_relat_1(sK0))),sK9(k5_relat_1(sK0,sK1),k9_relat_1(sK1,k2_relat_1(sK0)))),k5_relat_1(sK0,sK1))
    | ~ spl13_2 ),
    inference(avatar_component_clause,[],[f101])).

fof(f286,plain,
    ( ~ spl13_4
    | ~ spl13_13
    | ~ spl13_22
    | spl13_23
    | ~ spl13_2 ),
    inference(avatar_split_clause,[],[f271,f101,f283,f279,f219,f135])).

fof(f271,plain,
    ( r2_hidden(k4_tarski(sK10(k5_relat_1(sK0,sK1),k9_relat_1(sK1,k2_relat_1(sK0))),sK5(sK0,sK1,sK10(k5_relat_1(sK0,sK1),k9_relat_1(sK1,k2_relat_1(sK0))),sK9(k5_relat_1(sK0,sK1),k9_relat_1(sK1,k2_relat_1(sK0))))),sK0)
    | ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl13_2 ),
    inference(resolution,[],[f103,f55])).

fof(f55,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f253,plain,
    ( ~ spl13_13
    | spl13_17
    | spl13_1 ),
    inference(avatar_split_clause,[],[f247,f97,f251,f219])).

fof(f247,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK0))
        | ~ r2_hidden(k4_tarski(X0,sK9(k5_relat_1(sK0,sK1),k9_relat_1(sK1,k2_relat_1(sK0)))),sK1)
        | ~ v1_relat_1(sK1) )
    | spl13_1 ),
    inference(resolution,[],[f98,f56])).

fof(f56,plain,(
    ! [X6,X0,X7,X1] :
      ( r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X7,X6),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X7,X6),X0)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f98,plain,
    ( ~ r2_hidden(sK9(k5_relat_1(sK0,sK1),k9_relat_1(sK1,k2_relat_1(sK0))),k9_relat_1(sK1,k2_relat_1(sK0)))
    | spl13_1 ),
    inference(avatar_component_clause,[],[f97])).

fof(f249,plain,(
    spl13_13 ),
    inference(avatar_contradiction_clause,[],[f248])).

fof(f248,plain,
    ( $false
    | spl13_13 ),
    inference(resolution,[],[f221,f34])).

fof(f221,plain,
    ( ~ v1_relat_1(sK1)
    | spl13_13 ),
    inference(avatar_component_clause,[],[f219])).

fof(f163,plain,(
    spl13_4 ),
    inference(avatar_contradiction_clause,[],[f162])).

fof(f162,plain,
    ( $false
    | spl13_4 ),
    inference(resolution,[],[f137,f33])).

fof(f137,plain,
    ( ~ v1_relat_1(sK0)
    | spl13_4 ),
    inference(avatar_component_clause,[],[f135])).

fof(f108,plain,
    ( ~ spl13_1
    | spl13_3 ),
    inference(avatar_split_clause,[],[f95,f106,f97])).

fof(f95,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(X0,sK9(k5_relat_1(sK0,sK1),k9_relat_1(sK1,k2_relat_1(sK0)))),k5_relat_1(sK0,sK1))
      | ~ r2_hidden(sK9(k5_relat_1(sK0,sK1),k9_relat_1(sK1,k2_relat_1(sK0))),k9_relat_1(sK1,k2_relat_1(sK0))) ) ),
    inference(resolution,[],[f62,f69])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( sQ12_eqProxy(k2_relat_1(X0),X1)
      | ~ r2_hidden(k4_tarski(X3,sK9(X0,X1)),X0)
      | ~ r2_hidden(sK9(X0,X1),X1) ) ),
    inference(equality_proxy_replacement,[],[f52,f61])).

fof(f61,plain,(
    ! [X1,X0] :
      ( sQ12_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ12_eqProxy])])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( k2_relat_1(X0) = X1
      | ~ r2_hidden(k4_tarski(X3,sK9(X0,X1)),X0)
      | ~ r2_hidden(sK9(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f62,plain,(
    ~ sQ12_eqProxy(k2_relat_1(k5_relat_1(sK0,sK1)),k9_relat_1(sK1,k2_relat_1(sK0))) ),
    inference(equality_proxy_replacement,[],[f35,f61])).

fof(f35,plain,(
    k2_relat_1(k5_relat_1(sK0,sK1)) != k9_relat_1(sK1,k2_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f104,plain,
    ( spl13_1
    | spl13_2 ),
    inference(avatar_split_clause,[],[f94,f101,f97])).

fof(f94,plain,
    ( r2_hidden(k4_tarski(sK10(k5_relat_1(sK0,sK1),k9_relat_1(sK1,k2_relat_1(sK0))),sK9(k5_relat_1(sK0,sK1),k9_relat_1(sK1,k2_relat_1(sK0)))),k5_relat_1(sK0,sK1))
    | r2_hidden(sK9(k5_relat_1(sK0,sK1),k9_relat_1(sK1,k2_relat_1(sK0))),k9_relat_1(sK1,k2_relat_1(sK0))) ),
    inference(resolution,[],[f62,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( sQ12_eqProxy(k2_relat_1(X0),X1)
      | r2_hidden(k4_tarski(sK10(X0,X1),sK9(X0,X1)),X0)
      | r2_hidden(sK9(X0,X1),X1) ) ),
    inference(equality_proxy_replacement,[],[f51,f61])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK10(X0,X1),sK9(X0,X1)),X0)
      | r2_hidden(sK9(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f32])).

%------------------------------------------------------------------------------
