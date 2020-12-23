%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:24 EST 2020

% Result     : Theorem 2.59s
% Output     : Refutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 333 expanded)
%              Number of leaves         :   29 ( 142 expanded)
%              Depth                    :   15
%              Number of atoms          :  532 (1889 expanded)
%              Number of equality atoms :   11 (  54 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7889,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f54,f58,f62,f66,f70,f74,f88,f92,f448,f479,f694,f2486,f2860,f3254,f7781,f7803,f7840])).

fof(f7840,plain,
    ( ~ spl10_88
    | ~ spl10_528
    | spl10_1
    | ~ spl10_9
    | ~ spl10_1373 ),
    inference(avatar_split_clause,[],[f7824,f7801,f86,f48,f3207,f687])).

fof(f687,plain,
    ( spl10_88
  <=> v1_relat_1(k5_relat_1(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_88])])).

fof(f3207,plain,
    ( spl10_528
  <=> r1_tarski(k5_relat_1(sK0,sK3),k5_relat_1(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_528])])).

fof(f48,plain,
    ( spl10_1
  <=> r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f86,plain,
    ( spl10_9
  <=> ! [X0] :
        ( ~ r1_tarski(X0,k5_relat_1(sK1,sK3))
        | ~ r2_hidden(k4_tarski(sK8(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)),sK9(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3))),X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f7801,plain,
    ( spl10_1373
  <=> ! [X13] :
        ( r2_hidden(k4_tarski(sK8(k5_relat_1(sK0,sK2),X13),sK9(k5_relat_1(sK0,sK2),X13)),k5_relat_1(sK0,sK3))
        | r1_tarski(k5_relat_1(sK0,sK2),X13) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1373])])).

fof(f7824,plain,
    ( r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3))
    | ~ r1_tarski(k5_relat_1(sK0,sK3),k5_relat_1(sK1,sK3))
    | ~ v1_relat_1(k5_relat_1(sK0,sK3))
    | ~ spl10_9
    | ~ spl10_1373 ),
    inference(resolution,[],[f7802,f87])).

fof(f87,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK8(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)),sK9(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3))),X0)
        | ~ r1_tarski(X0,k5_relat_1(sK1,sK3))
        | ~ v1_relat_1(X0) )
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f86])).

fof(f7802,plain,
    ( ! [X13] :
        ( r2_hidden(k4_tarski(sK8(k5_relat_1(sK0,sK2),X13),sK9(k5_relat_1(sK0,sK2),X13)),k5_relat_1(sK0,sK3))
        | r1_tarski(k5_relat_1(sK0,sK2),X13) )
    | ~ spl10_1373 ),
    inference(avatar_component_clause,[],[f7801])).

fof(f7803,plain,
    ( ~ spl10_8
    | spl10_1373
    | ~ spl10_1370 ),
    inference(avatar_split_clause,[],[f7790,f7779,f7801,f83])).

fof(f83,plain,
    ( spl10_8
  <=> v1_relat_1(k5_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f7779,plain,
    ( spl10_1370
  <=> ! [X1,X0] :
        ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(sK0,sK2))
        | r2_hidden(k4_tarski(X0,X1),k5_relat_1(sK0,sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1370])])).

fof(f7790,plain,
    ( ! [X13] :
        ( r2_hidden(k4_tarski(sK8(k5_relat_1(sK0,sK2),X13),sK9(k5_relat_1(sK0,sK2),X13)),k5_relat_1(sK0,sK3))
        | r1_tarski(k5_relat_1(sK0,sK2),X13)
        | ~ v1_relat_1(k5_relat_1(sK0,sK2)) )
    | ~ spl10_1370 ),
    inference(resolution,[],[f7780,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X0)
      | r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1)
              & r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f24,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X1)
          & r2_hidden(k4_tarski(X2,X3),X0) )
     => ( ~ r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1)
        & r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
                | ~ r2_hidden(k4_tarski(X2,X3),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

fof(f7780,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(sK0,sK2))
        | r2_hidden(k4_tarski(X0,X1),k5_relat_1(sK0,sK3)) )
    | ~ spl10_1370 ),
    inference(avatar_component_clause,[],[f7779])).

fof(f7781,plain,
    ( ~ spl10_5
    | spl10_1370
    | ~ spl10_7
    | ~ spl10_49 ),
    inference(avatar_split_clause,[],[f7777,f477,f72,f7779,f64])).

fof(f64,plain,
    ( spl10_5
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f72,plain,
    ( spl10_7
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f477,plain,
    ( spl10_49
  <=> ! [X16,X13,X15,X14] :
        ( r2_hidden(k4_tarski(X13,X14),k5_relat_1(sK0,sK3))
        | ~ v1_relat_1(X15)
        | ~ r2_hidden(k4_tarski(X16,X14),k5_relat_1(X15,sK2))
        | ~ r2_hidden(k4_tarski(X13,sK7(X15,sK2,X16,X14)),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_49])])).

fof(f7777,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(sK0)
        | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(sK0,sK2))
        | r2_hidden(k4_tarski(X0,X1),k5_relat_1(sK0,sK3))
        | ~ v1_relat_1(sK2) )
    | ~ spl10_49 ),
    inference(duplicate_literal_removal,[],[f7774])).

fof(f7774,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(sK0)
        | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(sK0,sK2))
        | r2_hidden(k4_tarski(X0,X1),k5_relat_1(sK0,sK3))
        | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(sK0,sK2))
        | ~ v1_relat_1(sK2)
        | ~ v1_relat_1(sK0) )
    | ~ spl10_49 ),
    inference(resolution,[],[f478,f75])).

fof(f75,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK7(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f46,f43])).

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f46,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK7(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK7(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ( ( ! [X5] :
                          ( ~ r2_hidden(k4_tarski(X5,sK5(X0,X1,X2)),X1)
                          | ~ r2_hidden(k4_tarski(sK4(X0,X1,X2),X5),X0) )
                      | ~ r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2) )
                    & ( ( r2_hidden(k4_tarski(sK6(X0,X1,X2),sK5(X0,X1,X2)),X1)
                        & r2_hidden(k4_tarski(sK4(X0,X1,X2),sK6(X0,X1,X2)),X0) )
                      | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ( r2_hidden(k4_tarski(sK7(X0,X1,X7,X8),X8),X1)
                          & r2_hidden(k4_tarski(X7,sK7(X0,X1,X7,X8)),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f18,f21,f20,f19])).

fof(f19,plain,(
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
              ( ~ r2_hidden(k4_tarski(X5,sK5(X0,X1,X2)),X1)
              | ~ r2_hidden(k4_tarski(sK4(X0,X1,X2),X5),X0) )
          | ~ r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2) )
        & ( ? [X6] :
              ( r2_hidden(k4_tarski(X6,sK5(X0,X1,X2)),X1)
              & r2_hidden(k4_tarski(sK4(X0,X1,X2),X6),X0) )
          | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,sK5(X0,X1,X2)),X1)
          & r2_hidden(k4_tarski(sK4(X0,X1,X2),X6),X0) )
     => ( r2_hidden(k4_tarski(sK6(X0,X1,X2),sK5(X0,X1,X2)),X1)
        & r2_hidden(k4_tarski(sK4(X0,X1,X2),sK6(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X1)
          & r2_hidden(k4_tarski(X7,X10),X0) )
     => ( r2_hidden(k4_tarski(sK7(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK7(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
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
    inference(rectify,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f478,plain,
    ( ! [X14,X15,X13,X16] :
        ( ~ r2_hidden(k4_tarski(X13,sK7(X15,sK2,X16,X14)),sK0)
        | ~ v1_relat_1(X15)
        | ~ r2_hidden(k4_tarski(X16,X14),k5_relat_1(X15,sK2))
        | r2_hidden(k4_tarski(X13,X14),k5_relat_1(sK0,sK3)) )
    | ~ spl10_49 ),
    inference(avatar_component_clause,[],[f477])).

fof(f3254,plain,
    ( ~ spl10_88
    | spl10_528
    | ~ spl10_473 ),
    inference(avatar_split_clause,[],[f3202,f2858,f3207,f687])).

fof(f2858,plain,
    ( spl10_473
  <=> ! [X15] :
        ( r2_hidden(k4_tarski(sK8(k5_relat_1(sK0,sK3),X15),sK9(k5_relat_1(sK0,sK3),X15)),k5_relat_1(sK1,sK3))
        | r1_tarski(k5_relat_1(sK0,sK3),X15) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_473])])).

fof(f3202,plain,
    ( r1_tarski(k5_relat_1(sK0,sK3),k5_relat_1(sK1,sK3))
    | ~ v1_relat_1(k5_relat_1(sK0,sK3))
    | ~ spl10_473 ),
    inference(duplicate_literal_removal,[],[f3200])).

fof(f3200,plain,
    ( r1_tarski(k5_relat_1(sK0,sK3),k5_relat_1(sK1,sK3))
    | r1_tarski(k5_relat_1(sK0,sK3),k5_relat_1(sK1,sK3))
    | ~ v1_relat_1(k5_relat_1(sK0,sK3))
    | ~ spl10_473 ),
    inference(resolution,[],[f2859,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1)
      | r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2859,plain,
    ( ! [X15] :
        ( r2_hidden(k4_tarski(sK8(k5_relat_1(sK0,sK3),X15),sK9(k5_relat_1(sK0,sK3),X15)),k5_relat_1(sK1,sK3))
        | r1_tarski(k5_relat_1(sK0,sK3),X15) )
    | ~ spl10_473 ),
    inference(avatar_component_clause,[],[f2858])).

fof(f2860,plain,
    ( ~ spl10_88
    | spl10_473
    | ~ spl10_4
    | ~ spl10_405 ),
    inference(avatar_split_clause,[],[f2835,f2484,f60,f2858,f687])).

fof(f60,plain,
    ( spl10_4
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f2484,plain,
    ( spl10_405
  <=> ! [X3,X5,X4] :
        ( ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(sK0,X5))
        | ~ v1_relat_1(X5)
        | r2_hidden(k4_tarski(X3,X4),k5_relat_1(sK1,X5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_405])])).

fof(f2835,plain,
    ( ! [X15] :
        ( r2_hidden(k4_tarski(sK8(k5_relat_1(sK0,sK3),X15),sK9(k5_relat_1(sK0,sK3),X15)),k5_relat_1(sK1,sK3))
        | r1_tarski(k5_relat_1(sK0,sK3),X15)
        | ~ v1_relat_1(k5_relat_1(sK0,sK3)) )
    | ~ spl10_4
    | ~ spl10_405 ),
    inference(resolution,[],[f2686,f41])).

fof(f2686,plain,
    ( ! [X10,X11] :
        ( ~ r2_hidden(k4_tarski(X10,X11),k5_relat_1(sK0,sK3))
        | r2_hidden(k4_tarski(X10,X11),k5_relat_1(sK1,sK3)) )
    | ~ spl10_4
    | ~ spl10_405 ),
    inference(resolution,[],[f2485,f61])).

fof(f61,plain,
    ( v1_relat_1(sK3)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f60])).

fof(f2485,plain,
    ( ! [X4,X5,X3] :
        ( ~ v1_relat_1(X5)
        | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(sK0,X5))
        | r2_hidden(k4_tarski(X3,X4),k5_relat_1(sK1,X5)) )
    | ~ spl10_405 ),
    inference(avatar_component_clause,[],[f2484])).

fof(f2486,plain,
    ( ~ spl10_7
    | spl10_405
    | ~ spl10_6
    | ~ spl10_3 ),
    inference(avatar_split_clause,[],[f2474,f56,f68,f2484,f72])).

fof(f68,plain,
    ( spl10_6
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f56,plain,
    ( spl10_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f2474,plain,
    ( ! [X4,X5,X3] :
        ( ~ v1_relat_1(sK1)
        | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(sK0,X5))
        | ~ v1_relat_1(sK0)
        | r2_hidden(k4_tarski(X3,X4),k5_relat_1(sK1,X5))
        | ~ v1_relat_1(X5) )
    | ~ spl10_3 ),
    inference(resolution,[],[f1279,f57])).

fof(f57,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f56])).

fof(f1279,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r1_tarski(X4,X1)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(k4_tarski(X2,X3),k5_relat_1(X4,X0))
      | ~ v1_relat_1(X4)
      | r2_hidden(k4_tarski(X2,X3),k5_relat_1(X1,X0))
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f1273])).

fof(f1273,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(k4_tarski(X2,X3),k5_relat_1(X4,X0))
      | ~ v1_relat_1(X4)
      | r2_hidden(k4_tarski(X2,X3),k5_relat_1(X1,X0))
      | ~ r1_tarski(X4,X1)
      | ~ v1_relat_1(X4)
      | ~ r2_hidden(k4_tarski(X2,X3),k5_relat_1(X4,X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X4) ) ),
    inference(resolution,[],[f671,f75])).

fof(f671,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,sK7(X5,X3,X4,X1)),X6)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X4,X1),k5_relat_1(X5,X3))
      | ~ v1_relat_1(X5)
      | r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
      | ~ r1_tarski(X6,X2)
      | ~ v1_relat_1(X6) ) ),
    inference(resolution,[],[f202,f40])).

fof(f40,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r2_hidden(k4_tarski(X4,X5),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f202,plain,(
    ! [X21,X19,X17,X20,X18,X16] :
      ( ~ r2_hidden(k4_tarski(X16,sK7(X20,X19,X21,X17)),X18)
      | r2_hidden(k4_tarski(X16,X17),k5_relat_1(X18,X19))
      | ~ v1_relat_1(X19)
      | ~ v1_relat_1(X18)
      | ~ r2_hidden(k4_tarski(X21,X17),k5_relat_1(X20,X19))
      | ~ v1_relat_1(X20) ) ),
    inference(duplicate_literal_removal,[],[f201])).

fof(f201,plain,(
    ! [X21,X19,X17,X20,X18,X16] :
      ( r2_hidden(k4_tarski(X16,X17),k5_relat_1(X18,X19))
      | ~ r2_hidden(k4_tarski(X16,sK7(X20,X19,X21,X17)),X18)
      | ~ v1_relat_1(X19)
      | ~ v1_relat_1(X18)
      | ~ r2_hidden(k4_tarski(X21,X17),k5_relat_1(X20,X19))
      | ~ v1_relat_1(X19)
      | ~ v1_relat_1(X20) ) ),
    inference(resolution,[],[f77,f76])).

fof(f76,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK7(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f45,f43])).

fof(f45,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK7(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK7(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f77,plain,(
    ! [X0,X8,X7,X1,X9] :
      ( ~ r2_hidden(k4_tarski(X9,X8),X1)
      | r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f44,f43])).

fof(f44,plain,(
    ! [X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),X2)
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f694,plain,
    ( ~ spl10_7
    | ~ spl10_4
    | spl10_88 ),
    inference(avatar_split_clause,[],[f693,f687,f60,f72])).

fof(f693,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK0)
    | spl10_88 ),
    inference(resolution,[],[f688,f43])).

fof(f688,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,sK3))
    | spl10_88 ),
    inference(avatar_component_clause,[],[f687])).

fof(f479,plain,
    ( ~ spl10_5
    | spl10_49
    | ~ spl10_7
    | ~ spl10_44 ),
    inference(avatar_split_clause,[],[f462,f446,f72,f477,f64])).

fof(f446,plain,
    ( spl10_44
  <=> ! [X1,X3,X0,X2] :
        ( ~ r2_hidden(k4_tarski(X0,X1),X2)
        | r2_hidden(k4_tarski(X0,X3),k5_relat_1(X2,sK3))
        | ~ r2_hidden(k4_tarski(X1,X3),sK2)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_44])])).

fof(f462,plain,
    ( ! [X14,X15,X13,X16] :
        ( r2_hidden(k4_tarski(X13,X14),k5_relat_1(sK0,sK3))
        | ~ r2_hidden(k4_tarski(X13,sK7(X15,sK2,X16,X14)),sK0)
        | ~ r2_hidden(k4_tarski(X16,X14),k5_relat_1(X15,sK2))
        | ~ v1_relat_1(sK2)
        | ~ v1_relat_1(X15) )
    | ~ spl10_7
    | ~ spl10_44 ),
    inference(resolution,[],[f454,f76])).

fof(f454,plain,
    ( ! [X6,X7,X5] :
        ( ~ r2_hidden(k4_tarski(X7,X6),sK2)
        | r2_hidden(k4_tarski(X5,X6),k5_relat_1(sK0,sK3))
        | ~ r2_hidden(k4_tarski(X5,X7),sK0) )
    | ~ spl10_7
    | ~ spl10_44 ),
    inference(resolution,[],[f447,f73])).

fof(f73,plain,
    ( v1_relat_1(sK0)
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f72])).

fof(f447,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v1_relat_1(X2)
        | r2_hidden(k4_tarski(X0,X3),k5_relat_1(X2,sK3))
        | ~ r2_hidden(k4_tarski(X1,X3),sK2)
        | ~ r2_hidden(k4_tarski(X0,X1),X2) )
    | ~ spl10_44 ),
    inference(avatar_component_clause,[],[f446])).

fof(f448,plain,
    ( ~ spl10_5
    | ~ spl10_4
    | spl10_44
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f439,f52,f446,f60,f64])).

fof(f52,plain,
    ( spl10_2
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f439,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),X2)
        | ~ v1_relat_1(sK3)
        | ~ v1_relat_1(X2)
        | ~ r2_hidden(k4_tarski(X1,X3),sK2)
        | r2_hidden(k4_tarski(X0,X3),k5_relat_1(X2,sK3))
        | ~ v1_relat_1(sK2) )
    | ~ spl10_2 ),
    inference(resolution,[],[f199,f53])).

fof(f53,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f199,plain,(
    ! [X6,X4,X8,X7,X5,X9] :
      ( ~ r1_tarski(X9,X7)
      | ~ r2_hidden(k4_tarski(X4,X8),X6)
      | ~ v1_relat_1(X7)
      | ~ v1_relat_1(X6)
      | ~ r2_hidden(k4_tarski(X8,X5),X9)
      | r2_hidden(k4_tarski(X4,X5),k5_relat_1(X6,X7))
      | ~ v1_relat_1(X9) ) ),
    inference(resolution,[],[f77,f40])).

fof(f92,plain,
    ( ~ spl10_7
    | ~ spl10_5
    | spl10_8 ),
    inference(avatar_split_clause,[],[f89,f83,f64,f72])).

fof(f89,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK0)
    | spl10_8 ),
    inference(resolution,[],[f84,f43])).

fof(f84,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,sK2))
    | spl10_8 ),
    inference(avatar_component_clause,[],[f83])).

fof(f88,plain,
    ( ~ spl10_8
    | spl10_9
    | spl10_1 ),
    inference(avatar_split_clause,[],[f81,f48,f86,f83])).

fof(f81,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k5_relat_1(sK1,sK3))
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(k4_tarski(sK8(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)),sK9(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3))),X0)
        | ~ v1_relat_1(k5_relat_1(sK0,sK2)) )
    | spl10_1 ),
    inference(resolution,[],[f80,f49])).

fof(f49,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3))
    | spl10_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X1)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f40,f42])).

fof(f74,plain,(
    spl10_7 ),
    inference(avatar_split_clause,[],[f27,f72])).

fof(f27,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3))
    & r1_tarski(sK2,sK3)
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK3)
    & v1_relat_1(sK2)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f15,f14,f13,f12])).

fof(f12,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
                    & r1_tarski(X2,X3)
                    & r1_tarski(X0,X1)
                    & v1_relat_1(X3) )
                & v1_relat_1(X2) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k5_relat_1(sK0,X2),k5_relat_1(X1,X3))
                  & r1_tarski(X2,X3)
                  & r1_tarski(sK0,X1)
                  & v1_relat_1(X3) )
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_tarski(k5_relat_1(sK0,X2),k5_relat_1(X1,X3))
                & r1_tarski(X2,X3)
                & r1_tarski(sK0,X1)
                & v1_relat_1(X3) )
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k5_relat_1(sK0,X2),k5_relat_1(sK1,X3))
              & r1_tarski(X2,X3)
              & r1_tarski(sK0,sK1)
              & v1_relat_1(X3) )
          & v1_relat_1(X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r1_tarski(k5_relat_1(sK0,X2),k5_relat_1(sK1,X3))
            & r1_tarski(X2,X3)
            & r1_tarski(sK0,sK1)
            & v1_relat_1(X3) )
        & v1_relat_1(X2) )
   => ( ? [X3] :
          ( ~ r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,X3))
          & r1_tarski(sK2,X3)
          & r1_tarski(sK0,sK1)
          & v1_relat_1(X3) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X3] :
        ( ~ r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,X3))
        & r1_tarski(sK2,X3)
        & r1_tarski(sK0,sK1)
        & v1_relat_1(X3) )
   => ( ~ r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3))
      & r1_tarski(sK2,sK3)
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
                  & r1_tarski(X2,X3)
                  & r1_tarski(X0,X1)
                  & v1_relat_1(X3) )
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
                  & r1_tarski(X2,X3)
                  & r1_tarski(X0,X1)
                  & v1_relat_1(X3) )
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( v1_relat_1(X2)
               => ! [X3] :
                    ( v1_relat_1(X3)
                   => ( ( r1_tarski(X2,X3)
                        & r1_tarski(X0,X1) )
                     => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ! [X3] :
                  ( v1_relat_1(X3)
                 => ( ( r1_tarski(X2,X3)
                      & r1_tarski(X0,X1) )
                   => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relat_1)).

fof(f70,plain,(
    spl10_6 ),
    inference(avatar_split_clause,[],[f28,f68])).

fof(f28,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f66,plain,(
    spl10_5 ),
    inference(avatar_split_clause,[],[f29,f64])).

fof(f29,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f62,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f30,f60])).

fof(f30,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f58,plain,(
    spl10_3 ),
    inference(avatar_split_clause,[],[f31,f56])).

fof(f31,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f54,plain,(
    spl10_2 ),
    inference(avatar_split_clause,[],[f32,f52])).

fof(f32,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f50,plain,(
    ~ spl10_1 ),
    inference(avatar_split_clause,[],[f33,f48])).

fof(f33,plain,(
    ~ r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:16:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (10443)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.47  % (10442)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.47  % (10436)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.47  % (10442)Refutation not found, incomplete strategy% (10442)------------------------------
% 0.20/0.47  % (10442)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (10435)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.47  % (10442)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (10442)Memory used [KB]: 1663
% 0.20/0.47  % (10442)Time elapsed: 0.051 s
% 0.20/0.47  % (10442)------------------------------
% 0.20/0.47  % (10442)------------------------------
% 0.20/0.48  % (10431)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.48  % (10429)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.48  % (10450)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.49  % (10450)Refutation not found, incomplete strategy% (10450)------------------------------
% 0.20/0.49  % (10450)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (10450)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (10450)Memory used [KB]: 10490
% 0.20/0.49  % (10450)Time elapsed: 0.062 s
% 0.20/0.49  % (10450)------------------------------
% 0.20/0.49  % (10450)------------------------------
% 0.20/0.49  % (10434)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.49  % (10432)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.49  % (10441)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (10446)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.50  % (10447)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.50  % (10445)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.50  % (10430)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (10439)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.50  % (10430)Refutation not found, incomplete strategy% (10430)------------------------------
% 0.20/0.50  % (10430)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (10430)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (10430)Memory used [KB]: 10618
% 0.20/0.50  % (10430)Time elapsed: 0.085 s
% 0.20/0.50  % (10430)------------------------------
% 0.20/0.50  % (10430)------------------------------
% 0.20/0.50  % (10449)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.50  % (10433)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.50  % (10437)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.51  % (10438)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.51  % (10448)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.51  % (10440)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 2.59/0.73  % (10435)Refutation found. Thanks to Tanya!
% 2.59/0.73  % SZS status Theorem for theBenchmark
% 2.59/0.73  % SZS output start Proof for theBenchmark
% 2.59/0.73  fof(f7889,plain,(
% 2.59/0.73    $false),
% 2.59/0.73    inference(avatar_sat_refutation,[],[f50,f54,f58,f62,f66,f70,f74,f88,f92,f448,f479,f694,f2486,f2860,f3254,f7781,f7803,f7840])).
% 2.59/0.73  fof(f7840,plain,(
% 2.59/0.73    ~spl10_88 | ~spl10_528 | spl10_1 | ~spl10_9 | ~spl10_1373),
% 2.59/0.73    inference(avatar_split_clause,[],[f7824,f7801,f86,f48,f3207,f687])).
% 2.59/0.73  fof(f687,plain,(
% 2.59/0.73    spl10_88 <=> v1_relat_1(k5_relat_1(sK0,sK3))),
% 2.59/0.73    introduced(avatar_definition,[new_symbols(naming,[spl10_88])])).
% 2.59/0.73  fof(f3207,plain,(
% 2.59/0.73    spl10_528 <=> r1_tarski(k5_relat_1(sK0,sK3),k5_relat_1(sK1,sK3))),
% 2.59/0.73    introduced(avatar_definition,[new_symbols(naming,[spl10_528])])).
% 2.59/0.73  fof(f48,plain,(
% 2.59/0.73    spl10_1 <=> r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3))),
% 2.59/0.73    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 2.59/0.73  fof(f86,plain,(
% 2.59/0.73    spl10_9 <=> ! [X0] : (~r1_tarski(X0,k5_relat_1(sK1,sK3)) | ~r2_hidden(k4_tarski(sK8(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)),sK9(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3))),X0) | ~v1_relat_1(X0))),
% 2.59/0.73    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 2.59/0.73  fof(f7801,plain,(
% 2.59/0.73    spl10_1373 <=> ! [X13] : (r2_hidden(k4_tarski(sK8(k5_relat_1(sK0,sK2),X13),sK9(k5_relat_1(sK0,sK2),X13)),k5_relat_1(sK0,sK3)) | r1_tarski(k5_relat_1(sK0,sK2),X13))),
% 2.59/0.73    introduced(avatar_definition,[new_symbols(naming,[spl10_1373])])).
% 2.59/0.73  fof(f7824,plain,(
% 2.59/0.73    r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)) | ~r1_tarski(k5_relat_1(sK0,sK3),k5_relat_1(sK1,sK3)) | ~v1_relat_1(k5_relat_1(sK0,sK3)) | (~spl10_9 | ~spl10_1373)),
% 2.59/0.73    inference(resolution,[],[f7802,f87])).
% 2.59/0.73  fof(f87,plain,(
% 2.59/0.73    ( ! [X0] : (~r2_hidden(k4_tarski(sK8(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)),sK9(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3))),X0) | ~r1_tarski(X0,k5_relat_1(sK1,sK3)) | ~v1_relat_1(X0)) ) | ~spl10_9),
% 2.59/0.73    inference(avatar_component_clause,[],[f86])).
% 2.59/0.73  fof(f7802,plain,(
% 2.59/0.73    ( ! [X13] : (r2_hidden(k4_tarski(sK8(k5_relat_1(sK0,sK2),X13),sK9(k5_relat_1(sK0,sK2),X13)),k5_relat_1(sK0,sK3)) | r1_tarski(k5_relat_1(sK0,sK2),X13)) ) | ~spl10_1373),
% 2.59/0.73    inference(avatar_component_clause,[],[f7801])).
% 2.59/0.73  fof(f7803,plain,(
% 2.59/0.73    ~spl10_8 | spl10_1373 | ~spl10_1370),
% 2.59/0.73    inference(avatar_split_clause,[],[f7790,f7779,f7801,f83])).
% 2.59/0.73  fof(f83,plain,(
% 2.59/0.73    spl10_8 <=> v1_relat_1(k5_relat_1(sK0,sK2))),
% 2.59/0.73    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 2.59/0.73  fof(f7779,plain,(
% 2.59/0.73    spl10_1370 <=> ! [X1,X0] : (~r2_hidden(k4_tarski(X0,X1),k5_relat_1(sK0,sK2)) | r2_hidden(k4_tarski(X0,X1),k5_relat_1(sK0,sK3)))),
% 2.59/0.73    introduced(avatar_definition,[new_symbols(naming,[spl10_1370])])).
% 2.59/0.73  fof(f7790,plain,(
% 2.59/0.73    ( ! [X13] : (r2_hidden(k4_tarski(sK8(k5_relat_1(sK0,sK2),X13),sK9(k5_relat_1(sK0,sK2),X13)),k5_relat_1(sK0,sK3)) | r1_tarski(k5_relat_1(sK0,sK2),X13) | ~v1_relat_1(k5_relat_1(sK0,sK2))) ) | ~spl10_1370),
% 2.59/0.73    inference(resolution,[],[f7780,f41])).
% 2.59/0.73  fof(f41,plain,(
% 2.59/0.73    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X0) | r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 2.59/0.73    inference(cnf_transformation,[],[f26])).
% 2.59/0.73  fof(f26,plain,(
% 2.59/0.73    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | (~r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1) & r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 2.59/0.73    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f24,f25])).
% 2.59/0.73  fof(f25,plain,(
% 2.59/0.73    ! [X1,X0] : (? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0)) => (~r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1) & r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X0)))),
% 2.59/0.73    introduced(choice_axiom,[])).
% 2.59/0.73  fof(f24,plain,(
% 2.59/0.73    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 2.59/0.73    inference(rectify,[],[f23])).
% 2.59/0.73  fof(f23,plain,(
% 2.59/0.73    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 2.59/0.73    inference(nnf_transformation,[],[f9])).
% 2.59/0.73  fof(f9,plain,(
% 2.59/0.73    ! [X0] : (! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0))) | ~v1_relat_1(X0))),
% 2.59/0.73    inference(ennf_transformation,[],[f1])).
% 2.59/0.73  fof(f1,axiom,(
% 2.59/0.73    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) => r2_hidden(k4_tarski(X2,X3),X1))))),
% 2.59/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).
% 2.59/0.73  fof(f7780,plain,(
% 2.59/0.73    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k5_relat_1(sK0,sK2)) | r2_hidden(k4_tarski(X0,X1),k5_relat_1(sK0,sK3))) ) | ~spl10_1370),
% 2.59/0.73    inference(avatar_component_clause,[],[f7779])).
% 2.59/0.73  fof(f7781,plain,(
% 2.59/0.73    ~spl10_5 | spl10_1370 | ~spl10_7 | ~spl10_49),
% 2.59/0.73    inference(avatar_split_clause,[],[f7777,f477,f72,f7779,f64])).
% 2.59/0.73  fof(f64,plain,(
% 2.59/0.73    spl10_5 <=> v1_relat_1(sK2)),
% 2.59/0.73    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 2.59/0.73  fof(f72,plain,(
% 2.59/0.73    spl10_7 <=> v1_relat_1(sK0)),
% 2.59/0.73    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 2.59/0.73  fof(f477,plain,(
% 2.59/0.73    spl10_49 <=> ! [X16,X13,X15,X14] : (r2_hidden(k4_tarski(X13,X14),k5_relat_1(sK0,sK3)) | ~v1_relat_1(X15) | ~r2_hidden(k4_tarski(X16,X14),k5_relat_1(X15,sK2)) | ~r2_hidden(k4_tarski(X13,sK7(X15,sK2,X16,X14)),sK0))),
% 2.59/0.73    introduced(avatar_definition,[new_symbols(naming,[spl10_49])])).
% 2.59/0.73  fof(f7777,plain,(
% 2.59/0.73    ( ! [X0,X1] : (~v1_relat_1(sK0) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(sK0,sK2)) | r2_hidden(k4_tarski(X0,X1),k5_relat_1(sK0,sK3)) | ~v1_relat_1(sK2)) ) | ~spl10_49),
% 2.59/0.73    inference(duplicate_literal_removal,[],[f7774])).
% 2.59/0.73  fof(f7774,plain,(
% 2.59/0.73    ( ! [X0,X1] : (~v1_relat_1(sK0) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(sK0,sK2)) | r2_hidden(k4_tarski(X0,X1),k5_relat_1(sK0,sK3)) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(sK0,sK2)) | ~v1_relat_1(sK2) | ~v1_relat_1(sK0)) ) | ~spl10_49),
% 2.59/0.73    inference(resolution,[],[f478,f75])).
% 2.59/0.73  fof(f75,plain,(
% 2.59/0.73    ( ! [X0,X8,X7,X1] : (r2_hidden(k4_tarski(X7,sK7(X0,X1,X7,X8)),X0) | ~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.59/0.73    inference(subsumption_resolution,[],[f46,f43])).
% 2.59/0.73  fof(f43,plain,(
% 2.59/0.73    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.59/0.73    inference(cnf_transformation,[],[f11])).
% 2.59/0.73  fof(f11,plain,(
% 2.59/0.73    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 2.59/0.73    inference(flattening,[],[f10])).
% 2.59/0.73  fof(f10,plain,(
% 2.59/0.73    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 2.59/0.73    inference(ennf_transformation,[],[f3])).
% 2.59/0.73  fof(f3,axiom,(
% 2.59/0.73    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 2.59/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 2.59/0.73  fof(f46,plain,(
% 2.59/0.73    ( ! [X0,X8,X7,X1] : (r2_hidden(k4_tarski(X7,sK7(X0,X1,X7,X8)),X0) | ~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.59/0.73    inference(equality_resolution,[],[f34])).
% 2.59/0.73  fof(f34,plain,(
% 2.59/0.73    ( ! [X2,X0,X8,X7,X1] : (r2_hidden(k4_tarski(X7,sK7(X0,X1,X7,X8)),X0) | ~r2_hidden(k4_tarski(X7,X8),X2) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.59/0.73    inference(cnf_transformation,[],[f22])).
% 2.59/0.73  fof(f22,plain,(
% 2.59/0.73    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ((! [X5] : (~r2_hidden(k4_tarski(X5,sK5(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK4(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK6(X0,X1,X2),sK5(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK4(X0,X1,X2),sK6(X0,X1,X2)),X0)) | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & ((r2_hidden(k4_tarski(sK7(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK7(X0,X1,X7,X8)),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.59/0.73    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f18,f21,f20,f19])).
% 2.59/0.73  fof(f19,plain,(
% 2.59/0.73    ! [X2,X1,X0] : (? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((! [X5] : (~r2_hidden(k4_tarski(X5,sK5(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK4(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,sK5(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK4(X0,X1,X2),X6),X0)) | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2))))),
% 2.59/0.73    introduced(choice_axiom,[])).
% 2.59/0.73  fof(f20,plain,(
% 2.59/0.73    ! [X2,X1,X0] : (? [X6] : (r2_hidden(k4_tarski(X6,sK5(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK4(X0,X1,X2),X6),X0)) => (r2_hidden(k4_tarski(sK6(X0,X1,X2),sK5(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK4(X0,X1,X2),sK6(X0,X1,X2)),X0)))),
% 2.59/0.73    introduced(choice_axiom,[])).
% 2.59/0.73  fof(f21,plain,(
% 2.59/0.73    ! [X8,X7,X1,X0] : (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) => (r2_hidden(k4_tarski(sK7(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK7(X0,X1,X7,X8)),X0)))),
% 2.59/0.73    introduced(choice_axiom,[])).
% 2.59/0.73  fof(f18,plain,(
% 2.59/0.73    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.59/0.73    inference(rectify,[],[f17])).
% 2.59/0.73  fof(f17,plain,(
% 2.59/0.73    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0))) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.59/0.73    inference(nnf_transformation,[],[f8])).
% 2.59/0.73  fof(f8,plain,(
% 2.59/0.73    ! [X0] : (! [X1] : (! [X2] : ((k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.59/0.73    inference(ennf_transformation,[],[f2])).
% 2.59/0.73  fof(f2,axiom,(
% 2.59/0.73    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))))))),
% 2.59/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).
% 2.59/0.73  fof(f478,plain,(
% 2.59/0.73    ( ! [X14,X15,X13,X16] : (~r2_hidden(k4_tarski(X13,sK7(X15,sK2,X16,X14)),sK0) | ~v1_relat_1(X15) | ~r2_hidden(k4_tarski(X16,X14),k5_relat_1(X15,sK2)) | r2_hidden(k4_tarski(X13,X14),k5_relat_1(sK0,sK3))) ) | ~spl10_49),
% 2.59/0.73    inference(avatar_component_clause,[],[f477])).
% 2.59/0.73  fof(f3254,plain,(
% 2.59/0.73    ~spl10_88 | spl10_528 | ~spl10_473),
% 2.59/0.73    inference(avatar_split_clause,[],[f3202,f2858,f3207,f687])).
% 2.59/0.73  fof(f2858,plain,(
% 2.59/0.73    spl10_473 <=> ! [X15] : (r2_hidden(k4_tarski(sK8(k5_relat_1(sK0,sK3),X15),sK9(k5_relat_1(sK0,sK3),X15)),k5_relat_1(sK1,sK3)) | r1_tarski(k5_relat_1(sK0,sK3),X15))),
% 2.59/0.73    introduced(avatar_definition,[new_symbols(naming,[spl10_473])])).
% 2.59/0.73  fof(f3202,plain,(
% 2.59/0.73    r1_tarski(k5_relat_1(sK0,sK3),k5_relat_1(sK1,sK3)) | ~v1_relat_1(k5_relat_1(sK0,sK3)) | ~spl10_473),
% 2.59/0.73    inference(duplicate_literal_removal,[],[f3200])).
% 2.59/0.73  fof(f3200,plain,(
% 2.59/0.73    r1_tarski(k5_relat_1(sK0,sK3),k5_relat_1(sK1,sK3)) | r1_tarski(k5_relat_1(sK0,sK3),k5_relat_1(sK1,sK3)) | ~v1_relat_1(k5_relat_1(sK0,sK3)) | ~spl10_473),
% 2.59/0.73    inference(resolution,[],[f2859,f42])).
% 2.59/0.73  fof(f42,plain,(
% 2.59/0.73    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1) | r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 2.59/0.73    inference(cnf_transformation,[],[f26])).
% 2.59/0.73  fof(f2859,plain,(
% 2.59/0.73    ( ! [X15] : (r2_hidden(k4_tarski(sK8(k5_relat_1(sK0,sK3),X15),sK9(k5_relat_1(sK0,sK3),X15)),k5_relat_1(sK1,sK3)) | r1_tarski(k5_relat_1(sK0,sK3),X15)) ) | ~spl10_473),
% 2.59/0.73    inference(avatar_component_clause,[],[f2858])).
% 2.59/0.73  fof(f2860,plain,(
% 2.59/0.73    ~spl10_88 | spl10_473 | ~spl10_4 | ~spl10_405),
% 2.59/0.73    inference(avatar_split_clause,[],[f2835,f2484,f60,f2858,f687])).
% 2.59/0.73  fof(f60,plain,(
% 2.59/0.73    spl10_4 <=> v1_relat_1(sK3)),
% 2.59/0.73    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 2.59/0.73  fof(f2484,plain,(
% 2.59/0.73    spl10_405 <=> ! [X3,X5,X4] : (~r2_hidden(k4_tarski(X3,X4),k5_relat_1(sK0,X5)) | ~v1_relat_1(X5) | r2_hidden(k4_tarski(X3,X4),k5_relat_1(sK1,X5)))),
% 2.59/0.73    introduced(avatar_definition,[new_symbols(naming,[spl10_405])])).
% 2.59/0.73  fof(f2835,plain,(
% 2.59/0.73    ( ! [X15] : (r2_hidden(k4_tarski(sK8(k5_relat_1(sK0,sK3),X15),sK9(k5_relat_1(sK0,sK3),X15)),k5_relat_1(sK1,sK3)) | r1_tarski(k5_relat_1(sK0,sK3),X15) | ~v1_relat_1(k5_relat_1(sK0,sK3))) ) | (~spl10_4 | ~spl10_405)),
% 2.59/0.73    inference(resolution,[],[f2686,f41])).
% 2.59/0.73  fof(f2686,plain,(
% 2.59/0.73    ( ! [X10,X11] : (~r2_hidden(k4_tarski(X10,X11),k5_relat_1(sK0,sK3)) | r2_hidden(k4_tarski(X10,X11),k5_relat_1(sK1,sK3))) ) | (~spl10_4 | ~spl10_405)),
% 2.59/0.73    inference(resolution,[],[f2485,f61])).
% 2.59/0.73  fof(f61,plain,(
% 2.59/0.73    v1_relat_1(sK3) | ~spl10_4),
% 2.59/0.73    inference(avatar_component_clause,[],[f60])).
% 2.59/0.73  fof(f2485,plain,(
% 2.59/0.73    ( ! [X4,X5,X3] : (~v1_relat_1(X5) | ~r2_hidden(k4_tarski(X3,X4),k5_relat_1(sK0,X5)) | r2_hidden(k4_tarski(X3,X4),k5_relat_1(sK1,X5))) ) | ~spl10_405),
% 2.59/0.73    inference(avatar_component_clause,[],[f2484])).
% 2.59/0.73  fof(f2486,plain,(
% 2.59/0.73    ~spl10_7 | spl10_405 | ~spl10_6 | ~spl10_3),
% 2.59/0.73    inference(avatar_split_clause,[],[f2474,f56,f68,f2484,f72])).
% 2.59/0.73  fof(f68,plain,(
% 2.59/0.73    spl10_6 <=> v1_relat_1(sK1)),
% 2.59/0.73    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 2.59/0.73  fof(f56,plain,(
% 2.59/0.73    spl10_3 <=> r1_tarski(sK0,sK1)),
% 2.59/0.73    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 2.59/0.73  fof(f2474,plain,(
% 2.59/0.73    ( ! [X4,X5,X3] : (~v1_relat_1(sK1) | ~r2_hidden(k4_tarski(X3,X4),k5_relat_1(sK0,X5)) | ~v1_relat_1(sK0) | r2_hidden(k4_tarski(X3,X4),k5_relat_1(sK1,X5)) | ~v1_relat_1(X5)) ) | ~spl10_3),
% 2.59/0.73    inference(resolution,[],[f1279,f57])).
% 2.59/0.73  fof(f57,plain,(
% 2.59/0.73    r1_tarski(sK0,sK1) | ~spl10_3),
% 2.59/0.73    inference(avatar_component_clause,[],[f56])).
% 2.59/0.73  fof(f1279,plain,(
% 2.59/0.73    ( ! [X4,X2,X0,X3,X1] : (~r1_tarski(X4,X1) | ~v1_relat_1(X1) | ~r2_hidden(k4_tarski(X2,X3),k5_relat_1(X4,X0)) | ~v1_relat_1(X4) | r2_hidden(k4_tarski(X2,X3),k5_relat_1(X1,X0)) | ~v1_relat_1(X0)) )),
% 2.59/0.73    inference(duplicate_literal_removal,[],[f1273])).
% 2.59/0.73  fof(f1273,plain,(
% 2.59/0.73    ( ! [X4,X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~r2_hidden(k4_tarski(X2,X3),k5_relat_1(X4,X0)) | ~v1_relat_1(X4) | r2_hidden(k4_tarski(X2,X3),k5_relat_1(X1,X0)) | ~r1_tarski(X4,X1) | ~v1_relat_1(X4) | ~r2_hidden(k4_tarski(X2,X3),k5_relat_1(X4,X0)) | ~v1_relat_1(X0) | ~v1_relat_1(X4)) )),
% 2.59/0.73    inference(resolution,[],[f671,f75])).
% 2.59/0.73  fof(f671,plain,(
% 2.59/0.73    ( ! [X6,X4,X2,X0,X5,X3,X1] : (~r2_hidden(k4_tarski(X0,sK7(X5,X3,X4,X1)),X6) | ~v1_relat_1(X3) | ~v1_relat_1(X2) | ~r2_hidden(k4_tarski(X4,X1),k5_relat_1(X5,X3)) | ~v1_relat_1(X5) | r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3)) | ~r1_tarski(X6,X2) | ~v1_relat_1(X6)) )),
% 2.59/0.73    inference(resolution,[],[f202,f40])).
% 2.59/0.73  fof(f40,plain,(
% 2.59/0.73    ( ! [X4,X0,X5,X1] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 2.59/0.73    inference(cnf_transformation,[],[f26])).
% 2.59/0.73  fof(f202,plain,(
% 2.59/0.73    ( ! [X21,X19,X17,X20,X18,X16] : (~r2_hidden(k4_tarski(X16,sK7(X20,X19,X21,X17)),X18) | r2_hidden(k4_tarski(X16,X17),k5_relat_1(X18,X19)) | ~v1_relat_1(X19) | ~v1_relat_1(X18) | ~r2_hidden(k4_tarski(X21,X17),k5_relat_1(X20,X19)) | ~v1_relat_1(X20)) )),
% 2.59/0.73    inference(duplicate_literal_removal,[],[f201])).
% 2.59/0.73  fof(f201,plain,(
% 2.59/0.73    ( ! [X21,X19,X17,X20,X18,X16] : (r2_hidden(k4_tarski(X16,X17),k5_relat_1(X18,X19)) | ~r2_hidden(k4_tarski(X16,sK7(X20,X19,X21,X17)),X18) | ~v1_relat_1(X19) | ~v1_relat_1(X18) | ~r2_hidden(k4_tarski(X21,X17),k5_relat_1(X20,X19)) | ~v1_relat_1(X19) | ~v1_relat_1(X20)) )),
% 2.59/0.73    inference(resolution,[],[f77,f76])).
% 2.59/0.73  fof(f76,plain,(
% 2.59/0.73    ( ! [X0,X8,X7,X1] : (r2_hidden(k4_tarski(sK7(X0,X1,X7,X8),X8),X1) | ~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.59/0.73    inference(subsumption_resolution,[],[f45,f43])).
% 2.59/0.73  fof(f45,plain,(
% 2.59/0.73    ( ! [X0,X8,X7,X1] : (r2_hidden(k4_tarski(sK7(X0,X1,X7,X8),X8),X1) | ~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.59/0.73    inference(equality_resolution,[],[f35])).
% 2.59/0.73  fof(f35,plain,(
% 2.59/0.73    ( ! [X2,X0,X8,X7,X1] : (r2_hidden(k4_tarski(sK7(X0,X1,X7,X8),X8),X1) | ~r2_hidden(k4_tarski(X7,X8),X2) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.59/0.73    inference(cnf_transformation,[],[f22])).
% 2.59/0.73  fof(f77,plain,(
% 2.59/0.73    ( ! [X0,X8,X7,X1,X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~r2_hidden(k4_tarski(X7,X9),X0) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.59/0.73    inference(subsumption_resolution,[],[f44,f43])).
% 2.59/0.73  fof(f44,plain,(
% 2.59/0.73    ( ! [X0,X8,X7,X1,X9] : (r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.59/0.73    inference(equality_resolution,[],[f36])).
% 2.59/0.73  fof(f36,plain,(
% 2.59/0.73    ( ! [X2,X0,X8,X7,X1,X9] : (r2_hidden(k4_tarski(X7,X8),X2) | ~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.59/0.73    inference(cnf_transformation,[],[f22])).
% 2.59/0.73  fof(f694,plain,(
% 2.59/0.73    ~spl10_7 | ~spl10_4 | spl10_88),
% 2.59/0.73    inference(avatar_split_clause,[],[f693,f687,f60,f72])).
% 2.59/0.73  fof(f693,plain,(
% 2.59/0.73    ~v1_relat_1(sK3) | ~v1_relat_1(sK0) | spl10_88),
% 2.59/0.73    inference(resolution,[],[f688,f43])).
% 2.59/0.73  fof(f688,plain,(
% 2.59/0.73    ~v1_relat_1(k5_relat_1(sK0,sK3)) | spl10_88),
% 2.59/0.73    inference(avatar_component_clause,[],[f687])).
% 2.59/0.73  fof(f479,plain,(
% 2.59/0.73    ~spl10_5 | spl10_49 | ~spl10_7 | ~spl10_44),
% 2.59/0.73    inference(avatar_split_clause,[],[f462,f446,f72,f477,f64])).
% 2.59/0.73  fof(f446,plain,(
% 2.59/0.73    spl10_44 <=> ! [X1,X3,X0,X2] : (~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(k4_tarski(X0,X3),k5_relat_1(X2,sK3)) | ~r2_hidden(k4_tarski(X1,X3),sK2) | ~v1_relat_1(X2))),
% 2.59/0.73    introduced(avatar_definition,[new_symbols(naming,[spl10_44])])).
% 2.59/0.73  fof(f462,plain,(
% 2.59/0.73    ( ! [X14,X15,X13,X16] : (r2_hidden(k4_tarski(X13,X14),k5_relat_1(sK0,sK3)) | ~r2_hidden(k4_tarski(X13,sK7(X15,sK2,X16,X14)),sK0) | ~r2_hidden(k4_tarski(X16,X14),k5_relat_1(X15,sK2)) | ~v1_relat_1(sK2) | ~v1_relat_1(X15)) ) | (~spl10_7 | ~spl10_44)),
% 2.59/0.73    inference(resolution,[],[f454,f76])).
% 2.59/0.73  fof(f454,plain,(
% 2.59/0.73    ( ! [X6,X7,X5] : (~r2_hidden(k4_tarski(X7,X6),sK2) | r2_hidden(k4_tarski(X5,X6),k5_relat_1(sK0,sK3)) | ~r2_hidden(k4_tarski(X5,X7),sK0)) ) | (~spl10_7 | ~spl10_44)),
% 2.59/0.73    inference(resolution,[],[f447,f73])).
% 2.59/0.73  fof(f73,plain,(
% 2.59/0.73    v1_relat_1(sK0) | ~spl10_7),
% 2.59/0.73    inference(avatar_component_clause,[],[f72])).
% 2.59/0.73  fof(f447,plain,(
% 2.59/0.73    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X2) | r2_hidden(k4_tarski(X0,X3),k5_relat_1(X2,sK3)) | ~r2_hidden(k4_tarski(X1,X3),sK2) | ~r2_hidden(k4_tarski(X0,X1),X2)) ) | ~spl10_44),
% 2.59/0.73    inference(avatar_component_clause,[],[f446])).
% 2.59/0.73  fof(f448,plain,(
% 2.59/0.73    ~spl10_5 | ~spl10_4 | spl10_44 | ~spl10_2),
% 2.59/0.73    inference(avatar_split_clause,[],[f439,f52,f446,f60,f64])).
% 2.59/0.73  fof(f52,plain,(
% 2.59/0.73    spl10_2 <=> r1_tarski(sK2,sK3)),
% 2.59/0.73    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 2.59/0.73  fof(f439,plain,(
% 2.59/0.73    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(sK3) | ~v1_relat_1(X2) | ~r2_hidden(k4_tarski(X1,X3),sK2) | r2_hidden(k4_tarski(X0,X3),k5_relat_1(X2,sK3)) | ~v1_relat_1(sK2)) ) | ~spl10_2),
% 2.59/0.73    inference(resolution,[],[f199,f53])).
% 2.59/0.73  fof(f53,plain,(
% 2.59/0.73    r1_tarski(sK2,sK3) | ~spl10_2),
% 2.59/0.73    inference(avatar_component_clause,[],[f52])).
% 2.59/0.73  fof(f199,plain,(
% 2.59/0.73    ( ! [X6,X4,X8,X7,X5,X9] : (~r1_tarski(X9,X7) | ~r2_hidden(k4_tarski(X4,X8),X6) | ~v1_relat_1(X7) | ~v1_relat_1(X6) | ~r2_hidden(k4_tarski(X8,X5),X9) | r2_hidden(k4_tarski(X4,X5),k5_relat_1(X6,X7)) | ~v1_relat_1(X9)) )),
% 2.59/0.73    inference(resolution,[],[f77,f40])).
% 2.59/0.73  fof(f92,plain,(
% 2.59/0.73    ~spl10_7 | ~spl10_5 | spl10_8),
% 2.59/0.73    inference(avatar_split_clause,[],[f89,f83,f64,f72])).
% 2.59/0.73  fof(f89,plain,(
% 2.59/0.73    ~v1_relat_1(sK2) | ~v1_relat_1(sK0) | spl10_8),
% 2.59/0.73    inference(resolution,[],[f84,f43])).
% 2.59/0.73  fof(f84,plain,(
% 2.59/0.73    ~v1_relat_1(k5_relat_1(sK0,sK2)) | spl10_8),
% 2.59/0.73    inference(avatar_component_clause,[],[f83])).
% 2.59/0.73  fof(f88,plain,(
% 2.59/0.73    ~spl10_8 | spl10_9 | spl10_1),
% 2.59/0.73    inference(avatar_split_clause,[],[f81,f48,f86,f83])).
% 2.59/0.73  fof(f81,plain,(
% 2.59/0.73    ( ! [X0] : (~r1_tarski(X0,k5_relat_1(sK1,sK3)) | ~v1_relat_1(X0) | ~r2_hidden(k4_tarski(sK8(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)),sK9(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3))),X0) | ~v1_relat_1(k5_relat_1(sK0,sK2))) ) | spl10_1),
% 2.59/0.73    inference(resolution,[],[f80,f49])).
% 2.59/0.73  fof(f49,plain,(
% 2.59/0.73    ~r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)) | spl10_1),
% 2.59/0.73    inference(avatar_component_clause,[],[f48])).
% 2.59/0.73  fof(f80,plain,(
% 2.59/0.73    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X2,X1) | ~v1_relat_1(X2) | ~r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X2) | ~v1_relat_1(X0)) )),
% 2.59/0.73    inference(resolution,[],[f40,f42])).
% 2.59/0.73  fof(f74,plain,(
% 2.59/0.73    spl10_7),
% 2.59/0.73    inference(avatar_split_clause,[],[f27,f72])).
% 2.59/0.73  fof(f27,plain,(
% 2.59/0.73    v1_relat_1(sK0)),
% 2.59/0.73    inference(cnf_transformation,[],[f16])).
% 2.59/0.73  fof(f16,plain,(
% 2.59/0.73    (((~r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)) & r1_tarski(sK2,sK3) & r1_tarski(sK0,sK1) & v1_relat_1(sK3)) & v1_relat_1(sK2)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 2.59/0.73    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f15,f14,f13,f12])).
% 2.59/0.73  fof(f12,plain,(
% 2.59/0.73    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) & r1_tarski(X2,X3) & r1_tarski(X0,X1) & v1_relat_1(X3)) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r1_tarski(k5_relat_1(sK0,X2),k5_relat_1(X1,X3)) & r1_tarski(X2,X3) & r1_tarski(sK0,X1) & v1_relat_1(X3)) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 2.59/0.73    introduced(choice_axiom,[])).
% 2.59/0.73  fof(f13,plain,(
% 2.59/0.73    ? [X1] : (? [X2] : (? [X3] : (~r1_tarski(k5_relat_1(sK0,X2),k5_relat_1(X1,X3)) & r1_tarski(X2,X3) & r1_tarski(sK0,X1) & v1_relat_1(X3)) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (? [X3] : (~r1_tarski(k5_relat_1(sK0,X2),k5_relat_1(sK1,X3)) & r1_tarski(X2,X3) & r1_tarski(sK0,sK1) & v1_relat_1(X3)) & v1_relat_1(X2)) & v1_relat_1(sK1))),
% 2.59/0.73    introduced(choice_axiom,[])).
% 2.59/0.73  fof(f14,plain,(
% 2.59/0.73    ? [X2] : (? [X3] : (~r1_tarski(k5_relat_1(sK0,X2),k5_relat_1(sK1,X3)) & r1_tarski(X2,X3) & r1_tarski(sK0,sK1) & v1_relat_1(X3)) & v1_relat_1(X2)) => (? [X3] : (~r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,X3)) & r1_tarski(sK2,X3) & r1_tarski(sK0,sK1) & v1_relat_1(X3)) & v1_relat_1(sK2))),
% 2.59/0.73    introduced(choice_axiom,[])).
% 2.59/0.73  fof(f15,plain,(
% 2.59/0.73    ? [X3] : (~r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,X3)) & r1_tarski(sK2,X3) & r1_tarski(sK0,sK1) & v1_relat_1(X3)) => (~r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)) & r1_tarski(sK2,sK3) & r1_tarski(sK0,sK1) & v1_relat_1(sK3))),
% 2.59/0.73    introduced(choice_axiom,[])).
% 2.59/0.73  fof(f7,plain,(
% 2.59/0.73    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) & r1_tarski(X2,X3) & r1_tarski(X0,X1) & v1_relat_1(X3)) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 2.59/0.73    inference(flattening,[],[f6])).
% 2.59/0.73  fof(f6,plain,(
% 2.59/0.73    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) & (r1_tarski(X2,X3) & r1_tarski(X0,X1))) & v1_relat_1(X3)) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 2.59/0.73    inference(ennf_transformation,[],[f5])).
% 2.59/0.73  fof(f5,negated_conjecture,(
% 2.59/0.73    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)))))))),
% 2.59/0.73    inference(negated_conjecture,[],[f4])).
% 2.59/0.73  fof(f4,conjecture,(
% 2.59/0.73    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)))))))),
% 2.59/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relat_1)).
% 2.59/0.73  fof(f70,plain,(
% 2.59/0.73    spl10_6),
% 2.59/0.73    inference(avatar_split_clause,[],[f28,f68])).
% 2.59/0.73  fof(f28,plain,(
% 2.59/0.73    v1_relat_1(sK1)),
% 2.59/0.73    inference(cnf_transformation,[],[f16])).
% 2.59/0.73  fof(f66,plain,(
% 2.59/0.73    spl10_5),
% 2.59/0.73    inference(avatar_split_clause,[],[f29,f64])).
% 2.59/0.73  fof(f29,plain,(
% 2.59/0.73    v1_relat_1(sK2)),
% 2.59/0.73    inference(cnf_transformation,[],[f16])).
% 2.59/0.73  fof(f62,plain,(
% 2.59/0.73    spl10_4),
% 2.59/0.73    inference(avatar_split_clause,[],[f30,f60])).
% 2.59/0.73  fof(f30,plain,(
% 2.59/0.73    v1_relat_1(sK3)),
% 2.59/0.73    inference(cnf_transformation,[],[f16])).
% 2.59/0.73  fof(f58,plain,(
% 2.59/0.73    spl10_3),
% 2.59/0.73    inference(avatar_split_clause,[],[f31,f56])).
% 2.59/0.73  fof(f31,plain,(
% 2.59/0.73    r1_tarski(sK0,sK1)),
% 2.59/0.73    inference(cnf_transformation,[],[f16])).
% 2.59/0.73  fof(f54,plain,(
% 2.59/0.73    spl10_2),
% 2.59/0.73    inference(avatar_split_clause,[],[f32,f52])).
% 2.59/0.73  fof(f32,plain,(
% 2.59/0.73    r1_tarski(sK2,sK3)),
% 2.59/0.73    inference(cnf_transformation,[],[f16])).
% 2.59/0.73  fof(f50,plain,(
% 2.59/0.73    ~spl10_1),
% 2.59/0.73    inference(avatar_split_clause,[],[f33,f48])).
% 2.59/0.73  fof(f33,plain,(
% 2.59/0.73    ~r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3))),
% 2.59/0.73    inference(cnf_transformation,[],[f16])).
% 2.59/0.73  % SZS output end Proof for theBenchmark
% 2.59/0.73  % (10435)------------------------------
% 2.59/0.73  % (10435)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.59/0.73  % (10435)Termination reason: Refutation
% 2.59/0.73  
% 2.59/0.73  % (10435)Memory used [KB]: 18549
% 2.59/0.73  % (10435)Time elapsed: 0.318 s
% 2.59/0.73  % (10435)------------------------------
% 2.59/0.73  % (10435)------------------------------
% 2.59/0.73  % (10426)Success in time 0.375 s
%------------------------------------------------------------------------------
