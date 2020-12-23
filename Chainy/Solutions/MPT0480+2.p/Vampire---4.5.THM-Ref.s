%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0480+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:32 EST 2020

% Result     : Theorem 2.76s
% Output     : Refutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 184 expanded)
%              Number of leaves         :   20 (  65 expanded)
%              Depth                    :   15
%              Number of atoms          :  423 ( 980 expanded)
%              Number of equality atoms :   55 ( 135 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3230,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1011,f1014,f1016,f1020,f2526,f2549,f3201,f3205,f3210,f3211,f3229])).

fof(f3229,plain,
    ( spl45_1
    | ~ spl45_2
    | ~ spl45_3
    | ~ spl45_4 ),
    inference(avatar_contradiction_clause,[],[f3228])).

fof(f3228,plain,
    ( $false
    | spl45_1
    | ~ spl45_2
    | ~ spl45_3
    | ~ spl45_4 ),
    inference(subsumption_resolution,[],[f3227,f1015])).

fof(f1015,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl45_2 ),
    inference(avatar_component_clause,[],[f1006])).

fof(f1006,plain,
    ( spl45_2
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl45_2])])).

fof(f3227,plain,
    ( ~ r2_hidden(sK1,sK2)
    | spl45_1
    | ~ spl45_3
    | ~ spl45_4 ),
    inference(subsumption_resolution,[],[f3226,f1013])).

fof(f1013,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK3)
    | ~ spl45_3 ),
    inference(avatar_component_clause,[],[f1009])).

fof(f1009,plain,
    ( spl45_3
  <=> r2_hidden(k4_tarski(sK0,sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl45_3])])).

fof(f3226,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),sK3)
    | ~ r2_hidden(sK1,sK2)
    | spl45_1
    | ~ spl45_4 ),
    inference(resolution,[],[f3219,f1493])).

fof(f1493,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,X5),k6_relat_1(X0))
      | ~ r2_hidden(X5,X0) ) ),
    inference(subsumption_resolution,[],[f985,f907])).

fof(f907,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f654])).

fof(f654,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f985,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,X5),k6_relat_1(X0))
      | ~ r2_hidden(X5,X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f984])).

fof(f984,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X5),X1)
      | ~ r2_hidden(X5,X0)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f898])).

fof(f898,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | X4 != X5
      | ~ r2_hidden(X4,X0)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f802])).

fof(f802,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( ( sK11(X0,X1) != sK12(X0,X1)
              | ~ r2_hidden(sK11(X0,X1),X0)
              | ~ r2_hidden(k4_tarski(sK11(X0,X1),sK12(X0,X1)),X1) )
            & ( ( sK11(X0,X1) = sK12(X0,X1)
                & r2_hidden(sK11(X0,X1),X0) )
              | r2_hidden(k4_tarski(sK11(X0,X1),sK12(X0,X1)),X1) ) ) )
        & ( ! [X4,X5] :
              ( ( r2_hidden(k4_tarski(X4,X5),X1)
                | X4 != X5
                | ~ r2_hidden(X4,X0) )
              & ( ( X4 = X5
                  & r2_hidden(X4,X0) )
                | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12])],[f800,f801])).

fof(f801,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( X2 != X3
            | ~ r2_hidden(X2,X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( ( X2 = X3
              & r2_hidden(X2,X0) )
            | r2_hidden(k4_tarski(X2,X3),X1) ) )
     => ( ( sK11(X0,X1) != sK12(X0,X1)
          | ~ r2_hidden(sK11(X0,X1),X0)
          | ~ r2_hidden(k4_tarski(sK11(X0,X1),sK12(X0,X1)),X1) )
        & ( ( sK11(X0,X1) = sK12(X0,X1)
            & r2_hidden(sK11(X0,X1),X0) )
          | r2_hidden(k4_tarski(sK11(X0,X1),sK12(X0,X1)),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f800,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X4,X5] :
              ( ( r2_hidden(k4_tarski(X4,X5),X1)
                | X4 != X5
                | ~ r2_hidden(X4,X0) )
              & ( ( X4 = X5
                  & r2_hidden(X4,X0) )
                | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f799])).

fof(f799,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
                | X2 != X3
                | ~ r2_hidden(X2,X0) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f798])).

fof(f798,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
                | X2 != X3
                | ~ r2_hidden(X2,X0) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f752])).

fof(f752,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f640])).

fof(f640,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_relat_1)).

fof(f3219,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK1),k6_relat_1(sK2))
        | ~ r2_hidden(k4_tarski(sK0,X0),sK3) )
    | spl45_1
    | ~ spl45_4 ),
    inference(subsumption_resolution,[],[f3218,f1019])).

fof(f1019,plain,
    ( v1_relat_1(sK3)
    | ~ spl45_4 ),
    inference(avatar_component_clause,[],[f1018])).

fof(f1018,plain,
    ( spl45_4
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl45_4])])).

fof(f3218,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK1),k6_relat_1(sK2))
        | ~ r2_hidden(k4_tarski(sK0,X0),sK3)
        | ~ v1_relat_1(sK3) )
    | spl45_1 ),
    inference(subsumption_resolution,[],[f3216,f907])).

fof(f3216,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK1),k6_relat_1(sK2))
        | ~ r2_hidden(k4_tarski(sK0,X0),sK3)
        | ~ v1_relat_1(k6_relat_1(sK2))
        | ~ v1_relat_1(sK3) )
    | spl45_1 ),
    inference(resolution,[],[f1004,f1021])).

fof(f1021,plain,(
    ! [X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(global_subsumption,[],[f874,f981])).

fof(f981,plain,(
    ! [X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f878])).

fof(f878,plain,(
    ! [X2,X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),X2)
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f795])).

fof(f795,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ( ( ! [X5] :
                          ( ~ r2_hidden(k4_tarski(X5,sK8(X0,X1,X2)),X1)
                          | ~ r2_hidden(k4_tarski(sK7(X0,X1,X2),X5),X0) )
                      | ~ r2_hidden(k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)),X2) )
                    & ( ( r2_hidden(k4_tarski(sK9(X0,X1,X2),sK8(X0,X1,X2)),X1)
                        & r2_hidden(k4_tarski(sK7(X0,X1,X2),sK9(X0,X1,X2)),X0) )
                      | r2_hidden(k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ( r2_hidden(k4_tarski(sK10(X0,X1,X7,X8),X8),X1)
                          & r2_hidden(k4_tarski(X7,sK10(X0,X1,X7,X8)),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10])],[f791,f794,f793,f792])).

fof(f792,plain,(
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
              ( ~ r2_hidden(k4_tarski(X5,sK8(X0,X1,X2)),X1)
              | ~ r2_hidden(k4_tarski(sK7(X0,X1,X2),X5),X0) )
          | ~ r2_hidden(k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)),X2) )
        & ( ? [X6] :
              ( r2_hidden(k4_tarski(X6,sK8(X0,X1,X2)),X1)
              & r2_hidden(k4_tarski(sK7(X0,X1,X2),X6),X0) )
          | r2_hidden(k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f793,plain,(
    ! [X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,sK8(X0,X1,X2)),X1)
          & r2_hidden(k4_tarski(sK7(X0,X1,X2),X6),X0) )
     => ( r2_hidden(k4_tarski(sK9(X0,X1,X2),sK8(X0,X1,X2)),X1)
        & r2_hidden(k4_tarski(sK7(X0,X1,X2),sK9(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f794,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X1)
          & r2_hidden(k4_tarski(X7,X10),X0) )
     => ( r2_hidden(k4_tarski(sK10(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK10(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f791,plain,(
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
    inference(rectify,[],[f790])).

fof(f790,plain,(
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
    inference(nnf_transformation,[],[f736])).

fof(f736,plain,(
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
    inference(ennf_transformation,[],[f648])).

fof(f648,axiom,(
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

fof(f874,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f733])).

fof(f733,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f732])).

fof(f732,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f653])).

fof(f653,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f1004,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(sK3,k6_relat_1(sK2)))
    | spl45_1 ),
    inference(avatar_component_clause,[],[f1003])).

fof(f1003,plain,
    ( spl45_1
  <=> r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(sK3,k6_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl45_1])])).

fof(f3211,plain,
    ( sK1 != sK10(sK3,k6_relat_1(sK2),sK0,sK1)
    | ~ r2_hidden(sK10(sK3,k6_relat_1(sK2),sK0,sK1),sK2)
    | r2_hidden(sK1,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f3210,plain,
    ( sK1 != sK10(sK3,k6_relat_1(sK2),sK0,sK1)
    | ~ r2_hidden(k4_tarski(sK0,sK10(sK3,k6_relat_1(sK2),sK0,sK1)),sK3)
    | r2_hidden(k4_tarski(sK0,sK1),sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f3205,plain,
    ( spl45_162
    | ~ spl45_132 ),
    inference(avatar_split_clause,[],[f3196,f2524,f3203])).

fof(f3203,plain,
    ( spl45_162
  <=> sK1 = sK10(sK3,k6_relat_1(sK2),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl45_162])])).

fof(f2524,plain,
    ( spl45_132
  <=> r2_hidden(k4_tarski(sK10(sK3,k6_relat_1(sK2),sK0,sK1),sK1),k6_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl45_132])])).

fof(f3196,plain,
    ( sK1 = sK10(sK3,k6_relat_1(sK2),sK0,sK1)
    | ~ spl45_132 ),
    inference(resolution,[],[f2525,f1505])).

fof(f1505,plain,(
    ! [X4,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X5),k6_relat_1(X0))
      | X4 = X5 ) ),
    inference(subsumption_resolution,[],[f986,f907])).

fof(f986,plain,(
    ! [X4,X0,X5] :
      ( X4 = X5
      | ~ r2_hidden(k4_tarski(X4,X5),k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f897])).

fof(f897,plain,(
    ! [X4,X0,X5,X1] :
      ( X4 = X5
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f802])).

fof(f2525,plain,
    ( r2_hidden(k4_tarski(sK10(sK3,k6_relat_1(sK2),sK0,sK1),sK1),k6_relat_1(sK2))
    | ~ spl45_132 ),
    inference(avatar_component_clause,[],[f2524])).

fof(f3201,plain,
    ( spl45_161
    | ~ spl45_132 ),
    inference(avatar_split_clause,[],[f3195,f2524,f3199])).

fof(f3199,plain,
    ( spl45_161
  <=> r2_hidden(sK10(sK3,k6_relat_1(sK2),sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl45_161])])).

fof(f3195,plain,
    ( r2_hidden(sK10(sK3,k6_relat_1(sK2),sK0,sK1),sK2)
    | ~ spl45_132 ),
    inference(resolution,[],[f2525,f1517])).

fof(f1517,plain,(
    ! [X4,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X5),k6_relat_1(X0))
      | r2_hidden(X4,X0) ) ),
    inference(subsumption_resolution,[],[f987,f907])).

fof(f987,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(k4_tarski(X4,X5),k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f896])).

fof(f896,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f802])).

fof(f2549,plain,
    ( spl45_133
    | ~ spl45_1
    | ~ spl45_4 ),
    inference(avatar_split_clause,[],[f2545,f1018,f1003,f2547])).

fof(f2547,plain,
    ( spl45_133
  <=> r2_hidden(k4_tarski(sK0,sK10(sK3,k6_relat_1(sK2),sK0,sK1)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl45_133])])).

fof(f2545,plain,
    ( r2_hidden(k4_tarski(sK0,sK10(sK3,k6_relat_1(sK2),sK0,sK1)),sK3)
    | ~ spl45_1
    | ~ spl45_4 ),
    inference(subsumption_resolution,[],[f2544,f1019])).

fof(f2544,plain,
    ( r2_hidden(k4_tarski(sK0,sK10(sK3,k6_relat_1(sK2),sK0,sK1)),sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl45_1 ),
    inference(subsumption_resolution,[],[f2528,f907])).

fof(f2528,plain,
    ( r2_hidden(k4_tarski(sK0,sK10(sK3,k6_relat_1(sK2),sK0,sK1)),sK3)
    | ~ v1_relat_1(k6_relat_1(sK2))
    | ~ v1_relat_1(sK3)
    | ~ spl45_1 ),
    inference(resolution,[],[f1023,f1012])).

fof(f1012,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(sK3,k6_relat_1(sK2)))
    | ~ spl45_1 ),
    inference(avatar_component_clause,[],[f1003])).

fof(f1023,plain,(
    ! [X0,X8,X7,X1] :
      ( ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | r2_hidden(k4_tarski(X7,sK10(X0,X1,X7,X8)),X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(global_subsumption,[],[f874,f983])).

fof(f983,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK10(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f876])).

fof(f876,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK10(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f795])).

fof(f2526,plain,
    ( spl45_132
    | ~ spl45_1
    | ~ spl45_4 ),
    inference(avatar_split_clause,[],[f2522,f1018,f1003,f2524])).

fof(f2522,plain,
    ( r2_hidden(k4_tarski(sK10(sK3,k6_relat_1(sK2),sK0,sK1),sK1),k6_relat_1(sK2))
    | ~ spl45_1
    | ~ spl45_4 ),
    inference(subsumption_resolution,[],[f2521,f1019])).

fof(f2521,plain,
    ( r2_hidden(k4_tarski(sK10(sK3,k6_relat_1(sK2),sK0,sK1),sK1),k6_relat_1(sK2))
    | ~ v1_relat_1(sK3)
    | ~ spl45_1 ),
    inference(subsumption_resolution,[],[f2505,f907])).

fof(f2505,plain,
    ( r2_hidden(k4_tarski(sK10(sK3,k6_relat_1(sK2),sK0,sK1),sK1),k6_relat_1(sK2))
    | ~ v1_relat_1(k6_relat_1(sK2))
    | ~ v1_relat_1(sK3)
    | ~ spl45_1 ),
    inference(resolution,[],[f1022,f1012])).

fof(f1022,plain,(
    ! [X0,X8,X7,X1] :
      ( ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | r2_hidden(k4_tarski(sK10(X0,X1,X7,X8),X8),X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(global_subsumption,[],[f874,f982])).

fof(f982,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK10(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f877])).

fof(f877,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK10(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f795])).

fof(f1020,plain,(
    spl45_4 ),
    inference(avatar_split_clause,[],[f858,f1018])).

fof(f858,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f780])).

fof(f780,plain,
    ( ( ~ r2_hidden(k4_tarski(sK0,sK1),sK3)
      | ~ r2_hidden(sK1,sK2)
      | ~ r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(sK3,k6_relat_1(sK2))) )
    & ( ( r2_hidden(k4_tarski(sK0,sK1),sK3)
        & r2_hidden(sK1,sK2) )
      | r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(sK3,k6_relat_1(sK2))) )
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f778,f779])).

fof(f779,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r2_hidden(k4_tarski(X0,X1),X3)
          | ~ r2_hidden(X1,X2)
          | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) )
        & ( ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X1,X2) )
          | r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) )
        & v1_relat_1(X3) )
   => ( ( ~ r2_hidden(k4_tarski(sK0,sK1),sK3)
        | ~ r2_hidden(sK1,sK2)
        | ~ r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(sK3,k6_relat_1(sK2))) )
      & ( ( r2_hidden(k4_tarski(sK0,sK1),sK3)
          & r2_hidden(sK1,sK2) )
        | r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(sK3,k6_relat_1(sK2))) )
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f778,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r2_hidden(k4_tarski(X0,X1),X3)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) )
      & ( ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X1,X2) )
        | r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) )
      & v1_relat_1(X3) ) ),
    inference(flattening,[],[f777])).

fof(f777,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r2_hidden(k4_tarski(X0,X1),X3)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) )
      & ( ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X1,X2) )
        | r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) )
      & v1_relat_1(X3) ) ),
    inference(nnf_transformation,[],[f723])).

fof(f723,plain,(
    ? [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
      <~> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X1,X2) ) )
      & v1_relat_1(X3) ) ),
    inference(ennf_transformation,[],[f720])).

fof(f720,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
        <=> ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f719])).

fof(f719,conjecture,(
    ! [X0,X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_relat_1)).

fof(f1016,plain,
    ( spl45_1
    | spl45_2 ),
    inference(avatar_split_clause,[],[f859,f1006,f1003])).

fof(f859,plain,
    ( r2_hidden(sK1,sK2)
    | r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(sK3,k6_relat_1(sK2))) ),
    inference(cnf_transformation,[],[f780])).

fof(f1014,plain,
    ( spl45_1
    | spl45_3 ),
    inference(avatar_split_clause,[],[f860,f1009,f1003])).

fof(f860,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK3)
    | r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(sK3,k6_relat_1(sK2))) ),
    inference(cnf_transformation,[],[f780])).

fof(f1011,plain,
    ( ~ spl45_1
    | ~ spl45_2
    | ~ spl45_3 ),
    inference(avatar_split_clause,[],[f861,f1009,f1006,f1003])).

fof(f861,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),sK3)
    | ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(sK3,k6_relat_1(sK2))) ),
    inference(cnf_transformation,[],[f780])).
%------------------------------------------------------------------------------
