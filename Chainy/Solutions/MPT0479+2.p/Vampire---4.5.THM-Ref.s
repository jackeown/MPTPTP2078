%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0479+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:32 EST 2020

% Result     : Theorem 2.61s
% Output     : Refutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 183 expanded)
%              Number of leaves         :   18 (  64 expanded)
%              Depth                    :   15
%              Number of atoms          :  421 ( 980 expanded)
%              Number of equality atoms :   54 ( 134 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3242,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1004,f1007,f1009,f1013,f2137,f2598,f3221,f3226,f3227,f3241])).

fof(f3241,plain,
    ( spl45_1
    | ~ spl45_2
    | ~ spl45_3
    | ~ spl45_4 ),
    inference(avatar_contradiction_clause,[],[f3240])).

fof(f3240,plain,
    ( $false
    | spl45_1
    | ~ spl45_2
    | ~ spl45_3
    | ~ spl45_4 ),
    inference(subsumption_resolution,[],[f3239,f1008])).

fof(f1008,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl45_2 ),
    inference(avatar_component_clause,[],[f999])).

fof(f999,plain,
    ( spl45_2
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl45_2])])).

fof(f3239,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl45_1
    | ~ spl45_3
    | ~ spl45_4 ),
    inference(subsumption_resolution,[],[f3238,f1006])).

fof(f1006,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK3)
    | ~ spl45_3 ),
    inference(avatar_component_clause,[],[f1002])).

fof(f1002,plain,
    ( spl45_3
  <=> r2_hidden(k4_tarski(sK0,sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl45_3])])).

fof(f3238,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),sK3)
    | ~ r2_hidden(sK0,sK2)
    | spl45_1
    | ~ spl45_4 ),
    inference(resolution,[],[f3236,f1486])).

fof(f1486,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,X5),k6_relat_1(X0))
      | ~ r2_hidden(X5,X0) ) ),
    inference(subsumption_resolution,[],[f978,f900])).

fof(f900,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f654])).

fof(f654,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f978,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,X5),k6_relat_1(X0))
      | ~ r2_hidden(X5,X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f977])).

fof(f977,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X5),X1)
      | ~ r2_hidden(X5,X0)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f891])).

fof(f891,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | X4 != X5
      | ~ r2_hidden(X4,X0)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f798])).

fof(f798,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12])],[f796,f797])).

fof(f797,plain,(
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

fof(f796,plain,(
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
    inference(rectify,[],[f795])).

fof(f795,plain,(
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
    inference(flattening,[],[f794])).

fof(f794,plain,(
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
    inference(nnf_transformation,[],[f750])).

fof(f750,plain,(
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

fof(f3236,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK0,X0),k6_relat_1(sK2))
        | ~ r2_hidden(k4_tarski(X0,sK1),sK3) )
    | spl45_1
    | ~ spl45_4 ),
    inference(subsumption_resolution,[],[f3235,f900])).

fof(f3235,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK1),sK3)
        | ~ r2_hidden(k4_tarski(sK0,X0),k6_relat_1(sK2))
        | ~ v1_relat_1(k6_relat_1(sK2)) )
    | spl45_1
    | ~ spl45_4 ),
    inference(subsumption_resolution,[],[f3233,f1012])).

fof(f1012,plain,
    ( v1_relat_1(sK3)
    | ~ spl45_4 ),
    inference(avatar_component_clause,[],[f1011])).

fof(f1011,plain,
    ( spl45_4
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl45_4])])).

fof(f3233,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK1),sK3)
        | ~ r2_hidden(k4_tarski(sK0,X0),k6_relat_1(sK2))
        | ~ v1_relat_1(sK3)
        | ~ v1_relat_1(k6_relat_1(sK2)) )
    | spl45_1 ),
    inference(resolution,[],[f997,f1014])).

fof(f1014,plain,(
    ! [X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(global_subsumption,[],[f870,f974])).

fof(f974,plain,(
    ! [X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f874])).

fof(f874,plain,(
    ! [X2,X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),X2)
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f793])).

fof(f793,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10])],[f789,f792,f791,f790])).

fof(f790,plain,(
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

fof(f791,plain,(
    ! [X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,sK8(X0,X1,X2)),X1)
          & r2_hidden(k4_tarski(sK7(X0,X1,X2),X6),X0) )
     => ( r2_hidden(k4_tarski(sK9(X0,X1,X2),sK8(X0,X1,X2)),X1)
        & r2_hidden(k4_tarski(sK7(X0,X1,X2),sK9(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f792,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X1)
          & r2_hidden(k4_tarski(X7,X10),X0) )
     => ( r2_hidden(k4_tarski(sK10(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK10(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f789,plain,(
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
    inference(rectify,[],[f788])).

fof(f788,plain,(
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
    inference(nnf_transformation,[],[f735])).

fof(f735,plain,(
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

fof(f870,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f732])).

fof(f732,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f731])).

fof(f731,plain,(
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

fof(f997,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(k6_relat_1(sK2),sK3))
    | spl45_1 ),
    inference(avatar_component_clause,[],[f996])).

fof(f996,plain,
    ( spl45_1
  <=> r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(k6_relat_1(sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl45_1])])).

fof(f3227,plain,
    ( spl45_2
    | ~ spl45_144 ),
    inference(avatar_split_clause,[],[f3215,f2596,f999])).

fof(f2596,plain,
    ( spl45_144
  <=> r2_hidden(k4_tarski(sK0,sK10(k6_relat_1(sK2),sK3,sK0,sK1)),k6_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl45_144])])).

fof(f3215,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl45_144 ),
    inference(resolution,[],[f2597,f1510])).

fof(f1510,plain,(
    ! [X4,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X5),k6_relat_1(X0))
      | r2_hidden(X4,X0) ) ),
    inference(subsumption_resolution,[],[f980,f900])).

fof(f980,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(k4_tarski(X4,X5),k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f889])).

fof(f889,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f798])).

fof(f2597,plain,
    ( r2_hidden(k4_tarski(sK0,sK10(k6_relat_1(sK2),sK3,sK0,sK1)),k6_relat_1(sK2))
    | ~ spl45_144 ),
    inference(avatar_component_clause,[],[f2596])).

fof(f3226,plain,
    ( sK0 != sK10(k6_relat_1(sK2),sK3,sK0,sK1)
    | ~ r2_hidden(k4_tarski(sK10(k6_relat_1(sK2),sK3,sK0,sK1),sK1),sK3)
    | r2_hidden(k4_tarski(sK0,sK1),sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f3221,plain,
    ( spl45_176
    | ~ spl45_144 ),
    inference(avatar_split_clause,[],[f3216,f2596,f3219])).

fof(f3219,plain,
    ( spl45_176
  <=> sK0 = sK10(k6_relat_1(sK2),sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl45_176])])).

fof(f3216,plain,
    ( sK0 = sK10(k6_relat_1(sK2),sK3,sK0,sK1)
    | ~ spl45_144 ),
    inference(resolution,[],[f2597,f1498])).

fof(f1498,plain,(
    ! [X4,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X5),k6_relat_1(X0))
      | X4 = X5 ) ),
    inference(subsumption_resolution,[],[f979,f900])).

fof(f979,plain,(
    ! [X4,X0,X5] :
      ( X4 = X5
      | ~ r2_hidden(k4_tarski(X4,X5),k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f890])).

fof(f890,plain,(
    ! [X4,X0,X5,X1] :
      ( X4 = X5
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f798])).

fof(f2598,plain,
    ( spl45_144
    | ~ spl45_1
    | ~ spl45_4 ),
    inference(avatar_split_clause,[],[f2594,f1011,f996,f2596])).

fof(f2594,plain,
    ( r2_hidden(k4_tarski(sK0,sK10(k6_relat_1(sK2),sK3,sK0,sK1)),k6_relat_1(sK2))
    | ~ spl45_1
    | ~ spl45_4 ),
    inference(subsumption_resolution,[],[f2593,f900])).

fof(f2593,plain,
    ( r2_hidden(k4_tarski(sK0,sK10(k6_relat_1(sK2),sK3,sK0,sK1)),k6_relat_1(sK2))
    | ~ v1_relat_1(k6_relat_1(sK2))
    | ~ spl45_1
    | ~ spl45_4 ),
    inference(subsumption_resolution,[],[f2579,f1012])).

fof(f2579,plain,
    ( r2_hidden(k4_tarski(sK0,sK10(k6_relat_1(sK2),sK3,sK0,sK1)),k6_relat_1(sK2))
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(k6_relat_1(sK2))
    | ~ spl45_1 ),
    inference(resolution,[],[f1016,f1005])).

fof(f1005,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(k6_relat_1(sK2),sK3))
    | ~ spl45_1 ),
    inference(avatar_component_clause,[],[f996])).

fof(f1016,plain,(
    ! [X0,X8,X7,X1] :
      ( ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | r2_hidden(k4_tarski(X7,sK10(X0,X1,X7,X8)),X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(global_subsumption,[],[f870,f976])).

fof(f976,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK10(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f872])).

fof(f872,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK10(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f793])).

fof(f2137,plain,
    ( spl45_53
    | ~ spl45_1
    | ~ spl45_4 ),
    inference(avatar_split_clause,[],[f2133,f1011,f996,f2135])).

fof(f2135,plain,
    ( spl45_53
  <=> r2_hidden(k4_tarski(sK10(k6_relat_1(sK2),sK3,sK0,sK1),sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl45_53])])).

fof(f2133,plain,
    ( r2_hidden(k4_tarski(sK10(k6_relat_1(sK2),sK3,sK0,sK1),sK1),sK3)
    | ~ spl45_1
    | ~ spl45_4 ),
    inference(subsumption_resolution,[],[f2132,f900])).

fof(f2132,plain,
    ( r2_hidden(k4_tarski(sK10(k6_relat_1(sK2),sK3,sK0,sK1),sK1),sK3)
    | ~ v1_relat_1(k6_relat_1(sK2))
    | ~ spl45_1
    | ~ spl45_4 ),
    inference(subsumption_resolution,[],[f2115,f1012])).

fof(f2115,plain,
    ( r2_hidden(k4_tarski(sK10(k6_relat_1(sK2),sK3,sK0,sK1),sK1),sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(k6_relat_1(sK2))
    | ~ spl45_1 ),
    inference(resolution,[],[f1015,f1005])).

fof(f1015,plain,(
    ! [X0,X8,X7,X1] :
      ( ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | r2_hidden(k4_tarski(sK10(X0,X1,X7,X8),X8),X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(global_subsumption,[],[f870,f975])).

fof(f975,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK10(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f873])).

fof(f873,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK10(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f793])).

fof(f1013,plain,(
    spl45_4 ),
    inference(avatar_split_clause,[],[f854,f1011])).

fof(f854,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f778])).

fof(f778,plain,
    ( ( ~ r2_hidden(k4_tarski(sK0,sK1),sK3)
      | ~ r2_hidden(sK0,sK2)
      | ~ r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(k6_relat_1(sK2),sK3)) )
    & ( ( r2_hidden(k4_tarski(sK0,sK1),sK3)
        & r2_hidden(sK0,sK2) )
      | r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(k6_relat_1(sK2),sK3)) )
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f776,f777])).

fof(f777,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r2_hidden(k4_tarski(X0,X1),X3)
          | ~ r2_hidden(X0,X2)
          | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) )
        & ( ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X0,X2) )
          | r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) )
        & v1_relat_1(X3) )
   => ( ( ~ r2_hidden(k4_tarski(sK0,sK1),sK3)
        | ~ r2_hidden(sK0,sK2)
        | ~ r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(k6_relat_1(sK2),sK3)) )
      & ( ( r2_hidden(k4_tarski(sK0,sK1),sK3)
          & r2_hidden(sK0,sK2) )
        | r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(k6_relat_1(sK2),sK3)) )
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f776,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r2_hidden(k4_tarski(X0,X1),X3)
        | ~ r2_hidden(X0,X2)
        | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) )
      & ( ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X0,X2) )
        | r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) )
      & v1_relat_1(X3) ) ),
    inference(flattening,[],[f775])).

fof(f775,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r2_hidden(k4_tarski(X0,X1),X3)
        | ~ r2_hidden(X0,X2)
        | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) )
      & ( ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X0,X2) )
        | r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) )
      & v1_relat_1(X3) ) ),
    inference(nnf_transformation,[],[f722])).

fof(f722,plain,(
    ? [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      <~> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X0,X2) ) )
      & v1_relat_1(X3) ) ),
    inference(ennf_transformation,[],[f719])).

fof(f719,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
        <=> ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X0,X2) ) ) ) ),
    inference(negated_conjecture,[],[f718])).

fof(f718,conjecture,(
    ! [X0,X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X0,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_relat_1)).

fof(f1009,plain,
    ( spl45_1
    | spl45_2 ),
    inference(avatar_split_clause,[],[f855,f999,f996])).

fof(f855,plain,
    ( r2_hidden(sK0,sK2)
    | r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(k6_relat_1(sK2),sK3)) ),
    inference(cnf_transformation,[],[f778])).

fof(f1007,plain,
    ( spl45_1
    | spl45_3 ),
    inference(avatar_split_clause,[],[f856,f1002,f996])).

fof(f856,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK3)
    | r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(k6_relat_1(sK2),sK3)) ),
    inference(cnf_transformation,[],[f778])).

fof(f1004,plain,
    ( ~ spl45_1
    | ~ spl45_2
    | ~ spl45_3 ),
    inference(avatar_split_clause,[],[f857,f1002,f999,f996])).

fof(f857,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),sK3)
    | ~ r2_hidden(sK0,sK2)
    | ~ r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(k6_relat_1(sK2),sK3)) ),
    inference(cnf_transformation,[],[f778])).
%------------------------------------------------------------------------------
