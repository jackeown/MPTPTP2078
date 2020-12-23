%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relat_1__t74_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:04 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 204 expanded)
%              Number of leaves         :   15 (  60 expanded)
%              Depth                    :   16
%              Number of atoms          :  392 (1185 expanded)
%              Number of equality atoms :   52 ( 141 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f604,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f83,f90,f562,f572,f603])).

fof(f603,plain,
    ( spl10_1
    | ~ spl10_2
    | ~ spl10_4 ),
    inference(avatar_contradiction_clause,[],[f602])).

fof(f602,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f586,f73])).

fof(f73,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(k6_relat_1(sK2),sK3))
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl10_1
  <=> ~ r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(k6_relat_1(sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f586,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(k6_relat_1(sK2),sK3))
    | ~ spl10_2
    | ~ spl10_4 ),
    inference(unit_resulting_resolution,[],[f41,f59,f89,f102,f67])).

fof(f67,plain,(
    ! [X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(global_subsumption,[],[f46,f60])).

fof(f60,plain,(
    ! [X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),X2)
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f31,f34,f33,f32])).

fof(f32,plain,(
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

fof(f33,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,X4),X1)
          & r2_hidden(k4_tarski(X3,X6),X0) )
     => ( r2_hidden(k4_tarski(sK6(X0,X1,X2),X4),X1)
        & r2_hidden(k4_tarski(X3,sK6(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X1)
          & r2_hidden(k4_tarski(X7,X10),X0) )
     => ( r2_hidden(k4_tarski(sK7(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK7(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/relat_1__t74_relat_1.p',d8_relat_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t74_relat_1.p',dt_k5_relat_1)).

fof(f102,plain,
    ( r2_hidden(k4_tarski(sK0,sK0),k6_relat_1(sK2))
    | ~ spl10_2 ),
    inference(unit_resulting_resolution,[],[f82,f101])).

fof(f101,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,X5),k6_relat_1(X0))
      | ~ r2_hidden(X5,X0) ) ),
    inference(subsumption_resolution,[],[f64,f59])).

fof(f64,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,X5),k6_relat_1(X0))
      | ~ r2_hidden(X5,X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X5),X1)
      | ~ r2_hidden(X5,X0)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | X4 != X5
      | ~ r2_hidden(X4,X0)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( ( sK8(X0,X1) != sK9(X0,X1)
              | ~ r2_hidden(sK8(X0,X1),X0)
              | ~ r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1) )
            & ( ( sK8(X0,X1) = sK9(X0,X1)
                & r2_hidden(sK8(X0,X1),X0) )
              | r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1) ) ) )
        & ( ! [X4,X5] :
              ( ( r2_hidden(k4_tarski(X4,X5),X1)
                | X4 != X5
                | ~ r2_hidden(X4,X0) )
              & ( ( X4 = X5
                  & r2_hidden(X4,X0) )
                | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f38,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( X2 != X3
            | ~ r2_hidden(X2,X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( ( X2 = X3
              & r2_hidden(X2,X0) )
            | r2_hidden(k4_tarski(X2,X3),X1) ) )
     => ( ( sK8(X0,X1) != sK9(X0,X1)
          | ~ r2_hidden(sK8(X0,X1),X0)
          | ~ r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1) )
        & ( ( sK8(X0,X1) = sK9(X0,X1)
            & r2_hidden(sK8(X0,X1),X0) )
          | r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t74_relat_1.p',d10_relat_1)).

fof(f82,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl10_2
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f89,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK3)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl10_4
  <=> r2_hidden(k4_tarski(sK0,sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f59,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t74_relat_1.p',dt_k6_relat_1)).

fof(f41,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ( ~ r2_hidden(k4_tarski(sK0,sK1),sK3)
      | ~ r2_hidden(sK0,sK2)
      | ~ r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(k6_relat_1(sK2),sK3)) )
    & ( ( r2_hidden(k4_tarski(sK0,sK1),sK3)
        & r2_hidden(sK0,sK2) )
      | r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(k6_relat_1(sK2),sK3)) )
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f27,f28])).

fof(f28,plain,
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

fof(f27,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r2_hidden(k4_tarski(X0,X1),X3)
        | ~ r2_hidden(X0,X2)
        | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) )
      & ( ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X0,X2) )
        | r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) )
      & v1_relat_1(X3) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r2_hidden(k4_tarski(X0,X1),X3)
        | ~ r2_hidden(X0,X2)
        | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) )
      & ( ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X0,X2) )
        | r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) )
      & v1_relat_1(X3) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      <~> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X0,X2) ) )
      & v1_relat_1(X3) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
        <=> ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X0,X2) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X0,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t74_relat_1.p',t74_relat_1)).

fof(f572,plain,
    ( ~ spl10_0
    | spl10_3 ),
    inference(avatar_contradiction_clause,[],[f571])).

fof(f571,plain,
    ( $false
    | ~ spl10_0
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f358,f79])).

fof(f79,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl10_3
  <=> ~ r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f358,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl10_0 ),
    inference(unit_resulting_resolution,[],[f165,f129])).

fof(f129,plain,(
    ! [X4,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X5),k6_relat_1(X0))
      | r2_hidden(X4,X0) ) ),
    inference(subsumption_resolution,[],[f66,f59])).

fof(f66,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(k4_tarski(X4,X5),k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f165,plain,
    ( r2_hidden(k4_tarski(sK0,sK7(k6_relat_1(sK2),sK3,sK0,sK1)),k6_relat_1(sK2))
    | ~ spl10_0 ),
    inference(unit_resulting_resolution,[],[f41,f59,f76,f69])).

fof(f69,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK7(X0,X1,X7,X8)),X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) ) ),
    inference(global_subsumption,[],[f46,f62])).

fof(f62,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK7(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK7(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f76,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(k6_relat_1(sK2),sK3))
    | ~ spl10_0 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl10_0
  <=> r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(k6_relat_1(sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_0])])).

fof(f562,plain,
    ( ~ spl10_0
    | ~ spl10_2 ),
    inference(avatar_contradiction_clause,[],[f561])).

fof(f561,plain,
    ( $false
    | ~ spl10_0
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f560,f41])).

fof(f560,plain,
    ( ~ v1_relat_1(sK3)
    | ~ spl10_0
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f559,f59])).

fof(f559,plain,
    ( ~ v1_relat_1(k6_relat_1(sK2))
    | ~ v1_relat_1(sK3)
    | ~ spl10_0
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f558,f76])).

fof(f558,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(k6_relat_1(sK2),sK3))
    | ~ v1_relat_1(k6_relat_1(sK2))
    | ~ v1_relat_1(sK3)
    | ~ spl10_0
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f555,f92])).

fof(f92,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),sK3)
    | ~ spl10_0
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f91,f76])).

fof(f91,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),sK3)
    | ~ r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(k6_relat_1(sK2),sK3))
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f44,f82])).

fof(f44,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),sK3)
    | ~ r2_hidden(sK0,sK2)
    | ~ r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(k6_relat_1(sK2),sK3)) ),
    inference(cnf_transformation,[],[f29])).

fof(f555,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK3)
    | ~ r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(k6_relat_1(sK2),sK3))
    | ~ v1_relat_1(k6_relat_1(sK2))
    | ~ v1_relat_1(sK3)
    | ~ spl10_0 ),
    inference(superposition,[],[f68,f359])).

fof(f359,plain,
    ( sK0 = sK7(k6_relat_1(sK2),sK3,sK0,sK1)
    | ~ spl10_0 ),
    inference(unit_resulting_resolution,[],[f165,f110])).

fof(f110,plain,(
    ! [X4,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X5),k6_relat_1(X0))
      | X4 = X5 ) ),
    inference(subsumption_resolution,[],[f65,f59])).

fof(f65,plain,(
    ! [X4,X0,X5] :
      ( X4 = X5
      | ~ r2_hidden(k4_tarski(X4,X5),k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X4,X0,X5,X1] :
      ( X4 = X5
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f68,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK7(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1) ) ),
    inference(global_subsumption,[],[f46,f61])).

fof(f61,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK7(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK7(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f90,plain,
    ( spl10_0
    | spl10_4 ),
    inference(avatar_split_clause,[],[f43,f88,f75])).

fof(f43,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK3)
    | r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(k6_relat_1(sK2),sK3)) ),
    inference(cnf_transformation,[],[f29])).

fof(f83,plain,
    ( spl10_0
    | spl10_2 ),
    inference(avatar_split_clause,[],[f42,f81,f75])).

fof(f42,plain,
    ( r2_hidden(sK0,sK2)
    | r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(k6_relat_1(sK2),sK3)) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
