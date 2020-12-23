%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:23 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 209 expanded)
%              Number of leaves         :   21 (  77 expanded)
%              Depth                    :   17
%              Number of atoms          :  382 ( 985 expanded)
%              Number of equality atoms :   40 ( 155 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f530,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f109,f504,f529])).

fof(f529,plain,(
    ~ spl14_1 ),
    inference(avatar_contradiction_clause,[],[f528])).

fof(f528,plain,
    ( $false
    | ~ spl14_1 ),
    inference(subsumption_resolution,[],[f527,f40])).

fof(f40,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(sK1,sK0))
    & r1_tarski(k1_relat_1(sK0),k2_relat_1(sK1))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f15,f14])).

fof(f14,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,X0))
            & r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(X1,sK0))
          & r1_tarski(k1_relat_1(sK0),k2_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X1] :
        ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(X1,sK0))
        & r1_tarski(k1_relat_1(sK0),k2_relat_1(X1))
        & v1_relat_1(X1) )
   => ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(sK1,sK0))
      & r1_tarski(k1_relat_1(sK0),k2_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,X0))
          & r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,X0))
          & r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
             => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

fof(f527,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl14_1 ),
    inference(subsumption_resolution,[],[f526,f39])).

fof(f39,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f526,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl14_1 ),
    inference(subsumption_resolution,[],[f514,f508])).

fof(f508,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,sK7(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),sK0)
    | ~ spl14_1 ),
    inference(subsumption_resolution,[],[f506,f69])).

fof(f69,plain,(
    ~ sQ13_eqProxy(k2_relat_1(sK0),k2_relat_1(k5_relat_1(sK1,sK0))) ),
    inference(equality_proxy_replacement,[],[f42,f68])).

fof(f68,plain,(
    ! [X1,X0] :
      ( sQ13_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ13_eqProxy])])).

fof(f42,plain,(
    k2_relat_1(sK0) != k2_relat_1(k5_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f506,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK7(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),sK0)
        | sQ13_eqProxy(k2_relat_1(sK0),k2_relat_1(k5_relat_1(sK1,sK0))) )
    | ~ spl14_1 ),
    inference(resolution,[],[f104,f73])).

fof(f73,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(sK7(X0,X1),X1)
      | ~ r2_hidden(k4_tarski(X3,sK7(X0,X1)),X0)
      | sQ13_eqProxy(k2_relat_1(X0),X1) ) ),
    inference(equality_proxy_replacement,[],[f56,f68])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( k2_relat_1(X0) = X1
      | ~ r2_hidden(k4_tarski(X3,sK7(X0,X1)),X0)
      | ~ r2_hidden(sK7(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK7(X0,X1)),X0)
            | ~ r2_hidden(sK7(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0)
            | r2_hidden(sK7(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK9(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f28,f31,f30,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK7(X0,X1)),X0)
          | ~ r2_hidden(sK7(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK7(X0,X1)),X0)
          | r2_hidden(sK7(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK7(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK9(X0,X5),X5),X0) ) ),
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f104,plain,
    ( r2_hidden(sK7(sK0,k2_relat_1(k5_relat_1(sK1,sK0))),k2_relat_1(k5_relat_1(sK1,sK0)))
    | ~ spl14_1 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl14_1
  <=> r2_hidden(sK7(sK0,k2_relat_1(k5_relat_1(sK1,sK0))),k2_relat_1(k5_relat_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_1])])).

fof(f514,plain,
    ( r2_hidden(k4_tarski(sK5(sK1,sK0,sK9(k5_relat_1(sK1,sK0),sK7(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),sK7(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),sK7(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl14_1 ),
    inference(resolution,[],[f505,f79])).

fof(f79,plain,(
    ! [X0,X8,X7,X1] :
      ( ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f62,f43])).

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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f62,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1)
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f18,f21,f20,f19])).

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
              ( ~ r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X1)
              | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0) )
          | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) )
        & ( ? [X6] :
              ( r2_hidden(k4_tarski(X6,sK3(X0,X1,X2)),X1)
              & r2_hidden(k4_tarski(sK2(X0,X1,X2),X6),X0) )
          | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,sK3(X0,X1,X2)),X1)
          & r2_hidden(k4_tarski(sK2(X0,X1,X2),X6),X0) )
     => ( r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X1)
        & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK4(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X1)
          & r2_hidden(k4_tarski(X7,X10),X0) )
     => ( r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0) ) ) ),
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
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f505,plain,
    ( r2_hidden(k4_tarski(sK9(k5_relat_1(sK1,sK0),sK7(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),sK7(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),k5_relat_1(sK1,sK0))
    | ~ spl14_1 ),
    inference(resolution,[],[f104,f65])).

fof(f65,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,k2_relat_1(X0))
      | r2_hidden(k4_tarski(sK9(X0,X5),X5),X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK9(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f504,plain,(
    ~ spl14_2 ),
    inference(avatar_contradiction_clause,[],[f501])).

fof(f501,plain,
    ( $false
    | ~ spl14_2 ),
    inference(resolution,[],[f500,f108])).

fof(f108,plain,
    ( r2_hidden(k4_tarski(sK8(sK0,k2_relat_1(k5_relat_1(sK1,sK0))),sK7(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),sK0)
    | ~ spl14_2 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl14_2
  <=> r2_hidden(k4_tarski(sK8(sK0,k2_relat_1(k5_relat_1(sK1,sK0))),sK7(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_2])])).

fof(f500,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,sK7(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),sK0)
    | ~ spl14_2 ),
    inference(subsumption_resolution,[],[f498,f69])).

fof(f498,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK7(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),sK0)
        | sQ13_eqProxy(k2_relat_1(sK0),k2_relat_1(k5_relat_1(sK1,sK0))) )
    | ~ spl14_2 ),
    inference(resolution,[],[f486,f73])).

fof(f486,plain,
    ( r2_hidden(sK7(sK0,k2_relat_1(k5_relat_1(sK1,sK0))),k2_relat_1(k5_relat_1(sK1,sK0)))
    | ~ spl14_2 ),
    inference(resolution,[],[f477,f64])).

fof(f64,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X6,X5),X0)
      | r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f477,plain,
    ( r2_hidden(k4_tarski(sK9(sK1,sK8(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),sK7(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),k5_relat_1(sK1,sK0))
    | ~ spl14_2 ),
    inference(resolution,[],[f190,f108])).

fof(f190,plain,
    ( ! [X2] :
        ( ~ r2_hidden(k4_tarski(sK8(sK0,k2_relat_1(k5_relat_1(sK1,sK0))),X2),sK0)
        | r2_hidden(k4_tarski(sK9(sK1,sK8(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),X2),k5_relat_1(sK1,sK0)) )
    | ~ spl14_2 ),
    inference(resolution,[],[f184,f119])).

fof(f119,plain,
    ( r2_hidden(k4_tarski(sK9(sK1,sK8(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),sK8(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),sK1)
    | ~ spl14_2 ),
    inference(resolution,[],[f117,f65])).

fof(f117,plain,
    ( r2_hidden(sK8(sK0,k2_relat_1(k5_relat_1(sK1,sK0))),k2_relat_1(sK1))
    | ~ spl14_2 ),
    inference(resolution,[],[f114,f41])).

fof(f41,plain,(
    r1_tarski(k1_relat_1(sK0),k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f114,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(sK0),X0)
        | r2_hidden(sK8(sK0,k2_relat_1(k5_relat_1(sK1,sK0))),X0) )
    | ~ spl14_2 ),
    inference(resolution,[],[f111,f50])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f24,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f111,plain,
    ( r2_hidden(sK8(sK0,k2_relat_1(k5_relat_1(sK1,sK0))),k1_relat_1(sK0))
    | ~ spl14_2 ),
    inference(resolution,[],[f108,f66])).

fof(f66,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X0)
      | r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK10(X0,X1),X3),X0)
            | ~ r2_hidden(sK10(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK10(X0,X1),sK11(X0,X1)),X0)
            | r2_hidden(sK10(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK12(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11,sK12])],[f34,f37,f36,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK10(X0,X1),X3),X0)
          | ~ r2_hidden(sK10(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK10(X0,X1),X4),X0)
          | r2_hidden(sK10(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK10(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK10(X0,X1),sK11(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK12(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f184,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
      | ~ r2_hidden(k4_tarski(X1,X2),sK0)
      | r2_hidden(k4_tarski(X0,X2),k5_relat_1(sK1,sK0)) ) ),
    inference(resolution,[],[f147,f39])).

fof(f147,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ v1_relat_1(X6)
      | ~ r2_hidden(k4_tarski(X7,X4),sK1)
      | ~ r2_hidden(k4_tarski(X4,X5),X6)
      | r2_hidden(k4_tarski(X7,X5),k5_relat_1(sK1,X6)) ) ),
    inference(resolution,[],[f78,f40])).

fof(f78,plain,(
    ! [X0,X8,X7,X1,X9] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | ~ v1_relat_1(X1)
      | r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f61,f43])).

fof(f61,plain,(
    ! [X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),X2)
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f109,plain,
    ( spl14_1
    | spl14_2 ),
    inference(avatar_split_clause,[],[f100,f106,f102])).

fof(f100,plain,
    ( r2_hidden(k4_tarski(sK8(sK0,k2_relat_1(k5_relat_1(sK1,sK0))),sK7(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),sK0)
    | r2_hidden(sK7(sK0,k2_relat_1(k5_relat_1(sK1,sK0))),k2_relat_1(k5_relat_1(sK1,sK0))) ),
    inference(resolution,[],[f74,f69])).

fof(f74,plain,(
    ! [X0,X1] :
      ( sQ13_eqProxy(k2_relat_1(X0),X1)
      | r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0)
      | r2_hidden(sK7(X0,X1),X1) ) ),
    inference(equality_proxy_replacement,[],[f55,f68])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0)
      | r2_hidden(sK7(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:25:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (11993)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.50  % (11985)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.50  % (11983)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (11978)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.50  % (11977)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.50  % (11999)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.51  % (11973)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (11993)Refutation not found, incomplete strategy% (11993)------------------------------
% 0.21/0.51  % (11993)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (11993)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (11993)Memory used [KB]: 10746
% 0.21/0.51  % (11993)Time elapsed: 0.059 s
% 0.21/0.51  % (11993)------------------------------
% 0.21/0.51  % (11993)------------------------------
% 0.21/0.51  % (11975)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (11991)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  % (11979)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (11990)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (11981)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (11988)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (11998)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (11973)Refutation not found, incomplete strategy% (11973)------------------------------
% 0.21/0.53  % (11973)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (11973)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (11973)Memory used [KB]: 10746
% 0.21/0.53  % (11973)Time elapsed: 0.128 s
% 0.21/0.53  % (11973)------------------------------
% 0.21/0.53  % (11973)------------------------------
% 0.21/0.53  % (11974)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (11972)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (11980)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (12000)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (11994)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (11992)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (11984)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (11971)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (11976)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (11987)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (11996)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (11995)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (11986)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (11997)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (11982)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (11989)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.57  % (11988)Refutation found. Thanks to Tanya!
% 0.21/0.57  % SZS status Theorem for theBenchmark
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f530,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(avatar_sat_refutation,[],[f109,f504,f529])).
% 0.21/0.57  fof(f529,plain,(
% 0.21/0.57    ~spl14_1),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f528])).
% 0.21/0.57  fof(f528,plain,(
% 0.21/0.57    $false | ~spl14_1),
% 0.21/0.57    inference(subsumption_resolution,[],[f527,f40])).
% 0.21/0.57  fof(f40,plain,(
% 0.21/0.57    v1_relat_1(sK1)),
% 0.21/0.57    inference(cnf_transformation,[],[f16])).
% 0.21/0.57  fof(f16,plain,(
% 0.21/0.57    (k2_relat_1(sK0) != k2_relat_1(k5_relat_1(sK1,sK0)) & r1_tarski(k1_relat_1(sK0),k2_relat_1(sK1)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f15,f14])).
% 0.21/0.57  fof(f14,plain,(
% 0.21/0.57    ? [X0] : (? [X1] : (k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,X0)) & r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (k2_relat_1(sK0) != k2_relat_1(k5_relat_1(X1,sK0)) & r1_tarski(k1_relat_1(sK0),k2_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f15,plain,(
% 0.21/0.57    ? [X1] : (k2_relat_1(sK0) != k2_relat_1(k5_relat_1(X1,sK0)) & r1_tarski(k1_relat_1(sK0),k2_relat_1(X1)) & v1_relat_1(X1)) => (k2_relat_1(sK0) != k2_relat_1(k5_relat_1(sK1,sK0)) & r1_tarski(k1_relat_1(sK0),k2_relat_1(sK1)) & v1_relat_1(sK1))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f9,plain,(
% 0.21/0.57    ? [X0] : (? [X1] : (k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,X0)) & r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.57    inference(flattening,[],[f8])).
% 0.21/0.57  fof(f8,plain,(
% 0.21/0.57    ? [X0] : (? [X1] : ((k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,X0)) & r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f7])).
% 0.21/0.57  fof(f7,negated_conjecture,(
% 0.21/0.57    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)))))),
% 0.21/0.57    inference(negated_conjecture,[],[f6])).
% 0.21/0.57  fof(f6,conjecture,(
% 0.21/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).
% 0.21/0.57  fof(f527,plain,(
% 0.21/0.57    ~v1_relat_1(sK1) | ~spl14_1),
% 0.21/0.57    inference(subsumption_resolution,[],[f526,f39])).
% 0.21/0.57  fof(f39,plain,(
% 0.21/0.57    v1_relat_1(sK0)),
% 0.21/0.57    inference(cnf_transformation,[],[f16])).
% 0.21/0.57  fof(f526,plain,(
% 0.21/0.57    ~v1_relat_1(sK0) | ~v1_relat_1(sK1) | ~spl14_1),
% 0.21/0.57    inference(subsumption_resolution,[],[f514,f508])).
% 0.21/0.57  fof(f508,plain,(
% 0.21/0.57    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK7(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),sK0)) ) | ~spl14_1),
% 0.21/0.57    inference(subsumption_resolution,[],[f506,f69])).
% 0.21/0.57  fof(f69,plain,(
% 0.21/0.57    ~sQ13_eqProxy(k2_relat_1(sK0),k2_relat_1(k5_relat_1(sK1,sK0)))),
% 0.21/0.57    inference(equality_proxy_replacement,[],[f42,f68])).
% 0.21/0.57  fof(f68,plain,(
% 0.21/0.57    ! [X1,X0] : (sQ13_eqProxy(X0,X1) <=> X0 = X1)),
% 0.21/0.57    introduced(equality_proxy_definition,[new_symbols(naming,[sQ13_eqProxy])])).
% 0.21/0.57  fof(f42,plain,(
% 0.21/0.57    k2_relat_1(sK0) != k2_relat_1(k5_relat_1(sK1,sK0))),
% 0.21/0.57    inference(cnf_transformation,[],[f16])).
% 0.21/0.57  fof(f506,plain,(
% 0.21/0.57    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK7(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),sK0) | sQ13_eqProxy(k2_relat_1(sK0),k2_relat_1(k5_relat_1(sK1,sK0)))) ) | ~spl14_1),
% 0.21/0.57    inference(resolution,[],[f104,f73])).
% 0.21/0.57  fof(f73,plain,(
% 0.21/0.57    ( ! [X0,X3,X1] : (~r2_hidden(sK7(X0,X1),X1) | ~r2_hidden(k4_tarski(X3,sK7(X0,X1)),X0) | sQ13_eqProxy(k2_relat_1(X0),X1)) )),
% 0.21/0.57    inference(equality_proxy_replacement,[],[f56,f68])).
% 0.21/0.57  fof(f56,plain,(
% 0.21/0.57    ( ! [X0,X3,X1] : (k2_relat_1(X0) = X1 | ~r2_hidden(k4_tarski(X3,sK7(X0,X1)),X0) | ~r2_hidden(sK7(X0,X1),X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f32])).
% 0.21/0.57  fof(f32,plain,(
% 0.21/0.57    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK7(X0,X1)),X0) | ~r2_hidden(sK7(X0,X1),X1)) & (r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0) | r2_hidden(sK7(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK9(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f28,f31,f30,f29])).
% 0.21/0.57  fof(f29,plain,(
% 0.21/0.57    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK7(X0,X1)),X0) | ~r2_hidden(sK7(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK7(X0,X1)),X0) | r2_hidden(sK7(X0,X1),X1))))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f30,plain,(
% 0.21/0.57    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK7(X0,X1)),X0) => r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f31,plain,(
% 0.21/0.57    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK9(X0,X5),X5),X0))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f28,plain,(
% 0.21/0.57    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.21/0.57    inference(rectify,[],[f27])).
% 0.21/0.57  fof(f27,plain,(
% 0.21/0.57    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 0.21/0.57    inference(nnf_transformation,[],[f3])).
% 0.21/0.57  fof(f3,axiom,(
% 0.21/0.57    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 0.21/0.57  fof(f104,plain,(
% 0.21/0.57    r2_hidden(sK7(sK0,k2_relat_1(k5_relat_1(sK1,sK0))),k2_relat_1(k5_relat_1(sK1,sK0))) | ~spl14_1),
% 0.21/0.57    inference(avatar_component_clause,[],[f102])).
% 0.21/0.57  fof(f102,plain,(
% 0.21/0.57    spl14_1 <=> r2_hidden(sK7(sK0,k2_relat_1(k5_relat_1(sK1,sK0))),k2_relat_1(k5_relat_1(sK1,sK0)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl14_1])])).
% 0.21/0.57  fof(f514,plain,(
% 0.21/0.57    r2_hidden(k4_tarski(sK5(sK1,sK0,sK9(k5_relat_1(sK1,sK0),sK7(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),sK7(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),sK7(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),sK0) | ~v1_relat_1(sK0) | ~v1_relat_1(sK1) | ~spl14_1),
% 0.21/0.57    inference(resolution,[],[f505,f79])).
% 0.21/0.57  fof(f79,plain,(
% 0.21/0.57    ( ! [X0,X8,X7,X1] : (~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f62,f43])).
% 0.21/0.57  fof(f43,plain,(
% 0.21/0.57    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f11])).
% 0.21/0.57  fof(f11,plain,(
% 0.21/0.57    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(flattening,[],[f10])).
% 0.21/0.57  fof(f10,plain,(
% 0.21/0.57    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f5])).
% 0.21/0.57  fof(f5,axiom,(
% 0.21/0.57    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.21/0.57  fof(f62,plain,(
% 0.21/0.57    ( ! [X0,X8,X7,X1] : (r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1) | ~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.57    inference(equality_resolution,[],[f45])).
% 0.21/0.57  fof(f45,plain,(
% 0.21/0.57    ( ! [X2,X0,X8,X7,X1] : (r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1) | ~r2_hidden(k4_tarski(X7,X8),X2) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f22])).
% 0.21/0.57  fof(f22,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ((! [X5] : (~r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK4(X0,X1,X2)),X0)) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & ((r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f18,f21,f20,f19])).
% 0.21/0.57  fof(f19,plain,(
% 0.21/0.57    ! [X2,X1,X0] : (? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((! [X5] : (~r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,sK3(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),X6),X0)) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2))))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f20,plain,(
% 0.21/0.57    ! [X2,X1,X0] : (? [X6] : (r2_hidden(k4_tarski(X6,sK3(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),X6),X0)) => (r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK4(X0,X1,X2)),X0)))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f21,plain,(
% 0.21/0.57    ! [X8,X7,X1,X0] : (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) => (r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0)))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.58  fof(f18,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.58    inference(rectify,[],[f17])).
% 0.21/0.58  fof(f17,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0))) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.58    inference(nnf_transformation,[],[f12])).
% 0.21/0.58  fof(f12,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : (! [X2] : ((k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.58    inference(ennf_transformation,[],[f4])).
% 0.21/0.58  fof(f4,axiom,(
% 0.21/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))))))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).
% 0.21/0.58  fof(f505,plain,(
% 0.21/0.58    r2_hidden(k4_tarski(sK9(k5_relat_1(sK1,sK0),sK7(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),sK7(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),k5_relat_1(sK1,sK0)) | ~spl14_1),
% 0.21/0.58    inference(resolution,[],[f104,f65])).
% 0.21/0.58  fof(f65,plain,(
% 0.21/0.58    ( ! [X0,X5] : (~r2_hidden(X5,k2_relat_1(X0)) | r2_hidden(k4_tarski(sK9(X0,X5),X5),X0)) )),
% 0.21/0.58    inference(equality_resolution,[],[f53])).
% 0.21/0.58  fof(f53,plain,(
% 0.21/0.58    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK9(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 0.21/0.58    inference(cnf_transformation,[],[f32])).
% 0.21/0.58  fof(f504,plain,(
% 0.21/0.58    ~spl14_2),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f501])).
% 0.21/0.58  fof(f501,plain,(
% 0.21/0.58    $false | ~spl14_2),
% 0.21/0.58    inference(resolution,[],[f500,f108])).
% 0.21/0.58  fof(f108,plain,(
% 0.21/0.58    r2_hidden(k4_tarski(sK8(sK0,k2_relat_1(k5_relat_1(sK1,sK0))),sK7(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),sK0) | ~spl14_2),
% 0.21/0.58    inference(avatar_component_clause,[],[f106])).
% 0.21/0.58  fof(f106,plain,(
% 0.21/0.58    spl14_2 <=> r2_hidden(k4_tarski(sK8(sK0,k2_relat_1(k5_relat_1(sK1,sK0))),sK7(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),sK0)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl14_2])])).
% 0.21/0.58  fof(f500,plain,(
% 0.21/0.58    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK7(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),sK0)) ) | ~spl14_2),
% 0.21/0.58    inference(subsumption_resolution,[],[f498,f69])).
% 0.21/0.58  fof(f498,plain,(
% 0.21/0.58    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK7(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),sK0) | sQ13_eqProxy(k2_relat_1(sK0),k2_relat_1(k5_relat_1(sK1,sK0)))) ) | ~spl14_2),
% 0.21/0.58    inference(resolution,[],[f486,f73])).
% 0.21/0.58  fof(f486,plain,(
% 0.21/0.58    r2_hidden(sK7(sK0,k2_relat_1(k5_relat_1(sK1,sK0))),k2_relat_1(k5_relat_1(sK1,sK0))) | ~spl14_2),
% 0.21/0.58    inference(resolution,[],[f477,f64])).
% 0.21/0.58  fof(f64,plain,(
% 0.21/0.58    ( ! [X6,X0,X5] : (~r2_hidden(k4_tarski(X6,X5),X0) | r2_hidden(X5,k2_relat_1(X0))) )),
% 0.21/0.58    inference(equality_resolution,[],[f54])).
% 0.21/0.58  fof(f54,plain,(
% 0.21/0.58    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 0.21/0.58    inference(cnf_transformation,[],[f32])).
% 0.21/0.58  fof(f477,plain,(
% 0.21/0.58    r2_hidden(k4_tarski(sK9(sK1,sK8(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),sK7(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),k5_relat_1(sK1,sK0)) | ~spl14_2),
% 0.21/0.58    inference(resolution,[],[f190,f108])).
% 0.21/0.58  fof(f190,plain,(
% 0.21/0.58    ( ! [X2] : (~r2_hidden(k4_tarski(sK8(sK0,k2_relat_1(k5_relat_1(sK1,sK0))),X2),sK0) | r2_hidden(k4_tarski(sK9(sK1,sK8(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),X2),k5_relat_1(sK1,sK0))) ) | ~spl14_2),
% 0.21/0.58    inference(resolution,[],[f184,f119])).
% 0.21/0.58  fof(f119,plain,(
% 0.21/0.58    r2_hidden(k4_tarski(sK9(sK1,sK8(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),sK8(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),sK1) | ~spl14_2),
% 0.21/0.58    inference(resolution,[],[f117,f65])).
% 0.21/0.58  fof(f117,plain,(
% 0.21/0.58    r2_hidden(sK8(sK0,k2_relat_1(k5_relat_1(sK1,sK0))),k2_relat_1(sK1)) | ~spl14_2),
% 0.21/0.58    inference(resolution,[],[f114,f41])).
% 0.21/0.58  fof(f41,plain,(
% 0.21/0.58    r1_tarski(k1_relat_1(sK0),k2_relat_1(sK1))),
% 0.21/0.58    inference(cnf_transformation,[],[f16])).
% 0.21/0.58  fof(f114,plain,(
% 0.21/0.58    ( ! [X0] : (~r1_tarski(k1_relat_1(sK0),X0) | r2_hidden(sK8(sK0,k2_relat_1(k5_relat_1(sK1,sK0))),X0)) ) | ~spl14_2),
% 0.21/0.58    inference(resolution,[],[f111,f50])).
% 0.21/0.58  fof(f50,plain,(
% 0.21/0.58    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f26])).
% 0.21/0.58  fof(f26,plain,(
% 0.21/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f24,f25])).
% 0.21/0.58  fof(f25,plain,(
% 0.21/0.58    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 0.21/0.58    introduced(choice_axiom,[])).
% 0.21/0.58  fof(f24,plain,(
% 0.21/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.58    inference(rectify,[],[f23])).
% 0.21/0.58  fof(f23,plain,(
% 0.21/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.58    inference(nnf_transformation,[],[f13])).
% 0.21/0.58  fof(f13,plain,(
% 0.21/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f1])).
% 0.21/0.58  fof(f1,axiom,(
% 0.21/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.58  fof(f111,plain,(
% 0.21/0.58    r2_hidden(sK8(sK0,k2_relat_1(k5_relat_1(sK1,sK0))),k1_relat_1(sK0)) | ~spl14_2),
% 0.21/0.58    inference(resolution,[],[f108,f66])).
% 0.21/0.58  fof(f66,plain,(
% 0.21/0.58    ( ! [X6,X0,X5] : (~r2_hidden(k4_tarski(X5,X6),X0) | r2_hidden(X5,k1_relat_1(X0))) )),
% 0.21/0.58    inference(equality_resolution,[],[f58])).
% 0.21/0.58  fof(f58,plain,(
% 0.21/0.58    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 0.21/0.58    inference(cnf_transformation,[],[f38])).
% 1.84/0.60  fof(f38,plain,(
% 1.84/0.60    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK10(X0,X1),X3),X0) | ~r2_hidden(sK10(X0,X1),X1)) & (r2_hidden(k4_tarski(sK10(X0,X1),sK11(X0,X1)),X0) | r2_hidden(sK10(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK12(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 1.84/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11,sK12])],[f34,f37,f36,f35])).
% 1.84/0.60  fof(f35,plain,(
% 1.84/0.60    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK10(X0,X1),X3),X0) | ~r2_hidden(sK10(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK10(X0,X1),X4),X0) | r2_hidden(sK10(X0,X1),X1))))),
% 1.84/0.60    introduced(choice_axiom,[])).
% 1.84/0.60  fof(f36,plain,(
% 1.84/0.60    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK10(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK10(X0,X1),sK11(X0,X1)),X0))),
% 1.84/0.60    introduced(choice_axiom,[])).
% 1.84/0.60  fof(f37,plain,(
% 1.84/0.60    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK12(X0,X5)),X0))),
% 1.84/0.60    introduced(choice_axiom,[])).
% 1.84/0.60  fof(f34,plain,(
% 1.84/0.60    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 1.84/0.60    inference(rectify,[],[f33])).
% 1.84/0.60  fof(f33,plain,(
% 1.84/0.60    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 1.84/0.60    inference(nnf_transformation,[],[f2])).
% 1.84/0.60  fof(f2,axiom,(
% 1.84/0.60    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 1.84/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 1.84/0.60  fof(f184,plain,(
% 1.84/0.60    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK1) | ~r2_hidden(k4_tarski(X1,X2),sK0) | r2_hidden(k4_tarski(X0,X2),k5_relat_1(sK1,sK0))) )),
% 1.84/0.60    inference(resolution,[],[f147,f39])).
% 1.84/0.60  fof(f147,plain,(
% 1.84/0.60    ( ! [X6,X4,X7,X5] : (~v1_relat_1(X6) | ~r2_hidden(k4_tarski(X7,X4),sK1) | ~r2_hidden(k4_tarski(X4,X5),X6) | r2_hidden(k4_tarski(X7,X5),k5_relat_1(sK1,X6))) )),
% 1.84/0.60    inference(resolution,[],[f78,f40])).
% 1.84/0.60  fof(f78,plain,(
% 1.84/0.60    ( ! [X0,X8,X7,X1,X9] : (~v1_relat_1(X0) | ~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0) | ~v1_relat_1(X1) | r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))) )),
% 1.84/0.60    inference(subsumption_resolution,[],[f61,f43])).
% 1.84/0.60  fof(f61,plain,(
% 1.84/0.60    ( ! [X0,X8,X7,X1,X9] : (r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.84/0.60    inference(equality_resolution,[],[f46])).
% 1.84/0.60  fof(f46,plain,(
% 1.84/0.60    ( ! [X2,X0,X8,X7,X1,X9] : (r2_hidden(k4_tarski(X7,X8),X2) | ~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.84/0.60    inference(cnf_transformation,[],[f22])).
% 1.84/0.60  fof(f109,plain,(
% 1.84/0.60    spl14_1 | spl14_2),
% 1.84/0.60    inference(avatar_split_clause,[],[f100,f106,f102])).
% 1.84/0.60  fof(f100,plain,(
% 1.84/0.60    r2_hidden(k4_tarski(sK8(sK0,k2_relat_1(k5_relat_1(sK1,sK0))),sK7(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),sK0) | r2_hidden(sK7(sK0,k2_relat_1(k5_relat_1(sK1,sK0))),k2_relat_1(k5_relat_1(sK1,sK0)))),
% 1.84/0.60    inference(resolution,[],[f74,f69])).
% 1.84/0.60  fof(f74,plain,(
% 1.84/0.60    ( ! [X0,X1] : (sQ13_eqProxy(k2_relat_1(X0),X1) | r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0) | r2_hidden(sK7(X0,X1),X1)) )),
% 1.84/0.60    inference(equality_proxy_replacement,[],[f55,f68])).
% 1.84/0.60  fof(f55,plain,(
% 1.84/0.60    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0) | r2_hidden(sK7(X0,X1),X1)) )),
% 1.84/0.60    inference(cnf_transformation,[],[f32])).
% 1.84/0.60  % SZS output end Proof for theBenchmark
% 1.84/0.60  % (11988)------------------------------
% 1.84/0.60  % (11988)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.84/0.60  % (11988)Termination reason: Refutation
% 1.84/0.60  
% 1.84/0.60  % (11988)Memory used [KB]: 11513
% 1.84/0.60  % (11988)Time elapsed: 0.167 s
% 1.84/0.60  % (11988)------------------------------
% 1.84/0.60  % (11988)------------------------------
% 1.84/0.60  % (11970)Success in time 0.242 s
%------------------------------------------------------------------------------
