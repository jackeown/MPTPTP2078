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

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 260 expanded)
%              Number of leaves         :   18 (  91 expanded)
%              Depth                    :   20
%              Number of atoms          :  382 (1207 expanded)
%              Number of equality atoms :   32 ( 172 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f293,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f98,f270,f291])).

fof(f291,plain,(
    ~ spl11_1 ),
    inference(avatar_contradiction_clause,[],[f290])).

fof(f290,plain,
    ( $false
    | ~ spl11_1 ),
    inference(subsumption_resolution,[],[f289,f36])).

fof(f36,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(sK1,sK0))
    & r1_tarski(k1_relat_1(sK0),k2_relat_1(sK1))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f17,f16])).

fof(f16,plain,
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

fof(f17,plain,
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

fof(f289,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl11_1 ),
    inference(subsumption_resolution,[],[f288,f35])).

fof(f35,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f288,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl11_1 ),
    inference(subsumption_resolution,[],[f280,f274])).

fof(f274,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,sK2(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),sK0)
    | ~ spl11_1 ),
    inference(subsumption_resolution,[],[f272,f61])).

fof(f61,plain,(
    ~ sQ10_eqProxy(k2_relat_1(sK0),k2_relat_1(k5_relat_1(sK1,sK0))) ),
    inference(equality_proxy_replacement,[],[f38,f60])).

fof(f60,plain,(
    ! [X1,X0] :
      ( sQ10_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ10_eqProxy])])).

fof(f38,plain,(
    k2_relat_1(sK0) != k2_relat_1(k5_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f272,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK2(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),sK0)
        | sQ10_eqProxy(k2_relat_1(sK0),k2_relat_1(k5_relat_1(sK1,sK0))) )
    | ~ spl11_1 ),
    inference(resolution,[],[f93,f62])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | ~ r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0)
      | sQ10_eqProxy(k2_relat_1(X0),X1) ) ),
    inference(equality_proxy_replacement,[],[f42,f60])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( k2_relat_1(X0) = X1
      | ~ r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0)
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK4(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f20,f23,f22,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK2(X0,X1)),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK2(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK4(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
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
    inference(rectify,[],[f19])).

fof(f19,plain,(
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

fof(f93,plain,
    ( r2_hidden(sK2(sK0,k2_relat_1(k5_relat_1(sK1,sK0))),k2_relat_1(k5_relat_1(sK1,sK0)))
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl11_1
  <=> r2_hidden(sK2(sK0,k2_relat_1(k5_relat_1(sK1,sK0))),k2_relat_1(k5_relat_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f280,plain,
    ( r2_hidden(k4_tarski(sK8(sK1,sK0,sK4(k5_relat_1(sK1,sK0),sK2(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),sK2(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),sK2(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl11_1 ),
    inference(resolution,[],[f271,f108])).

fof(f108,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
      | r2_hidden(k4_tarski(sK8(X2,X3,X0,X1),X1),X3)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f107])).

fof(f107,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
      | r2_hidden(k4_tarski(sK8(X2,X3,X0,X1),X1),X3)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f58,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
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

fof(f58,plain,(
    ! [X0,X8,X7,X1] :
      ( ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | r2_hidden(k4_tarski(sK8(X0,X1,X7,X8),X8),X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK8(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ( ( ! [X5] :
                          ( ~ r2_hidden(k4_tarski(X5,sK6(X0,X1,X2)),X1)
                          | ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),X5),X0) )
                      | ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2) )
                    & ( ( r2_hidden(k4_tarski(sK7(X0,X1,X2),sK6(X0,X1,X2)),X1)
                        & r2_hidden(k4_tarski(sK5(X0,X1,X2),sK7(X0,X1,X2)),X0) )
                      | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ( r2_hidden(k4_tarski(sK8(X0,X1,X7,X8),X8),X1)
                          & r2_hidden(k4_tarski(X7,sK8(X0,X1,X7,X8)),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f26,f29,f28,f27])).

fof(f27,plain,(
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
              ( ~ r2_hidden(k4_tarski(X5,sK6(X0,X1,X2)),X1)
              | ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),X5),X0) )
          | ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2) )
        & ( ? [X6] :
              ( r2_hidden(k4_tarski(X6,sK6(X0,X1,X2)),X1)
              & r2_hidden(k4_tarski(sK5(X0,X1,X2),X6),X0) )
          | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,sK6(X0,X1,X2)),X1)
          & r2_hidden(k4_tarski(sK5(X0,X1,X2),X6),X0) )
     => ( r2_hidden(k4_tarski(sK7(X0,X1,X2),sK6(X0,X1,X2)),X1)
        & r2_hidden(k4_tarski(sK5(X0,X1,X2),sK7(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X1)
          & r2_hidden(k4_tarski(X7,X10),X0) )
     => ( r2_hidden(k4_tarski(sK8(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK8(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
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

fof(f271,plain,
    ( r2_hidden(k4_tarski(sK4(k5_relat_1(sK1,sK0),sK2(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),sK2(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),k5_relat_1(sK1,sK0))
    | ~ spl11_1 ),
    inference(resolution,[],[f93,f56])).

fof(f56,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,k2_relat_1(X0))
      | r2_hidden(k4_tarski(sK4(X0,X5),X5),X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f270,plain,(
    ~ spl11_2 ),
    inference(avatar_contradiction_clause,[],[f267])).

fof(f267,plain,
    ( $false
    | ~ spl11_2 ),
    inference(resolution,[],[f266,f103])).

fof(f103,plain,
    ( r2_hidden(k4_tarski(sK4(sK0,sK2(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),sK2(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),sK0)
    | ~ spl11_2 ),
    inference(resolution,[],[f101,f56])).

fof(f101,plain,
    ( r2_hidden(sK2(sK0,k2_relat_1(k5_relat_1(sK1,sK0))),k2_relat_1(sK0))
    | ~ spl11_2 ),
    inference(resolution,[],[f97,f55])).

fof(f55,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X6,X5),X0)
      | r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f97,plain,
    ( r2_hidden(k4_tarski(sK3(sK0,k2_relat_1(k5_relat_1(sK1,sK0))),sK2(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),sK0)
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl11_2
  <=> r2_hidden(k4_tarski(sK3(sK0,k2_relat_1(k5_relat_1(sK1,sK0))),sK2(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f266,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,sK2(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),sK0)
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f264,f61])).

fof(f264,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK2(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),sK0)
        | sQ10_eqProxy(k2_relat_1(sK0),k2_relat_1(k5_relat_1(sK1,sK0))) )
    | ~ spl11_2 ),
    inference(resolution,[],[f232,f62])).

fof(f232,plain,
    ( r2_hidden(sK2(sK0,k2_relat_1(k5_relat_1(sK1,sK0))),k2_relat_1(k5_relat_1(sK1,sK0)))
    | ~ spl11_2 ),
    inference(resolution,[],[f226,f55])).

fof(f226,plain,
    ( r2_hidden(k4_tarski(sK4(sK1,sK3(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),sK2(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),k5_relat_1(sK1,sK0))
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f225,f35])).

fof(f225,plain,
    ( ~ v1_relat_1(sK0)
    | r2_hidden(k4_tarski(sK4(sK1,sK3(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),sK2(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),k5_relat_1(sK1,sK0))
    | ~ spl11_2 ),
    inference(resolution,[],[f161,f97])).

fof(f161,plain,
    ( ! [X6,X7] :
        ( ~ r2_hidden(k4_tarski(sK3(sK0,k2_relat_1(k5_relat_1(sK1,sK0))),X6),X7)
        | ~ v1_relat_1(X7)
        | r2_hidden(k4_tarski(sK4(sK1,sK3(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),X6),k5_relat_1(sK1,X7)) )
    | ~ spl11_2 ),
    inference(resolution,[],[f154,f114])).

fof(f114,plain,
    ( r2_hidden(k4_tarski(sK4(sK1,sK3(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),sK3(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),sK1)
    | ~ spl11_2 ),
    inference(resolution,[],[f113,f56])).

fof(f113,plain,
    ( r2_hidden(sK3(sK0,k2_relat_1(k5_relat_1(sK1,sK0))),k2_relat_1(sK1))
    | ~ spl11_2 ),
    inference(resolution,[],[f111,f69])).

fof(f69,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f52,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK9(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK9(X0,X1),X1)
          & r2_hidden(sK9(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f32,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK9(X0,X1),X1)
        & r2_hidden(sK9(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
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

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK9(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f111,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK1),X0)
        | r2_hidden(sK3(sK0,k2_relat_1(k5_relat_1(sK1,sK0))),X0) )
    | ~ spl11_2 ),
    inference(resolution,[],[f109,f37])).

fof(f37,plain,(
    r1_tarski(k1_relat_1(sK0),k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f109,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_relat_1(sK0),X0)
        | r2_hidden(sK3(sK0,k2_relat_1(k5_relat_1(sK1,sK0))),X1)
        | ~ r1_tarski(X0,X1) )
    | ~ spl11_2 ),
    inference(resolution,[],[f105,f50])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f105,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(sK0,k2_relat_1(k5_relat_1(sK1,sK0))),X0)
        | ~ r1_tarski(k1_relat_1(sK0),X0) )
    | ~ spl11_2 ),
    inference(resolution,[],[f102,f50])).

fof(f102,plain,
    ( r2_hidden(sK3(sK0,k2_relat_1(k5_relat_1(sK1,sK0))),k1_relat_1(sK0))
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f100,f35])).

fof(f100,plain,
    ( r2_hidden(sK3(sK0,k2_relat_1(k5_relat_1(sK1,sK0))),k1_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl11_2 ),
    inference(resolution,[],[f97,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

fof(f154,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X5),sK1)
      | r2_hidden(k4_tarski(X4,X6),k5_relat_1(sK1,X7))
      | ~ v1_relat_1(X7)
      | ~ r2_hidden(k4_tarski(X5,X6),X7) ) ),
    inference(resolution,[],[f127,f36])).

fof(f127,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X4)
      | ~ r2_hidden(k4_tarski(X3,X0),X4)
      | r2_hidden(k4_tarski(X3,X1),k5_relat_1(X4,X2))
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(duplicate_literal_removal,[],[f126])).

fof(f126,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ r2_hidden(k4_tarski(X3,X0),X4)
      | r2_hidden(k4_tarski(X3,X1),k5_relat_1(X4,X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X4)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X4) ) ),
    inference(resolution,[],[f57,f49])).

fof(f57,plain,(
    ! [X0,X8,X7,X1,X9] :
      ( ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),X2)
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f98,plain,
    ( spl11_1
    | spl11_2 ),
    inference(avatar_split_clause,[],[f89,f95,f91])).

fof(f89,plain,
    ( r2_hidden(k4_tarski(sK3(sK0,k2_relat_1(k5_relat_1(sK1,sK0))),sK2(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),sK0)
    | r2_hidden(sK2(sK0,k2_relat_1(k5_relat_1(sK1,sK0))),k2_relat_1(k5_relat_1(sK1,sK0))) ),
    inference(resolution,[],[f63,f61])).

fof(f63,plain,(
    ! [X0,X1] :
      ( sQ10_eqProxy(k2_relat_1(X0),X1)
      | r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0)
      | r2_hidden(sK2(X0,X1),X1) ) ),
    inference(equality_proxy_replacement,[],[f41,f60])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0)
      | r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:10:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.48  % (19067)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.48  % (19046)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.51  % (19044)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (19043)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (19039)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (19042)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % (19066)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.52  % (19041)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (19041)Refutation not found, incomplete strategy% (19041)------------------------------
% 0.20/0.52  % (19041)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (19041)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (19041)Memory used [KB]: 10618
% 0.20/0.52  % (19041)Time elapsed: 0.115 s
% 0.20/0.52  % (19041)------------------------------
% 0.20/0.52  % (19041)------------------------------
% 0.20/0.52  % (19059)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.53  % (19061)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (19040)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (19053)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (19068)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.53  % (19056)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.53  % (19052)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.53  % (19047)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.53  % (19045)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (19061)Refutation not found, incomplete strategy% (19061)------------------------------
% 0.20/0.53  % (19061)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (19061)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (19061)Memory used [KB]: 10746
% 0.20/0.53  % (19061)Time elapsed: 0.095 s
% 0.20/0.53  % (19061)------------------------------
% 0.20/0.53  % (19061)------------------------------
% 0.20/0.53  % (19064)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.53  % (19063)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.54  % (19048)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.54  % (19065)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  % (19062)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.54  % (19060)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.54  % (19049)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.54  % (19054)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.55  % (19058)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.55  % (19057)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.55  % (19055)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.55  % (19051)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.55  % (19050)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.56  % (19056)Refutation found. Thanks to Tanya!
% 0.20/0.56  % SZS status Theorem for theBenchmark
% 0.20/0.56  % SZS output start Proof for theBenchmark
% 0.20/0.56  fof(f293,plain,(
% 0.20/0.56    $false),
% 0.20/0.56    inference(avatar_sat_refutation,[],[f98,f270,f291])).
% 0.20/0.56  fof(f291,plain,(
% 0.20/0.56    ~spl11_1),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f290])).
% 0.20/0.56  fof(f290,plain,(
% 0.20/0.56    $false | ~spl11_1),
% 0.20/0.56    inference(subsumption_resolution,[],[f289,f36])).
% 0.20/0.56  fof(f36,plain,(
% 0.20/0.56    v1_relat_1(sK1)),
% 0.20/0.56    inference(cnf_transformation,[],[f18])).
% 0.20/0.56  fof(f18,plain,(
% 0.20/0.56    (k2_relat_1(sK0) != k2_relat_1(k5_relat_1(sK1,sK0)) & r1_tarski(k1_relat_1(sK0),k2_relat_1(sK1)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.20/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f17,f16])).
% 0.20/0.56  fof(f16,plain,(
% 0.20/0.56    ? [X0] : (? [X1] : (k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,X0)) & r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (k2_relat_1(sK0) != k2_relat_1(k5_relat_1(X1,sK0)) & r1_tarski(k1_relat_1(sK0),k2_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f17,plain,(
% 0.20/0.56    ? [X1] : (k2_relat_1(sK0) != k2_relat_1(k5_relat_1(X1,sK0)) & r1_tarski(k1_relat_1(sK0),k2_relat_1(X1)) & v1_relat_1(X1)) => (k2_relat_1(sK0) != k2_relat_1(k5_relat_1(sK1,sK0)) & r1_tarski(k1_relat_1(sK0),k2_relat_1(sK1)) & v1_relat_1(sK1))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f9,plain,(
% 0.20/0.56    ? [X0] : (? [X1] : (k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,X0)) & r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.20/0.56    inference(flattening,[],[f8])).
% 0.20/0.56  fof(f8,plain,(
% 0.20/0.56    ? [X0] : (? [X1] : ((k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,X0)) & r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.20/0.56    inference(ennf_transformation,[],[f7])).
% 0.20/0.56  fof(f7,negated_conjecture,(
% 0.20/0.56    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)))))),
% 0.20/0.56    inference(negated_conjecture,[],[f6])).
% 0.20/0.56  fof(f6,conjecture,(
% 0.20/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)))))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).
% 0.20/0.56  fof(f289,plain,(
% 0.20/0.56    ~v1_relat_1(sK1) | ~spl11_1),
% 0.20/0.56    inference(subsumption_resolution,[],[f288,f35])).
% 0.20/0.56  fof(f35,plain,(
% 0.20/0.56    v1_relat_1(sK0)),
% 0.20/0.56    inference(cnf_transformation,[],[f18])).
% 0.20/0.56  fof(f288,plain,(
% 0.20/0.56    ~v1_relat_1(sK0) | ~v1_relat_1(sK1) | ~spl11_1),
% 0.20/0.56    inference(subsumption_resolution,[],[f280,f274])).
% 0.20/0.56  fof(f274,plain,(
% 0.20/0.56    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK2(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),sK0)) ) | ~spl11_1),
% 0.20/0.56    inference(subsumption_resolution,[],[f272,f61])).
% 0.20/0.56  fof(f61,plain,(
% 0.20/0.56    ~sQ10_eqProxy(k2_relat_1(sK0),k2_relat_1(k5_relat_1(sK1,sK0)))),
% 0.20/0.56    inference(equality_proxy_replacement,[],[f38,f60])).
% 0.20/0.56  fof(f60,plain,(
% 0.20/0.56    ! [X1,X0] : (sQ10_eqProxy(X0,X1) <=> X0 = X1)),
% 0.20/0.56    introduced(equality_proxy_definition,[new_symbols(naming,[sQ10_eqProxy])])).
% 0.20/0.56  fof(f38,plain,(
% 0.20/0.56    k2_relat_1(sK0) != k2_relat_1(k5_relat_1(sK1,sK0))),
% 0.20/0.56    inference(cnf_transformation,[],[f18])).
% 0.20/0.56  fof(f272,plain,(
% 0.20/0.56    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK2(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),sK0) | sQ10_eqProxy(k2_relat_1(sK0),k2_relat_1(k5_relat_1(sK1,sK0)))) ) | ~spl11_1),
% 0.20/0.56    inference(resolution,[],[f93,f62])).
% 0.20/0.56  fof(f62,plain,(
% 0.20/0.56    ( ! [X0,X3,X1] : (~r2_hidden(sK2(X0,X1),X1) | ~r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0) | sQ10_eqProxy(k2_relat_1(X0),X1)) )),
% 0.20/0.56    inference(equality_proxy_replacement,[],[f42,f60])).
% 0.20/0.56  fof(f42,plain,(
% 0.20/0.56    ( ! [X0,X3,X1] : (k2_relat_1(X0) = X1 | ~r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0) | ~r2_hidden(sK2(X0,X1),X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f24])).
% 0.20/0.56  fof(f24,plain,(
% 0.20/0.56    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK4(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.20/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f20,f23,f22,f21])).
% 0.20/0.56  fof(f21,plain,(
% 0.20/0.56    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK2(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f22,plain,(
% 0.20/0.56    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK2(X0,X1)),X0) => r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f23,plain,(
% 0.20/0.56    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK4(X0,X5),X5),X0))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f20,plain,(
% 0.20/0.56    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.20/0.56    inference(rectify,[],[f19])).
% 0.20/0.56  fof(f19,plain,(
% 0.20/0.56    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 0.20/0.56    inference(nnf_transformation,[],[f2])).
% 0.20/0.56  fof(f2,axiom,(
% 0.20/0.56    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 0.20/0.56  fof(f93,plain,(
% 0.20/0.56    r2_hidden(sK2(sK0,k2_relat_1(k5_relat_1(sK1,sK0))),k2_relat_1(k5_relat_1(sK1,sK0))) | ~spl11_1),
% 0.20/0.56    inference(avatar_component_clause,[],[f91])).
% 0.20/0.56  fof(f91,plain,(
% 0.20/0.56    spl11_1 <=> r2_hidden(sK2(sK0,k2_relat_1(k5_relat_1(sK1,sK0))),k2_relat_1(k5_relat_1(sK1,sK0)))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 0.20/0.56  fof(f280,plain,(
% 0.20/0.56    r2_hidden(k4_tarski(sK8(sK1,sK0,sK4(k5_relat_1(sK1,sK0),sK2(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),sK2(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),sK2(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),sK0) | ~v1_relat_1(sK0) | ~v1_relat_1(sK1) | ~spl11_1),
% 0.20/0.56    inference(resolution,[],[f271,f108])).
% 0.20/0.56  fof(f108,plain,(
% 0.20/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3)) | r2_hidden(k4_tarski(sK8(X2,X3,X0,X1),X1),X3) | ~v1_relat_1(X3) | ~v1_relat_1(X2)) )),
% 0.20/0.56    inference(duplicate_literal_removal,[],[f107])).
% 0.20/0.56  fof(f107,plain,(
% 0.20/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3)) | r2_hidden(k4_tarski(sK8(X2,X3,X0,X1),X1),X3) | ~v1_relat_1(X3) | ~v1_relat_1(X2) | ~v1_relat_1(X3) | ~v1_relat_1(X2)) )),
% 0.20/0.56    inference(resolution,[],[f58,f49])).
% 0.20/0.56  fof(f49,plain,(
% 0.20/0.56    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f12])).
% 0.20/0.56  fof(f12,plain,(
% 0.20/0.56    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.20/0.56    inference(flattening,[],[f11])).
% 0.20/0.56  fof(f11,plain,(
% 0.20/0.56    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f4])).
% 0.20/0.56  fof(f4,axiom,(
% 0.20/0.56    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.20/0.56  fof(f58,plain,(
% 0.20/0.56    ( ! [X0,X8,X7,X1] : (~v1_relat_1(k5_relat_1(X0,X1)) | ~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | r2_hidden(k4_tarski(sK8(X0,X1,X7,X8),X8),X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.56    inference(equality_resolution,[],[f44])).
% 0.20/0.56  fof(f44,plain,(
% 0.20/0.56    ( ! [X2,X0,X8,X7,X1] : (r2_hidden(k4_tarski(sK8(X0,X1,X7,X8),X8),X1) | ~r2_hidden(k4_tarski(X7,X8),X2) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f30])).
% 0.20/0.56  fof(f30,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ((! [X5] : (~r2_hidden(k4_tarski(X5,sK6(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK5(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK7(X0,X1,X2),sK6(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK5(X0,X1,X2),sK7(X0,X1,X2)),X0)) | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & ((r2_hidden(k4_tarski(sK8(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK8(X0,X1,X7,X8)),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f26,f29,f28,f27])).
% 0.20/0.56  fof(f27,plain,(
% 0.20/0.56    ! [X2,X1,X0] : (? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((! [X5] : (~r2_hidden(k4_tarski(X5,sK6(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK5(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,sK6(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK5(X0,X1,X2),X6),X0)) | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2))))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f28,plain,(
% 0.20/0.56    ! [X2,X1,X0] : (? [X6] : (r2_hidden(k4_tarski(X6,sK6(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK5(X0,X1,X2),X6),X0)) => (r2_hidden(k4_tarski(sK7(X0,X1,X2),sK6(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK5(X0,X1,X2),sK7(X0,X1,X2)),X0)))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f29,plain,(
% 0.20/0.56    ! [X8,X7,X1,X0] : (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) => (r2_hidden(k4_tarski(sK8(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK8(X0,X1,X7,X8)),X0)))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f26,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.56    inference(rectify,[],[f25])).
% 0.20/0.56  fof(f25,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0))) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.56    inference(nnf_transformation,[],[f10])).
% 0.20/0.56  fof(f10,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : (! [X2] : ((k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.56    inference(ennf_transformation,[],[f3])).
% 0.20/0.56  fof(f3,axiom,(
% 0.20/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))))))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).
% 0.20/0.56  fof(f271,plain,(
% 0.20/0.56    r2_hidden(k4_tarski(sK4(k5_relat_1(sK1,sK0),sK2(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),sK2(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),k5_relat_1(sK1,sK0)) | ~spl11_1),
% 0.20/0.56    inference(resolution,[],[f93,f56])).
% 0.20/0.56  fof(f56,plain,(
% 0.20/0.56    ( ! [X0,X5] : (~r2_hidden(X5,k2_relat_1(X0)) | r2_hidden(k4_tarski(sK4(X0,X5),X5),X0)) )),
% 0.20/0.56    inference(equality_resolution,[],[f39])).
% 0.20/0.56  fof(f39,plain,(
% 0.20/0.56    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK4(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 0.20/0.56    inference(cnf_transformation,[],[f24])).
% 0.20/0.56  fof(f270,plain,(
% 0.20/0.56    ~spl11_2),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f267])).
% 0.20/0.56  fof(f267,plain,(
% 0.20/0.56    $false | ~spl11_2),
% 0.20/0.56    inference(resolution,[],[f266,f103])).
% 0.20/0.56  fof(f103,plain,(
% 0.20/0.56    r2_hidden(k4_tarski(sK4(sK0,sK2(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),sK2(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),sK0) | ~spl11_2),
% 0.20/0.56    inference(resolution,[],[f101,f56])).
% 0.20/0.56  fof(f101,plain,(
% 0.20/0.56    r2_hidden(sK2(sK0,k2_relat_1(k5_relat_1(sK1,sK0))),k2_relat_1(sK0)) | ~spl11_2),
% 0.20/0.56    inference(resolution,[],[f97,f55])).
% 0.20/0.56  fof(f55,plain,(
% 0.20/0.56    ( ! [X6,X0,X5] : (~r2_hidden(k4_tarski(X6,X5),X0) | r2_hidden(X5,k2_relat_1(X0))) )),
% 0.20/0.56    inference(equality_resolution,[],[f40])).
% 0.20/0.56  fof(f40,plain,(
% 0.20/0.56    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 0.20/0.56    inference(cnf_transformation,[],[f24])).
% 0.20/0.56  fof(f97,plain,(
% 0.20/0.56    r2_hidden(k4_tarski(sK3(sK0,k2_relat_1(k5_relat_1(sK1,sK0))),sK2(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),sK0) | ~spl11_2),
% 0.20/0.56    inference(avatar_component_clause,[],[f95])).
% 0.20/0.56  fof(f95,plain,(
% 0.20/0.56    spl11_2 <=> r2_hidden(k4_tarski(sK3(sK0,k2_relat_1(k5_relat_1(sK1,sK0))),sK2(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),sK0)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 0.20/0.56  fof(f266,plain,(
% 0.20/0.56    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK2(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),sK0)) ) | ~spl11_2),
% 0.20/0.56    inference(subsumption_resolution,[],[f264,f61])).
% 0.20/0.56  fof(f264,plain,(
% 0.20/0.56    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK2(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),sK0) | sQ10_eqProxy(k2_relat_1(sK0),k2_relat_1(k5_relat_1(sK1,sK0)))) ) | ~spl11_2),
% 0.20/0.56    inference(resolution,[],[f232,f62])).
% 0.20/0.56  fof(f232,plain,(
% 0.20/0.56    r2_hidden(sK2(sK0,k2_relat_1(k5_relat_1(sK1,sK0))),k2_relat_1(k5_relat_1(sK1,sK0))) | ~spl11_2),
% 0.20/0.56    inference(resolution,[],[f226,f55])).
% 0.20/0.56  fof(f226,plain,(
% 0.20/0.56    r2_hidden(k4_tarski(sK4(sK1,sK3(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),sK2(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),k5_relat_1(sK1,sK0)) | ~spl11_2),
% 0.20/0.56    inference(subsumption_resolution,[],[f225,f35])).
% 0.20/0.56  fof(f225,plain,(
% 0.20/0.56    ~v1_relat_1(sK0) | r2_hidden(k4_tarski(sK4(sK1,sK3(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),sK2(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),k5_relat_1(sK1,sK0)) | ~spl11_2),
% 0.20/0.56    inference(resolution,[],[f161,f97])).
% 0.20/0.56  fof(f161,plain,(
% 0.20/0.56    ( ! [X6,X7] : (~r2_hidden(k4_tarski(sK3(sK0,k2_relat_1(k5_relat_1(sK1,sK0))),X6),X7) | ~v1_relat_1(X7) | r2_hidden(k4_tarski(sK4(sK1,sK3(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),X6),k5_relat_1(sK1,X7))) ) | ~spl11_2),
% 0.20/0.56    inference(resolution,[],[f154,f114])).
% 0.20/0.56  fof(f114,plain,(
% 0.20/0.56    r2_hidden(k4_tarski(sK4(sK1,sK3(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),sK3(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),sK1) | ~spl11_2),
% 0.20/0.56    inference(resolution,[],[f113,f56])).
% 0.20/0.56  fof(f113,plain,(
% 0.20/0.56    r2_hidden(sK3(sK0,k2_relat_1(k5_relat_1(sK1,sK0))),k2_relat_1(sK1)) | ~spl11_2),
% 0.20/0.56    inference(resolution,[],[f111,f69])).
% 0.20/0.56  fof(f69,plain,(
% 0.20/0.56    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.20/0.56    inference(duplicate_literal_removal,[],[f68])).
% 0.20/0.56  fof(f68,plain,(
% 0.20/0.56    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 0.20/0.56    inference(resolution,[],[f52,f51])).
% 0.20/0.56  fof(f51,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r2_hidden(sK9(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f34])).
% 0.20/0.56  fof(f34,plain,(
% 0.20/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK9(X0,X1),X1) & r2_hidden(sK9(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f32,f33])).
% 0.20/0.56  fof(f33,plain,(
% 0.20/0.56    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK9(X0,X1),X1) & r2_hidden(sK9(X0,X1),X0)))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f32,plain,(
% 0.20/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.56    inference(rectify,[],[f31])).
% 0.20/0.56  fof(f31,plain,(
% 0.20/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.56    inference(nnf_transformation,[],[f13])).
% 0.20/0.56  fof(f13,plain,(
% 0.20/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f1])).
% 0.20/0.56  fof(f1,axiom,(
% 0.20/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.56  fof(f52,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r2_hidden(sK9(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f34])).
% 0.20/0.56  fof(f111,plain,(
% 0.20/0.56    ( ! [X0] : (~r1_tarski(k2_relat_1(sK1),X0) | r2_hidden(sK3(sK0,k2_relat_1(k5_relat_1(sK1,sK0))),X0)) ) | ~spl11_2),
% 0.20/0.56    inference(resolution,[],[f109,f37])).
% 0.20/0.56  fof(f37,plain,(
% 0.20/0.56    r1_tarski(k1_relat_1(sK0),k2_relat_1(sK1))),
% 0.20/0.56    inference(cnf_transformation,[],[f18])).
% 0.20/0.56  fof(f109,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(sK0),X0) | r2_hidden(sK3(sK0,k2_relat_1(k5_relat_1(sK1,sK0))),X1) | ~r1_tarski(X0,X1)) ) | ~spl11_2),
% 0.20/0.56    inference(resolution,[],[f105,f50])).
% 0.20/0.56  fof(f50,plain,(
% 0.20/0.56    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f34])).
% 0.20/0.56  fof(f105,plain,(
% 0.20/0.56    ( ! [X0] : (r2_hidden(sK3(sK0,k2_relat_1(k5_relat_1(sK1,sK0))),X0) | ~r1_tarski(k1_relat_1(sK0),X0)) ) | ~spl11_2),
% 0.20/0.56    inference(resolution,[],[f102,f50])).
% 0.20/0.56  fof(f102,plain,(
% 0.20/0.56    r2_hidden(sK3(sK0,k2_relat_1(k5_relat_1(sK1,sK0))),k1_relat_1(sK0)) | ~spl11_2),
% 0.20/0.56    inference(subsumption_resolution,[],[f100,f35])).
% 0.20/0.56  fof(f100,plain,(
% 0.20/0.56    r2_hidden(sK3(sK0,k2_relat_1(k5_relat_1(sK1,sK0))),k1_relat_1(sK0)) | ~v1_relat_1(sK0) | ~spl11_2),
% 0.20/0.56    inference(resolution,[],[f97,f53])).
% 0.20/0.56  fof(f53,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X0,k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f15])).
% 0.20/0.56  fof(f15,plain,(
% 0.20/0.56    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.20/0.56    inference(flattening,[],[f14])).
% 0.20/0.56  fof(f14,plain,(
% 0.20/0.56    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 0.20/0.56    inference(ennf_transformation,[],[f5])).
% 0.20/0.56  fof(f5,axiom,(
% 0.20/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).
% 0.20/0.56  fof(f154,plain,(
% 0.20/0.56    ( ! [X6,X4,X7,X5] : (~r2_hidden(k4_tarski(X4,X5),sK1) | r2_hidden(k4_tarski(X4,X6),k5_relat_1(sK1,X7)) | ~v1_relat_1(X7) | ~r2_hidden(k4_tarski(X5,X6),X7)) )),
% 0.20/0.56    inference(resolution,[],[f127,f36])).
% 0.20/0.56  fof(f127,plain,(
% 0.20/0.56    ( ! [X4,X2,X0,X3,X1] : (~v1_relat_1(X4) | ~r2_hidden(k4_tarski(X3,X0),X4) | r2_hidden(k4_tarski(X3,X1),k5_relat_1(X4,X2)) | ~v1_relat_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.20/0.56    inference(duplicate_literal_removal,[],[f126])).
% 0.20/0.56  fof(f126,plain,(
% 0.20/0.56    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(k4_tarski(X3,X0),X4) | r2_hidden(k4_tarski(X3,X1),k5_relat_1(X4,X2)) | ~v1_relat_1(X2) | ~v1_relat_1(X4) | ~v1_relat_1(X2) | ~v1_relat_1(X4)) )),
% 0.20/0.56    inference(resolution,[],[f57,f49])).
% 0.20/0.56  fof(f57,plain,(
% 0.20/0.56    ( ! [X0,X8,X7,X1,X9] : (~v1_relat_1(k5_relat_1(X0,X1)) | ~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0) | r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.56    inference(equality_resolution,[],[f45])).
% 0.20/0.56  fof(f45,plain,(
% 0.20/0.56    ( ! [X2,X0,X8,X7,X1,X9] : (r2_hidden(k4_tarski(X7,X8),X2) | ~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f30])).
% 0.20/0.56  fof(f98,plain,(
% 0.20/0.56    spl11_1 | spl11_2),
% 0.20/0.56    inference(avatar_split_clause,[],[f89,f95,f91])).
% 0.20/0.56  fof(f89,plain,(
% 0.20/0.56    r2_hidden(k4_tarski(sK3(sK0,k2_relat_1(k5_relat_1(sK1,sK0))),sK2(sK0,k2_relat_1(k5_relat_1(sK1,sK0)))),sK0) | r2_hidden(sK2(sK0,k2_relat_1(k5_relat_1(sK1,sK0))),k2_relat_1(k5_relat_1(sK1,sK0)))),
% 0.20/0.56    inference(resolution,[],[f63,f61])).
% 0.20/0.56  fof(f63,plain,(
% 0.20/0.56    ( ! [X0,X1] : (sQ10_eqProxy(k2_relat_1(X0),X1) | r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1)) )),
% 0.20/0.56    inference(equality_proxy_replacement,[],[f41,f60])).
% 0.20/0.56  fof(f41,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f24])).
% 0.20/0.56  % SZS output end Proof for theBenchmark
% 0.20/0.56  % (19056)------------------------------
% 0.20/0.56  % (19056)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (19056)Termination reason: Refutation
% 0.20/0.56  
% 0.20/0.56  % (19056)Memory used [KB]: 11001
% 0.20/0.56  % (19056)Time elapsed: 0.155 s
% 0.20/0.56  % (19056)------------------------------
% 0.20/0.56  % (19056)------------------------------
% 0.20/0.56  % (19038)Success in time 0.205 s
%------------------------------------------------------------------------------
