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
% DateTime   : Thu Dec  3 13:00:06 EST 2020

% Result     : Theorem 53.11s
% Output     : Refutation 53.11s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 897 expanded)
%              Number of leaves         :   14 ( 251 expanded)
%              Depth                    :   31
%              Number of atoms          :  399 (3656 expanded)
%              Number of equality atoms :  118 (1524 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12197,plain,(
    $false ),
    inference(subsumption_resolution,[],[f12191,f466])).

fof(f466,plain,(
    k4_tarski(sK0,sK0) != sK5(k4_tarski(sK0,sK0),k1_wellord2(k1_enumset1(sK0,sK0,sK0))) ),
    inference(subsumption_resolution,[],[f441,f69])).

fof(f69,plain,(
    k1_wellord2(k1_enumset1(sK0,sK0,sK0)) != k1_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0)) ),
    inference(definition_unfolding,[],[f42,f68,f68])).

fof(f68,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f58,f67])).

fof(f67,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f58,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f42,plain,(
    k1_wellord2(k1_tarski(sK0)) != k1_tarski(k4_tarski(sK0,sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    k1_wellord2(k1_tarski(sK0)) != k1_tarski(k4_tarski(sK0,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f21])).

fof(f21,plain,
    ( ? [X0] : k1_wellord2(k1_tarski(X0)) != k1_tarski(k4_tarski(X0,X0))
   => k1_wellord2(k1_tarski(sK0)) != k1_tarski(k4_tarski(sK0,sK0)) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] : k1_wellord2(k1_tarski(X0)) != k1_tarski(k4_tarski(X0,X0)) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] : k1_wellord2(k1_tarski(X0)) = k1_tarski(k4_tarski(X0,X0)) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] : k1_wellord2(k1_tarski(X0)) = k1_tarski(k4_tarski(X0,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_wellord2)).

fof(f441,plain,
    ( k1_wellord2(k1_enumset1(sK0,sK0,sK0)) = k1_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0))
    | k4_tarski(sK0,sK0) != sK5(k4_tarski(sK0,sK0),k1_wellord2(k1_enumset1(sK0,sK0,sK0))) ),
    inference(resolution,[],[f432,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_enumset1(X0,X0,X0) = X1
      | sK5(X0,X1) != X0
      | ~ r2_hidden(sK5(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f57,f68])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK5(X0,X1) != X0
      | ~ r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK5(X0,X1) != X0
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( sK5(X0,X1) = X0
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f33,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK5(X0,X1) != X0
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( sK5(X0,X1) = X0
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f432,plain,(
    r2_hidden(sK5(k4_tarski(sK0,sK0),k1_wellord2(k1_enumset1(sK0,sK0,sK0))),k1_wellord2(k1_enumset1(sK0,sK0,sK0))) ),
    inference(subsumption_resolution,[],[f431,f69])).

fof(f431,plain,
    ( r2_hidden(sK5(k4_tarski(sK0,sK0),k1_wellord2(k1_enumset1(sK0,sK0,sK0))),k1_wellord2(k1_enumset1(sK0,sK0,sK0)))
    | k1_wellord2(k1_enumset1(sK0,sK0,sK0)) = k1_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0)) ),
    inference(trivial_inequality_removal,[],[f425])).

fof(f425,plain,
    ( r2_hidden(sK5(k4_tarski(sK0,sK0),k1_wellord2(k1_enumset1(sK0,sK0,sK0))),k1_wellord2(k1_enumset1(sK0,sK0,sK0)))
    | k1_wellord2(k1_enumset1(sK0,sK0,sK0)) != k1_wellord2(k1_enumset1(sK0,sK0,sK0))
    | k1_wellord2(k1_enumset1(sK0,sK0,sK0)) = k1_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0)) ),
    inference(resolution,[],[f424,f85])).

fof(f85,plain,(
    ! [X3] : r2_hidden(X3,k1_enumset1(X3,X3,X3)) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_enumset1(X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f55,f68])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f424,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK0,X1)
      | r2_hidden(sK5(k4_tarski(sK0,sK0),k1_wellord2(X1)),k1_wellord2(X1))
      | k1_wellord2(k1_enumset1(sK0,sK0,sK0)) != k1_wellord2(X1)
      | k1_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0)) = k1_wellord2(X1) ) ),
    inference(subsumption_resolution,[],[f419,f418])).

fof(f418,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK0,X0)
      | r2_hidden(sK5(k4_tarski(sK0,sK0),k1_wellord2(X0)),k1_wellord2(X0))
      | k1_wellord2(X0) != k1_wellord2(k1_enumset1(sK0,sK0,sK0))
      | k1_wellord2(X0) = k1_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0))
      | r2_hidden(sK6(sK0,sK0),sK0) ) ),
    inference(resolution,[],[f148,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK6(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f39,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
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

fof(f148,plain,(
    ! [X2] :
      ( ~ r1_tarski(sK0,sK0)
      | k1_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0)) = k1_wellord2(X2)
      | r2_hidden(sK5(k4_tarski(sK0,sK0),k1_wellord2(X2)),k1_wellord2(X2))
      | k1_wellord2(k1_enumset1(sK0,sK0,sK0)) != k1_wellord2(X2)
      | ~ r2_hidden(sK0,X2) ) ),
    inference(subsumption_resolution,[],[f147,f53])).

fof(f53,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f147,plain,(
    ! [X2] :
      ( k1_wellord2(k1_enumset1(sK0,sK0,sK0)) != k1_wellord2(X2)
      | k1_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0)) = k1_wellord2(X2)
      | r2_hidden(sK5(k4_tarski(sK0,sK0),k1_wellord2(X2)),k1_wellord2(X2))
      | ~ r1_tarski(sK0,sK0)
      | ~ r2_hidden(sK0,X2)
      | ~ v1_relat_1(k1_wellord2(X2)) ) ),
    inference(duplicate_literal_removal,[],[f140])).

fof(f140,plain,(
    ! [X2] :
      ( k1_wellord2(k1_enumset1(sK0,sK0,sK0)) != k1_wellord2(X2)
      | k1_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0)) = k1_wellord2(X2)
      | r2_hidden(sK5(k4_tarski(sK0,sK0),k1_wellord2(X2)),k1_wellord2(X2))
      | ~ r1_tarski(sK0,sK0)
      | ~ r2_hidden(sK0,X2)
      | ~ r2_hidden(sK0,X2)
      | ~ v1_relat_1(k1_wellord2(X2)) ) ),
    inference(resolution,[],[f104,f81])).

fof(f81,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0))
      | ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ( ( ~ r1_tarski(sK3(X0,X1),sK4(X0,X1))
              | ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) )
            & ( r1_tarski(sK3(X0,X1),sK4(X0,X1))
              | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) )
            & r2_hidden(sK4(X0,X1),X0)
            & r2_hidden(sK3(X0,X1),X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X4,X5] :
                ( ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r1_tarski(X4,X5) )
                  & ( r1_tarski(X4,X5)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f29,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r1_tarski(X2,X3)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r1_tarski(X2,X3)
            | r2_hidden(k4_tarski(X2,X3),X1) )
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
     => ( ( ~ r1_tarski(sK3(X0,X1),sK4(X0,X1))
          | ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) )
        & ( r1_tarski(sK3(X0,X1),sK4(X0,X1))
          | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) )
        & r2_hidden(sK4(X0,X1),X0)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X4,X5] :
                ( ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r1_tarski(X4,X5) )
                  & ( r1_tarski(X4,X5)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X2,X3] :
                ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r1_tarski(X2,X3) )
                  & ( r1_tarski(X2,X3)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
                | ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X2,X3] :
                ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r1_tarski(X2,X3) )
                  & ( r1_tarski(X2,X3)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
                | ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) ) )
          & k3_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).

fof(f104,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(sK0,sK0),X0)
      | k1_wellord2(k1_enumset1(sK0,sK0,sK0)) != X0
      | k1_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0)) = X0
      | r2_hidden(sK5(k4_tarski(sK0,sK0),X0),X0) ) ),
    inference(trivial_inequality_removal,[],[f103])).

fof(f103,plain,(
    ! [X0] :
      ( k4_tarski(sK0,sK0) != k4_tarski(sK0,sK0)
      | k1_wellord2(k1_enumset1(sK0,sK0,sK0)) != X0
      | ~ r2_hidden(k4_tarski(sK0,sK0),X0)
      | k1_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0)) = X0
      | r2_hidden(sK5(k4_tarski(sK0,sK0),X0),X0) ) ),
    inference(superposition,[],[f88,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_enumset1(X0,X0,X0) = X1
      | sK5(X0,X1) = X0
      | r2_hidden(sK5(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f56,f68])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK5(X0,X1) = X0
      | r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f88,plain,(
    ! [X1] :
      ( k4_tarski(sK0,sK0) != sK5(k4_tarski(sK0,sK0),X1)
      | k1_wellord2(k1_enumset1(sK0,sK0,sK0)) != X1
      | ~ r2_hidden(sK5(k4_tarski(sK0,sK0),X1),X1) ) ),
    inference(superposition,[],[f69,f70])).

fof(f419,plain,(
    ! [X1] :
      ( k1_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0)) = k1_wellord2(X1)
      | r2_hidden(sK5(k4_tarski(sK0,sK0),k1_wellord2(X1)),k1_wellord2(X1))
      | k1_wellord2(k1_enumset1(sK0,sK0,sK0)) != k1_wellord2(X1)
      | ~ r2_hidden(sK0,X1)
      | ~ r2_hidden(sK6(sK0,sK0),sK0) ) ),
    inference(resolution,[],[f148,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK6(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f12191,plain,(
    k4_tarski(sK0,sK0) = sK5(k4_tarski(sK0,sK0),k1_wellord2(k1_enumset1(sK0,sK0,sK0))) ),
    inference(resolution,[],[f12188,f85])).

fof(f12188,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(sK0,sK0),k1_enumset1(X0,X0,X0))
      | sK5(k4_tarski(sK0,sK0),k1_wellord2(k1_enumset1(sK0,sK0,sK0))) = X0 ) ),
    inference(duplicate_literal_removal,[],[f12185])).

fof(f12185,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(sK0,sK0),k1_enumset1(X0,X0,X0))
      | sK5(k4_tarski(sK0,sK0),k1_wellord2(k1_enumset1(sK0,sK0,sK0))) = X0
      | sK5(k4_tarski(sK0,sK0),k1_wellord2(k1_enumset1(sK0,sK0,sK0))) = X0 ) ),
    inference(superposition,[],[f9603,f9992])).

fof(f9992,plain,(
    ! [X42] :
      ( sK0 = sK2(k1_wellord2(k1_enumset1(sK0,sK0,sK0)),k1_enumset1(X42,X42,X42))
      | sK5(k4_tarski(sK0,sK0),k1_wellord2(k1_enumset1(sK0,sK0,sK0))) = X42 ) ),
    inference(resolution,[],[f9929,f86])).

fof(f86,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_enumset1(X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f54,f68])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f9929,plain,(
    ! [X1] :
      ( r2_hidden(sK5(k4_tarski(sK0,sK0),k1_wellord2(k1_enumset1(sK0,sK0,sK0))),X1)
      | sK0 = sK2(k1_wellord2(k1_enumset1(sK0,sK0,sK0)),X1) ) ),
    inference(resolution,[],[f9916,f86])).

fof(f9916,plain,(
    ! [X0] :
      ( r2_hidden(sK2(k1_wellord2(k1_enumset1(sK0,sK0,sK0)),X0),k1_enumset1(sK0,sK0,sK0))
      | r2_hidden(sK5(k4_tarski(sK0,sK0),k1_wellord2(k1_enumset1(sK0,sK0,sK0))),X0) ) ),
    inference(subsumption_resolution,[],[f9911,f53])).

fof(f9911,plain,(
    ! [X0] :
      ( r2_hidden(sK2(k1_wellord2(k1_enumset1(sK0,sK0,sK0)),X0),k1_enumset1(sK0,sK0,sK0))
      | r2_hidden(sK5(k4_tarski(sK0,sK0),k1_wellord2(k1_enumset1(sK0,sK0,sK0))),X0)
      | ~ v1_relat_1(k1_wellord2(k1_enumset1(sK0,sK0,sK0))) ) ),
    inference(superposition,[],[f9385,f83])).

fof(f83,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f9385,plain,(
    ! [X26] :
      ( r2_hidden(sK2(k1_wellord2(k1_enumset1(sK0,sK0,sK0)),X26),k3_relat_1(k1_wellord2(k1_enumset1(sK0,sK0,sK0))))
      | r2_hidden(sK5(k4_tarski(sK0,sK0),k1_wellord2(k1_enumset1(sK0,sK0,sK0))),X26) ) ),
    inference(subsumption_resolution,[],[f9341,f53])).

fof(f9341,plain,(
    ! [X26] :
      ( r2_hidden(sK5(k4_tarski(sK0,sK0),k1_wellord2(k1_enumset1(sK0,sK0,sK0))),X26)
      | r2_hidden(sK2(k1_wellord2(k1_enumset1(sK0,sK0,sK0)),X26),k3_relat_1(k1_wellord2(k1_enumset1(sK0,sK0,sK0))))
      | ~ v1_relat_1(k1_wellord2(k1_enumset1(sK0,sK0,sK0))) ) ),
    inference(resolution,[],[f507,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).

fof(f507,plain,(
    ! [X4] :
      ( r2_hidden(k4_tarski(sK1(k1_wellord2(k1_enumset1(sK0,sK0,sK0)),X4),sK2(k1_wellord2(k1_enumset1(sK0,sK0,sK0)),X4)),k1_wellord2(k1_enumset1(sK0,sK0,sK0)))
      | r2_hidden(sK5(k4_tarski(sK0,sK0),k1_wellord2(k1_enumset1(sK0,sK0,sK0))),X4) ) ),
    inference(subsumption_resolution,[],[f502,f53])).

fof(f502,plain,(
    ! [X4] :
      ( r2_hidden(sK5(k4_tarski(sK0,sK0),k1_wellord2(k1_enumset1(sK0,sK0,sK0))),X4)
      | r2_hidden(k4_tarski(sK1(k1_wellord2(k1_enumset1(sK0,sK0,sK0)),X4),sK2(k1_wellord2(k1_enumset1(sK0,sK0,sK0)),X4)),k1_wellord2(k1_enumset1(sK0,sK0,sK0)))
      | ~ v1_relat_1(k1_wellord2(k1_enumset1(sK0,sK0,sK0))) ) ),
    inference(resolution,[],[f442,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)
              & r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f24,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X1)
          & r2_hidden(k4_tarski(X2,X3),X0) )
     => ( ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)
        & r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) ) ) ),
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
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

fof(f442,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_wellord2(k1_enumset1(sK0,sK0,sK0)),X0)
      | r2_hidden(sK5(k4_tarski(sK0,sK0),k1_wellord2(k1_enumset1(sK0,sK0,sK0))),X0) ) ),
    inference(resolution,[],[f432,f62])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f9603,plain,(
    ! [X7] :
      ( ~ r2_hidden(k4_tarski(sK0,sK2(k1_wellord2(k1_enumset1(sK0,sK0,sK0)),k1_enumset1(X7,X7,X7))),k1_enumset1(X7,X7,X7))
      | sK5(k4_tarski(sK0,sK0),k1_wellord2(k1_enumset1(sK0,sK0,sK0))) = X7 ) ),
    inference(subsumption_resolution,[],[f9585,f86])).

fof(f9585,plain,(
    ! [X7] :
      ( ~ r2_hidden(k4_tarski(sK0,sK2(k1_wellord2(k1_enumset1(sK0,sK0,sK0)),k1_enumset1(X7,X7,X7))),k1_enumset1(X7,X7,X7))
      | r2_hidden(sK5(k4_tarski(sK0,sK0),k1_wellord2(k1_enumset1(sK0,sK0,sK0))),k1_enumset1(X7,X7,X7))
      | sK5(k4_tarski(sK0,sK0),k1_wellord2(k1_enumset1(sK0,sK0,sK0))) = X7 ) ),
    inference(superposition,[],[f508,f9538])).

fof(f9538,plain,(
    ! [X42] :
      ( sK0 = sK1(k1_wellord2(k1_enumset1(sK0,sK0,sK0)),k1_enumset1(X42,X42,X42))
      | sK5(k4_tarski(sK0,sK0),k1_wellord2(k1_enumset1(sK0,sK0,sK0))) = X42 ) ),
    inference(resolution,[],[f9475,f86])).

fof(f9475,plain,(
    ! [X1] :
      ( r2_hidden(sK5(k4_tarski(sK0,sK0),k1_wellord2(k1_enumset1(sK0,sK0,sK0))),X1)
      | sK0 = sK1(k1_wellord2(k1_enumset1(sK0,sK0,sK0)),X1) ) ),
    inference(resolution,[],[f9459,f86])).

fof(f9459,plain,(
    ! [X0] :
      ( r2_hidden(sK1(k1_wellord2(k1_enumset1(sK0,sK0,sK0)),X0),k1_enumset1(sK0,sK0,sK0))
      | r2_hidden(sK5(k4_tarski(sK0,sK0),k1_wellord2(k1_enumset1(sK0,sK0,sK0))),X0) ) ),
    inference(subsumption_resolution,[],[f9454,f53])).

fof(f9454,plain,(
    ! [X0] :
      ( r2_hidden(sK1(k1_wellord2(k1_enumset1(sK0,sK0,sK0)),X0),k1_enumset1(sK0,sK0,sK0))
      | r2_hidden(sK5(k4_tarski(sK0,sK0),k1_wellord2(k1_enumset1(sK0,sK0,sK0))),X0)
      | ~ v1_relat_1(k1_wellord2(k1_enumset1(sK0,sK0,sK0))) ) ),
    inference(superposition,[],[f9384,f83])).

fof(f9384,plain,(
    ! [X25] :
      ( r2_hidden(sK1(k1_wellord2(k1_enumset1(sK0,sK0,sK0)),X25),k3_relat_1(k1_wellord2(k1_enumset1(sK0,sK0,sK0))))
      | r2_hidden(sK5(k4_tarski(sK0,sK0),k1_wellord2(k1_enumset1(sK0,sK0,sK0))),X25) ) ),
    inference(subsumption_resolution,[],[f9340,f53])).

fof(f9340,plain,(
    ! [X25] :
      ( r2_hidden(sK5(k4_tarski(sK0,sK0),k1_wellord2(k1_enumset1(sK0,sK0,sK0))),X25)
      | r2_hidden(sK1(k1_wellord2(k1_enumset1(sK0,sK0,sK0)),X25),k3_relat_1(k1_wellord2(k1_enumset1(sK0,sK0,sK0))))
      | ~ v1_relat_1(k1_wellord2(k1_enumset1(sK0,sK0,sK0))) ) ),
    inference(resolution,[],[f507,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k3_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f508,plain,(
    ! [X5] :
      ( ~ r2_hidden(k4_tarski(sK1(k1_wellord2(k1_enumset1(sK0,sK0,sK0)),X5),sK2(k1_wellord2(k1_enumset1(sK0,sK0,sK0)),X5)),X5)
      | r2_hidden(sK5(k4_tarski(sK0,sK0),k1_wellord2(k1_enumset1(sK0,sK0,sK0))),X5) ) ),
    inference(subsumption_resolution,[],[f503,f53])).

fof(f503,plain,(
    ! [X5] :
      ( r2_hidden(sK5(k4_tarski(sK0,sK0),k1_wellord2(k1_enumset1(sK0,sK0,sK0))),X5)
      | ~ r2_hidden(k4_tarski(sK1(k1_wellord2(k1_enumset1(sK0,sK0,sK0)),X5),sK2(k1_wellord2(k1_enumset1(sK0,sK0,sK0)),X5)),X5)
      | ~ v1_relat_1(k1_wellord2(k1_enumset1(sK0,sK0,sK0))) ) ),
    inference(resolution,[],[f442,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:23:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.50  % (1685)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.50  % (1662)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (1668)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (1661)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (1659)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (1657)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (1658)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (1679)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (1671)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (1665)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (1665)Refutation not found, incomplete strategy% (1665)------------------------------
% 0.21/0.52  % (1665)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (1665)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (1665)Memory used [KB]: 10746
% 0.21/0.52  % (1665)Time elapsed: 0.115 s
% 0.21/0.52  % (1665)------------------------------
% 0.21/0.52  % (1665)------------------------------
% 0.21/0.52  % (1678)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.52  % (1676)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.52  % (1670)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (1664)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (1669)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (1678)Refutation not found, incomplete strategy% (1678)------------------------------
% 0.21/0.53  % (1678)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (1678)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (1678)Memory used [KB]: 1791
% 0.21/0.53  % (1678)Time elapsed: 0.127 s
% 0.21/0.53  % (1678)------------------------------
% 0.21/0.53  % (1678)------------------------------
% 0.21/0.53  % (1683)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  % (1686)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (1682)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (1660)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (1659)Refutation not found, incomplete strategy% (1659)------------------------------
% 0.21/0.53  % (1659)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (1659)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (1659)Memory used [KB]: 10746
% 0.21/0.53  % (1659)Time elapsed: 0.126 s
% 0.21/0.53  % (1659)------------------------------
% 0.21/0.53  % (1659)------------------------------
% 0.21/0.53  % (1663)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (1674)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (1687)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (1677)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (1677)Refutation not found, incomplete strategy% (1677)------------------------------
% 0.21/0.54  % (1677)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (1677)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (1677)Memory used [KB]: 10746
% 0.21/0.54  % (1677)Time elapsed: 0.140 s
% 0.21/0.54  % (1677)------------------------------
% 0.21/0.54  % (1677)------------------------------
% 0.21/0.54  % (1675)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (1681)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (1666)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (1667)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (1680)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (1667)Refutation not found, incomplete strategy% (1667)------------------------------
% 0.21/0.54  % (1667)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (1667)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (1667)Memory used [KB]: 10618
% 0.21/0.54  % (1667)Time elapsed: 0.139 s
% 0.21/0.54  % (1667)------------------------------
% 0.21/0.54  % (1667)------------------------------
% 0.21/0.55  % (1673)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.57  % (1672)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 2.11/0.66  % (1689)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.11/0.67  % (1688)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.11/0.67  % (1690)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.11/0.67  % (1691)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.11/0.68  % (1692)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 3.27/0.81  % (1662)Time limit reached!
% 3.27/0.81  % (1662)------------------------------
% 3.27/0.81  % (1662)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.27/0.81  % (1662)Termination reason: Time limit
% 3.27/0.81  
% 3.27/0.81  % (1662)Memory used [KB]: 7803
% 3.27/0.81  % (1662)Time elapsed: 0.404 s
% 3.27/0.81  % (1662)------------------------------
% 3.27/0.81  % (1662)------------------------------
% 4.18/0.90  % (1674)Time limit reached!
% 4.18/0.90  % (1674)------------------------------
% 4.18/0.90  % (1674)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.18/0.90  % (1674)Termination reason: Time limit
% 4.18/0.90  % (1674)Termination phase: Saturation
% 4.18/0.90  
% 4.18/0.90  % (1674)Memory used [KB]: 12792
% 4.18/0.90  % (1674)Time elapsed: 0.500 s
% 4.18/0.90  % (1674)------------------------------
% 4.18/0.90  % (1674)------------------------------
% 4.18/0.91  % (1658)Time limit reached!
% 4.18/0.91  % (1658)------------------------------
% 4.18/0.91  % (1658)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.18/0.91  % (1658)Termination reason: Time limit
% 4.18/0.91  
% 4.18/0.91  % (1658)Memory used [KB]: 8187
% 4.18/0.91  % (1658)Time elapsed: 0.510 s
% 4.18/0.91  % (1658)------------------------------
% 4.18/0.91  % (1658)------------------------------
% 4.45/0.93  % (1657)Time limit reached!
% 4.45/0.93  % (1657)------------------------------
% 4.45/0.93  % (1657)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.45/0.93  % (1657)Termination reason: Time limit
% 4.45/0.93  
% 4.45/0.93  % (1657)Memory used [KB]: 3198
% 4.45/0.93  % (1657)Time elapsed: 0.528 s
% 4.45/0.93  % (1657)------------------------------
% 4.45/0.93  % (1657)------------------------------
% 4.45/0.94  % (1693)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 4.45/0.95  % (1669)Time limit reached!
% 4.45/0.95  % (1669)------------------------------
% 4.45/0.95  % (1669)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.45/0.95  % (1669)Termination reason: Time limit
% 4.45/0.95  % (1669)Termination phase: Saturation
% 4.45/0.95  
% 4.45/0.95  % (1669)Memory used [KB]: 8187
% 4.45/0.95  % (1669)Time elapsed: 0.500 s
% 4.45/0.95  % (1669)------------------------------
% 4.45/0.95  % (1669)------------------------------
% 4.45/0.99  % (1691)Time limit reached!
% 4.45/0.99  % (1691)------------------------------
% 4.45/0.99  % (1691)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.45/0.99  % (1691)Termination reason: Time limit
% 4.45/0.99  
% 4.45/0.99  % (1691)Memory used [KB]: 7291
% 4.45/0.99  % (1691)Time elapsed: 0.423 s
% 4.45/0.99  % (1691)------------------------------
% 4.45/0.99  % (1691)------------------------------
% 4.97/1.00  % (1692)Time limit reached!
% 4.97/1.00  % (1692)------------------------------
% 4.97/1.00  % (1692)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.97/1.00  % (1692)Termination reason: Time limit
% 4.97/1.00  
% 4.97/1.00  % (1692)Memory used [KB]: 13688
% 4.97/1.00  % (1692)Time elapsed: 0.425 s
% 4.97/1.00  % (1692)------------------------------
% 4.97/1.00  % (1692)------------------------------
% 4.97/1.01  % (1664)Time limit reached!
% 4.97/1.01  % (1664)------------------------------
% 4.97/1.01  % (1664)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.97/1.01  % (1664)Termination reason: Time limit
% 4.97/1.01  
% 4.97/1.01  % (1664)Memory used [KB]: 9466
% 4.97/1.01  % (1664)Time elapsed: 0.602 s
% 4.97/1.01  % (1664)------------------------------
% 4.97/1.01  % (1664)------------------------------
% 4.97/1.02  % (1694)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 4.97/1.02  % (1673)Time limit reached!
% 4.97/1.02  % (1673)------------------------------
% 4.97/1.02  % (1673)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.97/1.02  % (1673)Termination reason: Time limit
% 4.97/1.02  
% 4.97/1.02  % (1673)Memory used [KB]: 15863
% 4.97/1.02  % (1673)Time elapsed: 0.614 s
% 4.97/1.02  % (1673)------------------------------
% 4.97/1.02  % (1673)------------------------------
% 4.97/1.04  % (1695)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 4.97/1.07  % (1696)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 4.97/1.09  % (1697)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 5.68/1.12  % (1699)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 5.68/1.14  % (1698)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 5.68/1.14  % (1686)Time limit reached!
% 5.68/1.14  % (1686)------------------------------
% 5.68/1.14  % (1686)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.68/1.14  % (1686)Termination reason: Time limit
% 5.68/1.14  % (1686)Termination phase: Saturation
% 5.68/1.14  
% 5.68/1.14  % (1686)Memory used [KB]: 7547
% 5.68/1.14  % (1686)Time elapsed: 0.600 s
% 5.68/1.14  % (1686)------------------------------
% 5.68/1.14  % (1686)------------------------------
% 5.68/1.15  % (1700)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 5.68/1.15  % (1701)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 5.68/1.15  % (1701)Refutation not found, incomplete strategy% (1701)------------------------------
% 5.68/1.15  % (1701)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.68/1.15  % (1701)Termination reason: Refutation not found, incomplete strategy
% 5.68/1.15  
% 5.68/1.15  % (1701)Memory used [KB]: 1791
% 5.68/1.15  % (1701)Time elapsed: 0.106 s
% 5.68/1.15  % (1701)------------------------------
% 5.68/1.15  % (1701)------------------------------
% 6.82/1.26  % (1702)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 6.82/1.30  % (1703)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 9.02/1.55  % (1700)Time limit reached!
% 9.02/1.55  % (1700)------------------------------
% 9.02/1.55  % (1700)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.02/1.55  % (1700)Termination reason: Time limit
% 9.02/1.55  
% 9.02/1.55  % (1700)Memory used [KB]: 3454
% 9.02/1.55  % (1700)Time elapsed: 0.522 s
% 9.02/1.55  % (1700)------------------------------
% 9.02/1.55  % (1700)------------------------------
% 9.64/1.63  % (1683)Time limit reached!
% 9.64/1.63  % (1683)------------------------------
% 9.64/1.63  % (1683)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.64/1.63  % (1683)Termination reason: Time limit
% 9.64/1.63  
% 9.64/1.63  % (1683)Memory used [KB]: 13432
% 9.64/1.63  % (1683)Time elapsed: 1.230 s
% 9.64/1.63  % (1683)------------------------------
% 9.64/1.63  % (1683)------------------------------
% 10.47/1.71  % (1704)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 10.47/1.72  % (1672)Time limit reached!
% 10.47/1.72  % (1672)------------------------------
% 10.47/1.72  % (1672)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.47/1.72  % (1672)Termination reason: Time limit
% 10.47/1.72  
% 10.47/1.72  % (1672)Memory used [KB]: 10874
% 10.47/1.72  % (1672)Time elapsed: 1.316 s
% 10.47/1.72  % (1672)------------------------------
% 10.47/1.72  % (1672)------------------------------
% 10.47/1.74  % (1681)Time limit reached!
% 10.47/1.74  % (1681)------------------------------
% 10.47/1.74  % (1681)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.47/1.74  % (1681)Termination reason: Time limit
% 10.47/1.74  % (1681)Termination phase: Saturation
% 10.47/1.74  
% 10.47/1.74  % (1681)Memory used [KB]: 12025
% 10.47/1.74  % (1681)Time elapsed: 1.300 s
% 10.47/1.74  % (1681)------------------------------
% 10.47/1.74  % (1681)------------------------------
% 11.22/1.79  % (1705)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 11.48/1.88  % (1707)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 11.48/1.90  % (1706)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 12.29/1.95  % (1661)Time limit reached!
% 12.29/1.95  % (1661)------------------------------
% 12.29/1.95  % (1661)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.29/1.95  % (1661)Termination reason: Time limit
% 12.29/1.95  
% 12.29/1.95  % (1661)Memory used [KB]: 16886
% 12.29/1.95  % (1661)Time elapsed: 1.534 s
% 12.29/1.95  % (1661)------------------------------
% 12.29/1.95  % (1661)------------------------------
% 12.85/2.02  % (1704)Time limit reached!
% 12.85/2.02  % (1704)------------------------------
% 12.85/2.02  % (1704)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.85/2.02  % (1704)Termination reason: Time limit
% 12.85/2.02  
% 12.85/2.02  % (1704)Memory used [KB]: 3709
% 12.85/2.02  % (1704)Time elapsed: 0.421 s
% 12.85/2.02  % (1704)------------------------------
% 12.85/2.02  % (1704)------------------------------
% 12.85/2.05  % (1668)Time limit reached!
% 12.85/2.05  % (1668)------------------------------
% 12.85/2.05  % (1668)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.85/2.05  % (1668)Termination reason: Time limit
% 12.85/2.05  % (1668)Termination phase: Saturation
% 12.85/2.05  
% 12.85/2.05  % (1668)Memory used [KB]: 11641
% 12.85/2.05  % (1668)Time elapsed: 1.600 s
% 12.85/2.05  % (1668)------------------------------
% 12.85/2.05  % (1668)------------------------------
% 13.43/2.08  % (1708)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
% 13.43/2.13  % (1685)Time limit reached!
% 13.43/2.13  % (1685)------------------------------
% 13.43/2.13  % (1685)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.43/2.13  % (1685)Termination reason: Time limit
% 13.43/2.13  
% 13.43/2.13  % (1685)Memory used [KB]: 9594
% 13.43/2.13  % (1685)Time elapsed: 1.724 s
% 13.43/2.13  % (1685)------------------------------
% 13.43/2.13  % (1685)------------------------------
% 13.43/2.15  % (1709)lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73 on theBenchmark
% 13.43/2.17  % (1707)Time limit reached!
% 13.43/2.17  % (1707)------------------------------
% 13.43/2.17  % (1707)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.43/2.17  % (1707)Termination reason: Time limit
% 13.43/2.17  
% 13.43/2.17  % (1707)Memory used [KB]: 3326
% 13.43/2.17  % (1707)Time elapsed: 0.409 s
% 13.43/2.17  % (1707)------------------------------
% 13.43/2.17  % (1707)------------------------------
% 14.18/2.18  % (1710)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_275 on theBenchmark
% 14.46/2.27  % (1694)Time limit reached!
% 14.46/2.27  % (1694)------------------------------
% 14.46/2.27  % (1694)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.46/2.27  % (1694)Termination reason: Time limit
% 14.46/2.27  % (1694)Termination phase: Saturation
% 14.46/2.27  
% 14.46/2.27  % (1694)Memory used [KB]: 13944
% 14.46/2.27  % (1694)Time elapsed: 1.200 s
% 14.46/2.27  % (1694)------------------------------
% 14.46/2.27  % (1694)------------------------------
% 14.46/2.28  % (1671)Time limit reached!
% 14.46/2.28  % (1671)------------------------------
% 14.46/2.28  % (1671)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.46/2.28  % (1671)Termination reason: Time limit
% 14.46/2.28  
% 14.46/2.28  % (1671)Memory used [KB]: 14711
% 14.46/2.28  % (1671)Time elapsed: 1.815 s
% 14.46/2.28  % (1671)------------------------------
% 14.46/2.28  % (1671)------------------------------
% 14.46/2.29  % (1711)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_117 on theBenchmark
% 14.46/2.30  % (1690)Time limit reached!
% 14.46/2.30  % (1690)------------------------------
% 14.46/2.30  % (1690)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.46/2.30  % (1690)Termination reason: Time limit
% 14.46/2.30  
% 14.46/2.30  % (1690)Memory used [KB]: 12153
% 14.46/2.30  % (1690)Time elapsed: 1.738 s
% 14.46/2.30  % (1690)------------------------------
% 14.46/2.30  % (1690)------------------------------
% 14.46/2.30  % (1712)ott+10_8:1_av=off:bd=preordered:bsr=on:cond=fast:fsr=off:gs=on:gsem=off:lcm=predicate:nm=0:nwc=1.2:sp=reverse_arity:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 15.07/2.40  % (1703)Time limit reached!
% 15.07/2.40  % (1703)------------------------------
% 15.07/2.40  % (1703)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.07/2.40  % (1703)Termination reason: Time limit
% 15.07/2.40  
% 15.07/2.40  % (1703)Memory used [KB]: 12792
% 15.07/2.40  % (1703)Time elapsed: 1.220 s
% 15.07/2.40  % (1703)------------------------------
% 15.07/2.40  % (1703)------------------------------
% 16.25/2.41  % (1713)dis+3_24_av=off:bd=off:bs=unit_only:fsr=off:fde=unused:gs=on:irw=on:lma=on:nm=0:nwc=1.1:sos=on:uhcvi=on_180 on theBenchmark
% 16.25/2.41  % (1713)Refutation not found, incomplete strategy% (1713)------------------------------
% 16.25/2.41  % (1713)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.25/2.41  % (1713)Termination reason: Refutation not found, incomplete strategy
% 16.25/2.41  
% 16.25/2.41  % (1713)Memory used [KB]: 6268
% 16.25/2.41  % (1713)Time elapsed: 0.099 s
% 16.25/2.41  % (1713)------------------------------
% 16.25/2.41  % (1713)------------------------------
% 16.25/2.41  % (1714)lrs+1011_10_av=off:bce=on:cond=on:fsr=off:fde=unused:gs=on:nm=2:nwc=1.1:stl=30:sd=4:ss=axioms:s2a=on:st=1.5:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 16.25/2.44  % (1715)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_34 on theBenchmark
% 16.25/2.44  % (1715)Refutation not found, incomplete strategy% (1715)------------------------------
% 16.25/2.44  % (1715)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.25/2.44  % (1715)Termination reason: Refutation not found, incomplete strategy
% 16.25/2.44  
% 16.25/2.44  % (1715)Memory used [KB]: 10746
% 16.25/2.44  % (1715)Time elapsed: 0.099 s
% 16.25/2.44  % (1715)------------------------------
% 16.25/2.44  % (1715)------------------------------
% 16.25/2.44  % (1675)Time limit reached!
% 16.25/2.44  % (1675)------------------------------
% 16.25/2.44  % (1675)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.25/2.44  % (1675)Termination reason: Time limit
% 16.25/2.44  % (1675)Termination phase: Saturation
% 16.25/2.44  
% 16.25/2.44  % (1675)Memory used [KB]: 10362
% 16.25/2.44  % (1675)Time elapsed: 2.0000 s
% 16.25/2.44  % (1675)------------------------------
% 16.25/2.44  % (1675)------------------------------
% 16.25/2.45  % (1663)Time limit reached!
% 16.25/2.45  % (1663)------------------------------
% 16.25/2.45  % (1663)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.25/2.45  % (1663)Termination reason: Time limit
% 16.25/2.45  
% 16.25/2.45  % (1663)Memory used [KB]: 12281
% 16.25/2.45  % (1663)Time elapsed: 2.015 s
% 16.25/2.45  % (1663)------------------------------
% 16.25/2.45  % (1663)------------------------------
% 17.88/2.62  % (1712)Time limit reached!
% 17.88/2.62  % (1712)------------------------------
% 17.88/2.62  % (1712)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.88/2.62  % (1712)Termination reason: Time limit
% 17.88/2.62  % (1712)Termination phase: Saturation
% 17.88/2.62  
% 17.88/2.62  % (1712)Memory used [KB]: 9083
% 17.88/2.62  % (1712)Time elapsed: 0.400 s
% 17.88/2.62  % (1712)------------------------------
% 17.88/2.62  % (1712)------------------------------
% 17.88/2.68  % (1696)Time limit reached!
% 17.88/2.68  % (1696)------------------------------
% 17.88/2.68  % (1696)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.88/2.69  % (1696)Termination reason: Time limit
% 17.88/2.69  
% 17.88/2.69  % (1696)Memory used [KB]: 11257
% 17.88/2.69  % (1696)Time elapsed: 1.720 s
% 17.88/2.69  % (1696)------------------------------
% 17.88/2.69  % (1696)------------------------------
% 18.67/2.72  % (1714)Time limit reached!
% 18.67/2.72  % (1714)------------------------------
% 18.67/2.72  % (1714)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 18.67/2.73  % (1714)Termination reason: Time limit
% 18.67/2.73  
% 18.67/2.73  % (1714)Memory used [KB]: 9722
% 18.67/2.73  % (1714)Time elapsed: 0.410 s
% 18.67/2.73  % (1714)------------------------------
% 18.67/2.73  % (1714)------------------------------
% 19.44/2.81  % (1679)Time limit reached!
% 19.44/2.81  % (1679)------------------------------
% 19.44/2.81  % (1679)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 19.44/2.81  % (1679)Termination reason: Time limit
% 19.44/2.81  % (1679)Termination phase: Saturation
% 19.44/2.81  
% 19.44/2.81  % (1679)Memory used [KB]: 34029
% 19.44/2.81  % (1679)Time elapsed: 1.200 s
% 19.44/2.81  % (1679)------------------------------
% 19.44/2.81  % (1679)------------------------------
% 21.20/3.02  % (1676)Time limit reached!
% 21.20/3.02  % (1676)------------------------------
% 21.20/3.02  % (1676)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 21.20/3.03  % (1676)Termination reason: Time limit
% 21.20/3.03  
% 21.20/3.03  % (1676)Memory used [KB]: 21875
% 21.20/3.03  % (1676)Time elapsed: 2.619 s
% 21.20/3.03  % (1676)------------------------------
% 21.20/3.03  % (1676)------------------------------
% 21.20/3.07  % (1706)Time limit reached!
% 21.20/3.07  % (1706)------------------------------
% 21.20/3.07  % (1706)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 21.20/3.07  % (1706)Termination reason: Time limit
% 21.20/3.07  % (1706)Termination phase: Saturation
% 21.20/3.07  
% 21.20/3.07  % (1706)Memory used [KB]: 10746
% 21.20/3.07  % (1706)Time elapsed: 1.300 s
% 21.20/3.07  % (1706)------------------------------
% 21.20/3.07  % (1706)------------------------------
% 23.37/3.37  % (1689)Time limit reached!
% 23.37/3.37  % (1689)------------------------------
% 23.37/3.37  % (1689)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 23.37/3.37  % (1689)Termination reason: Time limit
% 23.37/3.37  % (1689)Termination phase: Saturation
% 23.37/3.37  
% 23.37/3.37  % (1689)Memory used [KB]: 9722
% 23.37/3.37  % (1689)Time elapsed: 2.800 s
% 23.37/3.37  % (1689)------------------------------
% 23.37/3.37  % (1689)------------------------------
% 24.33/3.41  % (1670)Time limit reached!
% 24.33/3.41  % (1670)------------------------------
% 24.33/3.41  % (1670)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 24.33/3.41  % (1670)Termination reason: Time limit
% 24.33/3.41  
% 24.33/3.41  % (1670)Memory used [KB]: 14072
% 24.33/3.41  % (1670)Time elapsed: 3.008 s
% 24.33/3.41  % (1670)------------------------------
% 24.33/3.41  % (1670)------------------------------
% 31.43/4.35  % (1687)Time limit reached!
% 31.43/4.35  % (1687)------------------------------
% 31.43/4.35  % (1687)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 31.43/4.35  % (1687)Termination reason: Time limit
% 31.43/4.35  
% 31.43/4.35  % (1687)Memory used [KB]: 14967
% 31.43/4.35  % (1687)Time elapsed: 3.933 s
% 31.43/4.35  % (1687)------------------------------
% 31.43/4.35  % (1687)------------------------------
% 33.99/4.67  % (1702)Time limit reached!
% 33.99/4.67  % (1702)------------------------------
% 33.99/4.67  % (1702)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 33.99/4.67  % (1702)Termination reason: Time limit
% 33.99/4.67  % (1702)Termination phase: Saturation
% 33.99/4.67  
% 33.99/4.67  % (1702)Memory used [KB]: 49508
% 33.99/4.67  % (1702)Time elapsed: 3.500 s
% 33.99/4.67  % (1702)------------------------------
% 33.99/4.67  % (1702)------------------------------
% 36.97/5.00  % (1666)Time limit reached!
% 36.97/5.00  % (1666)------------------------------
% 36.97/5.00  % (1666)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 36.97/5.00  % (1666)Termination reason: Time limit
% 36.97/5.00  % (1666)Termination phase: Saturation
% 36.97/5.00  
% 36.97/5.00  % (1666)Memory used [KB]: 23794
% 36.97/5.00  % (1666)Time elapsed: 4.600 s
% 36.97/5.00  % (1666)------------------------------
% 36.97/5.00  % (1666)------------------------------
% 41.76/5.60  % (1660)Time limit reached!
% 41.76/5.60  % (1660)------------------------------
% 41.76/5.60  % (1660)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 41.76/5.60  % (1660)Termination reason: Time limit
% 41.76/5.60  % (1660)Termination phase: Saturation
% 41.76/5.60  
% 41.76/5.60  % (1660)Memory used [KB]: 37227
% 41.76/5.60  % (1660)Time elapsed: 5.200 s
% 41.76/5.60  % (1660)------------------------------
% 41.76/5.60  % (1660)------------------------------
% 48.32/6.43  % (1695)Time limit reached!
% 48.32/6.43  % (1695)------------------------------
% 48.32/6.43  % (1695)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 48.32/6.43  % (1695)Termination reason: Time limit
% 48.32/6.43  % (1695)Termination phase: Saturation
% 48.32/6.43  
% 48.32/6.43  % (1695)Memory used [KB]: 54370
% 48.32/6.43  % (1695)Time elapsed: 5.500 s
% 48.32/6.43  % (1695)------------------------------
% 48.32/6.43  % (1695)------------------------------
% 53.11/7.03  % (1688)Refutation found. Thanks to Tanya!
% 53.11/7.03  % SZS status Theorem for theBenchmark
% 53.11/7.04  % SZS output start Proof for theBenchmark
% 53.11/7.04  fof(f12197,plain,(
% 53.11/7.04    $false),
% 53.11/7.04    inference(subsumption_resolution,[],[f12191,f466])).
% 53.11/7.04  fof(f466,plain,(
% 53.11/7.04    k4_tarski(sK0,sK0) != sK5(k4_tarski(sK0,sK0),k1_wellord2(k1_enumset1(sK0,sK0,sK0)))),
% 53.11/7.04    inference(subsumption_resolution,[],[f441,f69])).
% 53.11/7.04  fof(f69,plain,(
% 53.11/7.04    k1_wellord2(k1_enumset1(sK0,sK0,sK0)) != k1_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0))),
% 53.11/7.04    inference(definition_unfolding,[],[f42,f68,f68])).
% 53.11/7.04  fof(f68,plain,(
% 53.11/7.04    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 53.11/7.04    inference(definition_unfolding,[],[f58,f67])).
% 53.11/7.04  fof(f67,plain,(
% 53.11/7.04    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 53.11/7.04    inference(cnf_transformation,[],[f4])).
% 53.11/7.04  fof(f4,axiom,(
% 53.11/7.04    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 53.11/7.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 53.11/7.04  fof(f58,plain,(
% 53.11/7.04    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 53.11/7.04    inference(cnf_transformation,[],[f3])).
% 53.11/7.04  fof(f3,axiom,(
% 53.11/7.04    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 53.11/7.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 53.11/7.04  fof(f42,plain,(
% 53.11/7.04    k1_wellord2(k1_tarski(sK0)) != k1_tarski(k4_tarski(sK0,sK0))),
% 53.11/7.04    inference(cnf_transformation,[],[f22])).
% 53.11/7.04  fof(f22,plain,(
% 53.11/7.04    k1_wellord2(k1_tarski(sK0)) != k1_tarski(k4_tarski(sK0,sK0))),
% 53.11/7.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f21])).
% 53.11/7.04  fof(f21,plain,(
% 53.11/7.04    ? [X0] : k1_wellord2(k1_tarski(X0)) != k1_tarski(k4_tarski(X0,X0)) => k1_wellord2(k1_tarski(sK0)) != k1_tarski(k4_tarski(sK0,sK0))),
% 53.11/7.04    introduced(choice_axiom,[])).
% 53.11/7.04  fof(f14,plain,(
% 53.11/7.04    ? [X0] : k1_wellord2(k1_tarski(X0)) != k1_tarski(k4_tarski(X0,X0))),
% 53.11/7.04    inference(ennf_transformation,[],[f13])).
% 53.11/7.04  fof(f13,negated_conjecture,(
% 53.11/7.04    ~! [X0] : k1_wellord2(k1_tarski(X0)) = k1_tarski(k4_tarski(X0,X0))),
% 53.11/7.04    inference(negated_conjecture,[],[f12])).
% 53.11/7.04  fof(f12,conjecture,(
% 53.11/7.04    ! [X0] : k1_wellord2(k1_tarski(X0)) = k1_tarski(k4_tarski(X0,X0))),
% 53.11/7.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_wellord2)).
% 53.11/7.04  fof(f441,plain,(
% 53.11/7.04    k1_wellord2(k1_enumset1(sK0,sK0,sK0)) = k1_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0)) | k4_tarski(sK0,sK0) != sK5(k4_tarski(sK0,sK0),k1_wellord2(k1_enumset1(sK0,sK0,sK0)))),
% 53.11/7.04    inference(resolution,[],[f432,f70])).
% 53.11/7.04  fof(f70,plain,(
% 53.11/7.04    ( ! [X0,X1] : (k1_enumset1(X0,X0,X0) = X1 | sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) )),
% 53.11/7.04    inference(definition_unfolding,[],[f57,f68])).
% 53.11/7.04  fof(f57,plain,(
% 53.11/7.04    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) )),
% 53.11/7.04    inference(cnf_transformation,[],[f35])).
% 53.11/7.04  fof(f35,plain,(
% 53.11/7.04    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 53.11/7.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f33,f34])).
% 53.11/7.04  fof(f34,plain,(
% 53.11/7.04    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1))))),
% 53.11/7.04    introduced(choice_axiom,[])).
% 53.11/7.04  fof(f33,plain,(
% 53.11/7.04    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 53.11/7.04    inference(rectify,[],[f32])).
% 53.11/7.04  fof(f32,plain,(
% 53.11/7.04    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 53.11/7.04    inference(nnf_transformation,[],[f2])).
% 53.11/7.04  fof(f2,axiom,(
% 53.11/7.04    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 53.11/7.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 53.11/7.04  fof(f432,plain,(
% 53.11/7.04    r2_hidden(sK5(k4_tarski(sK0,sK0),k1_wellord2(k1_enumset1(sK0,sK0,sK0))),k1_wellord2(k1_enumset1(sK0,sK0,sK0)))),
% 53.11/7.04    inference(subsumption_resolution,[],[f431,f69])).
% 53.11/7.04  fof(f431,plain,(
% 53.11/7.04    r2_hidden(sK5(k4_tarski(sK0,sK0),k1_wellord2(k1_enumset1(sK0,sK0,sK0))),k1_wellord2(k1_enumset1(sK0,sK0,sK0))) | k1_wellord2(k1_enumset1(sK0,sK0,sK0)) = k1_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0))),
% 53.11/7.04    inference(trivial_inequality_removal,[],[f425])).
% 53.11/7.04  fof(f425,plain,(
% 53.11/7.04    r2_hidden(sK5(k4_tarski(sK0,sK0),k1_wellord2(k1_enumset1(sK0,sK0,sK0))),k1_wellord2(k1_enumset1(sK0,sK0,sK0))) | k1_wellord2(k1_enumset1(sK0,sK0,sK0)) != k1_wellord2(k1_enumset1(sK0,sK0,sK0)) | k1_wellord2(k1_enumset1(sK0,sK0,sK0)) = k1_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0))),
% 53.11/7.04    inference(resolution,[],[f424,f85])).
% 53.11/7.04  fof(f85,plain,(
% 53.11/7.04    ( ! [X3] : (r2_hidden(X3,k1_enumset1(X3,X3,X3))) )),
% 53.11/7.04    inference(equality_resolution,[],[f84])).
% 53.11/7.04  fof(f84,plain,(
% 53.11/7.04    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_enumset1(X3,X3,X3) != X1) )),
% 53.11/7.04    inference(equality_resolution,[],[f72])).
% 53.11/7.04  fof(f72,plain,(
% 53.11/7.04    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_enumset1(X0,X0,X0) != X1) )),
% 53.11/7.04    inference(definition_unfolding,[],[f55,f68])).
% 53.11/7.04  fof(f55,plain,(
% 53.11/7.04    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 53.11/7.04    inference(cnf_transformation,[],[f35])).
% 53.11/7.04  fof(f424,plain,(
% 53.11/7.04    ( ! [X1] : (~r2_hidden(sK0,X1) | r2_hidden(sK5(k4_tarski(sK0,sK0),k1_wellord2(X1)),k1_wellord2(X1)) | k1_wellord2(k1_enumset1(sK0,sK0,sK0)) != k1_wellord2(X1) | k1_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0)) = k1_wellord2(X1)) )),
% 53.11/7.04    inference(subsumption_resolution,[],[f419,f418])).
% 53.11/7.04  fof(f418,plain,(
% 53.11/7.04    ( ! [X0] : (~r2_hidden(sK0,X0) | r2_hidden(sK5(k4_tarski(sK0,sK0),k1_wellord2(X0)),k1_wellord2(X0)) | k1_wellord2(X0) != k1_wellord2(k1_enumset1(sK0,sK0,sK0)) | k1_wellord2(X0) = k1_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0)) | r2_hidden(sK6(sK0,sK0),sK0)) )),
% 53.11/7.04    inference(resolution,[],[f148,f63])).
% 53.11/7.04  fof(f63,plain,(
% 53.11/7.04    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK6(X0,X1),X0)) )),
% 53.11/7.04    inference(cnf_transformation,[],[f41])).
% 53.11/7.04  fof(f41,plain,(
% 53.11/7.04    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 53.11/7.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f39,f40])).
% 53.11/7.04  fof(f40,plain,(
% 53.11/7.04    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 53.11/7.04    introduced(choice_axiom,[])).
% 53.11/7.04  fof(f39,plain,(
% 53.11/7.04    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 53.11/7.04    inference(rectify,[],[f38])).
% 53.11/7.04  fof(f38,plain,(
% 53.11/7.04    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 53.11/7.04    inference(nnf_transformation,[],[f18])).
% 53.11/7.04  fof(f18,plain,(
% 53.11/7.04    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 53.11/7.04    inference(ennf_transformation,[],[f1])).
% 53.11/7.04  fof(f1,axiom,(
% 53.11/7.04    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 53.11/7.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 53.11/7.04  fof(f148,plain,(
% 53.11/7.04    ( ! [X2] : (~r1_tarski(sK0,sK0) | k1_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0)) = k1_wellord2(X2) | r2_hidden(sK5(k4_tarski(sK0,sK0),k1_wellord2(X2)),k1_wellord2(X2)) | k1_wellord2(k1_enumset1(sK0,sK0,sK0)) != k1_wellord2(X2) | ~r2_hidden(sK0,X2)) )),
% 53.11/7.04    inference(subsumption_resolution,[],[f147,f53])).
% 53.11/7.04  fof(f53,plain,(
% 53.11/7.04    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 53.11/7.04    inference(cnf_transformation,[],[f11])).
% 53.11/7.04  fof(f11,axiom,(
% 53.11/7.04    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 53.11/7.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).
% 53.11/7.04  fof(f147,plain,(
% 53.11/7.04    ( ! [X2] : (k1_wellord2(k1_enumset1(sK0,sK0,sK0)) != k1_wellord2(X2) | k1_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0)) = k1_wellord2(X2) | r2_hidden(sK5(k4_tarski(sK0,sK0),k1_wellord2(X2)),k1_wellord2(X2)) | ~r1_tarski(sK0,sK0) | ~r2_hidden(sK0,X2) | ~v1_relat_1(k1_wellord2(X2))) )),
% 53.11/7.04    inference(duplicate_literal_removal,[],[f140])).
% 53.11/7.04  fof(f140,plain,(
% 53.11/7.04    ( ! [X2] : (k1_wellord2(k1_enumset1(sK0,sK0,sK0)) != k1_wellord2(X2) | k1_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0)) = k1_wellord2(X2) | r2_hidden(sK5(k4_tarski(sK0,sK0),k1_wellord2(X2)),k1_wellord2(X2)) | ~r1_tarski(sK0,sK0) | ~r2_hidden(sK0,X2) | ~r2_hidden(sK0,X2) | ~v1_relat_1(k1_wellord2(X2))) )),
% 53.11/7.04    inference(resolution,[],[f104,f81])).
% 53.11/7.04  fof(f81,plain,(
% 53.11/7.04    ( ! [X4,X0,X5] : (r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0)) | ~r1_tarski(X4,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0) | ~v1_relat_1(k1_wellord2(X0))) )),
% 53.11/7.04    inference(equality_resolution,[],[f48])).
% 53.11/7.04  fof(f48,plain,(
% 53.11/7.04    ( ! [X4,X0,X5,X1] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0) | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 53.11/7.04    inference(cnf_transformation,[],[f31])).
% 53.11/7.04  fof(f31,plain,(
% 53.11/7.04    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ((~r1_tarski(sK3(X0,X1),sK4(X0,X1)) | ~r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)) & (r1_tarski(sK3(X0,X1),sK4(X0,X1)) | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)) & r2_hidden(sK4(X0,X1),X0) & r2_hidden(sK3(X0,X1),X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 53.11/7.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f29,f30])).
% 53.11/7.04  fof(f30,plain,(
% 53.11/7.04    ! [X1,X0] : (? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => ((~r1_tarski(sK3(X0,X1),sK4(X0,X1)) | ~r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)) & (r1_tarski(sK3(X0,X1),sK4(X0,X1)) | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)) & r2_hidden(sK4(X0,X1),X0) & r2_hidden(sK3(X0,X1),X0)))),
% 53.11/7.04    introduced(choice_axiom,[])).
% 53.11/7.04  fof(f29,plain,(
% 53.11/7.04    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 53.11/7.04    inference(rectify,[],[f28])).
% 53.11/7.04  fof(f28,plain,(
% 53.11/7.04    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 53.11/7.04    inference(flattening,[],[f27])).
% 53.11/7.04  fof(f27,plain,(
% 53.11/7.04    ! [X0,X1] : (((k1_wellord2(X0) = X1 | (? [X2,X3] : (((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1))) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0)) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 53.11/7.04    inference(nnf_transformation,[],[f17])).
% 53.11/7.04  fof(f17,plain,(
% 53.11/7.04    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 53.11/7.04    inference(flattening,[],[f16])).
% 53.11/7.04  fof(f16,plain,(
% 53.11/7.04    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 53.11/7.04    inference(ennf_transformation,[],[f10])).
% 53.11/7.04  fof(f10,axiom,(
% 53.11/7.04    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 53.11/7.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).
% 53.11/7.04  fof(f104,plain,(
% 53.11/7.04    ( ! [X0] : (~r2_hidden(k4_tarski(sK0,sK0),X0) | k1_wellord2(k1_enumset1(sK0,sK0,sK0)) != X0 | k1_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0)) = X0 | r2_hidden(sK5(k4_tarski(sK0,sK0),X0),X0)) )),
% 53.11/7.04    inference(trivial_inequality_removal,[],[f103])).
% 53.11/7.04  fof(f103,plain,(
% 53.11/7.04    ( ! [X0] : (k4_tarski(sK0,sK0) != k4_tarski(sK0,sK0) | k1_wellord2(k1_enumset1(sK0,sK0,sK0)) != X0 | ~r2_hidden(k4_tarski(sK0,sK0),X0) | k1_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0)) = X0 | r2_hidden(sK5(k4_tarski(sK0,sK0),X0),X0)) )),
% 53.11/7.04    inference(superposition,[],[f88,f71])).
% 53.11/7.04  fof(f71,plain,(
% 53.11/7.04    ( ! [X0,X1] : (k1_enumset1(X0,X0,X0) = X1 | sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)) )),
% 53.11/7.04    inference(definition_unfolding,[],[f56,f68])).
% 53.11/7.04  fof(f56,plain,(
% 53.11/7.04    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)) )),
% 53.11/7.04    inference(cnf_transformation,[],[f35])).
% 53.11/7.04  fof(f88,plain,(
% 53.11/7.04    ( ! [X1] : (k4_tarski(sK0,sK0) != sK5(k4_tarski(sK0,sK0),X1) | k1_wellord2(k1_enumset1(sK0,sK0,sK0)) != X1 | ~r2_hidden(sK5(k4_tarski(sK0,sK0),X1),X1)) )),
% 53.11/7.04    inference(superposition,[],[f69,f70])).
% 53.11/7.04  fof(f419,plain,(
% 53.11/7.04    ( ! [X1] : (k1_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0)) = k1_wellord2(X1) | r2_hidden(sK5(k4_tarski(sK0,sK0),k1_wellord2(X1)),k1_wellord2(X1)) | k1_wellord2(k1_enumset1(sK0,sK0,sK0)) != k1_wellord2(X1) | ~r2_hidden(sK0,X1) | ~r2_hidden(sK6(sK0,sK0),sK0)) )),
% 53.11/7.04    inference(resolution,[],[f148,f64])).
% 53.11/7.04  fof(f64,plain,(
% 53.11/7.04    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK6(X0,X1),X1)) )),
% 53.11/7.04    inference(cnf_transformation,[],[f41])).
% 53.11/7.04  fof(f12191,plain,(
% 53.11/7.04    k4_tarski(sK0,sK0) = sK5(k4_tarski(sK0,sK0),k1_wellord2(k1_enumset1(sK0,sK0,sK0)))),
% 53.11/7.04    inference(resolution,[],[f12188,f85])).
% 53.11/7.04  fof(f12188,plain,(
% 53.11/7.04    ( ! [X0] : (~r2_hidden(k4_tarski(sK0,sK0),k1_enumset1(X0,X0,X0)) | sK5(k4_tarski(sK0,sK0),k1_wellord2(k1_enumset1(sK0,sK0,sK0))) = X0) )),
% 53.11/7.04    inference(duplicate_literal_removal,[],[f12185])).
% 53.11/7.04  fof(f12185,plain,(
% 53.11/7.04    ( ! [X0] : (~r2_hidden(k4_tarski(sK0,sK0),k1_enumset1(X0,X0,X0)) | sK5(k4_tarski(sK0,sK0),k1_wellord2(k1_enumset1(sK0,sK0,sK0))) = X0 | sK5(k4_tarski(sK0,sK0),k1_wellord2(k1_enumset1(sK0,sK0,sK0))) = X0) )),
% 53.11/7.04    inference(superposition,[],[f9603,f9992])).
% 53.11/7.04  fof(f9992,plain,(
% 53.11/7.04    ( ! [X42] : (sK0 = sK2(k1_wellord2(k1_enumset1(sK0,sK0,sK0)),k1_enumset1(X42,X42,X42)) | sK5(k4_tarski(sK0,sK0),k1_wellord2(k1_enumset1(sK0,sK0,sK0))) = X42) )),
% 53.11/7.04    inference(resolution,[],[f9929,f86])).
% 53.11/7.04  fof(f86,plain,(
% 53.11/7.04    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_enumset1(X0,X0,X0))) )),
% 53.11/7.04    inference(equality_resolution,[],[f73])).
% 53.11/7.04  fof(f73,plain,(
% 53.11/7.04    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_enumset1(X0,X0,X0) != X1) )),
% 53.11/7.04    inference(definition_unfolding,[],[f54,f68])).
% 53.11/7.04  fof(f54,plain,(
% 53.11/7.04    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 53.11/7.04    inference(cnf_transformation,[],[f35])).
% 53.11/7.04  fof(f9929,plain,(
% 53.11/7.04    ( ! [X1] : (r2_hidden(sK5(k4_tarski(sK0,sK0),k1_wellord2(k1_enumset1(sK0,sK0,sK0))),X1) | sK0 = sK2(k1_wellord2(k1_enumset1(sK0,sK0,sK0)),X1)) )),
% 53.11/7.04    inference(resolution,[],[f9916,f86])).
% 53.11/7.04  fof(f9916,plain,(
% 53.11/7.04    ( ! [X0] : (r2_hidden(sK2(k1_wellord2(k1_enumset1(sK0,sK0,sK0)),X0),k1_enumset1(sK0,sK0,sK0)) | r2_hidden(sK5(k4_tarski(sK0,sK0),k1_wellord2(k1_enumset1(sK0,sK0,sK0))),X0)) )),
% 53.11/7.04    inference(subsumption_resolution,[],[f9911,f53])).
% 53.11/7.04  fof(f9911,plain,(
% 53.11/7.04    ( ! [X0] : (r2_hidden(sK2(k1_wellord2(k1_enumset1(sK0,sK0,sK0)),X0),k1_enumset1(sK0,sK0,sK0)) | r2_hidden(sK5(k4_tarski(sK0,sK0),k1_wellord2(k1_enumset1(sK0,sK0,sK0))),X0) | ~v1_relat_1(k1_wellord2(k1_enumset1(sK0,sK0,sK0)))) )),
% 53.11/7.04    inference(superposition,[],[f9385,f83])).
% 53.11/7.04  fof(f83,plain,(
% 53.11/7.04    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0 | ~v1_relat_1(k1_wellord2(X0))) )),
% 53.11/7.04    inference(equality_resolution,[],[f46])).
% 53.11/7.04  fof(f46,plain,(
% 53.11/7.04    ( ! [X0,X1] : (k3_relat_1(X1) = X0 | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 53.11/7.04    inference(cnf_transformation,[],[f31])).
% 53.11/7.04  fof(f9385,plain,(
% 53.11/7.04    ( ! [X26] : (r2_hidden(sK2(k1_wellord2(k1_enumset1(sK0,sK0,sK0)),X26),k3_relat_1(k1_wellord2(k1_enumset1(sK0,sK0,sK0)))) | r2_hidden(sK5(k4_tarski(sK0,sK0),k1_wellord2(k1_enumset1(sK0,sK0,sK0))),X26)) )),
% 53.11/7.04    inference(subsumption_resolution,[],[f9341,f53])).
% 53.11/7.04  fof(f9341,plain,(
% 53.11/7.04    ( ! [X26] : (r2_hidden(sK5(k4_tarski(sK0,sK0),k1_wellord2(k1_enumset1(sK0,sK0,sK0))),X26) | r2_hidden(sK2(k1_wellord2(k1_enumset1(sK0,sK0,sK0)),X26),k3_relat_1(k1_wellord2(k1_enumset1(sK0,sK0,sK0)))) | ~v1_relat_1(k1_wellord2(k1_enumset1(sK0,sK0,sK0)))) )),
% 53.11/7.04    inference(resolution,[],[f507,f66])).
% 53.11/7.04  fof(f66,plain,(
% 53.11/7.04    ( ! [X2,X0,X1] : (r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 53.11/7.04    inference(cnf_transformation,[],[f20])).
% 53.11/7.04  fof(f20,plain,(
% 53.11/7.04    ! [X0,X1,X2] : ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 53.11/7.04    inference(flattening,[],[f19])).
% 53.11/7.04  fof(f19,plain,(
% 53.11/7.04    ! [X0,X1,X2] : (((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 53.11/7.04    inference(ennf_transformation,[],[f9])).
% 53.11/7.04  fof(f9,axiom,(
% 53.11/7.04    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 53.11/7.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).
% 53.11/7.04  fof(f507,plain,(
% 53.11/7.04    ( ! [X4] : (r2_hidden(k4_tarski(sK1(k1_wellord2(k1_enumset1(sK0,sK0,sK0)),X4),sK2(k1_wellord2(k1_enumset1(sK0,sK0,sK0)),X4)),k1_wellord2(k1_enumset1(sK0,sK0,sK0))) | r2_hidden(sK5(k4_tarski(sK0,sK0),k1_wellord2(k1_enumset1(sK0,sK0,sK0))),X4)) )),
% 53.11/7.04    inference(subsumption_resolution,[],[f502,f53])).
% 53.11/7.04  fof(f502,plain,(
% 53.11/7.04    ( ! [X4] : (r2_hidden(sK5(k4_tarski(sK0,sK0),k1_wellord2(k1_enumset1(sK0,sK0,sK0))),X4) | r2_hidden(k4_tarski(sK1(k1_wellord2(k1_enumset1(sK0,sK0,sK0)),X4),sK2(k1_wellord2(k1_enumset1(sK0,sK0,sK0)),X4)),k1_wellord2(k1_enumset1(sK0,sK0,sK0))) | ~v1_relat_1(k1_wellord2(k1_enumset1(sK0,sK0,sK0)))) )),
% 53.11/7.04    inference(resolution,[],[f442,f44])).
% 53.11/7.04  fof(f44,plain,(
% 53.11/7.04    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) | ~v1_relat_1(X0)) )),
% 53.11/7.04    inference(cnf_transformation,[],[f26])).
% 53.11/7.04  fof(f26,plain,(
% 53.11/7.04    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | (~r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1) & r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 53.11/7.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f24,f25])).
% 53.11/7.04  fof(f25,plain,(
% 53.11/7.04    ! [X1,X0] : (? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0)) => (~r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1) & r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)))),
% 53.11/7.04    introduced(choice_axiom,[])).
% 53.11/7.04  fof(f24,plain,(
% 53.11/7.04    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 53.11/7.04    inference(rectify,[],[f23])).
% 53.11/7.04  fof(f23,plain,(
% 53.11/7.04    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 53.11/7.04    inference(nnf_transformation,[],[f15])).
% 53.11/7.04  fof(f15,plain,(
% 53.11/7.04    ! [X0] : (! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0))) | ~v1_relat_1(X0))),
% 53.11/7.04    inference(ennf_transformation,[],[f8])).
% 53.11/7.04  fof(f8,axiom,(
% 53.11/7.04    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) => r2_hidden(k4_tarski(X2,X3),X1))))),
% 53.11/7.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).
% 53.11/7.04  fof(f442,plain,(
% 53.11/7.04    ( ! [X0] : (~r1_tarski(k1_wellord2(k1_enumset1(sK0,sK0,sK0)),X0) | r2_hidden(sK5(k4_tarski(sK0,sK0),k1_wellord2(k1_enumset1(sK0,sK0,sK0))),X0)) )),
% 53.11/7.04    inference(resolution,[],[f432,f62])).
% 53.11/7.04  fof(f62,plain,(
% 53.11/7.04    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 53.11/7.04    inference(cnf_transformation,[],[f41])).
% 53.11/7.04  fof(f9603,plain,(
% 53.11/7.04    ( ! [X7] : (~r2_hidden(k4_tarski(sK0,sK2(k1_wellord2(k1_enumset1(sK0,sK0,sK0)),k1_enumset1(X7,X7,X7))),k1_enumset1(X7,X7,X7)) | sK5(k4_tarski(sK0,sK0),k1_wellord2(k1_enumset1(sK0,sK0,sK0))) = X7) )),
% 53.11/7.04    inference(subsumption_resolution,[],[f9585,f86])).
% 53.11/7.04  fof(f9585,plain,(
% 53.11/7.04    ( ! [X7] : (~r2_hidden(k4_tarski(sK0,sK2(k1_wellord2(k1_enumset1(sK0,sK0,sK0)),k1_enumset1(X7,X7,X7))),k1_enumset1(X7,X7,X7)) | r2_hidden(sK5(k4_tarski(sK0,sK0),k1_wellord2(k1_enumset1(sK0,sK0,sK0))),k1_enumset1(X7,X7,X7)) | sK5(k4_tarski(sK0,sK0),k1_wellord2(k1_enumset1(sK0,sK0,sK0))) = X7) )),
% 53.11/7.04    inference(superposition,[],[f508,f9538])).
% 53.11/7.04  fof(f9538,plain,(
% 53.11/7.04    ( ! [X42] : (sK0 = sK1(k1_wellord2(k1_enumset1(sK0,sK0,sK0)),k1_enumset1(X42,X42,X42)) | sK5(k4_tarski(sK0,sK0),k1_wellord2(k1_enumset1(sK0,sK0,sK0))) = X42) )),
% 53.11/7.04    inference(resolution,[],[f9475,f86])).
% 53.11/7.04  fof(f9475,plain,(
% 53.11/7.04    ( ! [X1] : (r2_hidden(sK5(k4_tarski(sK0,sK0),k1_wellord2(k1_enumset1(sK0,sK0,sK0))),X1) | sK0 = sK1(k1_wellord2(k1_enumset1(sK0,sK0,sK0)),X1)) )),
% 53.11/7.04    inference(resolution,[],[f9459,f86])).
% 53.11/7.04  fof(f9459,plain,(
% 53.11/7.04    ( ! [X0] : (r2_hidden(sK1(k1_wellord2(k1_enumset1(sK0,sK0,sK0)),X0),k1_enumset1(sK0,sK0,sK0)) | r2_hidden(sK5(k4_tarski(sK0,sK0),k1_wellord2(k1_enumset1(sK0,sK0,sK0))),X0)) )),
% 53.11/7.04    inference(subsumption_resolution,[],[f9454,f53])).
% 53.11/7.04  fof(f9454,plain,(
% 53.11/7.04    ( ! [X0] : (r2_hidden(sK1(k1_wellord2(k1_enumset1(sK0,sK0,sK0)),X0),k1_enumset1(sK0,sK0,sK0)) | r2_hidden(sK5(k4_tarski(sK0,sK0),k1_wellord2(k1_enumset1(sK0,sK0,sK0))),X0) | ~v1_relat_1(k1_wellord2(k1_enumset1(sK0,sK0,sK0)))) )),
% 53.11/7.04    inference(superposition,[],[f9384,f83])).
% 53.11/7.04  fof(f9384,plain,(
% 53.11/7.04    ( ! [X25] : (r2_hidden(sK1(k1_wellord2(k1_enumset1(sK0,sK0,sK0)),X25),k3_relat_1(k1_wellord2(k1_enumset1(sK0,sK0,sK0)))) | r2_hidden(sK5(k4_tarski(sK0,sK0),k1_wellord2(k1_enumset1(sK0,sK0,sK0))),X25)) )),
% 53.11/7.04    inference(subsumption_resolution,[],[f9340,f53])).
% 53.11/7.04  fof(f9340,plain,(
% 53.11/7.04    ( ! [X25] : (r2_hidden(sK5(k4_tarski(sK0,sK0),k1_wellord2(k1_enumset1(sK0,sK0,sK0))),X25) | r2_hidden(sK1(k1_wellord2(k1_enumset1(sK0,sK0,sK0)),X25),k3_relat_1(k1_wellord2(k1_enumset1(sK0,sK0,sK0)))) | ~v1_relat_1(k1_wellord2(k1_enumset1(sK0,sK0,sK0)))) )),
% 53.11/7.04    inference(resolution,[],[f507,f65])).
% 53.11/7.04  fof(f65,plain,(
% 53.11/7.04    ( ! [X2,X0,X1] : (r2_hidden(X0,k3_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 53.11/7.04    inference(cnf_transformation,[],[f20])).
% 53.11/7.04  fof(f508,plain,(
% 53.11/7.04    ( ! [X5] : (~r2_hidden(k4_tarski(sK1(k1_wellord2(k1_enumset1(sK0,sK0,sK0)),X5),sK2(k1_wellord2(k1_enumset1(sK0,sK0,sK0)),X5)),X5) | r2_hidden(sK5(k4_tarski(sK0,sK0),k1_wellord2(k1_enumset1(sK0,sK0,sK0))),X5)) )),
% 53.11/7.04    inference(subsumption_resolution,[],[f503,f53])).
% 53.11/7.04  fof(f503,plain,(
% 53.11/7.04    ( ! [X5] : (r2_hidden(sK5(k4_tarski(sK0,sK0),k1_wellord2(k1_enumset1(sK0,sK0,sK0))),X5) | ~r2_hidden(k4_tarski(sK1(k1_wellord2(k1_enumset1(sK0,sK0,sK0)),X5),sK2(k1_wellord2(k1_enumset1(sK0,sK0,sK0)),X5)),X5) | ~v1_relat_1(k1_wellord2(k1_enumset1(sK0,sK0,sK0)))) )),
% 53.11/7.04    inference(resolution,[],[f442,f45])).
% 53.11/7.04  fof(f45,plain,(
% 53.11/7.04    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1) | ~v1_relat_1(X0)) )),
% 53.11/7.04    inference(cnf_transformation,[],[f26])).
% 53.11/7.04  % SZS output end Proof for theBenchmark
% 53.11/7.04  % (1688)------------------------------
% 53.11/7.04  % (1688)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 53.11/7.04  % (1688)Termination reason: Refutation
% 53.11/7.04  
% 53.11/7.04  % (1688)Memory used [KB]: 25074
% 53.11/7.04  % (1688)Time elapsed: 6.435 s
% 53.11/7.04  % (1688)------------------------------
% 53.11/7.04  % (1688)------------------------------
% 53.11/7.05  % (1656)Success in time 6.695 s
%------------------------------------------------------------------------------
