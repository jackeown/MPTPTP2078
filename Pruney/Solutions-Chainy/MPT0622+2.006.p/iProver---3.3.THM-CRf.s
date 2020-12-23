%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:49:29 EST 2020

% Result     : Theorem 2.96s
% Output     : CNFRefutation 2.96s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 396 expanded)
%              Number of clauses        :   47 (  88 expanded)
%              Number of leaves         :   15 ( 112 expanded)
%              Depth                    :   14
%              Number of atoms          :  434 (2462 expanded)
%              Number of equality atoms :  282 (1397 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( ( k1_tarski(X0) = k2_relat_1(X2)
              & k1_tarski(X0) = k2_relat_1(X1)
              & k1_relat_1(X1) = k1_relat_1(X2) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ( ( k1_tarski(X0) = k2_relat_1(X2)
                & k1_tarski(X0) = k2_relat_1(X1)
                & k1_relat_1(X1) = k1_relat_1(X2) )
             => X1 = X2 ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & k1_tarski(X0) = k2_relat_1(X2)
          & k1_tarski(X0) = k2_relat_1(X1)
          & k1_relat_1(X1) = k1_relat_1(X2)
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & k1_tarski(X0) = k2_relat_1(X2)
          & k1_tarski(X0) = k2_relat_1(X1)
          & k1_relat_1(X1) = k1_relat_1(X2)
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & k1_tarski(X0) = k2_relat_1(X2)
          & k1_tarski(X0) = k2_relat_1(X1)
          & k1_relat_1(X1) = k1_relat_1(X2)
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( sK6 != X1
        & k1_tarski(X0) = k2_relat_1(sK6)
        & k1_tarski(X0) = k2_relat_1(X1)
        & k1_relat_1(sK6) = k1_relat_1(X1)
        & v1_funct_1(sK6)
        & v1_relat_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( X1 != X2
            & k1_tarski(X0) = k2_relat_1(X2)
            & k1_tarski(X0) = k2_relat_1(X1)
            & k1_relat_1(X1) = k1_relat_1(X2)
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( sK5 != X2
          & k1_tarski(sK4) = k2_relat_1(X2)
          & k1_tarski(sK4) = k2_relat_1(sK5)
          & k1_relat_1(sK5) = k1_relat_1(X2)
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(sK5)
      & v1_relat_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( sK5 != sK6
    & k1_tarski(sK4) = k2_relat_1(sK6)
    & k1_tarski(sK4) = k2_relat_1(sK5)
    & k1_relat_1(sK5) = k1_relat_1(sK6)
    & v1_funct_1(sK6)
    & v1_relat_1(sK6)
    & v1_funct_1(sK5)
    & v1_relat_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f18,f32,f31])).

fof(f61,plain,(
    k1_relat_1(sK5) = k1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f33])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & k1_relat_1(X0) = k1_relat_1(X1) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X1)) != k1_funct_1(X1,sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK3(X0,X1)) != k1_funct_1(X1,sK3(X0,X1))
            & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f29])).

fof(f55,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK3(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f59,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f33])).

fof(f60,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f33])).

fof(f57,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f33])).

fof(f58,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f33])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f62,plain,(
    k1_tarski(sK4) = k2_relat_1(sK5) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f65,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f36,f37])).

fof(f66,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f35,f65])).

fof(f67,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f34,f66])).

fof(f71,plain,(
    k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k2_relat_1(sK5) ),
    inference(definition_unfolding,[],[f62,f67])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X3 != X5
              & X2 != X5
              & X1 != X5
              & X0 != X5 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ( X3 = X5
            | X2 = X5
            | X1 = X5
            | X0 = X5 ) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X3,X2,X1,X0,X4] :
      ( sP0(X3,X2,X1,X0,X4)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ( X3 = X5
            | X2 = X5
            | X1 = X5
            | X0 = X5 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f20,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> sP0(X3,X2,X1,X0,X4) ) ),
    inference(definition_folding,[],[f11,f19])).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_enumset1(X0,X1,X2,X3) = X4
        | ~ sP0(X3,X2,X1,X0,X4) )
      & ( sP0(X3,X2,X1,X0,X4)
        | k2_enumset1(X0,X1,X2,X3) != X4 ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X3,X2,X1,X0,X4)
      | k2_enumset1(X0,X1,X2,X3) != X4 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X3,X2,X1,X0,X4)
      | k3_enumset1(X0,X0,X1,X2,X3) != X4 ) ),
    inference(definition_unfolding,[],[f48,f37])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] : sP0(X3,X2,X1,X0,k3_enumset1(X0,X0,X1,X2,X3)) ),
    inference(equality_resolution,[],[f69])).

fof(f21,plain,(
    ! [X3,X2,X1,X0,X4] :
      ( ( sP0(X3,X2,X1,X0,X4)
        | ? [X5] :
            ( ( ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 )
              | ~ r2_hidden(X5,X4) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X4)
              | ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X4) ) )
        | ~ sP0(X3,X2,X1,X0,X4) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f22,plain,(
    ! [X3,X2,X1,X0,X4] :
      ( ( sP0(X3,X2,X1,X0,X4)
        | ? [X5] :
            ( ( ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 )
              | ~ r2_hidden(X5,X4) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X4)
              | ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X4) ) )
        | ~ sP0(X3,X2,X1,X0,X4) ) ) ),
    inference(flattening,[],[f21])).

fof(f23,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP0(X0,X1,X2,X3,X4)
        | ? [X5] :
            ( ( ( X0 != X5
                & X1 != X5
                & X2 != X5
                & X3 != X5 )
              | ~ r2_hidden(X5,X4) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | X3 = X5
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X4)
              | ( X0 != X6
                & X1 != X6
                & X2 != X6
                & X3 != X6 ) )
            & ( X0 = X6
              | X1 = X6
              | X2 = X6
              | X3 = X6
              | ~ r2_hidden(X6,X4) ) )
        | ~ sP0(X0,X1,X2,X3,X4) ) ) ),
    inference(rectify,[],[f22])).

fof(f24,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( ( ( X0 != X5
              & X1 != X5
              & X2 != X5
              & X3 != X5 )
            | ~ r2_hidden(X5,X4) )
          & ( X0 = X5
            | X1 = X5
            | X2 = X5
            | X3 = X5
            | r2_hidden(X5,X4) ) )
     => ( ( ( sK1(X0,X1,X2,X3,X4) != X0
            & sK1(X0,X1,X2,X3,X4) != X1
            & sK1(X0,X1,X2,X3,X4) != X2
            & sK1(X0,X1,X2,X3,X4) != X3 )
          | ~ r2_hidden(sK1(X0,X1,X2,X3,X4),X4) )
        & ( sK1(X0,X1,X2,X3,X4) = X0
          | sK1(X0,X1,X2,X3,X4) = X1
          | sK1(X0,X1,X2,X3,X4) = X2
          | sK1(X0,X1,X2,X3,X4) = X3
          | r2_hidden(sK1(X0,X1,X2,X3,X4),X4) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP0(X0,X1,X2,X3,X4)
        | ( ( ( sK1(X0,X1,X2,X3,X4) != X0
              & sK1(X0,X1,X2,X3,X4) != X1
              & sK1(X0,X1,X2,X3,X4) != X2
              & sK1(X0,X1,X2,X3,X4) != X3 )
            | ~ r2_hidden(sK1(X0,X1,X2,X3,X4),X4) )
          & ( sK1(X0,X1,X2,X3,X4) = X0
            | sK1(X0,X1,X2,X3,X4) = X1
            | sK1(X0,X1,X2,X3,X4) = X2
            | sK1(X0,X1,X2,X3,X4) = X3
            | r2_hidden(sK1(X0,X1,X2,X3,X4),X4) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X4)
              | ( X0 != X6
                & X1 != X6
                & X2 != X6
                & X3 != X6 ) )
            & ( X0 = X6
              | X1 = X6
              | X2 = X6
              | X3 = X6
              | ~ r2_hidden(X6,X4) ) )
        | ~ sP0(X0,X1,X2,X3,X4) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f24])).

fof(f38,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( X0 = X6
      | X1 = X6
      | X2 = X6
      | X3 = X6
      | ~ r2_hidden(X6,X4)
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f63,plain,(
    k1_tarski(sK4) = k2_relat_1(sK6) ),
    inference(cnf_transformation,[],[f33])).

fof(f70,plain,(
    k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k2_relat_1(sK6) ),
    inference(definition_unfolding,[],[f63,f67])).

fof(f56,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_funct_1(X0,sK3(X0,X1)) != k1_funct_1(X1,sK3(X0,X1))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f64,plain,(
    sK5 != sK6 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_22,negated_conjecture,
    ( k1_relat_1(sK5) = k1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_18,plain,
    ( r2_hidden(sK3(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | X1 = X0
    | k1_relat_1(X0) != k1_relat_1(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1318,plain,
    ( X0 = X1
    | k1_relat_1(X1) != k1_relat_1(X0)
    | r2_hidden(sK3(X1,X0),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1762,plain,
    ( k1_relat_1(X0) != k1_relat_1(sK5)
    | sK6 = X0
    | r2_hidden(sK3(X0,sK6),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_22,c_1318])).

cnf(c_24,negated_conjecture,
    ( v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_29,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_30,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2070,plain,
    ( v1_funct_1(X0) != iProver_top
    | k1_relat_1(X0) != k1_relat_1(sK5)
    | sK6 = X0
    | r2_hidden(sK3(X0,sK6),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1762,c_29,c_30])).

cnf(c_2071,plain,
    ( k1_relat_1(X0) != k1_relat_1(sK5)
    | sK6 = X0
    | r2_hidden(sK3(X0,sK6),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2070])).

cnf(c_2083,plain,
    ( sK6 = sK5
    | r2_hidden(sK3(sK5,sK6),k1_relat_1(sK5)) = iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2071])).

cnf(c_26,negated_conjecture,
    ( v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_27,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_28,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2218,plain,
    ( sK6 = sK5
    | r2_hidden(sK3(sK5,sK6),k1_relat_1(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2083,c_27,c_28])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1320,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_21,negated_conjecture,
    ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k2_relat_1(sK5) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_11,plain,
    ( sP0(X0,X1,X2,X3,k3_enumset1(X3,X3,X2,X1,X0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1324,plain,
    ( sP0(X0,X1,X2,X3,k3_enumset1(X3,X3,X2,X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1967,plain,
    ( sP0(sK4,sK4,sK4,sK4,k2_relat_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_21,c_1324])).

cnf(c_9,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | ~ r2_hidden(X5,X4)
    | X5 = X3
    | X5 = X2
    | X5 = X1
    | X5 = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1326,plain,
    ( X0 = X1
    | X0 = X2
    | X0 = X3
    | X0 = X4
    | sP0(X4,X3,X2,X1,X5) != iProver_top
    | r2_hidden(X0,X5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_6556,plain,
    ( sK4 = X0
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1967,c_1326])).

cnf(c_6576,plain,
    ( k1_funct_1(sK5,X0) = sK4
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1320,c_6556])).

cnf(c_6700,plain,
    ( k1_funct_1(sK5,X0) = sK4
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6576,c_27,c_28])).

cnf(c_6708,plain,
    ( k1_funct_1(sK5,sK3(sK5,sK6)) = sK4
    | sK6 = sK5 ),
    inference(superposition,[status(thm)],[c_2218,c_6700])).

cnf(c_20,negated_conjecture,
    ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k2_relat_1(sK6) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1356,plain,
    ( k2_relat_1(sK5) = k2_relat_1(sK6) ),
    inference(light_normalisation,[status(thm)],[c_20,c_21])).

cnf(c_4108,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK5)) = iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1356,c_1320])).

cnf(c_4122,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK5)) = iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4108,c_22])).

cnf(c_4442,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4122,c_29,c_30])).

cnf(c_6578,plain,
    ( k1_funct_1(sK6,X0) = sK4
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4442,c_6556])).

cnf(c_6677,plain,
    ( k1_funct_1(sK6,sK3(sK5,sK6)) = sK4
    | sK6 = sK5 ),
    inference(superposition,[status(thm)],[c_2218,c_6578])).

cnf(c_922,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3610,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_922])).

cnf(c_923,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2383,plain,
    ( k1_funct_1(sK6,sK3(sK5,sK6)) != X0
    | k1_funct_1(sK6,sK3(sK5,sK6)) = k1_funct_1(sK5,sK3(sK5,sK6))
    | k1_funct_1(sK5,sK3(sK5,sK6)) != X0 ),
    inference(instantiation,[status(thm)],[c_923])).

cnf(c_2384,plain,
    ( k1_funct_1(sK6,sK3(sK5,sK6)) = k1_funct_1(sK5,sK3(sK5,sK6))
    | k1_funct_1(sK6,sK3(sK5,sK6)) != sK4
    | k1_funct_1(sK5,sK3(sK5,sK6)) != sK4 ),
    inference(instantiation,[status(thm)],[c_2383])).

cnf(c_1549,plain,
    ( sK6 != X0
    | sK5 != X0
    | sK5 = sK6 ),
    inference(instantiation,[status(thm)],[c_923])).

cnf(c_2295,plain,
    ( sK6 != sK5
    | sK5 = sK6
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1549])).

cnf(c_17,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | X0 = X1
    | k1_funct_1(X0,sK3(X1,X0)) != k1_funct_1(X1,sK3(X1,X0))
    | k1_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1674,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK5)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK5)
    | X0 = sK5
    | k1_funct_1(X0,sK3(sK5,X0)) != k1_funct_1(sK5,sK3(sK5,X0))
    | k1_relat_1(sK5) != k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1976,plain,
    ( ~ v1_relat_1(sK6)
    | ~ v1_relat_1(sK5)
    | ~ v1_funct_1(sK6)
    | ~ v1_funct_1(sK5)
    | k1_funct_1(sK6,sK3(sK5,sK6)) != k1_funct_1(sK5,sK3(sK5,sK6))
    | k1_relat_1(sK5) != k1_relat_1(sK6)
    | sK6 = sK5 ),
    inference(instantiation,[status(thm)],[c_1674])).

cnf(c_19,negated_conjecture,
    ( sK5 != sK6 ),
    inference(cnf_transformation,[],[f64])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6708,c_6677,c_3610,c_2384,c_2295,c_1976,c_19,c_22,c_23,c_24,c_25,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:08:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.96/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.96/1.01  
% 2.96/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.96/1.01  
% 2.96/1.01  ------  iProver source info
% 2.96/1.01  
% 2.96/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.96/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.96/1.01  git: non_committed_changes: false
% 2.96/1.01  git: last_make_outside_of_git: false
% 2.96/1.01  
% 2.96/1.01  ------ 
% 2.96/1.01  
% 2.96/1.01  ------ Input Options
% 2.96/1.01  
% 2.96/1.01  --out_options                           all
% 2.96/1.01  --tptp_safe_out                         true
% 2.96/1.01  --problem_path                          ""
% 2.96/1.01  --include_path                          ""
% 2.96/1.01  --clausifier                            res/vclausify_rel
% 2.96/1.01  --clausifier_options                    --mode clausify
% 2.96/1.01  --stdin                                 false
% 2.96/1.01  --stats_out                             all
% 2.96/1.01  
% 2.96/1.01  ------ General Options
% 2.96/1.01  
% 2.96/1.01  --fof                                   false
% 2.96/1.01  --time_out_real                         305.
% 2.96/1.01  --time_out_virtual                      -1.
% 2.96/1.01  --symbol_type_check                     false
% 2.96/1.01  --clausify_out                          false
% 2.96/1.01  --sig_cnt_out                           false
% 2.96/1.01  --trig_cnt_out                          false
% 2.96/1.01  --trig_cnt_out_tolerance                1.
% 2.96/1.01  --trig_cnt_out_sk_spl                   false
% 2.96/1.01  --abstr_cl_out                          false
% 2.96/1.01  
% 2.96/1.01  ------ Global Options
% 2.96/1.01  
% 2.96/1.01  --schedule                              default
% 2.96/1.01  --add_important_lit                     false
% 2.96/1.01  --prop_solver_per_cl                    1000
% 2.96/1.01  --min_unsat_core                        false
% 2.96/1.01  --soft_assumptions                      false
% 2.96/1.01  --soft_lemma_size                       3
% 2.96/1.01  --prop_impl_unit_size                   0
% 2.96/1.01  --prop_impl_unit                        []
% 2.96/1.01  --share_sel_clauses                     true
% 2.96/1.01  --reset_solvers                         false
% 2.96/1.01  --bc_imp_inh                            [conj_cone]
% 2.96/1.01  --conj_cone_tolerance                   3.
% 2.96/1.01  --extra_neg_conj                        none
% 2.96/1.01  --large_theory_mode                     true
% 2.96/1.01  --prolific_symb_bound                   200
% 2.96/1.01  --lt_threshold                          2000
% 2.96/1.01  --clause_weak_htbl                      true
% 2.96/1.01  --gc_record_bc_elim                     false
% 2.96/1.01  
% 2.96/1.01  ------ Preprocessing Options
% 2.96/1.01  
% 2.96/1.01  --preprocessing_flag                    true
% 2.96/1.01  --time_out_prep_mult                    0.1
% 2.96/1.01  --splitting_mode                        input
% 2.96/1.01  --splitting_grd                         true
% 2.96/1.01  --splitting_cvd                         false
% 2.96/1.01  --splitting_cvd_svl                     false
% 2.96/1.01  --splitting_nvd                         32
% 2.96/1.01  --sub_typing                            true
% 2.96/1.01  --prep_gs_sim                           true
% 2.96/1.01  --prep_unflatten                        true
% 2.96/1.01  --prep_res_sim                          true
% 2.96/1.01  --prep_upred                            true
% 2.96/1.01  --prep_sem_filter                       exhaustive
% 2.96/1.01  --prep_sem_filter_out                   false
% 2.96/1.01  --pred_elim                             true
% 2.96/1.01  --res_sim_input                         true
% 2.96/1.01  --eq_ax_congr_red                       true
% 2.96/1.01  --pure_diseq_elim                       true
% 2.96/1.01  --brand_transform                       false
% 2.96/1.01  --non_eq_to_eq                          false
% 2.96/1.01  --prep_def_merge                        true
% 2.96/1.01  --prep_def_merge_prop_impl              false
% 2.96/1.01  --prep_def_merge_mbd                    true
% 2.96/1.01  --prep_def_merge_tr_red                 false
% 2.96/1.01  --prep_def_merge_tr_cl                  false
% 2.96/1.01  --smt_preprocessing                     true
% 2.96/1.01  --smt_ac_axioms                         fast
% 2.96/1.01  --preprocessed_out                      false
% 2.96/1.01  --preprocessed_stats                    false
% 2.96/1.01  
% 2.96/1.01  ------ Abstraction refinement Options
% 2.96/1.01  
% 2.96/1.01  --abstr_ref                             []
% 2.96/1.01  --abstr_ref_prep                        false
% 2.96/1.01  --abstr_ref_until_sat                   false
% 2.96/1.01  --abstr_ref_sig_restrict                funpre
% 2.96/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.96/1.01  --abstr_ref_under                       []
% 2.96/1.01  
% 2.96/1.01  ------ SAT Options
% 2.96/1.01  
% 2.96/1.01  --sat_mode                              false
% 2.96/1.01  --sat_fm_restart_options                ""
% 2.96/1.01  --sat_gr_def                            false
% 2.96/1.01  --sat_epr_types                         true
% 2.96/1.01  --sat_non_cyclic_types                  false
% 2.96/1.01  --sat_finite_models                     false
% 2.96/1.01  --sat_fm_lemmas                         false
% 2.96/1.01  --sat_fm_prep                           false
% 2.96/1.01  --sat_fm_uc_incr                        true
% 2.96/1.01  --sat_out_model                         small
% 2.96/1.01  --sat_out_clauses                       false
% 2.96/1.01  
% 2.96/1.01  ------ QBF Options
% 2.96/1.01  
% 2.96/1.01  --qbf_mode                              false
% 2.96/1.01  --qbf_elim_univ                         false
% 2.96/1.01  --qbf_dom_inst                          none
% 2.96/1.01  --qbf_dom_pre_inst                      false
% 2.96/1.01  --qbf_sk_in                             false
% 2.96/1.01  --qbf_pred_elim                         true
% 2.96/1.01  --qbf_split                             512
% 2.96/1.01  
% 2.96/1.01  ------ BMC1 Options
% 2.96/1.01  
% 2.96/1.01  --bmc1_incremental                      false
% 2.96/1.01  --bmc1_axioms                           reachable_all
% 2.96/1.01  --bmc1_min_bound                        0
% 2.96/1.01  --bmc1_max_bound                        -1
% 2.96/1.01  --bmc1_max_bound_default                -1
% 2.96/1.01  --bmc1_symbol_reachability              true
% 2.96/1.01  --bmc1_property_lemmas                  false
% 2.96/1.01  --bmc1_k_induction                      false
% 2.96/1.01  --bmc1_non_equiv_states                 false
% 2.96/1.01  --bmc1_deadlock                         false
% 2.96/1.01  --bmc1_ucm                              false
% 2.96/1.01  --bmc1_add_unsat_core                   none
% 2.96/1.01  --bmc1_unsat_core_children              false
% 2.96/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.96/1.01  --bmc1_out_stat                         full
% 2.96/1.01  --bmc1_ground_init                      false
% 2.96/1.01  --bmc1_pre_inst_next_state              false
% 2.96/1.01  --bmc1_pre_inst_state                   false
% 2.96/1.01  --bmc1_pre_inst_reach_state             false
% 2.96/1.01  --bmc1_out_unsat_core                   false
% 2.96/1.01  --bmc1_aig_witness_out                  false
% 2.96/1.01  --bmc1_verbose                          false
% 2.96/1.01  --bmc1_dump_clauses_tptp                false
% 2.96/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.96/1.01  --bmc1_dump_file                        -
% 2.96/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.96/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.96/1.01  --bmc1_ucm_extend_mode                  1
% 2.96/1.01  --bmc1_ucm_init_mode                    2
% 2.96/1.01  --bmc1_ucm_cone_mode                    none
% 2.96/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.96/1.01  --bmc1_ucm_relax_model                  4
% 2.96/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.96/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.96/1.01  --bmc1_ucm_layered_model                none
% 2.96/1.02  --bmc1_ucm_max_lemma_size               10
% 2.96/1.02  
% 2.96/1.02  ------ AIG Options
% 2.96/1.02  
% 2.96/1.02  --aig_mode                              false
% 2.96/1.02  
% 2.96/1.02  ------ Instantiation Options
% 2.96/1.02  
% 2.96/1.02  --instantiation_flag                    true
% 2.96/1.02  --inst_sos_flag                         false
% 2.96/1.02  --inst_sos_phase                        true
% 2.96/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.96/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.96/1.02  --inst_lit_sel_side                     num_symb
% 2.96/1.02  --inst_solver_per_active                1400
% 2.96/1.02  --inst_solver_calls_frac                1.
% 2.96/1.02  --inst_passive_queue_type               priority_queues
% 2.96/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.96/1.02  --inst_passive_queues_freq              [25;2]
% 2.96/1.02  --inst_dismatching                      true
% 2.96/1.02  --inst_eager_unprocessed_to_passive     true
% 2.96/1.02  --inst_prop_sim_given                   true
% 2.96/1.02  --inst_prop_sim_new                     false
% 2.96/1.02  --inst_subs_new                         false
% 2.96/1.02  --inst_eq_res_simp                      false
% 2.96/1.02  --inst_subs_given                       false
% 2.96/1.02  --inst_orphan_elimination               true
% 2.96/1.02  --inst_learning_loop_flag               true
% 2.96/1.02  --inst_learning_start                   3000
% 2.96/1.02  --inst_learning_factor                  2
% 2.96/1.02  --inst_start_prop_sim_after_learn       3
% 2.96/1.02  --inst_sel_renew                        solver
% 2.96/1.02  --inst_lit_activity_flag                true
% 2.96/1.02  --inst_restr_to_given                   false
% 2.96/1.02  --inst_activity_threshold               500
% 2.96/1.02  --inst_out_proof                        true
% 2.96/1.02  
% 2.96/1.02  ------ Resolution Options
% 2.96/1.02  
% 2.96/1.02  --resolution_flag                       true
% 2.96/1.02  --res_lit_sel                           adaptive
% 2.96/1.02  --res_lit_sel_side                      none
% 2.96/1.02  --res_ordering                          kbo
% 2.96/1.02  --res_to_prop_solver                    active
% 2.96/1.02  --res_prop_simpl_new                    false
% 2.96/1.02  --res_prop_simpl_given                  true
% 2.96/1.02  --res_passive_queue_type                priority_queues
% 2.96/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.96/1.02  --res_passive_queues_freq               [15;5]
% 2.96/1.02  --res_forward_subs                      full
% 2.96/1.02  --res_backward_subs                     full
% 2.96/1.02  --res_forward_subs_resolution           true
% 2.96/1.02  --res_backward_subs_resolution          true
% 2.96/1.02  --res_orphan_elimination                true
% 2.96/1.02  --res_time_limit                        2.
% 2.96/1.02  --res_out_proof                         true
% 2.96/1.02  
% 2.96/1.02  ------ Superposition Options
% 2.96/1.02  
% 2.96/1.02  --superposition_flag                    true
% 2.96/1.02  --sup_passive_queue_type                priority_queues
% 2.96/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.96/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.96/1.02  --demod_completeness_check              fast
% 2.96/1.02  --demod_use_ground                      true
% 2.96/1.02  --sup_to_prop_solver                    passive
% 2.96/1.02  --sup_prop_simpl_new                    true
% 2.96/1.02  --sup_prop_simpl_given                  true
% 2.96/1.02  --sup_fun_splitting                     false
% 2.96/1.02  --sup_smt_interval                      50000
% 2.96/1.02  
% 2.96/1.02  ------ Superposition Simplification Setup
% 2.96/1.02  
% 2.96/1.02  --sup_indices_passive                   []
% 2.96/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.96/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.96/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.96/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.96/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.96/1.02  --sup_full_bw                           [BwDemod]
% 2.96/1.02  --sup_immed_triv                        [TrivRules]
% 2.96/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.96/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.96/1.02  --sup_immed_bw_main                     []
% 2.96/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.96/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.96/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.96/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.96/1.02  
% 2.96/1.02  ------ Combination Options
% 2.96/1.02  
% 2.96/1.02  --comb_res_mult                         3
% 2.96/1.02  --comb_sup_mult                         2
% 2.96/1.02  --comb_inst_mult                        10
% 2.96/1.02  
% 2.96/1.02  ------ Debug Options
% 2.96/1.02  
% 2.96/1.02  --dbg_backtrace                         false
% 2.96/1.02  --dbg_dump_prop_clauses                 false
% 2.96/1.02  --dbg_dump_prop_clauses_file            -
% 2.96/1.02  --dbg_out_stat                          false
% 2.96/1.02  ------ Parsing...
% 2.96/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.96/1.02  
% 2.96/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.96/1.02  
% 2.96/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.96/1.02  
% 2.96/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.96/1.02  ------ Proving...
% 2.96/1.02  ------ Problem Properties 
% 2.96/1.02  
% 2.96/1.02  
% 2.96/1.02  clauses                                 27
% 2.96/1.02  conjectures                             8
% 2.96/1.02  EPR                                     10
% 2.96/1.02  Horn                                    24
% 2.96/1.02  unary                                   12
% 2.96/1.02  binary                                  6
% 2.96/1.02  lits                                    66
% 2.96/1.02  lits eq                                 24
% 2.96/1.02  fd_pure                                 0
% 2.96/1.02  fd_pseudo                               0
% 2.96/1.02  fd_cond                                 0
% 2.96/1.02  fd_pseudo_cond                          4
% 2.96/1.02  AC symbols                              0
% 2.96/1.02  
% 2.96/1.02  ------ Schedule dynamic 5 is on 
% 2.96/1.02  
% 2.96/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.96/1.02  
% 2.96/1.02  
% 2.96/1.02  ------ 
% 2.96/1.02  Current options:
% 2.96/1.02  ------ 
% 2.96/1.02  
% 2.96/1.02  ------ Input Options
% 2.96/1.02  
% 2.96/1.02  --out_options                           all
% 2.96/1.02  --tptp_safe_out                         true
% 2.96/1.02  --problem_path                          ""
% 2.96/1.02  --include_path                          ""
% 2.96/1.02  --clausifier                            res/vclausify_rel
% 2.96/1.02  --clausifier_options                    --mode clausify
% 2.96/1.02  --stdin                                 false
% 2.96/1.02  --stats_out                             all
% 2.96/1.02  
% 2.96/1.02  ------ General Options
% 2.96/1.02  
% 2.96/1.02  --fof                                   false
% 2.96/1.02  --time_out_real                         305.
% 2.96/1.02  --time_out_virtual                      -1.
% 2.96/1.02  --symbol_type_check                     false
% 2.96/1.02  --clausify_out                          false
% 2.96/1.02  --sig_cnt_out                           false
% 2.96/1.02  --trig_cnt_out                          false
% 2.96/1.02  --trig_cnt_out_tolerance                1.
% 2.96/1.02  --trig_cnt_out_sk_spl                   false
% 2.96/1.02  --abstr_cl_out                          false
% 2.96/1.02  
% 2.96/1.02  ------ Global Options
% 2.96/1.02  
% 2.96/1.02  --schedule                              default
% 2.96/1.02  --add_important_lit                     false
% 2.96/1.02  --prop_solver_per_cl                    1000
% 2.96/1.02  --min_unsat_core                        false
% 2.96/1.02  --soft_assumptions                      false
% 2.96/1.02  --soft_lemma_size                       3
% 2.96/1.02  --prop_impl_unit_size                   0
% 2.96/1.02  --prop_impl_unit                        []
% 2.96/1.02  --share_sel_clauses                     true
% 2.96/1.02  --reset_solvers                         false
% 2.96/1.02  --bc_imp_inh                            [conj_cone]
% 2.96/1.02  --conj_cone_tolerance                   3.
% 2.96/1.02  --extra_neg_conj                        none
% 2.96/1.02  --large_theory_mode                     true
% 2.96/1.02  --prolific_symb_bound                   200
% 2.96/1.02  --lt_threshold                          2000
% 2.96/1.02  --clause_weak_htbl                      true
% 2.96/1.02  --gc_record_bc_elim                     false
% 2.96/1.02  
% 2.96/1.02  ------ Preprocessing Options
% 2.96/1.02  
% 2.96/1.02  --preprocessing_flag                    true
% 2.96/1.02  --time_out_prep_mult                    0.1
% 2.96/1.02  --splitting_mode                        input
% 2.96/1.02  --splitting_grd                         true
% 2.96/1.02  --splitting_cvd                         false
% 2.96/1.02  --splitting_cvd_svl                     false
% 2.96/1.02  --splitting_nvd                         32
% 2.96/1.02  --sub_typing                            true
% 2.96/1.02  --prep_gs_sim                           true
% 2.96/1.02  --prep_unflatten                        true
% 2.96/1.02  --prep_res_sim                          true
% 2.96/1.02  --prep_upred                            true
% 2.96/1.02  --prep_sem_filter                       exhaustive
% 2.96/1.02  --prep_sem_filter_out                   false
% 2.96/1.02  --pred_elim                             true
% 2.96/1.02  --res_sim_input                         true
% 2.96/1.02  --eq_ax_congr_red                       true
% 2.96/1.02  --pure_diseq_elim                       true
% 2.96/1.02  --brand_transform                       false
% 2.96/1.02  --non_eq_to_eq                          false
% 2.96/1.02  --prep_def_merge                        true
% 2.96/1.02  --prep_def_merge_prop_impl              false
% 2.96/1.02  --prep_def_merge_mbd                    true
% 2.96/1.02  --prep_def_merge_tr_red                 false
% 2.96/1.02  --prep_def_merge_tr_cl                  false
% 2.96/1.02  --smt_preprocessing                     true
% 2.96/1.02  --smt_ac_axioms                         fast
% 2.96/1.02  --preprocessed_out                      false
% 2.96/1.02  --preprocessed_stats                    false
% 2.96/1.02  
% 2.96/1.02  ------ Abstraction refinement Options
% 2.96/1.02  
% 2.96/1.02  --abstr_ref                             []
% 2.96/1.02  --abstr_ref_prep                        false
% 2.96/1.02  --abstr_ref_until_sat                   false
% 2.96/1.02  --abstr_ref_sig_restrict                funpre
% 2.96/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.96/1.02  --abstr_ref_under                       []
% 2.96/1.02  
% 2.96/1.02  ------ SAT Options
% 2.96/1.02  
% 2.96/1.02  --sat_mode                              false
% 2.96/1.02  --sat_fm_restart_options                ""
% 2.96/1.02  --sat_gr_def                            false
% 2.96/1.02  --sat_epr_types                         true
% 2.96/1.02  --sat_non_cyclic_types                  false
% 2.96/1.02  --sat_finite_models                     false
% 2.96/1.02  --sat_fm_lemmas                         false
% 2.96/1.02  --sat_fm_prep                           false
% 2.96/1.02  --sat_fm_uc_incr                        true
% 2.96/1.02  --sat_out_model                         small
% 2.96/1.02  --sat_out_clauses                       false
% 2.96/1.02  
% 2.96/1.02  ------ QBF Options
% 2.96/1.02  
% 2.96/1.02  --qbf_mode                              false
% 2.96/1.02  --qbf_elim_univ                         false
% 2.96/1.02  --qbf_dom_inst                          none
% 2.96/1.02  --qbf_dom_pre_inst                      false
% 2.96/1.02  --qbf_sk_in                             false
% 2.96/1.02  --qbf_pred_elim                         true
% 2.96/1.02  --qbf_split                             512
% 2.96/1.02  
% 2.96/1.02  ------ BMC1 Options
% 2.96/1.02  
% 2.96/1.02  --bmc1_incremental                      false
% 2.96/1.02  --bmc1_axioms                           reachable_all
% 2.96/1.02  --bmc1_min_bound                        0
% 2.96/1.02  --bmc1_max_bound                        -1
% 2.96/1.02  --bmc1_max_bound_default                -1
% 2.96/1.02  --bmc1_symbol_reachability              true
% 2.96/1.02  --bmc1_property_lemmas                  false
% 2.96/1.02  --bmc1_k_induction                      false
% 2.96/1.02  --bmc1_non_equiv_states                 false
% 2.96/1.02  --bmc1_deadlock                         false
% 2.96/1.02  --bmc1_ucm                              false
% 2.96/1.02  --bmc1_add_unsat_core                   none
% 2.96/1.02  --bmc1_unsat_core_children              false
% 2.96/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.96/1.02  --bmc1_out_stat                         full
% 2.96/1.02  --bmc1_ground_init                      false
% 2.96/1.02  --bmc1_pre_inst_next_state              false
% 2.96/1.02  --bmc1_pre_inst_state                   false
% 2.96/1.02  --bmc1_pre_inst_reach_state             false
% 2.96/1.02  --bmc1_out_unsat_core                   false
% 2.96/1.02  --bmc1_aig_witness_out                  false
% 2.96/1.02  --bmc1_verbose                          false
% 2.96/1.02  --bmc1_dump_clauses_tptp                false
% 2.96/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.96/1.02  --bmc1_dump_file                        -
% 2.96/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.96/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.96/1.02  --bmc1_ucm_extend_mode                  1
% 2.96/1.02  --bmc1_ucm_init_mode                    2
% 2.96/1.02  --bmc1_ucm_cone_mode                    none
% 2.96/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.96/1.02  --bmc1_ucm_relax_model                  4
% 2.96/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.96/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.96/1.02  --bmc1_ucm_layered_model                none
% 2.96/1.02  --bmc1_ucm_max_lemma_size               10
% 2.96/1.02  
% 2.96/1.02  ------ AIG Options
% 2.96/1.02  
% 2.96/1.02  --aig_mode                              false
% 2.96/1.02  
% 2.96/1.02  ------ Instantiation Options
% 2.96/1.02  
% 2.96/1.02  --instantiation_flag                    true
% 2.96/1.02  --inst_sos_flag                         false
% 2.96/1.02  --inst_sos_phase                        true
% 2.96/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.96/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.96/1.02  --inst_lit_sel_side                     none
% 2.96/1.02  --inst_solver_per_active                1400
% 2.96/1.02  --inst_solver_calls_frac                1.
% 2.96/1.02  --inst_passive_queue_type               priority_queues
% 2.96/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.96/1.02  --inst_passive_queues_freq              [25;2]
% 2.96/1.02  --inst_dismatching                      true
% 2.96/1.02  --inst_eager_unprocessed_to_passive     true
% 2.96/1.02  --inst_prop_sim_given                   true
% 2.96/1.02  --inst_prop_sim_new                     false
% 2.96/1.02  --inst_subs_new                         false
% 2.96/1.02  --inst_eq_res_simp                      false
% 2.96/1.02  --inst_subs_given                       false
% 2.96/1.02  --inst_orphan_elimination               true
% 2.96/1.02  --inst_learning_loop_flag               true
% 2.96/1.02  --inst_learning_start                   3000
% 2.96/1.02  --inst_learning_factor                  2
% 2.96/1.02  --inst_start_prop_sim_after_learn       3
% 2.96/1.02  --inst_sel_renew                        solver
% 2.96/1.02  --inst_lit_activity_flag                true
% 2.96/1.02  --inst_restr_to_given                   false
% 2.96/1.02  --inst_activity_threshold               500
% 2.96/1.02  --inst_out_proof                        true
% 2.96/1.02  
% 2.96/1.02  ------ Resolution Options
% 2.96/1.02  
% 2.96/1.02  --resolution_flag                       false
% 2.96/1.02  --res_lit_sel                           adaptive
% 2.96/1.02  --res_lit_sel_side                      none
% 2.96/1.02  --res_ordering                          kbo
% 2.96/1.02  --res_to_prop_solver                    active
% 2.96/1.02  --res_prop_simpl_new                    false
% 2.96/1.02  --res_prop_simpl_given                  true
% 2.96/1.02  --res_passive_queue_type                priority_queues
% 2.96/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.96/1.02  --res_passive_queues_freq               [15;5]
% 2.96/1.02  --res_forward_subs                      full
% 2.96/1.02  --res_backward_subs                     full
% 2.96/1.02  --res_forward_subs_resolution           true
% 2.96/1.02  --res_backward_subs_resolution          true
% 2.96/1.02  --res_orphan_elimination                true
% 2.96/1.02  --res_time_limit                        2.
% 2.96/1.02  --res_out_proof                         true
% 2.96/1.02  
% 2.96/1.02  ------ Superposition Options
% 2.96/1.02  
% 2.96/1.02  --superposition_flag                    true
% 2.96/1.02  --sup_passive_queue_type                priority_queues
% 2.96/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.96/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.96/1.02  --demod_completeness_check              fast
% 2.96/1.02  --demod_use_ground                      true
% 2.96/1.02  --sup_to_prop_solver                    passive
% 2.96/1.02  --sup_prop_simpl_new                    true
% 2.96/1.02  --sup_prop_simpl_given                  true
% 2.96/1.02  --sup_fun_splitting                     false
% 2.96/1.02  --sup_smt_interval                      50000
% 2.96/1.02  
% 2.96/1.02  ------ Superposition Simplification Setup
% 2.96/1.02  
% 2.96/1.02  --sup_indices_passive                   []
% 2.96/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.96/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.96/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.96/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.96/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.96/1.02  --sup_full_bw                           [BwDemod]
% 2.96/1.02  --sup_immed_triv                        [TrivRules]
% 2.96/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.96/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.96/1.02  --sup_immed_bw_main                     []
% 2.96/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.96/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.96/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.96/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.96/1.02  
% 2.96/1.02  ------ Combination Options
% 2.96/1.02  
% 2.96/1.02  --comb_res_mult                         3
% 2.96/1.02  --comb_sup_mult                         2
% 2.96/1.02  --comb_inst_mult                        10
% 2.96/1.02  
% 2.96/1.02  ------ Debug Options
% 2.96/1.02  
% 2.96/1.02  --dbg_backtrace                         false
% 2.96/1.02  --dbg_dump_prop_clauses                 false
% 2.96/1.02  --dbg_dump_prop_clauses_file            -
% 2.96/1.02  --dbg_out_stat                          false
% 2.96/1.02  
% 2.96/1.02  
% 2.96/1.02  
% 2.96/1.02  
% 2.96/1.02  ------ Proving...
% 2.96/1.02  
% 2.96/1.02  
% 2.96/1.02  % SZS status Theorem for theBenchmark.p
% 2.96/1.02  
% 2.96/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 2.96/1.02  
% 2.96/1.02  fof(f9,conjecture,(
% 2.96/1.02    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_tarski(X0) = k2_relat_1(X2) & k1_tarski(X0) = k2_relat_1(X1) & k1_relat_1(X1) = k1_relat_1(X2)) => X1 = X2)))),
% 2.96/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.96/1.02  
% 2.96/1.02  fof(f10,negated_conjecture,(
% 2.96/1.02    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_tarski(X0) = k2_relat_1(X2) & k1_tarski(X0) = k2_relat_1(X1) & k1_relat_1(X1) = k1_relat_1(X2)) => X1 = X2)))),
% 2.96/1.02    inference(negated_conjecture,[],[f9])).
% 2.96/1.02  
% 2.96/1.02  fof(f17,plain,(
% 2.96/1.02    ? [X0,X1] : (? [X2] : ((X1 != X2 & (k1_tarski(X0) = k2_relat_1(X2) & k1_tarski(X0) = k2_relat_1(X1) & k1_relat_1(X1) = k1_relat_1(X2))) & (v1_funct_1(X2) & v1_relat_1(X2))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 2.96/1.02    inference(ennf_transformation,[],[f10])).
% 2.96/1.02  
% 2.96/1.02  fof(f18,plain,(
% 2.96/1.02    ? [X0,X1] : (? [X2] : (X1 != X2 & k1_tarski(X0) = k2_relat_1(X2) & k1_tarski(X0) = k2_relat_1(X1) & k1_relat_1(X1) = k1_relat_1(X2) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 2.96/1.02    inference(flattening,[],[f17])).
% 2.96/1.02  
% 2.96/1.02  fof(f32,plain,(
% 2.96/1.02    ( ! [X0,X1] : (? [X2] : (X1 != X2 & k1_tarski(X0) = k2_relat_1(X2) & k1_tarski(X0) = k2_relat_1(X1) & k1_relat_1(X1) = k1_relat_1(X2) & v1_funct_1(X2) & v1_relat_1(X2)) => (sK6 != X1 & k1_tarski(X0) = k2_relat_1(sK6) & k1_tarski(X0) = k2_relat_1(X1) & k1_relat_1(sK6) = k1_relat_1(X1) & v1_funct_1(sK6) & v1_relat_1(sK6))) )),
% 2.96/1.02    introduced(choice_axiom,[])).
% 2.96/1.02  
% 2.96/1.02  fof(f31,plain,(
% 2.96/1.02    ? [X0,X1] : (? [X2] : (X1 != X2 & k1_tarski(X0) = k2_relat_1(X2) & k1_tarski(X0) = k2_relat_1(X1) & k1_relat_1(X1) = k1_relat_1(X2) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : (sK5 != X2 & k1_tarski(sK4) = k2_relat_1(X2) & k1_tarski(sK4) = k2_relat_1(sK5) & k1_relat_1(sK5) = k1_relat_1(X2) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(sK5) & v1_relat_1(sK5))),
% 2.96/1.02    introduced(choice_axiom,[])).
% 2.96/1.02  
% 2.96/1.02  fof(f33,plain,(
% 2.96/1.02    (sK5 != sK6 & k1_tarski(sK4) = k2_relat_1(sK6) & k1_tarski(sK4) = k2_relat_1(sK5) & k1_relat_1(sK5) = k1_relat_1(sK6) & v1_funct_1(sK6) & v1_relat_1(sK6)) & v1_funct_1(sK5) & v1_relat_1(sK5)),
% 2.96/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f18,f32,f31])).
% 2.96/1.02  
% 2.96/1.02  fof(f61,plain,(
% 2.96/1.02    k1_relat_1(sK5) = k1_relat_1(sK6)),
% 2.96/1.02    inference(cnf_transformation,[],[f33])).
% 2.96/1.02  
% 2.96/1.02  fof(f8,axiom,(
% 2.96/1.02    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 2.96/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.96/1.02  
% 2.96/1.02  fof(f15,plain,(
% 2.96/1.02    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.96/1.02    inference(ennf_transformation,[],[f8])).
% 2.96/1.02  
% 2.96/1.02  fof(f16,plain,(
% 2.96/1.02    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.96/1.02    inference(flattening,[],[f15])).
% 2.96/1.02  
% 2.96/1.02  fof(f29,plain,(
% 2.96/1.02    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X1)) != k1_funct_1(X1,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))))),
% 2.96/1.02    introduced(choice_axiom,[])).
% 2.96/1.02  
% 2.96/1.02  fof(f30,plain,(
% 2.96/1.02    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK3(X0,X1)) != k1_funct_1(X1,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.96/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f29])).
% 2.96/1.02  
% 2.96/1.02  fof(f55,plain,(
% 2.96/1.02    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK3(X0,X1),k1_relat_1(X0)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.96/1.02    inference(cnf_transformation,[],[f30])).
% 2.96/1.02  
% 2.96/1.02  fof(f59,plain,(
% 2.96/1.02    v1_relat_1(sK6)),
% 2.96/1.02    inference(cnf_transformation,[],[f33])).
% 2.96/1.02  
% 2.96/1.02  fof(f60,plain,(
% 2.96/1.02    v1_funct_1(sK6)),
% 2.96/1.02    inference(cnf_transformation,[],[f33])).
% 2.96/1.02  
% 2.96/1.02  fof(f57,plain,(
% 2.96/1.02    v1_relat_1(sK5)),
% 2.96/1.02    inference(cnf_transformation,[],[f33])).
% 2.96/1.02  
% 2.96/1.02  fof(f58,plain,(
% 2.96/1.02    v1_funct_1(sK5)),
% 2.96/1.02    inference(cnf_transformation,[],[f33])).
% 2.96/1.02  
% 2.96/1.02  fof(f7,axiom,(
% 2.96/1.02    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 2.96/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.96/1.02  
% 2.96/1.02  fof(f13,plain,(
% 2.96/1.02    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.96/1.02    inference(ennf_transformation,[],[f7])).
% 2.96/1.02  
% 2.96/1.02  fof(f14,plain,(
% 2.96/1.02    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.96/1.02    inference(flattening,[],[f13])).
% 2.96/1.02  
% 2.96/1.02  fof(f54,plain,(
% 2.96/1.02    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.96/1.02    inference(cnf_transformation,[],[f14])).
% 2.96/1.02  
% 2.96/1.02  fof(f62,plain,(
% 2.96/1.02    k1_tarski(sK4) = k2_relat_1(sK5)),
% 2.96/1.02    inference(cnf_transformation,[],[f33])).
% 2.96/1.02  
% 2.96/1.02  fof(f1,axiom,(
% 2.96/1.02    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.96/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.96/1.02  
% 2.96/1.02  fof(f34,plain,(
% 2.96/1.02    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.96/1.02    inference(cnf_transformation,[],[f1])).
% 2.96/1.02  
% 2.96/1.02  fof(f2,axiom,(
% 2.96/1.02    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.96/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.96/1.02  
% 2.96/1.02  fof(f35,plain,(
% 2.96/1.02    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.96/1.02    inference(cnf_transformation,[],[f2])).
% 2.96/1.02  
% 2.96/1.02  fof(f3,axiom,(
% 2.96/1.02    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.96/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.96/1.02  
% 2.96/1.02  fof(f36,plain,(
% 2.96/1.02    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.96/1.02    inference(cnf_transformation,[],[f3])).
% 2.96/1.02  
% 2.96/1.02  fof(f4,axiom,(
% 2.96/1.02    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.96/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.96/1.02  
% 2.96/1.02  fof(f37,plain,(
% 2.96/1.02    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.96/1.02    inference(cnf_transformation,[],[f4])).
% 2.96/1.02  
% 2.96/1.02  fof(f65,plain,(
% 2.96/1.02    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 2.96/1.02    inference(definition_unfolding,[],[f36,f37])).
% 2.96/1.02  
% 2.96/1.02  fof(f66,plain,(
% 2.96/1.02    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 2.96/1.02    inference(definition_unfolding,[],[f35,f65])).
% 2.96/1.02  
% 2.96/1.02  fof(f67,plain,(
% 2.96/1.02    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 2.96/1.02    inference(definition_unfolding,[],[f34,f66])).
% 2.96/1.02  
% 2.96/1.02  fof(f71,plain,(
% 2.96/1.02    k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k2_relat_1(sK5)),
% 2.96/1.02    inference(definition_unfolding,[],[f62,f67])).
% 2.96/1.02  
% 2.96/1.02  fof(f5,axiom,(
% 2.96/1.02    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> ! [X5] : (r2_hidden(X5,X4) <=> ~(X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)))),
% 2.96/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.96/1.02  
% 2.96/1.02  fof(f11,plain,(
% 2.96/1.02    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> ! [X5] : (r2_hidden(X5,X4) <=> (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5)))),
% 2.96/1.02    inference(ennf_transformation,[],[f5])).
% 2.96/1.02  
% 2.96/1.02  fof(f19,plain,(
% 2.96/1.02    ! [X3,X2,X1,X0,X4] : (sP0(X3,X2,X1,X0,X4) <=> ! [X5] : (r2_hidden(X5,X4) <=> (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5)))),
% 2.96/1.02    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.96/1.02  
% 2.96/1.02  fof(f20,plain,(
% 2.96/1.02    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> sP0(X3,X2,X1,X0,X4))),
% 2.96/1.02    inference(definition_folding,[],[f11,f19])).
% 2.96/1.02  
% 2.96/1.02  fof(f26,plain,(
% 2.96/1.02    ! [X0,X1,X2,X3,X4] : ((k2_enumset1(X0,X1,X2,X3) = X4 | ~sP0(X3,X2,X1,X0,X4)) & (sP0(X3,X2,X1,X0,X4) | k2_enumset1(X0,X1,X2,X3) != X4))),
% 2.96/1.02    inference(nnf_transformation,[],[f20])).
% 2.96/1.02  
% 2.96/1.02  fof(f48,plain,(
% 2.96/1.02    ( ! [X4,X2,X0,X3,X1] : (sP0(X3,X2,X1,X0,X4) | k2_enumset1(X0,X1,X2,X3) != X4) )),
% 2.96/1.02    inference(cnf_transformation,[],[f26])).
% 2.96/1.02  
% 2.96/1.02  fof(f69,plain,(
% 2.96/1.02    ( ! [X4,X2,X0,X3,X1] : (sP0(X3,X2,X1,X0,X4) | k3_enumset1(X0,X0,X1,X2,X3) != X4) )),
% 2.96/1.02    inference(definition_unfolding,[],[f48,f37])).
% 2.96/1.02  
% 2.96/1.02  fof(f76,plain,(
% 2.96/1.02    ( ! [X2,X0,X3,X1] : (sP0(X3,X2,X1,X0,k3_enumset1(X0,X0,X1,X2,X3))) )),
% 2.96/1.02    inference(equality_resolution,[],[f69])).
% 2.96/1.02  
% 2.96/1.02  fof(f21,plain,(
% 2.96/1.02    ! [X3,X2,X1,X0,X4] : ((sP0(X3,X2,X1,X0,X4) | ? [X5] : (((X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5) | ~r2_hidden(X5,X4)) & ((X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5) | r2_hidden(X5,X4)))) & (! [X5] : ((r2_hidden(X5,X4) | (X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)) & ((X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5) | ~r2_hidden(X5,X4))) | ~sP0(X3,X2,X1,X0,X4)))),
% 2.96/1.02    inference(nnf_transformation,[],[f19])).
% 2.96/1.02  
% 2.96/1.02  fof(f22,plain,(
% 2.96/1.02    ! [X3,X2,X1,X0,X4] : ((sP0(X3,X2,X1,X0,X4) | ? [X5] : (((X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5) | ~r2_hidden(X5,X4)) & (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5 | r2_hidden(X5,X4)))) & (! [X5] : ((r2_hidden(X5,X4) | (X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)) & (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X4))) | ~sP0(X3,X2,X1,X0,X4)))),
% 2.96/1.02    inference(flattening,[],[f21])).
% 2.96/1.02  
% 2.96/1.02  fof(f23,plain,(
% 2.96/1.02    ! [X0,X1,X2,X3,X4] : ((sP0(X0,X1,X2,X3,X4) | ? [X5] : (((X0 != X5 & X1 != X5 & X2 != X5 & X3 != X5) | ~r2_hidden(X5,X4)) & (X0 = X5 | X1 = X5 | X2 = X5 | X3 = X5 | r2_hidden(X5,X4)))) & (! [X6] : ((r2_hidden(X6,X4) | (X0 != X6 & X1 != X6 & X2 != X6 & X3 != X6)) & (X0 = X6 | X1 = X6 | X2 = X6 | X3 = X6 | ~r2_hidden(X6,X4))) | ~sP0(X0,X1,X2,X3,X4)))),
% 2.96/1.02    inference(rectify,[],[f22])).
% 2.96/1.02  
% 2.96/1.02  fof(f24,plain,(
% 2.96/1.02    ! [X4,X3,X2,X1,X0] : (? [X5] : (((X0 != X5 & X1 != X5 & X2 != X5 & X3 != X5) | ~r2_hidden(X5,X4)) & (X0 = X5 | X1 = X5 | X2 = X5 | X3 = X5 | r2_hidden(X5,X4))) => (((sK1(X0,X1,X2,X3,X4) != X0 & sK1(X0,X1,X2,X3,X4) != X1 & sK1(X0,X1,X2,X3,X4) != X2 & sK1(X0,X1,X2,X3,X4) != X3) | ~r2_hidden(sK1(X0,X1,X2,X3,X4),X4)) & (sK1(X0,X1,X2,X3,X4) = X0 | sK1(X0,X1,X2,X3,X4) = X1 | sK1(X0,X1,X2,X3,X4) = X2 | sK1(X0,X1,X2,X3,X4) = X3 | r2_hidden(sK1(X0,X1,X2,X3,X4),X4))))),
% 2.96/1.02    introduced(choice_axiom,[])).
% 2.96/1.02  
% 2.96/1.02  fof(f25,plain,(
% 2.96/1.02    ! [X0,X1,X2,X3,X4] : ((sP0(X0,X1,X2,X3,X4) | (((sK1(X0,X1,X2,X3,X4) != X0 & sK1(X0,X1,X2,X3,X4) != X1 & sK1(X0,X1,X2,X3,X4) != X2 & sK1(X0,X1,X2,X3,X4) != X3) | ~r2_hidden(sK1(X0,X1,X2,X3,X4),X4)) & (sK1(X0,X1,X2,X3,X4) = X0 | sK1(X0,X1,X2,X3,X4) = X1 | sK1(X0,X1,X2,X3,X4) = X2 | sK1(X0,X1,X2,X3,X4) = X3 | r2_hidden(sK1(X0,X1,X2,X3,X4),X4)))) & (! [X6] : ((r2_hidden(X6,X4) | (X0 != X6 & X1 != X6 & X2 != X6 & X3 != X6)) & (X0 = X6 | X1 = X6 | X2 = X6 | X3 = X6 | ~r2_hidden(X6,X4))) | ~sP0(X0,X1,X2,X3,X4)))),
% 2.96/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f24])).
% 2.96/1.02  
% 2.96/1.02  fof(f38,plain,(
% 2.96/1.02    ( ! [X6,X4,X2,X0,X3,X1] : (X0 = X6 | X1 = X6 | X2 = X6 | X3 = X6 | ~r2_hidden(X6,X4) | ~sP0(X0,X1,X2,X3,X4)) )),
% 2.96/1.02    inference(cnf_transformation,[],[f25])).
% 2.96/1.02  
% 2.96/1.02  fof(f63,plain,(
% 2.96/1.02    k1_tarski(sK4) = k2_relat_1(sK6)),
% 2.96/1.02    inference(cnf_transformation,[],[f33])).
% 2.96/1.02  
% 2.96/1.02  fof(f70,plain,(
% 2.96/1.02    k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k2_relat_1(sK6)),
% 2.96/1.02    inference(definition_unfolding,[],[f63,f67])).
% 2.96/1.02  
% 2.96/1.02  fof(f56,plain,(
% 2.96/1.02    ( ! [X0,X1] : (X0 = X1 | k1_funct_1(X0,sK3(X0,X1)) != k1_funct_1(X1,sK3(X0,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.96/1.02    inference(cnf_transformation,[],[f30])).
% 2.96/1.02  
% 2.96/1.02  fof(f64,plain,(
% 2.96/1.02    sK5 != sK6),
% 2.96/1.02    inference(cnf_transformation,[],[f33])).
% 2.96/1.02  
% 2.96/1.02  cnf(c_22,negated_conjecture,
% 2.96/1.02      ( k1_relat_1(sK5) = k1_relat_1(sK6) ),
% 2.96/1.02      inference(cnf_transformation,[],[f61]) ).
% 2.96/1.02  
% 2.96/1.02  cnf(c_18,plain,
% 2.96/1.02      ( r2_hidden(sK3(X0,X1),k1_relat_1(X0))
% 2.96/1.02      | ~ v1_relat_1(X1)
% 2.96/1.02      | ~ v1_relat_1(X0)
% 2.96/1.02      | ~ v1_funct_1(X1)
% 2.96/1.02      | ~ v1_funct_1(X0)
% 2.96/1.02      | X1 = X0
% 2.96/1.02      | k1_relat_1(X0) != k1_relat_1(X1) ),
% 2.96/1.02      inference(cnf_transformation,[],[f55]) ).
% 2.96/1.02  
% 2.96/1.02  cnf(c_1318,plain,
% 2.96/1.02      ( X0 = X1
% 2.96/1.02      | k1_relat_1(X1) != k1_relat_1(X0)
% 2.96/1.02      | r2_hidden(sK3(X1,X0),k1_relat_1(X1)) = iProver_top
% 2.96/1.02      | v1_relat_1(X0) != iProver_top
% 2.96/1.02      | v1_relat_1(X1) != iProver_top
% 2.96/1.02      | v1_funct_1(X0) != iProver_top
% 2.96/1.02      | v1_funct_1(X1) != iProver_top ),
% 2.96/1.02      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.96/1.02  
% 2.96/1.02  cnf(c_1762,plain,
% 2.96/1.02      ( k1_relat_1(X0) != k1_relat_1(sK5)
% 2.96/1.02      | sK6 = X0
% 2.96/1.02      | r2_hidden(sK3(X0,sK6),k1_relat_1(X0)) = iProver_top
% 2.96/1.02      | v1_relat_1(X0) != iProver_top
% 2.96/1.02      | v1_relat_1(sK6) != iProver_top
% 2.96/1.02      | v1_funct_1(X0) != iProver_top
% 2.96/1.02      | v1_funct_1(sK6) != iProver_top ),
% 2.96/1.02      inference(superposition,[status(thm)],[c_22,c_1318]) ).
% 2.96/1.02  
% 2.96/1.02  cnf(c_24,negated_conjecture,
% 2.96/1.02      ( v1_relat_1(sK6) ),
% 2.96/1.02      inference(cnf_transformation,[],[f59]) ).
% 2.96/1.02  
% 2.96/1.02  cnf(c_29,plain,
% 2.96/1.02      ( v1_relat_1(sK6) = iProver_top ),
% 2.96/1.02      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.96/1.02  
% 2.96/1.02  cnf(c_23,negated_conjecture,
% 2.96/1.02      ( v1_funct_1(sK6) ),
% 2.96/1.02      inference(cnf_transformation,[],[f60]) ).
% 2.96/1.02  
% 2.96/1.02  cnf(c_30,plain,
% 2.96/1.02      ( v1_funct_1(sK6) = iProver_top ),
% 2.96/1.02      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.96/1.02  
% 2.96/1.02  cnf(c_2070,plain,
% 2.96/1.02      ( v1_funct_1(X0) != iProver_top
% 2.96/1.02      | k1_relat_1(X0) != k1_relat_1(sK5)
% 2.96/1.02      | sK6 = X0
% 2.96/1.02      | r2_hidden(sK3(X0,sK6),k1_relat_1(X0)) = iProver_top
% 2.96/1.02      | v1_relat_1(X0) != iProver_top ),
% 2.96/1.02      inference(global_propositional_subsumption,
% 2.96/1.02                [status(thm)],
% 2.96/1.02                [c_1762,c_29,c_30]) ).
% 2.96/1.02  
% 2.96/1.02  cnf(c_2071,plain,
% 2.96/1.02      ( k1_relat_1(X0) != k1_relat_1(sK5)
% 2.96/1.02      | sK6 = X0
% 2.96/1.02      | r2_hidden(sK3(X0,sK6),k1_relat_1(X0)) = iProver_top
% 2.96/1.02      | v1_relat_1(X0) != iProver_top
% 2.96/1.02      | v1_funct_1(X0) != iProver_top ),
% 2.96/1.02      inference(renaming,[status(thm)],[c_2070]) ).
% 2.96/1.02  
% 2.96/1.02  cnf(c_2083,plain,
% 2.96/1.02      ( sK6 = sK5
% 2.96/1.02      | r2_hidden(sK3(sK5,sK6),k1_relat_1(sK5)) = iProver_top
% 2.96/1.02      | v1_relat_1(sK5) != iProver_top
% 2.96/1.02      | v1_funct_1(sK5) != iProver_top ),
% 2.96/1.02      inference(equality_resolution,[status(thm)],[c_2071]) ).
% 2.96/1.02  
% 2.96/1.02  cnf(c_26,negated_conjecture,
% 2.96/1.02      ( v1_relat_1(sK5) ),
% 2.96/1.02      inference(cnf_transformation,[],[f57]) ).
% 2.96/1.02  
% 2.96/1.02  cnf(c_27,plain,
% 2.96/1.02      ( v1_relat_1(sK5) = iProver_top ),
% 2.96/1.02      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.96/1.02  
% 2.96/1.02  cnf(c_25,negated_conjecture,
% 2.96/1.02      ( v1_funct_1(sK5) ),
% 2.96/1.02      inference(cnf_transformation,[],[f58]) ).
% 2.96/1.02  
% 2.96/1.02  cnf(c_28,plain,
% 2.96/1.02      ( v1_funct_1(sK5) = iProver_top ),
% 2.96/1.02      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.96/1.02  
% 2.96/1.02  cnf(c_2218,plain,
% 2.96/1.02      ( sK6 = sK5
% 2.96/1.02      | r2_hidden(sK3(sK5,sK6),k1_relat_1(sK5)) = iProver_top ),
% 2.96/1.02      inference(global_propositional_subsumption,
% 2.96/1.02                [status(thm)],
% 2.96/1.02                [c_2083,c_27,c_28]) ).
% 2.96/1.02  
% 2.96/1.02  cnf(c_16,plain,
% 2.96/1.02      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.96/1.02      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 2.96/1.02      | ~ v1_relat_1(X1)
% 2.96/1.02      | ~ v1_funct_1(X1) ),
% 2.96/1.02      inference(cnf_transformation,[],[f54]) ).
% 2.96/1.02  
% 2.96/1.02  cnf(c_1320,plain,
% 2.96/1.02      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 2.96/1.02      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
% 2.96/1.02      | v1_relat_1(X1) != iProver_top
% 2.96/1.02      | v1_funct_1(X1) != iProver_top ),
% 2.96/1.02      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.96/1.02  
% 2.96/1.02  cnf(c_21,negated_conjecture,
% 2.96/1.02      ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k2_relat_1(sK5) ),
% 2.96/1.02      inference(cnf_transformation,[],[f71]) ).
% 2.96/1.02  
% 2.96/1.02  cnf(c_11,plain,
% 2.96/1.02      ( sP0(X0,X1,X2,X3,k3_enumset1(X3,X3,X2,X1,X0)) ),
% 2.96/1.02      inference(cnf_transformation,[],[f76]) ).
% 2.96/1.02  
% 2.96/1.02  cnf(c_1324,plain,
% 2.96/1.02      ( sP0(X0,X1,X2,X3,k3_enumset1(X3,X3,X2,X1,X0)) = iProver_top ),
% 2.96/1.02      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.96/1.02  
% 2.96/1.02  cnf(c_1967,plain,
% 2.96/1.02      ( sP0(sK4,sK4,sK4,sK4,k2_relat_1(sK5)) = iProver_top ),
% 2.96/1.02      inference(superposition,[status(thm)],[c_21,c_1324]) ).
% 2.96/1.02  
% 2.96/1.02  cnf(c_9,plain,
% 2.96/1.02      ( ~ sP0(X0,X1,X2,X3,X4)
% 2.96/1.02      | ~ r2_hidden(X5,X4)
% 2.96/1.02      | X5 = X3
% 2.96/1.02      | X5 = X2
% 2.96/1.02      | X5 = X1
% 2.96/1.02      | X5 = X0 ),
% 2.96/1.02      inference(cnf_transformation,[],[f38]) ).
% 2.96/1.02  
% 2.96/1.02  cnf(c_1326,plain,
% 2.96/1.02      ( X0 = X1
% 2.96/1.02      | X0 = X2
% 2.96/1.02      | X0 = X3
% 2.96/1.02      | X0 = X4
% 2.96/1.02      | sP0(X4,X3,X2,X1,X5) != iProver_top
% 2.96/1.02      | r2_hidden(X0,X5) != iProver_top ),
% 2.96/1.02      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.96/1.02  
% 2.96/1.02  cnf(c_6556,plain,
% 2.96/1.02      ( sK4 = X0 | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 2.96/1.02      inference(superposition,[status(thm)],[c_1967,c_1326]) ).
% 2.96/1.02  
% 2.96/1.02  cnf(c_6576,plain,
% 2.96/1.02      ( k1_funct_1(sK5,X0) = sK4
% 2.96/1.02      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 2.96/1.02      | v1_relat_1(sK5) != iProver_top
% 2.96/1.02      | v1_funct_1(sK5) != iProver_top ),
% 2.96/1.02      inference(superposition,[status(thm)],[c_1320,c_6556]) ).
% 2.96/1.02  
% 2.96/1.02  cnf(c_6700,plain,
% 2.96/1.02      ( k1_funct_1(sK5,X0) = sK4
% 2.96/1.02      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 2.96/1.02      inference(global_propositional_subsumption,
% 2.96/1.02                [status(thm)],
% 2.96/1.02                [c_6576,c_27,c_28]) ).
% 2.96/1.02  
% 2.96/1.02  cnf(c_6708,plain,
% 2.96/1.02      ( k1_funct_1(sK5,sK3(sK5,sK6)) = sK4 | sK6 = sK5 ),
% 2.96/1.02      inference(superposition,[status(thm)],[c_2218,c_6700]) ).
% 2.96/1.02  
% 2.96/1.02  cnf(c_20,negated_conjecture,
% 2.96/1.02      ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k2_relat_1(sK6) ),
% 2.96/1.02      inference(cnf_transformation,[],[f70]) ).
% 2.96/1.02  
% 2.96/1.02  cnf(c_1356,plain,
% 2.96/1.02      ( k2_relat_1(sK5) = k2_relat_1(sK6) ),
% 2.96/1.02      inference(light_normalisation,[status(thm)],[c_20,c_21]) ).
% 2.96/1.02  
% 2.96/1.02  cnf(c_4108,plain,
% 2.96/1.02      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 2.96/1.02      | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK5)) = iProver_top
% 2.96/1.02      | v1_relat_1(sK6) != iProver_top
% 2.96/1.02      | v1_funct_1(sK6) != iProver_top ),
% 2.96/1.02      inference(superposition,[status(thm)],[c_1356,c_1320]) ).
% 2.96/1.02  
% 2.96/1.02  cnf(c_4122,plain,
% 2.96/1.02      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 2.96/1.02      | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK5)) = iProver_top
% 2.96/1.02      | v1_relat_1(sK6) != iProver_top
% 2.96/1.02      | v1_funct_1(sK6) != iProver_top ),
% 2.96/1.02      inference(light_normalisation,[status(thm)],[c_4108,c_22]) ).
% 2.96/1.02  
% 2.96/1.02  cnf(c_4442,plain,
% 2.96/1.02      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 2.96/1.02      | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK5)) = iProver_top ),
% 2.96/1.02      inference(global_propositional_subsumption,
% 2.96/1.02                [status(thm)],
% 2.96/1.02                [c_4122,c_29,c_30]) ).
% 2.96/1.02  
% 2.96/1.02  cnf(c_6578,plain,
% 2.96/1.02      ( k1_funct_1(sK6,X0) = sK4
% 2.96/1.02      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 2.96/1.02      inference(superposition,[status(thm)],[c_4442,c_6556]) ).
% 2.96/1.02  
% 2.96/1.02  cnf(c_6677,plain,
% 2.96/1.02      ( k1_funct_1(sK6,sK3(sK5,sK6)) = sK4 | sK6 = sK5 ),
% 2.96/1.02      inference(superposition,[status(thm)],[c_2218,c_6578]) ).
% 2.96/1.02  
% 2.96/1.02  cnf(c_922,plain,( X0 = X0 ),theory(equality) ).
% 2.96/1.02  
% 2.96/1.02  cnf(c_3610,plain,
% 2.96/1.02      ( sK5 = sK5 ),
% 2.96/1.02      inference(instantiation,[status(thm)],[c_922]) ).
% 2.96/1.02  
% 2.96/1.02  cnf(c_923,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.96/1.02  
% 2.96/1.02  cnf(c_2383,plain,
% 2.96/1.02      ( k1_funct_1(sK6,sK3(sK5,sK6)) != X0
% 2.96/1.02      | k1_funct_1(sK6,sK3(sK5,sK6)) = k1_funct_1(sK5,sK3(sK5,sK6))
% 2.96/1.02      | k1_funct_1(sK5,sK3(sK5,sK6)) != X0 ),
% 2.96/1.02      inference(instantiation,[status(thm)],[c_923]) ).
% 2.96/1.02  
% 2.96/1.02  cnf(c_2384,plain,
% 2.96/1.02      ( k1_funct_1(sK6,sK3(sK5,sK6)) = k1_funct_1(sK5,sK3(sK5,sK6))
% 2.96/1.02      | k1_funct_1(sK6,sK3(sK5,sK6)) != sK4
% 2.96/1.02      | k1_funct_1(sK5,sK3(sK5,sK6)) != sK4 ),
% 2.96/1.02      inference(instantiation,[status(thm)],[c_2383]) ).
% 2.96/1.02  
% 2.96/1.02  cnf(c_1549,plain,
% 2.96/1.02      ( sK6 != X0 | sK5 != X0 | sK5 = sK6 ),
% 2.96/1.02      inference(instantiation,[status(thm)],[c_923]) ).
% 2.96/1.02  
% 2.96/1.02  cnf(c_2295,plain,
% 2.96/1.02      ( sK6 != sK5 | sK5 = sK6 | sK5 != sK5 ),
% 2.96/1.02      inference(instantiation,[status(thm)],[c_1549]) ).
% 2.96/1.02  
% 2.96/1.02  cnf(c_17,plain,
% 2.96/1.02      ( ~ v1_relat_1(X0)
% 2.96/1.02      | ~ v1_relat_1(X1)
% 2.96/1.02      | ~ v1_funct_1(X0)
% 2.96/1.02      | ~ v1_funct_1(X1)
% 2.96/1.02      | X0 = X1
% 2.96/1.02      | k1_funct_1(X0,sK3(X1,X0)) != k1_funct_1(X1,sK3(X1,X0))
% 2.96/1.02      | k1_relat_1(X1) != k1_relat_1(X0) ),
% 2.96/1.02      inference(cnf_transformation,[],[f56]) ).
% 2.96/1.02  
% 2.96/1.02  cnf(c_1674,plain,
% 2.96/1.02      ( ~ v1_relat_1(X0)
% 2.96/1.02      | ~ v1_relat_1(sK5)
% 2.96/1.02      | ~ v1_funct_1(X0)
% 2.96/1.02      | ~ v1_funct_1(sK5)
% 2.96/1.02      | X0 = sK5
% 2.96/1.02      | k1_funct_1(X0,sK3(sK5,X0)) != k1_funct_1(sK5,sK3(sK5,X0))
% 2.96/1.02      | k1_relat_1(sK5) != k1_relat_1(X0) ),
% 2.96/1.02      inference(instantiation,[status(thm)],[c_17]) ).
% 2.96/1.02  
% 2.96/1.02  cnf(c_1976,plain,
% 2.96/1.02      ( ~ v1_relat_1(sK6)
% 2.96/1.02      | ~ v1_relat_1(sK5)
% 2.96/1.02      | ~ v1_funct_1(sK6)
% 2.96/1.02      | ~ v1_funct_1(sK5)
% 2.96/1.02      | k1_funct_1(sK6,sK3(sK5,sK6)) != k1_funct_1(sK5,sK3(sK5,sK6))
% 2.96/1.02      | k1_relat_1(sK5) != k1_relat_1(sK6)
% 2.96/1.02      | sK6 = sK5 ),
% 2.96/1.02      inference(instantiation,[status(thm)],[c_1674]) ).
% 2.96/1.02  
% 2.96/1.02  cnf(c_19,negated_conjecture,
% 2.96/1.02      ( sK5 != sK6 ),
% 2.96/1.02      inference(cnf_transformation,[],[f64]) ).
% 2.96/1.02  
% 2.96/1.02  cnf(contradiction,plain,
% 2.96/1.02      ( $false ),
% 2.96/1.02      inference(minisat,
% 2.96/1.02                [status(thm)],
% 2.96/1.02                [c_6708,c_6677,c_3610,c_2384,c_2295,c_1976,c_19,c_22,
% 2.96/1.02                 c_23,c_24,c_25,c_26]) ).
% 2.96/1.02  
% 2.96/1.02  
% 2.96/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.96/1.02  
% 2.96/1.02  ------                               Statistics
% 2.96/1.02  
% 2.96/1.02  ------ General
% 2.96/1.02  
% 2.96/1.02  abstr_ref_over_cycles:                  0
% 2.96/1.02  abstr_ref_under_cycles:                 0
% 2.96/1.02  gc_basic_clause_elim:                   0
% 2.96/1.02  forced_gc_time:                         0
% 2.96/1.02  parsing_time:                           0.01
% 2.96/1.02  unif_index_cands_time:                  0.
% 2.96/1.02  unif_index_add_time:                    0.
% 2.96/1.02  orderings_time:                         0.
% 2.96/1.02  out_proof_time:                         0.009
% 2.96/1.02  total_time:                             0.224
% 2.96/1.02  num_of_symbols:                         45
% 2.96/1.02  num_of_terms:                           8858
% 2.96/1.02  
% 2.96/1.02  ------ Preprocessing
% 2.96/1.02  
% 2.96/1.02  num_of_splits:                          0
% 2.96/1.02  num_of_split_atoms:                     0
% 2.96/1.02  num_of_reused_defs:                     0
% 2.96/1.02  num_eq_ax_congr_red:                    26
% 2.96/1.02  num_of_sem_filtered_clauses:            1
% 2.96/1.02  num_of_subtypes:                        0
% 2.96/1.02  monotx_restored_types:                  0
% 2.96/1.02  sat_num_of_epr_types:                   0
% 2.96/1.02  sat_num_of_non_cyclic_types:            0
% 2.96/1.02  sat_guarded_non_collapsed_types:        0
% 2.96/1.02  num_pure_diseq_elim:                    0
% 2.96/1.02  simp_replaced_by:                       0
% 2.96/1.02  res_preprocessed:                       102
% 2.96/1.02  prep_upred:                             0
% 2.96/1.02  prep_unflattend:                        30
% 2.96/1.02  smt_new_axioms:                         0
% 2.96/1.02  pred_elim_cands:                        4
% 2.96/1.02  pred_elim:                              0
% 2.96/1.02  pred_elim_cl:                           0
% 2.96/1.02  pred_elim_cycles:                       1
% 2.96/1.02  merged_defs:                            0
% 2.96/1.02  merged_defs_ncl:                        0
% 2.96/1.02  bin_hyper_res:                          0
% 2.96/1.02  prep_cycles:                            3
% 2.96/1.02  pred_elim_time:                         0.01
% 2.96/1.02  splitting_time:                         0.
% 2.96/1.02  sem_filter_time:                        0.
% 2.96/1.02  monotx_time:                            0.
% 2.96/1.02  subtype_inf_time:                       0.
% 2.96/1.02  
% 2.96/1.02  ------ Problem properties
% 2.96/1.02  
% 2.96/1.02  clauses:                                27
% 2.96/1.02  conjectures:                            8
% 2.96/1.02  epr:                                    10
% 2.96/1.02  horn:                                   24
% 2.96/1.02  ground:                                 8
% 2.96/1.02  unary:                                  12
% 2.96/1.02  binary:                                 6
% 2.96/1.02  lits:                                   66
% 2.96/1.02  lits_eq:                                24
% 2.96/1.02  fd_pure:                                0
% 2.96/1.02  fd_pseudo:                              0
% 2.96/1.02  fd_cond:                                0
% 2.96/1.02  fd_pseudo_cond:                         4
% 2.96/1.02  ac_symbols:                             0
% 2.96/1.02  
% 2.96/1.02  ------ Propositional Solver
% 2.96/1.02  
% 2.96/1.02  prop_solver_calls:                      24
% 2.96/1.02  prop_fast_solver_calls:                 854
% 2.96/1.02  smt_solver_calls:                       0
% 2.96/1.02  smt_fast_solver_calls:                  0
% 2.96/1.02  prop_num_of_clauses:                    2647
% 2.96/1.02  prop_preprocess_simplified:             7438
% 2.96/1.02  prop_fo_subsumed:                       25
% 2.96/1.02  prop_solver_time:                       0.
% 2.96/1.02  smt_solver_time:                        0.
% 2.96/1.02  smt_fast_solver_time:                   0.
% 2.96/1.02  prop_fast_solver_time:                  0.
% 2.96/1.02  prop_unsat_core_time:                   0.
% 2.96/1.02  
% 2.96/1.02  ------ QBF
% 2.96/1.02  
% 2.96/1.02  qbf_q_res:                              0
% 2.96/1.02  qbf_num_tautologies:                    0
% 2.96/1.02  qbf_prep_cycles:                        0
% 2.96/1.02  
% 2.96/1.02  ------ BMC1
% 2.96/1.02  
% 2.96/1.02  bmc1_current_bound:                     -1
% 2.96/1.02  bmc1_last_solved_bound:                 -1
% 2.96/1.02  bmc1_unsat_core_size:                   -1
% 2.96/1.02  bmc1_unsat_core_parents_size:           -1
% 2.96/1.02  bmc1_merge_next_fun:                    0
% 2.96/1.02  bmc1_unsat_core_clauses_time:           0.
% 2.96/1.02  
% 2.96/1.02  ------ Instantiation
% 2.96/1.02  
% 2.96/1.02  inst_num_of_clauses:                    724
% 2.96/1.02  inst_num_in_passive:                    431
% 2.96/1.02  inst_num_in_active:                     216
% 2.96/1.02  inst_num_in_unprocessed:                77
% 2.96/1.02  inst_num_of_loops:                      270
% 2.96/1.02  inst_num_of_learning_restarts:          0
% 2.96/1.02  inst_num_moves_active_passive:          52
% 2.96/1.02  inst_lit_activity:                      0
% 2.96/1.02  inst_lit_activity_moves:                0
% 2.96/1.02  inst_num_tautologies:                   0
% 2.96/1.02  inst_num_prop_implied:                  0
% 2.96/1.02  inst_num_existing_simplified:           0
% 2.96/1.02  inst_num_eq_res_simplified:             0
% 2.96/1.02  inst_num_child_elim:                    0
% 2.96/1.02  inst_num_of_dismatching_blockings:      353
% 2.96/1.02  inst_num_of_non_proper_insts:           671
% 2.96/1.02  inst_num_of_duplicates:                 0
% 2.96/1.02  inst_inst_num_from_inst_to_res:         0
% 2.96/1.02  inst_dismatching_checking_time:         0.
% 2.96/1.02  
% 2.96/1.02  ------ Resolution
% 2.96/1.02  
% 2.96/1.02  res_num_of_clauses:                     0
% 2.96/1.02  res_num_in_passive:                     0
% 2.96/1.02  res_num_in_active:                      0
% 2.96/1.02  res_num_of_loops:                       105
% 2.96/1.02  res_forward_subset_subsumed:            147
% 2.96/1.02  res_backward_subset_subsumed:           2
% 2.96/1.02  res_forward_subsumed:                   0
% 2.96/1.02  res_backward_subsumed:                  0
% 2.96/1.02  res_forward_subsumption_resolution:     0
% 2.96/1.02  res_backward_subsumption_resolution:    0
% 2.96/1.02  res_clause_to_clause_subsumption:       459
% 2.96/1.02  res_orphan_elimination:                 0
% 2.96/1.02  res_tautology_del:                      30
% 2.96/1.02  res_num_eq_res_simplified:              0
% 2.96/1.02  res_num_sel_changes:                    0
% 2.96/1.02  res_moves_from_active_to_pass:          0
% 2.96/1.02  
% 2.96/1.02  ------ Superposition
% 2.96/1.02  
% 2.96/1.02  sup_time_total:                         0.
% 2.96/1.02  sup_time_generating:                    0.
% 2.96/1.02  sup_time_sim_full:                      0.
% 2.96/1.02  sup_time_sim_immed:                     0.
% 2.96/1.02  
% 2.96/1.02  sup_num_of_clauses:                     77
% 2.96/1.02  sup_num_in_active:                      54
% 2.96/1.02  sup_num_in_passive:                     23
% 2.96/1.02  sup_num_of_loops:                       53
% 2.96/1.02  sup_fw_superposition:                   45
% 2.96/1.02  sup_bw_superposition:                   13
% 2.96/1.02  sup_immediate_simplified:               17
% 2.96/1.02  sup_given_eliminated:                   0
% 2.96/1.02  comparisons_done:                       0
% 2.96/1.02  comparisons_avoided:                    18
% 2.96/1.02  
% 2.96/1.02  ------ Simplifications
% 2.96/1.02  
% 2.96/1.02  
% 2.96/1.02  sim_fw_subset_subsumed:                 0
% 2.96/1.02  sim_bw_subset_subsumed:                 2
% 2.96/1.02  sim_fw_subsumed:                        1
% 2.96/1.02  sim_bw_subsumed:                        0
% 2.96/1.02  sim_fw_subsumption_res:                 6
% 2.96/1.02  sim_bw_subsumption_res:                 0
% 2.96/1.02  sim_tautology_del:                      0
% 2.96/1.02  sim_eq_tautology_del:                   5
% 2.96/1.02  sim_eq_res_simp:                        2
% 2.96/1.02  sim_fw_demodulated:                     12
% 2.96/1.02  sim_bw_demodulated:                     0
% 2.96/1.02  sim_light_normalised:                   8
% 2.96/1.02  sim_joinable_taut:                      0
% 2.96/1.02  sim_joinable_simp:                      0
% 2.96/1.02  sim_ac_normalised:                      0
% 2.96/1.02  sim_smt_subsumption:                    0
% 2.96/1.02  
%------------------------------------------------------------------------------
