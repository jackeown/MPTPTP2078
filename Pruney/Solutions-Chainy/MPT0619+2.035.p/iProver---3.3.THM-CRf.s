%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:49:17 EST 2020

% Result     : Theorem 3.96s
% Output     : CNFRefutation 3.96s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 569 expanded)
%              Number of clauses        :   50 (  93 expanded)
%              Number of leaves         :   21 ( 159 expanded)
%              Depth                    :   16
%              Number of atoms          :  380 (1652 expanded)
%              Number of equality atoms :  163 ( 937 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f19,plain,(
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
    inference(rectify,[],[f18])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK0(X0,X1) != X0
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( sK0(X0,X1) = X0
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK0(X0,X1) != X0
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( sK0(X0,X1) = X0
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK0(X0,X1) = X0
      | r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f62,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f44,f45])).

fof(f63,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f43,f62])).

fof(f64,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f42,f63])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k3_enumset1(X0,X0,X0,X0,X0) = X1
      | sK0(X0,X1) = X0
      | r2_hidden(sK0(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f40,f64])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f32,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK5(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK4(X0,X1)),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK6(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f29,f32,f31,f30])).

fof(f50,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f77,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK6(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f50])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f26,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK2(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK1(X0,X1),X3),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK1(X0,X1),X4),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK1(X0,X1),X3),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f23,f26,f25,f24])).

fof(f47,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f74,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( k1_tarski(X0) = k1_relat_1(X1)
         => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f16,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1)
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f17,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1)
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f36,plain,
    ( ? [X0,X1] :
        ( k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1)
        & k1_tarski(X0) = k1_relat_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k1_tarski(k1_funct_1(sK8,sK7)) != k2_relat_1(sK8)
      & k1_tarski(sK7) = k1_relat_1(sK8)
      & v1_funct_1(sK8)
      & v1_relat_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( k1_tarski(k1_funct_1(sK8,sK7)) != k2_relat_1(sK8)
    & k1_tarski(sK7) = k1_relat_1(sK8)
    & v1_funct_1(sK8)
    & v1_relat_1(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f17,f36])).

fof(f60,plain,(
    k1_tarski(sK7) = k1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f37])).

fof(f70,plain,(
    k3_enumset1(sK7,sK7,sK7,sK7,sK7) = k1_relat_1(sK8) ),
    inference(definition_unfolding,[],[f60,f64])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f38,f64])).

fof(f73,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f68])).

fof(f61,plain,(
    k1_tarski(k1_funct_1(sK8,sK7)) != k2_relat_1(sK8) ),
    inference(cnf_transformation,[],[f37])).

fof(f69,plain,(
    k3_enumset1(k1_funct_1(sK8,sK7),k1_funct_1(sK8,sK7),k1_funct_1(sK8,sK7),k1_funct_1(sK8,sK7),k1_funct_1(sK8,sK7)) != k2_relat_1(sK8) ),
    inference(definition_unfolding,[],[f61,f64])).

fof(f58,plain,(
    v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f37])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f59,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f37])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f39,f64])).

fof(f71,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k3_enumset1(X3,X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f67])).

fof(f72,plain,(
    ! [X3] : r2_hidden(X3,k3_enumset1(X3,X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f71])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK0(X0,X1) != X0
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k3_enumset1(X0,X0,X0,X0,X0) = X1
      | sK0(X0,X1) != X0
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f41,f64])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | k3_enumset1(X0,X0,X0,X0,X0) = X1
    | sK0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_667,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = X1
    | sK0(X0,X1) = X0
    | r2_hidden(sK0(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK6(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_657,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(sK6(X1,X0),X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_6,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_662,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1374,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(sK6(X1,X0),k1_relat_1(X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_657,c_662])).

cnf(c_17,negated_conjecture,
    ( k3_enumset1(sK7,sK7,sK7,sK7,sK7) = k1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_665,plain,
    ( X0 = X1
    | r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1179,plain,
    ( sK7 = X0
    | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_17,c_665])).

cnf(c_2617,plain,
    ( sK6(sK8,X0) = sK7
    | r2_hidden(X0,k2_relat_1(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1374,c_1179])).

cnf(c_2759,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = k2_relat_1(sK8)
    | sK6(sK8,sK0(X0,k2_relat_1(sK8))) = sK7
    | sK0(X0,k2_relat_1(sK8)) = X0 ),
    inference(superposition,[status(thm)],[c_667,c_2617])).

cnf(c_16,negated_conjecture,
    ( k3_enumset1(k1_funct_1(sK8,sK7),k1_funct_1(sK8,sK7),k1_funct_1(sK8,sK7),k1_funct_1(sK8,sK7),k1_funct_1(sK8,sK7)) != k2_relat_1(sK8) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_11738,plain,
    ( sK6(sK8,sK0(k1_funct_1(sK8,sK7),k2_relat_1(sK8))) = sK7
    | sK0(k1_funct_1(sK8,sK7),k2_relat_1(sK8)) = k1_funct_1(sK8,sK7) ),
    inference(superposition,[status(thm)],[c_2759,c_16])).

cnf(c_4045,plain,
    ( r2_hidden(sK0(k1_funct_1(sK8,sK7),k2_relat_1(sK8)),k2_relat_1(sK8))
    | sK0(k1_funct_1(sK8,sK7),k2_relat_1(sK8)) = k1_funct_1(sK8,sK7) ),
    inference(resolution,[status(thm)],[c_1,c_16])).

cnf(c_19,negated_conjecture,
    ( v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_18,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_230,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_18])).

cnf(c_231,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK8))
    | r2_hidden(k1_funct_1(sK8,X0),k2_relat_1(sK8))
    | ~ v1_relat_1(sK8) ),
    inference(unflattening,[status(thm)],[c_230])).

cnf(c_233,plain,
    ( r2_hidden(k1_funct_1(sK8,sK7),k2_relat_1(sK8))
    | ~ r2_hidden(sK7,k1_relat_1(sK8))
    | ~ v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_231])).

cnf(c_2,plain,
    ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_666,plain,
    ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_747,plain,
    ( r2_hidden(sK7,k1_relat_1(sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_17,c_666])).

cnf(c_748,plain,
    ( r2_hidden(sK7,k1_relat_1(sK8)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_747])).

cnf(c_765,plain,
    ( r2_hidden(sK0(k1_funct_1(sK8,sK7),k2_relat_1(sK8)),k2_relat_1(sK8))
    | k3_enumset1(k1_funct_1(sK8,sK7),k1_funct_1(sK8,sK7),k1_funct_1(sK8,sK7),k1_funct_1(sK8,sK7),k1_funct_1(sK8,sK7)) = k2_relat_1(sK8)
    | sK0(k1_funct_1(sK8,sK7),k2_relat_1(sK8)) = k1_funct_1(sK8,sK7) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_389,plain,
    ( X0 != X1
    | k2_relat_1(X0) = k2_relat_1(X1) ),
    theory(equality)).

cnf(c_862,plain,
    ( k2_relat_1(sK8) = k2_relat_1(X0)
    | sK8 != X0 ),
    inference(instantiation,[status(thm)],[c_389])).

cnf(c_917,plain,
    ( k2_relat_1(sK8) = k2_relat_1(sK8)
    | sK8 != sK8 ),
    inference(instantiation,[status(thm)],[c_862])).

cnf(c_383,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_918,plain,
    ( sK8 = sK8 ),
    inference(instantiation,[status(thm)],[c_383])).

cnf(c_386,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1012,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k1_funct_1(sK8,X2),k2_relat_1(sK8))
    | X0 != k1_funct_1(sK8,X2)
    | X1 != k2_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_386])).

cnf(c_1454,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k1_funct_1(sK8,X2),k2_relat_1(sK8))
    | X0 != k1_funct_1(sK8,X2)
    | k2_relat_1(X1) != k2_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_1012])).

cnf(c_3117,plain,
    ( ~ r2_hidden(k1_funct_1(sK8,sK7),k2_relat_1(sK8))
    | r2_hidden(sK0(k1_funct_1(sK8,sK7),k2_relat_1(sK8)),k2_relat_1(X0))
    | sK0(k1_funct_1(sK8,sK7),k2_relat_1(sK8)) != k1_funct_1(sK8,sK7)
    | k2_relat_1(X0) != k2_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_1454])).

cnf(c_4456,plain,
    ( ~ r2_hidden(k1_funct_1(sK8,sK7),k2_relat_1(sK8))
    | r2_hidden(sK0(k1_funct_1(sK8,sK7),k2_relat_1(sK8)),k2_relat_1(sK8))
    | sK0(k1_funct_1(sK8,sK7),k2_relat_1(sK8)) != k1_funct_1(sK8,sK7)
    | k2_relat_1(sK8) != k2_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_3117])).

cnf(c_4558,plain,
    ( r2_hidden(sK0(k1_funct_1(sK8,sK7),k2_relat_1(sK8)),k2_relat_1(sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4045,c_19,c_16,c_233,c_748,c_765,c_917,c_918,c_4456])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | k3_enumset1(X0,X0,X0,X0,X0) = X1
    | sK0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_4570,plain,
    ( k3_enumset1(k1_funct_1(sK8,sK7),k1_funct_1(sK8,sK7),k1_funct_1(sK8,sK7),k1_funct_1(sK8,sK7),k1_funct_1(sK8,sK7)) = k2_relat_1(sK8)
    | sK0(k1_funct_1(sK8,sK7),k2_relat_1(sK8)) != k1_funct_1(sK8,sK7) ),
    inference(resolution,[status(thm)],[c_4558,c_0])).

cnf(c_12179,plain,
    ( sK6(sK8,sK0(k1_funct_1(sK8,sK7),k2_relat_1(sK8))) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11738,c_16,c_4570])).

cnf(c_14,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_248,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1
    | sK8 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_18])).

cnf(c_249,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK8)
    | ~ v1_relat_1(sK8)
    | k1_funct_1(sK8,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_248])).

cnf(c_253,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK8)
    | k1_funct_1(sK8,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_249,c_19])).

cnf(c_654,plain,
    ( k1_funct_1(sK8,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_253])).

cnf(c_1377,plain,
    ( k1_funct_1(sK8,sK6(sK8,X0)) = X0
    | r2_hidden(X0,k2_relat_1(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_657,c_654])).

cnf(c_2327,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = k2_relat_1(sK8)
    | k1_funct_1(sK8,sK6(sK8,sK0(X0,k2_relat_1(sK8)))) = sK0(X0,k2_relat_1(sK8))
    | sK0(X0,k2_relat_1(sK8)) = X0 ),
    inference(superposition,[status(thm)],[c_667,c_1377])).

cnf(c_12575,plain,
    ( k3_enumset1(k1_funct_1(sK8,sK7),k1_funct_1(sK8,sK7),k1_funct_1(sK8,sK7),k1_funct_1(sK8,sK7),k1_funct_1(sK8,sK7)) = k2_relat_1(sK8)
    | sK0(k1_funct_1(sK8,sK7),k2_relat_1(sK8)) = k1_funct_1(sK8,sK7) ),
    inference(superposition,[status(thm)],[c_12179,c_2327])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12575,c_4570,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:01:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.96/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.96/0.99  
% 3.96/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.96/0.99  
% 3.96/0.99  ------  iProver source info
% 3.96/0.99  
% 3.96/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.96/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.96/0.99  git: non_committed_changes: false
% 3.96/0.99  git: last_make_outside_of_git: false
% 3.96/0.99  
% 3.96/0.99  ------ 
% 3.96/0.99  ------ Parsing...
% 3.96/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.96/0.99  
% 3.96/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.96/0.99  
% 3.96/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.96/0.99  
% 3.96/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.96/0.99  ------ Proving...
% 3.96/0.99  ------ Problem Properties 
% 3.96/0.99  
% 3.96/0.99  
% 3.96/0.99  clauses                                 17
% 3.96/0.99  conjectures                             2
% 3.96/0.99  EPR                                     0
% 3.96/0.99  Horn                                    14
% 3.96/0.99  unary                                   3
% 3.96/0.99  binary                                  8
% 3.96/0.99  lits                                    37
% 3.96/0.99  lits eq                                 12
% 3.96/0.99  fd_pure                                 0
% 3.96/0.99  fd_pseudo                               0
% 3.96/0.99  fd_cond                                 0
% 3.96/0.99  fd_pseudo_cond                          7
% 3.96/0.99  AC symbols                              0
% 3.96/0.99  
% 3.96/0.99  ------ Input Options Time Limit: Unbounded
% 3.96/0.99  
% 3.96/0.99  
% 3.96/0.99  ------ 
% 3.96/0.99  Current options:
% 3.96/0.99  ------ 
% 3.96/0.99  
% 3.96/0.99  
% 3.96/0.99  
% 3.96/0.99  
% 3.96/0.99  ------ Proving...
% 3.96/0.99  
% 3.96/0.99  
% 3.96/0.99  % SZS status Theorem for theBenchmark.p
% 3.96/0.99  
% 3.96/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.96/0.99  
% 3.96/0.99  fof(f1,axiom,(
% 3.96/0.99    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.96/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/0.99  
% 3.96/0.99  fof(f18,plain,(
% 3.96/0.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 3.96/0.99    inference(nnf_transformation,[],[f1])).
% 3.96/0.99  
% 3.96/0.99  fof(f19,plain,(
% 3.96/0.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.96/0.99    inference(rectify,[],[f18])).
% 3.96/0.99  
% 3.96/0.99  fof(f20,plain,(
% 3.96/0.99    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1))))),
% 3.96/0.99    introduced(choice_axiom,[])).
% 3.96/0.99  
% 3.96/0.99  fof(f21,plain,(
% 3.96/0.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.96/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).
% 3.96/0.99  
% 3.96/0.99  fof(f40,plain,(
% 3.96/0.99    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1)) )),
% 3.96/0.99    inference(cnf_transformation,[],[f21])).
% 3.96/0.99  
% 3.96/0.99  fof(f2,axiom,(
% 3.96/0.99    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.96/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/0.99  
% 3.96/0.99  fof(f42,plain,(
% 3.96/0.99    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.96/0.99    inference(cnf_transformation,[],[f2])).
% 3.96/0.99  
% 3.96/0.99  fof(f3,axiom,(
% 3.96/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.96/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/0.99  
% 3.96/0.99  fof(f43,plain,(
% 3.96/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.96/0.99    inference(cnf_transformation,[],[f3])).
% 3.96/0.99  
% 3.96/0.99  fof(f4,axiom,(
% 3.96/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.96/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/0.99  
% 3.96/0.99  fof(f44,plain,(
% 3.96/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.96/0.99    inference(cnf_transformation,[],[f4])).
% 3.96/0.99  
% 3.96/0.99  fof(f5,axiom,(
% 3.96/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.96/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/0.99  
% 3.96/0.99  fof(f45,plain,(
% 3.96/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.96/0.99    inference(cnf_transformation,[],[f5])).
% 3.96/0.99  
% 3.96/0.99  fof(f62,plain,(
% 3.96/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 3.96/0.99    inference(definition_unfolding,[],[f44,f45])).
% 3.96/0.99  
% 3.96/0.99  fof(f63,plain,(
% 3.96/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 3.96/0.99    inference(definition_unfolding,[],[f43,f62])).
% 3.96/0.99  
% 3.96/0.99  fof(f64,plain,(
% 3.96/0.99    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 3.96/0.99    inference(definition_unfolding,[],[f42,f63])).
% 3.96/0.99  
% 3.96/0.99  fof(f66,plain,(
% 3.96/0.99    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X0) = X1 | sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1)) )),
% 3.96/0.99    inference(definition_unfolding,[],[f40,f64])).
% 3.96/0.99  
% 3.96/0.99  fof(f7,axiom,(
% 3.96/0.99    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 3.96/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/0.99  
% 3.96/0.99  fof(f28,plain,(
% 3.96/0.99    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 3.96/0.99    inference(nnf_transformation,[],[f7])).
% 3.96/0.99  
% 3.96/0.99  fof(f29,plain,(
% 3.96/0.99    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 3.96/0.99    inference(rectify,[],[f28])).
% 3.96/0.99  
% 3.96/0.99  fof(f32,plain,(
% 3.96/0.99    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK6(X0,X5),X5),X0))),
% 3.96/0.99    introduced(choice_axiom,[])).
% 3.96/0.99  
% 3.96/0.99  fof(f31,plain,(
% 3.96/0.99    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK5(X0,X1),X2),X0))) )),
% 3.96/0.99    introduced(choice_axiom,[])).
% 3.96/0.99  
% 3.96/0.99  fof(f30,plain,(
% 3.96/0.99    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK4(X0,X1)),X0) | r2_hidden(sK4(X0,X1),X1))))),
% 3.96/0.99    introduced(choice_axiom,[])).
% 3.96/0.99  
% 3.96/0.99  fof(f33,plain,(
% 3.96/0.99    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 3.96/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f29,f32,f31,f30])).
% 3.96/0.99  
% 3.96/0.99  fof(f50,plain,(
% 3.96/0.99    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 3.96/0.99    inference(cnf_transformation,[],[f33])).
% 3.96/0.99  
% 3.96/0.99  fof(f77,plain,(
% 3.96/0.99    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 3.96/0.99    inference(equality_resolution,[],[f50])).
% 3.96/0.99  
% 3.96/0.99  fof(f6,axiom,(
% 3.96/0.99    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 3.96/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/0.99  
% 3.96/0.99  fof(f22,plain,(
% 3.96/0.99    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 3.96/0.99    inference(nnf_transformation,[],[f6])).
% 3.96/0.99  
% 3.96/0.99  fof(f23,plain,(
% 3.96/0.99    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 3.96/0.99    inference(rectify,[],[f22])).
% 3.96/0.99  
% 3.96/0.99  fof(f26,plain,(
% 3.96/0.99    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0))),
% 3.96/0.99    introduced(choice_axiom,[])).
% 3.96/0.99  
% 3.96/0.99  fof(f25,plain,(
% 3.96/0.99    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) => r2_hidden(k4_tarski(X2,sK2(X0,X1)),X0))) )),
% 3.96/0.99    introduced(choice_axiom,[])).
% 3.96/0.99  
% 3.96/0.99  fof(f24,plain,(
% 3.96/0.99    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK1(X0,X1),X3),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK1(X0,X1),X4),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 3.96/0.99    introduced(choice_axiom,[])).
% 3.96/0.99  
% 3.96/0.99  fof(f27,plain,(
% 3.96/0.99    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK1(X0,X1),X3),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 3.96/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f23,f26,f25,f24])).
% 3.96/0.99  
% 3.96/0.99  fof(f47,plain,(
% 3.96/0.99    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 3.96/0.99    inference(cnf_transformation,[],[f27])).
% 3.96/0.99  
% 3.96/0.99  fof(f74,plain,(
% 3.96/0.99    ( ! [X6,X0,X5] : (r2_hidden(X5,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X6),X0)) )),
% 3.96/0.99    inference(equality_resolution,[],[f47])).
% 3.96/0.99  
% 3.96/0.99  fof(f10,conjecture,(
% 3.96/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 3.96/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/0.99  
% 3.96/0.99  fof(f11,negated_conjecture,(
% 3.96/0.99    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 3.96/0.99    inference(negated_conjecture,[],[f10])).
% 3.96/0.99  
% 3.96/0.99  fof(f16,plain,(
% 3.96/0.99    ? [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1) & k1_tarski(X0) = k1_relat_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 3.96/0.99    inference(ennf_transformation,[],[f11])).
% 3.96/0.99  
% 3.96/0.99  fof(f17,plain,(
% 3.96/0.99    ? [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 3.96/0.99    inference(flattening,[],[f16])).
% 3.96/0.99  
% 3.96/0.99  fof(f36,plain,(
% 3.96/0.99    ? [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(k1_funct_1(sK8,sK7)) != k2_relat_1(sK8) & k1_tarski(sK7) = k1_relat_1(sK8) & v1_funct_1(sK8) & v1_relat_1(sK8))),
% 3.96/0.99    introduced(choice_axiom,[])).
% 3.96/0.99  
% 3.96/0.99  fof(f37,plain,(
% 3.96/0.99    k1_tarski(k1_funct_1(sK8,sK7)) != k2_relat_1(sK8) & k1_tarski(sK7) = k1_relat_1(sK8) & v1_funct_1(sK8) & v1_relat_1(sK8)),
% 3.96/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f17,f36])).
% 3.96/0.99  
% 3.96/0.99  fof(f60,plain,(
% 3.96/0.99    k1_tarski(sK7) = k1_relat_1(sK8)),
% 3.96/0.99    inference(cnf_transformation,[],[f37])).
% 3.96/0.99  
% 3.96/0.99  fof(f70,plain,(
% 3.96/0.99    k3_enumset1(sK7,sK7,sK7,sK7,sK7) = k1_relat_1(sK8)),
% 3.96/0.99    inference(definition_unfolding,[],[f60,f64])).
% 3.96/0.99  
% 3.96/0.99  fof(f38,plain,(
% 3.96/0.99    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 3.96/0.99    inference(cnf_transformation,[],[f21])).
% 3.96/0.99  
% 3.96/0.99  fof(f68,plain,(
% 3.96/0.99    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 3.96/0.99    inference(definition_unfolding,[],[f38,f64])).
% 3.96/0.99  
% 3.96/0.99  fof(f73,plain,(
% 3.96/0.99    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0))) )),
% 3.96/0.99    inference(equality_resolution,[],[f68])).
% 3.96/0.99  
% 3.96/0.99  fof(f61,plain,(
% 3.96/0.99    k1_tarski(k1_funct_1(sK8,sK7)) != k2_relat_1(sK8)),
% 3.96/0.99    inference(cnf_transformation,[],[f37])).
% 3.96/0.99  
% 3.96/0.99  fof(f69,plain,(
% 3.96/0.99    k3_enumset1(k1_funct_1(sK8,sK7),k1_funct_1(sK8,sK7),k1_funct_1(sK8,sK7),k1_funct_1(sK8,sK7),k1_funct_1(sK8,sK7)) != k2_relat_1(sK8)),
% 3.96/0.99    inference(definition_unfolding,[],[f61,f64])).
% 3.96/0.99  
% 3.96/0.99  fof(f58,plain,(
% 3.96/0.99    v1_relat_1(sK8)),
% 3.96/0.99    inference(cnf_transformation,[],[f37])).
% 3.96/0.99  
% 3.96/0.99  fof(f8,axiom,(
% 3.96/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 3.96/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/0.99  
% 3.96/0.99  fof(f12,plain,(
% 3.96/0.99    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.96/0.99    inference(ennf_transformation,[],[f8])).
% 3.96/0.99  
% 3.96/0.99  fof(f13,plain,(
% 3.96/0.99    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.96/0.99    inference(flattening,[],[f12])).
% 3.96/0.99  
% 3.96/0.99  fof(f54,plain,(
% 3.96/0.99    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.96/0.99    inference(cnf_transformation,[],[f13])).
% 3.96/0.99  
% 3.96/0.99  fof(f59,plain,(
% 3.96/0.99    v1_funct_1(sK8)),
% 3.96/0.99    inference(cnf_transformation,[],[f37])).
% 3.96/0.99  
% 3.96/0.99  fof(f39,plain,(
% 3.96/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 3.96/0.99    inference(cnf_transformation,[],[f21])).
% 3.96/0.99  
% 3.96/0.99  fof(f67,plain,(
% 3.96/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 3.96/0.99    inference(definition_unfolding,[],[f39,f64])).
% 3.96/0.99  
% 3.96/0.99  fof(f71,plain,(
% 3.96/0.99    ( ! [X3,X1] : (r2_hidden(X3,X1) | k3_enumset1(X3,X3,X3,X3,X3) != X1) )),
% 3.96/0.99    inference(equality_resolution,[],[f67])).
% 3.96/0.99  
% 3.96/0.99  fof(f72,plain,(
% 3.96/0.99    ( ! [X3] : (r2_hidden(X3,k3_enumset1(X3,X3,X3,X3,X3))) )),
% 3.96/0.99    inference(equality_resolution,[],[f71])).
% 3.96/0.99  
% 3.96/0.99  fof(f41,plain,(
% 3.96/0.99    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.96/0.99    inference(cnf_transformation,[],[f21])).
% 3.96/0.99  
% 3.96/0.99  fof(f65,plain,(
% 3.96/0.99    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X0) = X1 | sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.96/0.99    inference(definition_unfolding,[],[f41,f64])).
% 3.96/0.99  
% 3.96/0.99  fof(f9,axiom,(
% 3.96/0.99    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 3.96/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/0.99  
% 3.96/0.99  fof(f14,plain,(
% 3.96/0.99    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.96/0.99    inference(ennf_transformation,[],[f9])).
% 3.96/0.99  
% 3.96/0.99  fof(f15,plain,(
% 3.96/0.99    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.96/0.99    inference(flattening,[],[f14])).
% 3.96/0.99  
% 3.96/0.99  fof(f34,plain,(
% 3.96/0.99    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.96/0.99    inference(nnf_transformation,[],[f15])).
% 3.96/0.99  
% 3.96/0.99  fof(f35,plain,(
% 3.96/0.99    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.96/0.99    inference(flattening,[],[f34])).
% 3.96/0.99  
% 3.96/0.99  fof(f56,plain,(
% 3.96/0.99    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.96/0.99    inference(cnf_transformation,[],[f35])).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1,plain,
% 3.96/0.99      ( r2_hidden(sK0(X0,X1),X1)
% 3.96/0.99      | k3_enumset1(X0,X0,X0,X0,X0) = X1
% 3.96/0.99      | sK0(X0,X1) = X0 ),
% 3.96/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_667,plain,
% 3.96/0.99      ( k3_enumset1(X0,X0,X0,X0,X0) = X1
% 3.96/0.99      | sK0(X0,X1) = X0
% 3.96/0.99      | r2_hidden(sK0(X0,X1),X1) = iProver_top ),
% 3.96/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_11,plain,
% 3.96/0.99      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.96/0.99      | r2_hidden(k4_tarski(sK6(X1,X0),X0),X1) ),
% 3.96/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_657,plain,
% 3.96/0.99      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 3.96/0.99      | r2_hidden(k4_tarski(sK6(X1,X0),X0),X1) = iProver_top ),
% 3.96/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_6,plain,
% 3.96/0.99      ( r2_hidden(X0,k1_relat_1(X1)) | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
% 3.96/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_662,plain,
% 3.96/0.99      ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
% 3.96/0.99      | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top ),
% 3.96/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1374,plain,
% 3.96/0.99      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 3.96/0.99      | r2_hidden(sK6(X1,X0),k1_relat_1(X1)) = iProver_top ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_657,c_662]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_17,negated_conjecture,
% 3.96/0.99      ( k3_enumset1(sK7,sK7,sK7,sK7,sK7) = k1_relat_1(sK8) ),
% 3.96/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_3,plain,
% 3.96/0.99      ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1)) | X0 = X1 ),
% 3.96/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_665,plain,
% 3.96/0.99      ( X0 = X1
% 3.96/0.99      | r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1)) != iProver_top ),
% 3.96/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1179,plain,
% 3.96/0.99      ( sK7 = X0 | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_17,c_665]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_2617,plain,
% 3.96/0.99      ( sK6(sK8,X0) = sK7
% 3.96/0.99      | r2_hidden(X0,k2_relat_1(sK8)) != iProver_top ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_1374,c_1179]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_2759,plain,
% 3.96/0.99      ( k3_enumset1(X0,X0,X0,X0,X0) = k2_relat_1(sK8)
% 3.96/0.99      | sK6(sK8,sK0(X0,k2_relat_1(sK8))) = sK7
% 3.96/0.99      | sK0(X0,k2_relat_1(sK8)) = X0 ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_667,c_2617]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_16,negated_conjecture,
% 3.96/0.99      ( k3_enumset1(k1_funct_1(sK8,sK7),k1_funct_1(sK8,sK7),k1_funct_1(sK8,sK7),k1_funct_1(sK8,sK7),k1_funct_1(sK8,sK7)) != k2_relat_1(sK8) ),
% 3.96/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_11738,plain,
% 3.96/0.99      ( sK6(sK8,sK0(k1_funct_1(sK8,sK7),k2_relat_1(sK8))) = sK7
% 3.96/0.99      | sK0(k1_funct_1(sK8,sK7),k2_relat_1(sK8)) = k1_funct_1(sK8,sK7) ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_2759,c_16]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_4045,plain,
% 3.96/0.99      ( r2_hidden(sK0(k1_funct_1(sK8,sK7),k2_relat_1(sK8)),k2_relat_1(sK8))
% 3.96/0.99      | sK0(k1_funct_1(sK8,sK7),k2_relat_1(sK8)) = k1_funct_1(sK8,sK7) ),
% 3.96/0.99      inference(resolution,[status(thm)],[c_1,c_16]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_19,negated_conjecture,
% 3.96/0.99      ( v1_relat_1(sK8) ),
% 3.96/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_12,plain,
% 3.96/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.96/0.99      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 3.96/0.99      | ~ v1_relat_1(X1)
% 3.96/0.99      | ~ v1_funct_1(X1) ),
% 3.96/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_18,negated_conjecture,
% 3.96/0.99      ( v1_funct_1(sK8) ),
% 3.96/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_230,plain,
% 3.96/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.96/0.99      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 3.96/0.99      | ~ v1_relat_1(X1)
% 3.96/0.99      | sK8 != X1 ),
% 3.96/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_18]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_231,plain,
% 3.96/0.99      ( ~ r2_hidden(X0,k1_relat_1(sK8))
% 3.96/0.99      | r2_hidden(k1_funct_1(sK8,X0),k2_relat_1(sK8))
% 3.96/0.99      | ~ v1_relat_1(sK8) ),
% 3.96/0.99      inference(unflattening,[status(thm)],[c_230]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_233,plain,
% 3.96/0.99      ( r2_hidden(k1_funct_1(sK8,sK7),k2_relat_1(sK8))
% 3.96/0.99      | ~ r2_hidden(sK7,k1_relat_1(sK8))
% 3.96/0.99      | ~ v1_relat_1(sK8) ),
% 3.96/0.99      inference(instantiation,[status(thm)],[c_231]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_2,plain,
% 3.96/0.99      ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) ),
% 3.96/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_666,plain,
% 3.96/0.99      ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) = iProver_top ),
% 3.96/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_747,plain,
% 3.96/0.99      ( r2_hidden(sK7,k1_relat_1(sK8)) = iProver_top ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_17,c_666]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_748,plain,
% 3.96/0.99      ( r2_hidden(sK7,k1_relat_1(sK8)) ),
% 3.96/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_747]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_765,plain,
% 3.96/0.99      ( r2_hidden(sK0(k1_funct_1(sK8,sK7),k2_relat_1(sK8)),k2_relat_1(sK8))
% 3.96/0.99      | k3_enumset1(k1_funct_1(sK8,sK7),k1_funct_1(sK8,sK7),k1_funct_1(sK8,sK7),k1_funct_1(sK8,sK7),k1_funct_1(sK8,sK7)) = k2_relat_1(sK8)
% 3.96/0.99      | sK0(k1_funct_1(sK8,sK7),k2_relat_1(sK8)) = k1_funct_1(sK8,sK7) ),
% 3.96/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_389,plain,
% 3.96/0.99      ( X0 != X1 | k2_relat_1(X0) = k2_relat_1(X1) ),
% 3.96/0.99      theory(equality) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_862,plain,
% 3.96/0.99      ( k2_relat_1(sK8) = k2_relat_1(X0) | sK8 != X0 ),
% 3.96/0.99      inference(instantiation,[status(thm)],[c_389]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_917,plain,
% 3.96/0.99      ( k2_relat_1(sK8) = k2_relat_1(sK8) | sK8 != sK8 ),
% 3.96/0.99      inference(instantiation,[status(thm)],[c_862]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_383,plain,( X0 = X0 ),theory(equality) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_918,plain,
% 3.96/0.99      ( sK8 = sK8 ),
% 3.96/0.99      inference(instantiation,[status(thm)],[c_383]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_386,plain,
% 3.96/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.96/0.99      theory(equality) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1012,plain,
% 3.96/0.99      ( r2_hidden(X0,X1)
% 3.96/0.99      | ~ r2_hidden(k1_funct_1(sK8,X2),k2_relat_1(sK8))
% 3.96/0.99      | X0 != k1_funct_1(sK8,X2)
% 3.96/0.99      | X1 != k2_relat_1(sK8) ),
% 3.96/0.99      inference(instantiation,[status(thm)],[c_386]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1454,plain,
% 3.96/0.99      ( r2_hidden(X0,k2_relat_1(X1))
% 3.96/0.99      | ~ r2_hidden(k1_funct_1(sK8,X2),k2_relat_1(sK8))
% 3.96/0.99      | X0 != k1_funct_1(sK8,X2)
% 3.96/0.99      | k2_relat_1(X1) != k2_relat_1(sK8) ),
% 3.96/0.99      inference(instantiation,[status(thm)],[c_1012]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_3117,plain,
% 3.96/0.99      ( ~ r2_hidden(k1_funct_1(sK8,sK7),k2_relat_1(sK8))
% 3.96/0.99      | r2_hidden(sK0(k1_funct_1(sK8,sK7),k2_relat_1(sK8)),k2_relat_1(X0))
% 3.96/0.99      | sK0(k1_funct_1(sK8,sK7),k2_relat_1(sK8)) != k1_funct_1(sK8,sK7)
% 3.96/0.99      | k2_relat_1(X0) != k2_relat_1(sK8) ),
% 3.96/0.99      inference(instantiation,[status(thm)],[c_1454]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_4456,plain,
% 3.96/0.99      ( ~ r2_hidden(k1_funct_1(sK8,sK7),k2_relat_1(sK8))
% 3.96/0.99      | r2_hidden(sK0(k1_funct_1(sK8,sK7),k2_relat_1(sK8)),k2_relat_1(sK8))
% 3.96/0.99      | sK0(k1_funct_1(sK8,sK7),k2_relat_1(sK8)) != k1_funct_1(sK8,sK7)
% 3.96/0.99      | k2_relat_1(sK8) != k2_relat_1(sK8) ),
% 3.96/0.99      inference(instantiation,[status(thm)],[c_3117]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_4558,plain,
% 3.96/0.99      ( r2_hidden(sK0(k1_funct_1(sK8,sK7),k2_relat_1(sK8)),k2_relat_1(sK8)) ),
% 3.96/0.99      inference(global_propositional_subsumption,
% 3.96/0.99                [status(thm)],
% 3.96/0.99                [c_4045,c_19,c_16,c_233,c_748,c_765,c_917,c_918,c_4456]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_0,plain,
% 3.96/0.99      ( ~ r2_hidden(sK0(X0,X1),X1)
% 3.96/0.99      | k3_enumset1(X0,X0,X0,X0,X0) = X1
% 3.96/0.99      | sK0(X0,X1) != X0 ),
% 3.96/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_4570,plain,
% 3.96/0.99      ( k3_enumset1(k1_funct_1(sK8,sK7),k1_funct_1(sK8,sK7),k1_funct_1(sK8,sK7),k1_funct_1(sK8,sK7),k1_funct_1(sK8,sK7)) = k2_relat_1(sK8)
% 3.96/0.99      | sK0(k1_funct_1(sK8,sK7),k2_relat_1(sK8)) != k1_funct_1(sK8,sK7) ),
% 3.96/0.99      inference(resolution,[status(thm)],[c_4558,c_0]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_12179,plain,
% 3.96/0.99      ( sK6(sK8,sK0(k1_funct_1(sK8,sK7),k2_relat_1(sK8))) = sK7 ),
% 3.96/0.99      inference(global_propositional_subsumption,
% 3.96/0.99                [status(thm)],
% 3.96/0.99                [c_11738,c_16,c_4570]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_14,plain,
% 3.96/0.99      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.96/0.99      | ~ v1_relat_1(X2)
% 3.96/0.99      | ~ v1_funct_1(X2)
% 3.96/0.99      | k1_funct_1(X2,X0) = X1 ),
% 3.96/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_248,plain,
% 3.96/0.99      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.96/0.99      | ~ v1_relat_1(X2)
% 3.96/0.99      | k1_funct_1(X2,X0) = X1
% 3.96/0.99      | sK8 != X2 ),
% 3.96/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_18]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_249,plain,
% 3.96/0.99      ( ~ r2_hidden(k4_tarski(X0,X1),sK8)
% 3.96/0.99      | ~ v1_relat_1(sK8)
% 3.96/0.99      | k1_funct_1(sK8,X0) = X1 ),
% 3.96/0.99      inference(unflattening,[status(thm)],[c_248]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_253,plain,
% 3.96/0.99      ( ~ r2_hidden(k4_tarski(X0,X1),sK8) | k1_funct_1(sK8,X0) = X1 ),
% 3.96/0.99      inference(global_propositional_subsumption,
% 3.96/0.99                [status(thm)],
% 3.96/0.99                [c_249,c_19]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_654,plain,
% 3.96/0.99      ( k1_funct_1(sK8,X0) = X1
% 3.96/0.99      | r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top ),
% 3.96/0.99      inference(predicate_to_equality,[status(thm)],[c_253]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1377,plain,
% 3.96/0.99      ( k1_funct_1(sK8,sK6(sK8,X0)) = X0
% 3.96/0.99      | r2_hidden(X0,k2_relat_1(sK8)) != iProver_top ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_657,c_654]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_2327,plain,
% 3.96/0.99      ( k3_enumset1(X0,X0,X0,X0,X0) = k2_relat_1(sK8)
% 3.96/0.99      | k1_funct_1(sK8,sK6(sK8,sK0(X0,k2_relat_1(sK8)))) = sK0(X0,k2_relat_1(sK8))
% 3.96/0.99      | sK0(X0,k2_relat_1(sK8)) = X0 ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_667,c_1377]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_12575,plain,
% 3.96/0.99      ( k3_enumset1(k1_funct_1(sK8,sK7),k1_funct_1(sK8,sK7),k1_funct_1(sK8,sK7),k1_funct_1(sK8,sK7),k1_funct_1(sK8,sK7)) = k2_relat_1(sK8)
% 3.96/0.99      | sK0(k1_funct_1(sK8,sK7),k2_relat_1(sK8)) = k1_funct_1(sK8,sK7) ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_12179,c_2327]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(contradiction,plain,
% 3.96/0.99      ( $false ),
% 3.96/0.99      inference(minisat,[status(thm)],[c_12575,c_4570,c_16]) ).
% 3.96/0.99  
% 3.96/0.99  
% 3.96/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.96/0.99  
% 3.96/0.99  ------                               Statistics
% 3.96/0.99  
% 3.96/0.99  ------ Selected
% 3.96/0.99  
% 3.96/0.99  total_time:                             0.445
% 3.96/0.99  
%------------------------------------------------------------------------------
