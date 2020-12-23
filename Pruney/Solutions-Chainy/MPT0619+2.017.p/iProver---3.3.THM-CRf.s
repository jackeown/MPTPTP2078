%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:49:14 EST 2020

% Result     : Theorem 7.58s
% Output     : CNFRefutation 7.58s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 527 expanded)
%              Number of clauses        :   58 (  93 expanded)
%              Number of leaves         :   24 ( 142 expanded)
%              Depth                    :   16
%              Number of atoms          :  412 (1397 expanded)
%              Number of equality atoms :  207 ( 808 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK1(X0,X1) != X1
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( sK1(X0,X1) != X1
        & r2_hidden(sK1(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f27])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f75,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f52,f53])).

fof(f76,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f51,f75])).

fof(f77,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f50,f76])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | k1_xboole_0 = X0
      | k3_enumset1(X1,X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f54,f77])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f39,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK6(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0)
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0)
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0)
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0)
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK7(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f36,f39,f38,f37])).

fof(f61,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK7(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f93,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK7(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f61])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f33,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK3(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK2(X0,X1),X3),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK2(X0,X1),X4),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK2(X0,X1),X3),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f30,f33,f32,f31])).

fof(f58,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f90,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( k1_tarski(X0) = k1_relat_1(X1)
         => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f21,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1)
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f22,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1)
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f44,plain,
    ( ? [X0,X1] :
        ( k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1)
        & k1_tarski(X0) = k1_relat_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k1_tarski(k1_funct_1(sK9,sK8)) != k2_relat_1(sK9)
      & k1_tarski(sK8) = k1_relat_1(sK9)
      & v1_funct_1(sK9)
      & v1_relat_1(sK9) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( k1_tarski(k1_funct_1(sK9,sK8)) != k2_relat_1(sK9)
    & k1_tarski(sK8) = k1_relat_1(sK9)
    & v1_funct_1(sK9)
    & v1_relat_1(sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f22,f44])).

fof(f73,plain,(
    k1_tarski(sK8) = k1_relat_1(sK9) ),
    inference(cnf_transformation,[],[f45])).

fof(f86,plain,(
    k3_enumset1(sK8,sK8,sK8,sK8,sK8) = k1_relat_1(sK9) ),
    inference(definition_unfolding,[],[f73,f77])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
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

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f25,plain,(
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

fof(f26,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f81,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f46,f77])).

fof(f89,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f81])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f80,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f47,f77])).

fof(f87,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k3_enumset1(X3,X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f80])).

fof(f88,plain,(
    ! [X3] : r2_hidden(X3,k3_enumset1(X3,X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f87])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f65,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f71,plain,(
    v1_relat_1(sK9) ),
    inference(cnf_transformation,[],[f45])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k3_enumset1(X1,X1,X1,X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f56,f77])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,k1_relat_1(X1))
          | k1_xboole_0 = k11_relat_1(X1,X0) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f74,plain,(
    k1_tarski(k1_funct_1(sK9,sK8)) != k2_relat_1(sK9) ),
    inference(cnf_transformation,[],[f45])).

fof(f85,plain,(
    k3_enumset1(k1_funct_1(sK9,sK8),k1_funct_1(sK9,sK8),k1_funct_1(sK9,sK8),k1_funct_1(sK9,sK8),k1_funct_1(sK9,sK8)) != k2_relat_1(sK9) ),
    inference(definition_unfolding,[],[f74,f77])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f42])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f72,plain,(
    v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f45])).

fof(f55,plain,(
    ! [X0,X1] :
      ( sK1(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f82,plain,(
    ! [X0,X1] :
      ( sK1(X0,X1) != X1
      | k1_xboole_0 = X0
      | k3_enumset1(X1,X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f55,f77])).

cnf(c_5,plain,
    ( r2_hidden(sK1(X0,X1),X0)
    | k3_enumset1(X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_971,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r2_hidden(sK1(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK7(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_963,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(sK7(X1,X0),X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_9,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_968,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2076,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(sK7(X1,X0),k1_relat_1(X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_963,c_968])).

cnf(c_22,negated_conjecture,
    ( k3_enumset1(sK8,sK8,sK8,sK8,sK8) = k1_relat_1(sK9) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_972,plain,
    ( X0 = X1
    | r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1719,plain,
    ( sK8 = X0
    | r2_hidden(X0,k1_relat_1(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_22,c_972])).

cnf(c_4226,plain,
    ( sK7(sK9,X0) = sK8
    | r2_hidden(X0,k2_relat_1(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2076,c_1719])).

cnf(c_4239,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = k2_relat_1(sK9)
    | sK7(sK9,sK1(k2_relat_1(sK9),X0)) = sK8
    | k2_relat_1(sK9) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_971,c_4226])).

cnf(c_2,plain,
    ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_973,plain,
    ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1122,plain,
    ( r2_hidden(sK8,k1_relat_1(sK9)) = iProver_top ),
    inference(superposition,[status(thm)],[c_22,c_973])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_24,negated_conjecture,
    ( v1_relat_1(sK9) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_303,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_24])).

cnf(c_304,plain,
    ( k9_relat_1(sK9,k1_relat_1(sK9)) = k2_relat_1(sK9) ),
    inference(unflattening,[status(thm)],[c_303])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k3_enumset1(X1,X1,X1,X1,X1)) = k11_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_308,plain,
    ( k9_relat_1(X0,k3_enumset1(X1,X1,X1,X1,X1)) = k11_relat_1(X0,X1)
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_24])).

cnf(c_309,plain,
    ( k9_relat_1(sK9,k3_enumset1(X0,X0,X0,X0,X0)) = k11_relat_1(sK9,X0) ),
    inference(unflattening,[status(thm)],[c_308])).

cnf(c_1124,plain,
    ( k9_relat_1(sK9,k1_relat_1(sK9)) = k11_relat_1(sK9,sK8) ),
    inference(superposition,[status(thm)],[c_22,c_309])).

cnf(c_1202,plain,
    ( k11_relat_1(sK9,sK8) = k2_relat_1(sK9) ),
    inference(superposition,[status(thm)],[c_304,c_1124])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k11_relat_1(X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_314,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | k11_relat_1(X1,X0) != k1_xboole_0
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_24])).

cnf(c_315,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK9))
    | k11_relat_1(sK9,X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_314])).

cnf(c_406,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK9))
    | k11_relat_1(sK9,X0) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_315])).

cnf(c_960,plain,
    ( k11_relat_1(sK9,X0) != k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_406])).

cnf(c_2888,plain,
    ( k2_relat_1(sK9) != k1_xboole_0
    | r2_hidden(sK8,k1_relat_1(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1202,c_960])).

cnf(c_17609,plain,
    ( sK7(sK9,sK1(k2_relat_1(sK9),X0)) = sK8
    | k3_enumset1(X0,X0,X0,X0,X0) = k2_relat_1(sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4239,c_1122,c_2888])).

cnf(c_17610,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = k2_relat_1(sK9)
    | sK7(sK9,sK1(k2_relat_1(sK9),X0)) = sK8 ),
    inference(renaming,[status(thm)],[c_17609])).

cnf(c_21,negated_conjecture,
    ( k3_enumset1(k1_funct_1(sK9,sK8),k1_funct_1(sK9,sK8),k1_funct_1(sK9,sK8),k1_funct_1(sK9,sK8),k1_funct_1(sK9,sK8)) != k2_relat_1(sK9) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_17666,plain,
    ( sK7(sK9,sK1(k2_relat_1(sK9),k1_funct_1(sK9,sK8))) = sK8 ),
    inference(superposition,[status(thm)],[c_17610,c_21])).

cnf(c_17724,plain,
    ( r2_hidden(k4_tarski(sK8,sK1(k2_relat_1(sK9),k1_funct_1(sK9,sK8))),sK9) = iProver_top
    | r2_hidden(sK1(k2_relat_1(sK9),k1_funct_1(sK9,sK8)),k2_relat_1(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_17666,c_963])).

cnf(c_518,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1154,plain,
    ( X0 != X1
    | k2_relat_1(sK9) != X1
    | k2_relat_1(sK9) = X0 ),
    inference(instantiation,[status(thm)],[c_518])).

cnf(c_1906,plain,
    ( X0 != k2_relat_1(sK9)
    | k2_relat_1(sK9) = X0
    | k2_relat_1(sK9) != k2_relat_1(sK9) ),
    inference(instantiation,[status(thm)],[c_1154])).

cnf(c_15110,plain,
    ( k2_relat_1(sK9) != k2_relat_1(sK9)
    | k2_relat_1(sK9) = k1_xboole_0
    | k1_xboole_0 != k2_relat_1(sK9) ),
    inference(instantiation,[status(thm)],[c_1906])).

cnf(c_517,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1436,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_518,c_517])).

cnf(c_19,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_279,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1
    | sK9 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_23])).

cnf(c_280,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK9)
    | ~ v1_relat_1(sK9)
    | k1_funct_1(sK9,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_279])).

cnf(c_284,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK9)
    | k1_funct_1(sK9,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_280,c_24])).

cnf(c_7769,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK9)
    | X1 = k1_funct_1(sK9,X0) ),
    inference(resolution,[status(thm)],[c_1436,c_284])).

cnf(c_4,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = X1
    | sK1(X1,X0) != X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_5818,plain,
    ( sK1(k2_relat_1(sK9),k1_funct_1(sK9,sK8)) != k1_funct_1(sK9,sK8)
    | k1_xboole_0 = k2_relat_1(sK9) ),
    inference(resolution,[status(thm)],[c_4,c_21])).

cnf(c_8585,plain,
    ( ~ r2_hidden(k4_tarski(sK8,sK1(k2_relat_1(sK9),k1_funct_1(sK9,sK8))),sK9)
    | k1_xboole_0 = k2_relat_1(sK9) ),
    inference(resolution,[status(thm)],[c_7769,c_5818])).

cnf(c_8586,plain,
    ( k1_xboole_0 = k2_relat_1(sK9)
    | r2_hidden(k4_tarski(sK8,sK1(k2_relat_1(sK9),k1_funct_1(sK9,sK8))),sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8585])).

cnf(c_1339,plain,
    ( r2_hidden(k2_relat_1(sK9),k3_enumset1(k2_relat_1(sK9),k2_relat_1(sK9),k2_relat_1(sK9),k2_relat_1(sK9),k2_relat_1(sK9))) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1155,plain,
    ( ~ r2_hidden(k2_relat_1(sK9),k3_enumset1(X0,X0,X0,X0,X0))
    | k2_relat_1(sK9) = X0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1338,plain,
    ( ~ r2_hidden(k2_relat_1(sK9),k3_enumset1(k2_relat_1(sK9),k2_relat_1(sK9),k2_relat_1(sK9),k2_relat_1(sK9),k2_relat_1(sK9)))
    | k2_relat_1(sK9) = k2_relat_1(sK9) ),
    inference(instantiation,[status(thm)],[c_1155])).

cnf(c_1109,plain,
    ( r2_hidden(sK1(k2_relat_1(sK9),k1_funct_1(sK9,sK8)),k2_relat_1(sK9))
    | k3_enumset1(k1_funct_1(sK9,sK8),k1_funct_1(sK9,sK8),k1_funct_1(sK9,sK8),k1_funct_1(sK9,sK8),k1_funct_1(sK9,sK8)) = k2_relat_1(sK9)
    | k1_xboole_0 = k2_relat_1(sK9) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1110,plain,
    ( k3_enumset1(k1_funct_1(sK9,sK8),k1_funct_1(sK9,sK8),k1_funct_1(sK9,sK8),k1_funct_1(sK9,sK8),k1_funct_1(sK9,sK8)) = k2_relat_1(sK9)
    | k1_xboole_0 = k2_relat_1(sK9)
    | r2_hidden(sK1(k2_relat_1(sK9),k1_funct_1(sK9,sK8)),k2_relat_1(sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1109])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17724,c_15110,c_8586,c_2888,c_1339,c_1338,c_1122,c_1110,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:22:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.58/1.52  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.58/1.52  
% 7.58/1.52  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.58/1.52  
% 7.58/1.52  ------  iProver source info
% 7.58/1.52  
% 7.58/1.52  git: date: 2020-06-30 10:37:57 +0100
% 7.58/1.52  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.58/1.52  git: non_committed_changes: false
% 7.58/1.52  git: last_make_outside_of_git: false
% 7.58/1.52  
% 7.58/1.52  ------ 
% 7.58/1.52  ------ Parsing...
% 7.58/1.52  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.58/1.52  
% 7.58/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.58/1.52  
% 7.58/1.52  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.58/1.52  
% 7.58/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.58/1.52  ------ Proving...
% 7.58/1.52  ------ Problem Properties 
% 7.58/1.52  
% 7.58/1.52  
% 7.58/1.52  clauses                                 22
% 7.58/1.52  conjectures                             2
% 7.58/1.52  EPR                                     0
% 7.58/1.52  Horn                                    16
% 7.58/1.52  unary                                   5
% 7.58/1.52  binary                                  9
% 7.58/1.52  lits                                    47
% 7.58/1.52  lits eq                                 21
% 7.58/1.52  fd_pure                                 0
% 7.58/1.52  fd_pseudo                               0
% 7.58/1.52  fd_cond                                 0
% 7.58/1.52  fd_pseudo_cond                          9
% 7.58/1.52  AC symbols                              0
% 7.58/1.52  
% 7.58/1.52  ------ Input Options Time Limit: Unbounded
% 7.58/1.52  
% 7.58/1.52  
% 7.58/1.52  ------ 
% 7.58/1.52  Current options:
% 7.58/1.52  ------ 
% 7.58/1.52  
% 7.58/1.52  
% 7.58/1.52  
% 7.58/1.52  
% 7.58/1.52  ------ Proving...
% 7.58/1.52  
% 7.58/1.52  
% 7.58/1.52  % SZS status Theorem for theBenchmark.p
% 7.58/1.52  
% 7.58/1.52  % SZS output start CNFRefutation for theBenchmark.p
% 7.58/1.52  
% 7.58/1.52  fof(f6,axiom,(
% 7.58/1.52    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 7.58/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.52  
% 7.58/1.52  fof(f15,plain,(
% 7.58/1.52    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 7.58/1.52    inference(ennf_transformation,[],[f6])).
% 7.58/1.52  
% 7.58/1.52  fof(f27,plain,(
% 7.58/1.52    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK1(X0,X1) != X1 & r2_hidden(sK1(X0,X1),X0)))),
% 7.58/1.52    introduced(choice_axiom,[])).
% 7.58/1.52  
% 7.58/1.52  fof(f28,plain,(
% 7.58/1.52    ! [X0,X1] : ((sK1(X0,X1) != X1 & r2_hidden(sK1(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 7.58/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f27])).
% 7.58/1.52  
% 7.58/1.52  fof(f54,plain,(
% 7.58/1.52    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 7.58/1.52    inference(cnf_transformation,[],[f28])).
% 7.58/1.52  
% 7.58/1.52  fof(f2,axiom,(
% 7.58/1.52    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 7.58/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.52  
% 7.58/1.52  fof(f50,plain,(
% 7.58/1.52    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 7.58/1.52    inference(cnf_transformation,[],[f2])).
% 7.58/1.52  
% 7.58/1.52  fof(f3,axiom,(
% 7.58/1.52    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.58/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.52  
% 7.58/1.52  fof(f51,plain,(
% 7.58/1.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.58/1.52    inference(cnf_transformation,[],[f3])).
% 7.58/1.52  
% 7.58/1.52  fof(f4,axiom,(
% 7.58/1.52    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.58/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.52  
% 7.58/1.52  fof(f52,plain,(
% 7.58/1.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.58/1.52    inference(cnf_transformation,[],[f4])).
% 7.58/1.52  
% 7.58/1.52  fof(f5,axiom,(
% 7.58/1.52    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.58/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.52  
% 7.58/1.52  fof(f53,plain,(
% 7.58/1.52    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.58/1.52    inference(cnf_transformation,[],[f5])).
% 7.58/1.52  
% 7.58/1.52  fof(f75,plain,(
% 7.58/1.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 7.58/1.52    inference(definition_unfolding,[],[f52,f53])).
% 7.58/1.52  
% 7.58/1.52  fof(f76,plain,(
% 7.58/1.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 7.58/1.52    inference(definition_unfolding,[],[f51,f75])).
% 7.58/1.52  
% 7.58/1.52  fof(f77,plain,(
% 7.58/1.52    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 7.58/1.52    inference(definition_unfolding,[],[f50,f76])).
% 7.58/1.52  
% 7.58/1.52  fof(f83,plain,(
% 7.58/1.52    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | k1_xboole_0 = X0 | k3_enumset1(X1,X1,X1,X1,X1) = X0) )),
% 7.58/1.52    inference(definition_unfolding,[],[f54,f77])).
% 7.58/1.52  
% 7.58/1.52  fof(f9,axiom,(
% 7.58/1.52    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 7.58/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.52  
% 7.58/1.52  fof(f35,plain,(
% 7.58/1.52    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 7.58/1.52    inference(nnf_transformation,[],[f9])).
% 7.58/1.52  
% 7.58/1.52  fof(f36,plain,(
% 7.58/1.52    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 7.58/1.52    inference(rectify,[],[f35])).
% 7.58/1.52  
% 7.58/1.52  fof(f39,plain,(
% 7.58/1.52    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK7(X0,X5),X5),X0))),
% 7.58/1.52    introduced(choice_axiom,[])).
% 7.58/1.52  
% 7.58/1.52  fof(f38,plain,(
% 7.58/1.52    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK6(X0,X1),X2),X0))) )),
% 7.58/1.52    introduced(choice_axiom,[])).
% 7.58/1.52  
% 7.58/1.52  fof(f37,plain,(
% 7.58/1.52    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1))))),
% 7.58/1.52    introduced(choice_axiom,[])).
% 7.58/1.52  
% 7.58/1.52  fof(f40,plain,(
% 7.58/1.52    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 7.58/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f36,f39,f38,f37])).
% 7.58/1.52  
% 7.58/1.52  fof(f61,plain,(
% 7.58/1.52    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 7.58/1.52    inference(cnf_transformation,[],[f40])).
% 7.58/1.52  
% 7.58/1.52  fof(f93,plain,(
% 7.58/1.52    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 7.58/1.52    inference(equality_resolution,[],[f61])).
% 7.58/1.52  
% 7.58/1.52  fof(f8,axiom,(
% 7.58/1.52    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 7.58/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.52  
% 7.58/1.52  fof(f29,plain,(
% 7.58/1.52    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 7.58/1.52    inference(nnf_transformation,[],[f8])).
% 7.58/1.52  
% 7.58/1.52  fof(f30,plain,(
% 7.58/1.52    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 7.58/1.52    inference(rectify,[],[f29])).
% 7.58/1.52  
% 7.58/1.52  fof(f33,plain,(
% 7.58/1.52    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0))),
% 7.58/1.52    introduced(choice_axiom,[])).
% 7.58/1.52  
% 7.58/1.52  fof(f32,plain,(
% 7.58/1.52    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) => r2_hidden(k4_tarski(X2,sK3(X0,X1)),X0))) )),
% 7.58/1.52    introduced(choice_axiom,[])).
% 7.58/1.52  
% 7.58/1.52  fof(f31,plain,(
% 7.58/1.52    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK2(X0,X1),X3),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK2(X0,X1),X4),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 7.58/1.52    introduced(choice_axiom,[])).
% 7.58/1.52  
% 7.58/1.52  fof(f34,plain,(
% 7.58/1.52    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK2(X0,X1),X3),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 7.58/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f30,f33,f32,f31])).
% 7.58/1.52  
% 7.58/1.52  fof(f58,plain,(
% 7.58/1.52    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 7.58/1.52    inference(cnf_transformation,[],[f34])).
% 7.58/1.52  
% 7.58/1.52  fof(f90,plain,(
% 7.58/1.52    ( ! [X6,X0,X5] : (r2_hidden(X5,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X6),X0)) )),
% 7.58/1.52    inference(equality_resolution,[],[f58])).
% 7.58/1.52  
% 7.58/1.52  fof(f13,conjecture,(
% 7.58/1.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 7.58/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.52  
% 7.58/1.52  fof(f14,negated_conjecture,(
% 7.58/1.52    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 7.58/1.52    inference(negated_conjecture,[],[f13])).
% 7.58/1.52  
% 7.58/1.52  fof(f21,plain,(
% 7.58/1.52    ? [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1) & k1_tarski(X0) = k1_relat_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 7.58/1.52    inference(ennf_transformation,[],[f14])).
% 7.58/1.52  
% 7.58/1.52  fof(f22,plain,(
% 7.58/1.52    ? [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 7.58/1.52    inference(flattening,[],[f21])).
% 7.58/1.52  
% 7.58/1.52  fof(f44,plain,(
% 7.58/1.52    ? [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(k1_funct_1(sK9,sK8)) != k2_relat_1(sK9) & k1_tarski(sK8) = k1_relat_1(sK9) & v1_funct_1(sK9) & v1_relat_1(sK9))),
% 7.58/1.52    introduced(choice_axiom,[])).
% 7.58/1.52  
% 7.58/1.52  fof(f45,plain,(
% 7.58/1.52    k1_tarski(k1_funct_1(sK9,sK8)) != k2_relat_1(sK9) & k1_tarski(sK8) = k1_relat_1(sK9) & v1_funct_1(sK9) & v1_relat_1(sK9)),
% 7.58/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f22,f44])).
% 7.58/1.52  
% 7.58/1.52  fof(f73,plain,(
% 7.58/1.52    k1_tarski(sK8) = k1_relat_1(sK9)),
% 7.58/1.52    inference(cnf_transformation,[],[f45])).
% 7.58/1.52  
% 7.58/1.52  fof(f86,plain,(
% 7.58/1.52    k3_enumset1(sK8,sK8,sK8,sK8,sK8) = k1_relat_1(sK9)),
% 7.58/1.52    inference(definition_unfolding,[],[f73,f77])).
% 7.58/1.52  
% 7.58/1.52  fof(f1,axiom,(
% 7.58/1.52    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 7.58/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.52  
% 7.58/1.52  fof(f23,plain,(
% 7.58/1.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 7.58/1.52    inference(nnf_transformation,[],[f1])).
% 7.58/1.52  
% 7.58/1.52  fof(f24,plain,(
% 7.58/1.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.58/1.52    inference(rectify,[],[f23])).
% 7.58/1.52  
% 7.58/1.52  fof(f25,plain,(
% 7.58/1.52    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1))))),
% 7.58/1.52    introduced(choice_axiom,[])).
% 7.58/1.52  
% 7.58/1.52  fof(f26,plain,(
% 7.58/1.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.58/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).
% 7.58/1.52  
% 7.58/1.52  fof(f46,plain,(
% 7.58/1.52    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 7.58/1.52    inference(cnf_transformation,[],[f26])).
% 7.58/1.52  
% 7.58/1.52  fof(f81,plain,(
% 7.58/1.52    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 7.58/1.52    inference(definition_unfolding,[],[f46,f77])).
% 7.58/1.52  
% 7.58/1.52  fof(f89,plain,(
% 7.58/1.52    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0))) )),
% 7.58/1.52    inference(equality_resolution,[],[f81])).
% 7.58/1.52  
% 7.58/1.52  fof(f47,plain,(
% 7.58/1.52    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 7.58/1.52    inference(cnf_transformation,[],[f26])).
% 7.58/1.52  
% 7.58/1.52  fof(f80,plain,(
% 7.58/1.52    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 7.58/1.52    inference(definition_unfolding,[],[f47,f77])).
% 7.58/1.52  
% 7.58/1.52  fof(f87,plain,(
% 7.58/1.52    ( ! [X3,X1] : (r2_hidden(X3,X1) | k3_enumset1(X3,X3,X3,X3,X3) != X1) )),
% 7.58/1.52    inference(equality_resolution,[],[f80])).
% 7.58/1.52  
% 7.58/1.52  fof(f88,plain,(
% 7.58/1.52    ( ! [X3] : (r2_hidden(X3,k3_enumset1(X3,X3,X3,X3,X3))) )),
% 7.58/1.52    inference(equality_resolution,[],[f87])).
% 7.58/1.52  
% 7.58/1.52  fof(f10,axiom,(
% 7.58/1.52    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 7.58/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.52  
% 7.58/1.52  fof(f17,plain,(
% 7.58/1.52    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 7.58/1.52    inference(ennf_transformation,[],[f10])).
% 7.58/1.52  
% 7.58/1.52  fof(f65,plain,(
% 7.58/1.52    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 7.58/1.52    inference(cnf_transformation,[],[f17])).
% 7.58/1.52  
% 7.58/1.52  fof(f71,plain,(
% 7.58/1.52    v1_relat_1(sK9)),
% 7.58/1.52    inference(cnf_transformation,[],[f45])).
% 7.58/1.52  
% 7.58/1.52  fof(f7,axiom,(
% 7.58/1.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 7.58/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.52  
% 7.58/1.52  fof(f16,plain,(
% 7.58/1.52    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 7.58/1.52    inference(ennf_transformation,[],[f7])).
% 7.58/1.52  
% 7.58/1.52  fof(f56,plain,(
% 7.58/1.52    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 7.58/1.52    inference(cnf_transformation,[],[f16])).
% 7.58/1.52  
% 7.58/1.52  fof(f84,plain,(
% 7.58/1.52    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k3_enumset1(X1,X1,X1,X1,X1)) | ~v1_relat_1(X0)) )),
% 7.58/1.52    inference(definition_unfolding,[],[f56,f77])).
% 7.58/1.52  
% 7.58/1.52  fof(f11,axiom,(
% 7.58/1.52    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 7.58/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.52  
% 7.58/1.52  fof(f18,plain,(
% 7.58/1.52    ! [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 7.58/1.52    inference(ennf_transformation,[],[f11])).
% 7.58/1.52  
% 7.58/1.52  fof(f41,plain,(
% 7.58/1.52    ! [X0,X1] : (((r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 = k11_relat_1(X1,X0)) & (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)))) | ~v1_relat_1(X1))),
% 7.58/1.52    inference(nnf_transformation,[],[f18])).
% 7.58/1.52  
% 7.58/1.52  fof(f66,plain,(
% 7.58/1.52    ( ! [X0,X1] : (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 7.58/1.52    inference(cnf_transformation,[],[f41])).
% 7.58/1.52  
% 7.58/1.52  fof(f74,plain,(
% 7.58/1.52    k1_tarski(k1_funct_1(sK9,sK8)) != k2_relat_1(sK9)),
% 7.58/1.52    inference(cnf_transformation,[],[f45])).
% 7.58/1.52  
% 7.58/1.52  fof(f85,plain,(
% 7.58/1.52    k3_enumset1(k1_funct_1(sK9,sK8),k1_funct_1(sK9,sK8),k1_funct_1(sK9,sK8),k1_funct_1(sK9,sK8),k1_funct_1(sK9,sK8)) != k2_relat_1(sK9)),
% 7.58/1.52    inference(definition_unfolding,[],[f74,f77])).
% 7.58/1.52  
% 7.58/1.52  fof(f12,axiom,(
% 7.58/1.52    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 7.58/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.52  
% 7.58/1.52  fof(f19,plain,(
% 7.58/1.52    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 7.58/1.52    inference(ennf_transformation,[],[f12])).
% 7.58/1.52  
% 7.58/1.52  fof(f20,plain,(
% 7.58/1.52    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 7.58/1.52    inference(flattening,[],[f19])).
% 7.58/1.52  
% 7.58/1.52  fof(f42,plain,(
% 7.58/1.52    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 7.58/1.52    inference(nnf_transformation,[],[f20])).
% 7.58/1.52  
% 7.58/1.52  fof(f43,plain,(
% 7.58/1.52    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 7.58/1.52    inference(flattening,[],[f42])).
% 7.58/1.52  
% 7.58/1.52  fof(f69,plain,(
% 7.58/1.52    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.58/1.52    inference(cnf_transformation,[],[f43])).
% 7.58/1.52  
% 7.58/1.52  fof(f72,plain,(
% 7.58/1.52    v1_funct_1(sK9)),
% 7.58/1.52    inference(cnf_transformation,[],[f45])).
% 7.58/1.52  
% 7.58/1.52  fof(f55,plain,(
% 7.58/1.52    ( ! [X0,X1] : (sK1(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 7.58/1.52    inference(cnf_transformation,[],[f28])).
% 7.58/1.52  
% 7.58/1.52  fof(f82,plain,(
% 7.58/1.52    ( ! [X0,X1] : (sK1(X0,X1) != X1 | k1_xboole_0 = X0 | k3_enumset1(X1,X1,X1,X1,X1) = X0) )),
% 7.58/1.52    inference(definition_unfolding,[],[f55,f77])).
% 7.58/1.52  
% 7.58/1.52  cnf(c_5,plain,
% 7.58/1.52      ( r2_hidden(sK1(X0,X1),X0)
% 7.58/1.52      | k3_enumset1(X1,X1,X1,X1,X1) = X0
% 7.58/1.52      | k1_xboole_0 = X0 ),
% 7.58/1.52      inference(cnf_transformation,[],[f83]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_971,plain,
% 7.58/1.52      ( k3_enumset1(X0,X0,X0,X0,X0) = X1
% 7.58/1.52      | k1_xboole_0 = X1
% 7.58/1.52      | r2_hidden(sK1(X1,X0),X1) = iProver_top ),
% 7.58/1.52      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_14,plain,
% 7.58/1.52      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 7.58/1.52      | r2_hidden(k4_tarski(sK7(X1,X0),X0),X1) ),
% 7.58/1.52      inference(cnf_transformation,[],[f93]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_963,plain,
% 7.58/1.52      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 7.58/1.52      | r2_hidden(k4_tarski(sK7(X1,X0),X0),X1) = iProver_top ),
% 7.58/1.52      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_9,plain,
% 7.58/1.52      ( r2_hidden(X0,k1_relat_1(X1)) | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
% 7.58/1.52      inference(cnf_transformation,[],[f90]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_968,plain,
% 7.58/1.52      ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
% 7.58/1.52      | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top ),
% 7.58/1.52      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_2076,plain,
% 7.58/1.52      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 7.58/1.52      | r2_hidden(sK7(X1,X0),k1_relat_1(X1)) = iProver_top ),
% 7.58/1.52      inference(superposition,[status(thm)],[c_963,c_968]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_22,negated_conjecture,
% 7.58/1.52      ( k3_enumset1(sK8,sK8,sK8,sK8,sK8) = k1_relat_1(sK9) ),
% 7.58/1.52      inference(cnf_transformation,[],[f86]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_3,plain,
% 7.58/1.52      ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1)) | X0 = X1 ),
% 7.58/1.52      inference(cnf_transformation,[],[f89]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_972,plain,
% 7.58/1.52      ( X0 = X1
% 7.58/1.52      | r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1)) != iProver_top ),
% 7.58/1.52      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_1719,plain,
% 7.58/1.52      ( sK8 = X0 | r2_hidden(X0,k1_relat_1(sK9)) != iProver_top ),
% 7.58/1.52      inference(superposition,[status(thm)],[c_22,c_972]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_4226,plain,
% 7.58/1.52      ( sK7(sK9,X0) = sK8
% 7.58/1.52      | r2_hidden(X0,k2_relat_1(sK9)) != iProver_top ),
% 7.58/1.52      inference(superposition,[status(thm)],[c_2076,c_1719]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_4239,plain,
% 7.58/1.52      ( k3_enumset1(X0,X0,X0,X0,X0) = k2_relat_1(sK9)
% 7.58/1.52      | sK7(sK9,sK1(k2_relat_1(sK9),X0)) = sK8
% 7.58/1.52      | k2_relat_1(sK9) = k1_xboole_0 ),
% 7.58/1.52      inference(superposition,[status(thm)],[c_971,c_4226]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_2,plain,
% 7.58/1.52      ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) ),
% 7.58/1.52      inference(cnf_transformation,[],[f88]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_973,plain,
% 7.58/1.52      ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) = iProver_top ),
% 7.58/1.52      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_1122,plain,
% 7.58/1.52      ( r2_hidden(sK8,k1_relat_1(sK9)) = iProver_top ),
% 7.58/1.52      inference(superposition,[status(thm)],[c_22,c_973]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_15,plain,
% 7.58/1.52      ( ~ v1_relat_1(X0)
% 7.58/1.52      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 7.58/1.52      inference(cnf_transformation,[],[f65]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_24,negated_conjecture,
% 7.58/1.52      ( v1_relat_1(sK9) ),
% 7.58/1.52      inference(cnf_transformation,[],[f71]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_303,plain,
% 7.58/1.52      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | sK9 != X0 ),
% 7.58/1.52      inference(resolution_lifted,[status(thm)],[c_15,c_24]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_304,plain,
% 7.58/1.52      ( k9_relat_1(sK9,k1_relat_1(sK9)) = k2_relat_1(sK9) ),
% 7.58/1.52      inference(unflattening,[status(thm)],[c_303]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_6,plain,
% 7.58/1.52      ( ~ v1_relat_1(X0)
% 7.58/1.52      | k9_relat_1(X0,k3_enumset1(X1,X1,X1,X1,X1)) = k11_relat_1(X0,X1) ),
% 7.58/1.52      inference(cnf_transformation,[],[f84]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_308,plain,
% 7.58/1.52      ( k9_relat_1(X0,k3_enumset1(X1,X1,X1,X1,X1)) = k11_relat_1(X0,X1)
% 7.58/1.52      | sK9 != X0 ),
% 7.58/1.52      inference(resolution_lifted,[status(thm)],[c_6,c_24]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_309,plain,
% 7.58/1.52      ( k9_relat_1(sK9,k3_enumset1(X0,X0,X0,X0,X0)) = k11_relat_1(sK9,X0) ),
% 7.58/1.52      inference(unflattening,[status(thm)],[c_308]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_1124,plain,
% 7.58/1.52      ( k9_relat_1(sK9,k1_relat_1(sK9)) = k11_relat_1(sK9,sK8) ),
% 7.58/1.52      inference(superposition,[status(thm)],[c_22,c_309]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_1202,plain,
% 7.58/1.52      ( k11_relat_1(sK9,sK8) = k2_relat_1(sK9) ),
% 7.58/1.52      inference(superposition,[status(thm)],[c_304,c_1124]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_17,plain,
% 7.58/1.52      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 7.58/1.52      | ~ v1_relat_1(X1)
% 7.58/1.52      | k11_relat_1(X1,X0) != k1_xboole_0 ),
% 7.58/1.52      inference(cnf_transformation,[],[f66]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_314,plain,
% 7.58/1.52      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 7.58/1.52      | k11_relat_1(X1,X0) != k1_xboole_0
% 7.58/1.52      | sK9 != X1 ),
% 7.58/1.52      inference(resolution_lifted,[status(thm)],[c_17,c_24]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_315,plain,
% 7.58/1.52      ( ~ r2_hidden(X0,k1_relat_1(sK9))
% 7.58/1.52      | k11_relat_1(sK9,X0) != k1_xboole_0 ),
% 7.58/1.52      inference(unflattening,[status(thm)],[c_314]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_406,plain,
% 7.58/1.52      ( ~ r2_hidden(X0,k1_relat_1(sK9))
% 7.58/1.52      | k11_relat_1(sK9,X0) != k1_xboole_0 ),
% 7.58/1.52      inference(prop_impl,[status(thm)],[c_315]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_960,plain,
% 7.58/1.52      ( k11_relat_1(sK9,X0) != k1_xboole_0
% 7.58/1.52      | r2_hidden(X0,k1_relat_1(sK9)) != iProver_top ),
% 7.58/1.52      inference(predicate_to_equality,[status(thm)],[c_406]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_2888,plain,
% 7.58/1.52      ( k2_relat_1(sK9) != k1_xboole_0
% 7.58/1.52      | r2_hidden(sK8,k1_relat_1(sK9)) != iProver_top ),
% 7.58/1.52      inference(superposition,[status(thm)],[c_1202,c_960]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_17609,plain,
% 7.58/1.52      ( sK7(sK9,sK1(k2_relat_1(sK9),X0)) = sK8
% 7.58/1.52      | k3_enumset1(X0,X0,X0,X0,X0) = k2_relat_1(sK9) ),
% 7.58/1.52      inference(global_propositional_subsumption,
% 7.58/1.52                [status(thm)],
% 7.58/1.52                [c_4239,c_1122,c_2888]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_17610,plain,
% 7.58/1.52      ( k3_enumset1(X0,X0,X0,X0,X0) = k2_relat_1(sK9)
% 7.58/1.52      | sK7(sK9,sK1(k2_relat_1(sK9),X0)) = sK8 ),
% 7.58/1.52      inference(renaming,[status(thm)],[c_17609]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_21,negated_conjecture,
% 7.58/1.52      ( k3_enumset1(k1_funct_1(sK9,sK8),k1_funct_1(sK9,sK8),k1_funct_1(sK9,sK8),k1_funct_1(sK9,sK8),k1_funct_1(sK9,sK8)) != k2_relat_1(sK9) ),
% 7.58/1.52      inference(cnf_transformation,[],[f85]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_17666,plain,
% 7.58/1.52      ( sK7(sK9,sK1(k2_relat_1(sK9),k1_funct_1(sK9,sK8))) = sK8 ),
% 7.58/1.52      inference(superposition,[status(thm)],[c_17610,c_21]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_17724,plain,
% 7.58/1.52      ( r2_hidden(k4_tarski(sK8,sK1(k2_relat_1(sK9),k1_funct_1(sK9,sK8))),sK9) = iProver_top
% 7.58/1.52      | r2_hidden(sK1(k2_relat_1(sK9),k1_funct_1(sK9,sK8)),k2_relat_1(sK9)) != iProver_top ),
% 7.58/1.52      inference(superposition,[status(thm)],[c_17666,c_963]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_518,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_1154,plain,
% 7.58/1.52      ( X0 != X1 | k2_relat_1(sK9) != X1 | k2_relat_1(sK9) = X0 ),
% 7.58/1.52      inference(instantiation,[status(thm)],[c_518]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_1906,plain,
% 7.58/1.52      ( X0 != k2_relat_1(sK9)
% 7.58/1.52      | k2_relat_1(sK9) = X0
% 7.58/1.52      | k2_relat_1(sK9) != k2_relat_1(sK9) ),
% 7.58/1.52      inference(instantiation,[status(thm)],[c_1154]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_15110,plain,
% 7.58/1.52      ( k2_relat_1(sK9) != k2_relat_1(sK9)
% 7.58/1.52      | k2_relat_1(sK9) = k1_xboole_0
% 7.58/1.52      | k1_xboole_0 != k2_relat_1(sK9) ),
% 7.58/1.52      inference(instantiation,[status(thm)],[c_1906]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_517,plain,( X0 = X0 ),theory(equality) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_1436,plain,
% 7.58/1.52      ( X0 != X1 | X1 = X0 ),
% 7.58/1.52      inference(resolution,[status(thm)],[c_518,c_517]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_19,plain,
% 7.58/1.52      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 7.58/1.52      | ~ v1_funct_1(X2)
% 7.58/1.52      | ~ v1_relat_1(X2)
% 7.58/1.52      | k1_funct_1(X2,X0) = X1 ),
% 7.58/1.52      inference(cnf_transformation,[],[f69]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_23,negated_conjecture,
% 7.58/1.52      ( v1_funct_1(sK9) ),
% 7.58/1.52      inference(cnf_transformation,[],[f72]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_279,plain,
% 7.58/1.52      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 7.58/1.52      | ~ v1_relat_1(X2)
% 7.58/1.52      | k1_funct_1(X2,X0) = X1
% 7.58/1.52      | sK9 != X2 ),
% 7.58/1.52      inference(resolution_lifted,[status(thm)],[c_19,c_23]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_280,plain,
% 7.58/1.52      ( ~ r2_hidden(k4_tarski(X0,X1),sK9)
% 7.58/1.52      | ~ v1_relat_1(sK9)
% 7.58/1.52      | k1_funct_1(sK9,X0) = X1 ),
% 7.58/1.52      inference(unflattening,[status(thm)],[c_279]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_284,plain,
% 7.58/1.52      ( ~ r2_hidden(k4_tarski(X0,X1),sK9) | k1_funct_1(sK9,X0) = X1 ),
% 7.58/1.52      inference(global_propositional_subsumption,
% 7.58/1.52                [status(thm)],
% 7.58/1.52                [c_280,c_24]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_7769,plain,
% 7.58/1.52      ( ~ r2_hidden(k4_tarski(X0,X1),sK9) | X1 = k1_funct_1(sK9,X0) ),
% 7.58/1.52      inference(resolution,[status(thm)],[c_1436,c_284]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_4,plain,
% 7.58/1.52      ( k3_enumset1(X0,X0,X0,X0,X0) = X1
% 7.58/1.52      | sK1(X1,X0) != X0
% 7.58/1.52      | k1_xboole_0 = X1 ),
% 7.58/1.52      inference(cnf_transformation,[],[f82]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_5818,plain,
% 7.58/1.52      ( sK1(k2_relat_1(sK9),k1_funct_1(sK9,sK8)) != k1_funct_1(sK9,sK8)
% 7.58/1.52      | k1_xboole_0 = k2_relat_1(sK9) ),
% 7.58/1.52      inference(resolution,[status(thm)],[c_4,c_21]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_8585,plain,
% 7.58/1.52      ( ~ r2_hidden(k4_tarski(sK8,sK1(k2_relat_1(sK9),k1_funct_1(sK9,sK8))),sK9)
% 7.58/1.52      | k1_xboole_0 = k2_relat_1(sK9) ),
% 7.58/1.52      inference(resolution,[status(thm)],[c_7769,c_5818]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_8586,plain,
% 7.58/1.52      ( k1_xboole_0 = k2_relat_1(sK9)
% 7.58/1.52      | r2_hidden(k4_tarski(sK8,sK1(k2_relat_1(sK9),k1_funct_1(sK9,sK8))),sK9) != iProver_top ),
% 7.58/1.52      inference(predicate_to_equality,[status(thm)],[c_8585]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_1339,plain,
% 7.58/1.52      ( r2_hidden(k2_relat_1(sK9),k3_enumset1(k2_relat_1(sK9),k2_relat_1(sK9),k2_relat_1(sK9),k2_relat_1(sK9),k2_relat_1(sK9))) ),
% 7.58/1.52      inference(instantiation,[status(thm)],[c_2]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_1155,plain,
% 7.58/1.52      ( ~ r2_hidden(k2_relat_1(sK9),k3_enumset1(X0,X0,X0,X0,X0))
% 7.58/1.52      | k2_relat_1(sK9) = X0 ),
% 7.58/1.52      inference(instantiation,[status(thm)],[c_3]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_1338,plain,
% 7.58/1.52      ( ~ r2_hidden(k2_relat_1(sK9),k3_enumset1(k2_relat_1(sK9),k2_relat_1(sK9),k2_relat_1(sK9),k2_relat_1(sK9),k2_relat_1(sK9)))
% 7.58/1.52      | k2_relat_1(sK9) = k2_relat_1(sK9) ),
% 7.58/1.52      inference(instantiation,[status(thm)],[c_1155]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_1109,plain,
% 7.58/1.52      ( r2_hidden(sK1(k2_relat_1(sK9),k1_funct_1(sK9,sK8)),k2_relat_1(sK9))
% 7.58/1.52      | k3_enumset1(k1_funct_1(sK9,sK8),k1_funct_1(sK9,sK8),k1_funct_1(sK9,sK8),k1_funct_1(sK9,sK8),k1_funct_1(sK9,sK8)) = k2_relat_1(sK9)
% 7.58/1.52      | k1_xboole_0 = k2_relat_1(sK9) ),
% 7.58/1.52      inference(instantiation,[status(thm)],[c_5]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_1110,plain,
% 7.58/1.52      ( k3_enumset1(k1_funct_1(sK9,sK8),k1_funct_1(sK9,sK8),k1_funct_1(sK9,sK8),k1_funct_1(sK9,sK8),k1_funct_1(sK9,sK8)) = k2_relat_1(sK9)
% 7.58/1.52      | k1_xboole_0 = k2_relat_1(sK9)
% 7.58/1.52      | r2_hidden(sK1(k2_relat_1(sK9),k1_funct_1(sK9,sK8)),k2_relat_1(sK9)) = iProver_top ),
% 7.58/1.52      inference(predicate_to_equality,[status(thm)],[c_1109]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(contradiction,plain,
% 7.58/1.52      ( $false ),
% 7.58/1.52      inference(minisat,
% 7.58/1.52                [status(thm)],
% 7.58/1.52                [c_17724,c_15110,c_8586,c_2888,c_1339,c_1338,c_1122,
% 7.58/1.52                 c_1110,c_21]) ).
% 7.58/1.52  
% 7.58/1.52  
% 7.58/1.52  % SZS output end CNFRefutation for theBenchmark.p
% 7.58/1.52  
% 7.58/1.52  ------                               Statistics
% 7.58/1.52  
% 7.58/1.52  ------ Selected
% 7.58/1.52  
% 7.58/1.52  total_time:                             0.587
% 7.58/1.52  
%------------------------------------------------------------------------------
