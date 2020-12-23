%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:51:15 EST 2020

% Result     : Theorem 3.64s
% Output     : CNFRefutation 3.64s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 897 expanded)
%              Number of clauses        :   73 ( 250 expanded)
%              Number of leaves         :   15 ( 182 expanded)
%              Depth                    :   19
%              Number of atoms          :  482 (5917 expanded)
%              Number of equality atoms :  238 (1297 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK2(X0,X1) != X1
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( sK2(X0,X1) != X1
        & r2_hidden(sK2(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f34])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f75,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f59,f60])).

fof(f76,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f58,f75])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | k1_xboole_0 = X0
      | k2_enumset1(X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f61,f76])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ r2_hidden(X1,k11_relat_1(X2,X0)) )
        & ( r2_hidden(X1,k11_relat_1(X2,X0))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r2_hidden(X0,k1_relat_1(X1))
         => k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f21,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) != k11_relat_1(X1,X0)
      & r2_hidden(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f22,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) != k11_relat_1(X1,X0)
      & r2_hidden(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f40,plain,
    ( ? [X0,X1] :
        ( k1_tarski(k1_funct_1(X1,X0)) != k11_relat_1(X1,X0)
        & r2_hidden(X0,k1_relat_1(X1))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k1_tarski(k1_funct_1(sK4,sK3)) != k11_relat_1(sK4,sK3)
      & r2_hidden(sK3,k1_relat_1(sK4))
      & v1_funct_1(sK4)
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( k1_tarski(k1_funct_1(sK4,sK3)) != k11_relat_1(sK4,sK3)
    & r2_hidden(sK3,k1_relat_1(sK4))
    & v1_funct_1(sK4)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f22,f40])).

fof(f71,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f38,plain,(
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

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f72,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f74,plain,(
    k1_tarski(k1_funct_1(sK4,sK3)) != k11_relat_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f88,plain,(
    k2_enumset1(k1_funct_1(sK4,sK3),k1_funct_1(sK4,sK3),k1_funct_1(sK4,sK3),k1_funct_1(sK4,sK3)) != k11_relat_1(sK4,sK3) ),
    inference(definition_unfolding,[],[f74,f76])).

fof(f62,plain,(
    ! [X0,X1] :
      ( sK2(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f85,plain,(
    ! [X0,X1] :
      ( sK2(X0,X1) != X1
      | k1_xboole_0 = X0
      | k2_enumset1(X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f62,f76])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f99,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f70])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f73,plain,(
    r2_hidden(sK3,k1_relat_1(sK4)) ),
    inference(cnf_transformation,[],[f41])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f23])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f91,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f90,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f43])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f29])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK1(X0,X1,X2,X3) != X2
            & sK1(X0,X1,X2,X3) != X1
            & sK1(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK1(X0,X1,X2,X3),X3) )
        & ( sK1(X0,X1,X2,X3) = X2
          | sK1(X0,X1,X2,X3) = X1
          | sK1(X0,X1,X2,X3) = X0
          | r2_hidden(sK1(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK1(X0,X1,X2,X3) != X2
              & sK1(X0,X1,X2,X3) != X1
              & sK1(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK1(X0,X1,X2,X3),X3) )
          & ( sK1(X0,X1,X2,X3) = X2
            | sK1(X0,X1,X2,X3) = X1
            | sK1(X0,X1,X2,X3) = X0
            | r2_hidden(sK1(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).

fof(f51,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f83,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f51,f60])).

fof(f96,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f83])).

fof(f97,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k2_enumset1(X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f96])).

cnf(c_17,plain,
    ( r2_hidden(sK2(X0,X1),X0)
    | k2_enumset1(X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1248,plain,
    ( k2_enumset1(X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r2_hidden(sK2(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,k11_relat_1(X1,X2))
    | r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_29,negated_conjecture,
    ( v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_483,plain,
    ( ~ r2_hidden(X0,k11_relat_1(X1,X2))
    | r2_hidden(k4_tarski(X2,X0),X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_29])).

cnf(c_484,plain,
    ( ~ r2_hidden(X0,k11_relat_1(sK4,X1))
    | r2_hidden(k4_tarski(X1,X0),sK4) ),
    inference(unflattening,[status(thm)],[c_483])).

cnf(c_602,plain,
    ( r2_hidden(k4_tarski(X1,X0),sK4)
    | ~ r2_hidden(X0,k11_relat_1(sK4,X1)) ),
    inference(prop_impl,[status(thm)],[c_484])).

cnf(c_603,plain,
    ( ~ r2_hidden(X0,k11_relat_1(sK4,X1))
    | r2_hidden(k4_tarski(X1,X0),sK4) ),
    inference(renaming,[status(thm)],[c_602])).

cnf(c_1242,plain,
    ( r2_hidden(X0,k11_relat_1(sK4,X1)) != iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_603])).

cnf(c_2591,plain,
    ( k2_enumset1(X0,X0,X0,X0) = k11_relat_1(sK4,X1)
    | k11_relat_1(sK4,X1) = k1_xboole_0
    | r2_hidden(k4_tarski(X1,sK2(k11_relat_1(sK4,X1),X0)),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1248,c_1242])).

cnf(c_24,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_378,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_28])).

cnf(c_379,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK4)
    | ~ v1_relat_1(sK4)
    | k1_funct_1(sK4,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_378])).

cnf(c_383,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK4)
    | k1_funct_1(sK4,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_379,c_29])).

cnf(c_1246,plain,
    ( k1_funct_1(sK4,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_383])).

cnf(c_8178,plain,
    ( k2_enumset1(X0,X0,X0,X0) = k11_relat_1(sK4,X1)
    | k11_relat_1(sK4,X1) = k1_xboole_0
    | sK2(k11_relat_1(sK4,X1),X0) = k1_funct_1(sK4,X1) ),
    inference(superposition,[status(thm)],[c_2591,c_1246])).

cnf(c_26,negated_conjecture,
    ( k2_enumset1(k1_funct_1(sK4,sK3),k1_funct_1(sK4,sK3),k1_funct_1(sK4,sK3),k1_funct_1(sK4,sK3)) != k11_relat_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_8726,plain,
    ( k11_relat_1(sK4,X0) != k11_relat_1(sK4,sK3)
    | k11_relat_1(sK4,X0) = k1_xboole_0
    | sK2(k11_relat_1(sK4,X0),k1_funct_1(sK4,sK3)) = k1_funct_1(sK4,X0) ),
    inference(superposition,[status(thm)],[c_8178,c_26])).

cnf(c_9116,plain,
    ( k11_relat_1(sK4,sK3) = k1_xboole_0
    | sK2(k11_relat_1(sK4,sK3),k1_funct_1(sK4,sK3)) = k1_funct_1(sK4,sK3) ),
    inference(equality_resolution,[status(thm)],[c_8726])).

cnf(c_16,plain,
    ( k2_enumset1(X0,X0,X0,X0) = X1
    | sK2(X1,X0) != X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1500,plain,
    ( k2_enumset1(k1_funct_1(sK4,sK3),k1_funct_1(sK4,sK3),k1_funct_1(sK4,sK3),k1_funct_1(sK4,sK3)) = k11_relat_1(sK4,sK3)
    | sK2(k11_relat_1(sK4,sK3),k1_funct_1(sK4,sK3)) != k1_funct_1(sK4,sK3)
    | k1_xboole_0 = k11_relat_1(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_740,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1787,plain,
    ( k11_relat_1(sK4,sK3) = k11_relat_1(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_740])).

cnf(c_741,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1568,plain,
    ( X0 != X1
    | k11_relat_1(sK4,sK3) != X1
    | k11_relat_1(sK4,sK3) = X0 ),
    inference(instantiation,[status(thm)],[c_741])).

cnf(c_1786,plain,
    ( X0 != k11_relat_1(sK4,sK3)
    | k11_relat_1(sK4,sK3) = X0
    | k11_relat_1(sK4,sK3) != k11_relat_1(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_1568])).

cnf(c_2771,plain,
    ( k11_relat_1(sK4,sK3) != k11_relat_1(sK4,sK3)
    | k11_relat_1(sK4,sK3) = k1_xboole_0
    | k1_xboole_0 != k11_relat_1(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_1786])).

cnf(c_9134,plain,
    ( k11_relat_1(sK4,sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9116,c_26,c_1500,c_1787,c_2771])).

cnf(c_23,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_414,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_28])).

cnf(c_415,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK4,X0)),sK4)
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_414])).

cnf(c_419,plain,
    ( r2_hidden(k4_tarski(X0,k1_funct_1(sK4,X0)),sK4)
    | ~ r2_hidden(X0,k1_relat_1(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_415,c_29])).

cnf(c_420,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK4,X0)),sK4) ),
    inference(renaming,[status(thm)],[c_419])).

cnf(c_1244,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK4,X0)),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_420])).

cnf(c_22,plain,
    ( r2_hidden(X0,k11_relat_1(X1,X2))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_471,plain,
    ( r2_hidden(X0,k11_relat_1(X1,X2))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_29])).

cnf(c_472,plain,
    ( r2_hidden(X0,k11_relat_1(sK4,X1))
    | ~ r2_hidden(k4_tarski(X1,X0),sK4) ),
    inference(unflattening,[status(thm)],[c_471])).

cnf(c_604,plain,
    ( ~ r2_hidden(k4_tarski(X1,X0),sK4)
    | r2_hidden(X0,k11_relat_1(sK4,X1)) ),
    inference(prop_impl,[status(thm)],[c_472])).

cnf(c_605,plain,
    ( r2_hidden(X0,k11_relat_1(sK4,X1))
    | ~ r2_hidden(k4_tarski(X1,X0),sK4) ),
    inference(renaming,[status(thm)],[c_604])).

cnf(c_1243,plain,
    ( r2_hidden(X0,k11_relat_1(sK4,X1)) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_605])).

cnf(c_2214,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),k11_relat_1(sK4,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1244,c_1243])).

cnf(c_9150,plain,
    ( r2_hidden(k1_funct_1(sK4,sK3),k1_xboole_0) = iProver_top
    | r2_hidden(sK3,k1_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9134,c_2214])).

cnf(c_27,negated_conjecture,
    ( r2_hidden(sK3,k1_relat_1(sK4)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_32,plain,
    ( r2_hidden(sK3,k1_relat_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_12937,plain,
    ( r2_hidden(k1_funct_1(sK4,sK3),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9150,c_32])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1260,plain,
    ( k4_xboole_0(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1261,plain,
    ( k4_xboole_0(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2927,plain,
    ( k4_xboole_0(X0,X0) = X1
    | r2_hidden(sK0(X0,X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1260,c_1261])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1257,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3376,plain,
    ( k4_xboole_0(X0,X0) = k4_xboole_0(X1,X2)
    | r2_hidden(sK0(X0,X0,k4_xboole_0(X1,X2)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2927,c_1257])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1258,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3377,plain,
    ( k4_xboole_0(X0,X0) = k4_xboole_0(X1,X2)
    | r2_hidden(sK0(X0,X0,k4_xboole_0(X1,X2)),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2927,c_1258])).

cnf(c_3487,plain,
    ( k4_xboole_0(X0,X0) = k4_xboole_0(X1,X1) ),
    inference(superposition,[status(thm)],[c_3376,c_3377])).

cnf(c_3542,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3487,c_1257])).

cnf(c_3543,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3487,c_1258])).

cnf(c_3557,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,X1)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3542,c_3543])).

cnf(c_3738,plain,
    ( k2_enumset1(X0,X0,X0,X0) = k4_xboole_0(X1,X1)
    | k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1248,c_3557])).

cnf(c_4327,plain,
    ( k4_xboole_0(X0,X0) != k11_relat_1(sK4,sK3)
    | k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3738,c_26])).

cnf(c_4456,plain,
    ( k4_xboole_0(X0,X0) != k11_relat_1(sK4,sK3)
    | k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3487,c_4327])).

cnf(c_3565,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,X1)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3557])).

cnf(c_14,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1250,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4321,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0
    | r2_hidden(X1,k4_xboole_0(X0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3738,c_1250])).

cnf(c_4443,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,X1))
    | k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4321])).

cnf(c_4511,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4456,c_3565,c_4443])).

cnf(c_4512,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_4511])).

cnf(c_4522,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4512,c_3557])).

cnf(c_12942,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_12937,c_4522])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:49:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.64/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.64/0.98  
% 3.64/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.64/0.98  
% 3.64/0.98  ------  iProver source info
% 3.64/0.98  
% 3.64/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.64/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.64/0.98  git: non_committed_changes: false
% 3.64/0.98  git: last_make_outside_of_git: false
% 3.64/0.98  
% 3.64/0.98  ------ 
% 3.64/0.98  
% 3.64/0.98  ------ Input Options
% 3.64/0.98  
% 3.64/0.98  --out_options                           all
% 3.64/0.98  --tptp_safe_out                         true
% 3.64/0.98  --problem_path                          ""
% 3.64/0.98  --include_path                          ""
% 3.64/0.98  --clausifier                            res/vclausify_rel
% 3.64/0.98  --clausifier_options                    --mode clausify
% 3.64/0.98  --stdin                                 false
% 3.64/0.98  --stats_out                             all
% 3.64/0.98  
% 3.64/0.98  ------ General Options
% 3.64/0.98  
% 3.64/0.98  --fof                                   false
% 3.64/0.98  --time_out_real                         305.
% 3.64/0.98  --time_out_virtual                      -1.
% 3.64/0.98  --symbol_type_check                     false
% 3.64/0.98  --clausify_out                          false
% 3.64/0.98  --sig_cnt_out                           false
% 3.64/0.98  --trig_cnt_out                          false
% 3.64/0.98  --trig_cnt_out_tolerance                1.
% 3.64/0.98  --trig_cnt_out_sk_spl                   false
% 3.64/0.98  --abstr_cl_out                          false
% 3.64/0.98  
% 3.64/0.98  ------ Global Options
% 3.64/0.98  
% 3.64/0.98  --schedule                              default
% 3.64/0.98  --add_important_lit                     false
% 3.64/0.98  --prop_solver_per_cl                    1000
% 3.64/0.98  --min_unsat_core                        false
% 3.64/0.98  --soft_assumptions                      false
% 3.64/0.98  --soft_lemma_size                       3
% 3.64/0.98  --prop_impl_unit_size                   0
% 3.64/0.98  --prop_impl_unit                        []
% 3.64/0.98  --share_sel_clauses                     true
% 3.64/0.98  --reset_solvers                         false
% 3.64/0.98  --bc_imp_inh                            [conj_cone]
% 3.64/0.98  --conj_cone_tolerance                   3.
% 3.64/0.98  --extra_neg_conj                        none
% 3.64/0.98  --large_theory_mode                     true
% 3.64/0.98  --prolific_symb_bound                   200
% 3.64/0.98  --lt_threshold                          2000
% 3.64/0.98  --clause_weak_htbl                      true
% 3.64/0.98  --gc_record_bc_elim                     false
% 3.64/0.98  
% 3.64/0.98  ------ Preprocessing Options
% 3.64/0.98  
% 3.64/0.98  --preprocessing_flag                    true
% 3.64/0.98  --time_out_prep_mult                    0.1
% 3.64/0.98  --splitting_mode                        input
% 3.64/0.98  --splitting_grd                         true
% 3.64/0.98  --splitting_cvd                         false
% 3.64/0.98  --splitting_cvd_svl                     false
% 3.64/0.98  --splitting_nvd                         32
% 3.64/0.98  --sub_typing                            true
% 3.64/0.98  --prep_gs_sim                           true
% 3.64/0.98  --prep_unflatten                        true
% 3.64/0.98  --prep_res_sim                          true
% 3.64/0.98  --prep_upred                            true
% 3.64/0.98  --prep_sem_filter                       exhaustive
% 3.64/0.98  --prep_sem_filter_out                   false
% 3.64/0.98  --pred_elim                             true
% 3.64/0.98  --res_sim_input                         true
% 3.64/0.98  --eq_ax_congr_red                       true
% 3.64/0.98  --pure_diseq_elim                       true
% 3.64/0.98  --brand_transform                       false
% 3.64/0.98  --non_eq_to_eq                          false
% 3.64/0.98  --prep_def_merge                        true
% 3.64/0.98  --prep_def_merge_prop_impl              false
% 3.64/0.98  --prep_def_merge_mbd                    true
% 3.64/0.98  --prep_def_merge_tr_red                 false
% 3.64/0.98  --prep_def_merge_tr_cl                  false
% 3.64/0.98  --smt_preprocessing                     true
% 3.64/0.98  --smt_ac_axioms                         fast
% 3.64/0.98  --preprocessed_out                      false
% 3.64/0.98  --preprocessed_stats                    false
% 3.64/0.98  
% 3.64/0.98  ------ Abstraction refinement Options
% 3.64/0.98  
% 3.64/0.98  --abstr_ref                             []
% 3.64/0.98  --abstr_ref_prep                        false
% 3.64/0.98  --abstr_ref_until_sat                   false
% 3.64/0.98  --abstr_ref_sig_restrict                funpre
% 3.64/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.64/0.98  --abstr_ref_under                       []
% 3.64/0.98  
% 3.64/0.98  ------ SAT Options
% 3.64/0.98  
% 3.64/0.98  --sat_mode                              false
% 3.64/0.98  --sat_fm_restart_options                ""
% 3.64/0.98  --sat_gr_def                            false
% 3.64/0.98  --sat_epr_types                         true
% 3.64/0.98  --sat_non_cyclic_types                  false
% 3.64/0.98  --sat_finite_models                     false
% 3.64/0.98  --sat_fm_lemmas                         false
% 3.64/0.98  --sat_fm_prep                           false
% 3.64/0.98  --sat_fm_uc_incr                        true
% 3.64/0.98  --sat_out_model                         small
% 3.64/0.98  --sat_out_clauses                       false
% 3.64/0.98  
% 3.64/0.98  ------ QBF Options
% 3.64/0.98  
% 3.64/0.98  --qbf_mode                              false
% 3.64/0.98  --qbf_elim_univ                         false
% 3.64/0.98  --qbf_dom_inst                          none
% 3.64/0.98  --qbf_dom_pre_inst                      false
% 3.64/0.98  --qbf_sk_in                             false
% 3.64/0.98  --qbf_pred_elim                         true
% 3.64/0.98  --qbf_split                             512
% 3.64/0.98  
% 3.64/0.98  ------ BMC1 Options
% 3.64/0.98  
% 3.64/0.98  --bmc1_incremental                      false
% 3.64/0.98  --bmc1_axioms                           reachable_all
% 3.64/0.98  --bmc1_min_bound                        0
% 3.64/0.98  --bmc1_max_bound                        -1
% 3.64/0.98  --bmc1_max_bound_default                -1
% 3.64/0.98  --bmc1_symbol_reachability              true
% 3.64/0.98  --bmc1_property_lemmas                  false
% 3.64/0.98  --bmc1_k_induction                      false
% 3.64/0.98  --bmc1_non_equiv_states                 false
% 3.64/0.98  --bmc1_deadlock                         false
% 3.64/0.98  --bmc1_ucm                              false
% 3.64/0.98  --bmc1_add_unsat_core                   none
% 3.64/0.98  --bmc1_unsat_core_children              false
% 3.64/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.64/0.98  --bmc1_out_stat                         full
% 3.64/0.98  --bmc1_ground_init                      false
% 3.64/0.98  --bmc1_pre_inst_next_state              false
% 3.64/0.98  --bmc1_pre_inst_state                   false
% 3.64/0.98  --bmc1_pre_inst_reach_state             false
% 3.64/0.98  --bmc1_out_unsat_core                   false
% 3.64/0.98  --bmc1_aig_witness_out                  false
% 3.64/0.98  --bmc1_verbose                          false
% 3.64/0.98  --bmc1_dump_clauses_tptp                false
% 3.64/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.64/0.98  --bmc1_dump_file                        -
% 3.64/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.64/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.64/0.98  --bmc1_ucm_extend_mode                  1
% 3.64/0.98  --bmc1_ucm_init_mode                    2
% 3.64/0.98  --bmc1_ucm_cone_mode                    none
% 3.64/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.64/0.98  --bmc1_ucm_relax_model                  4
% 3.64/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.64/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.64/0.98  --bmc1_ucm_layered_model                none
% 3.64/0.98  --bmc1_ucm_max_lemma_size               10
% 3.64/0.98  
% 3.64/0.98  ------ AIG Options
% 3.64/0.98  
% 3.64/0.98  --aig_mode                              false
% 3.64/0.98  
% 3.64/0.98  ------ Instantiation Options
% 3.64/0.98  
% 3.64/0.98  --instantiation_flag                    true
% 3.64/0.98  --inst_sos_flag                         false
% 3.64/0.98  --inst_sos_phase                        true
% 3.64/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.64/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.64/0.98  --inst_lit_sel_side                     num_symb
% 3.64/0.98  --inst_solver_per_active                1400
% 3.64/0.98  --inst_solver_calls_frac                1.
% 3.64/0.98  --inst_passive_queue_type               priority_queues
% 3.64/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.64/0.98  --inst_passive_queues_freq              [25;2]
% 3.64/0.98  --inst_dismatching                      true
% 3.64/0.98  --inst_eager_unprocessed_to_passive     true
% 3.64/0.98  --inst_prop_sim_given                   true
% 3.64/0.98  --inst_prop_sim_new                     false
% 3.64/0.98  --inst_subs_new                         false
% 3.64/0.98  --inst_eq_res_simp                      false
% 3.64/0.98  --inst_subs_given                       false
% 3.64/0.98  --inst_orphan_elimination               true
% 3.64/0.98  --inst_learning_loop_flag               true
% 3.64/0.98  --inst_learning_start                   3000
% 3.64/0.98  --inst_learning_factor                  2
% 3.64/0.98  --inst_start_prop_sim_after_learn       3
% 3.64/0.98  --inst_sel_renew                        solver
% 3.64/0.98  --inst_lit_activity_flag                true
% 3.64/0.98  --inst_restr_to_given                   false
% 3.64/0.98  --inst_activity_threshold               500
% 3.64/0.98  --inst_out_proof                        true
% 3.64/0.98  
% 3.64/0.98  ------ Resolution Options
% 3.64/0.98  
% 3.64/0.98  --resolution_flag                       true
% 3.64/0.98  --res_lit_sel                           adaptive
% 3.64/0.98  --res_lit_sel_side                      none
% 3.64/0.98  --res_ordering                          kbo
% 3.64/0.98  --res_to_prop_solver                    active
% 3.64/0.98  --res_prop_simpl_new                    false
% 3.64/0.98  --res_prop_simpl_given                  true
% 3.64/0.98  --res_passive_queue_type                priority_queues
% 3.64/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.64/0.98  --res_passive_queues_freq               [15;5]
% 3.64/0.98  --res_forward_subs                      full
% 3.64/0.98  --res_backward_subs                     full
% 3.64/0.98  --res_forward_subs_resolution           true
% 3.64/0.98  --res_backward_subs_resolution          true
% 3.64/0.98  --res_orphan_elimination                true
% 3.64/0.98  --res_time_limit                        2.
% 3.64/0.98  --res_out_proof                         true
% 3.64/0.98  
% 3.64/0.98  ------ Superposition Options
% 3.64/0.98  
% 3.64/0.98  --superposition_flag                    true
% 3.64/0.98  --sup_passive_queue_type                priority_queues
% 3.64/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.64/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.64/0.98  --demod_completeness_check              fast
% 3.64/0.98  --demod_use_ground                      true
% 3.64/0.98  --sup_to_prop_solver                    passive
% 3.64/0.98  --sup_prop_simpl_new                    true
% 3.64/0.98  --sup_prop_simpl_given                  true
% 3.64/0.98  --sup_fun_splitting                     false
% 3.64/0.98  --sup_smt_interval                      50000
% 3.64/0.98  
% 3.64/0.98  ------ Superposition Simplification Setup
% 3.64/0.98  
% 3.64/0.98  --sup_indices_passive                   []
% 3.64/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.64/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.64/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.64/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.64/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.64/0.98  --sup_full_bw                           [BwDemod]
% 3.64/0.98  --sup_immed_triv                        [TrivRules]
% 3.64/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.64/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.64/0.98  --sup_immed_bw_main                     []
% 3.64/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.64/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.64/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.64/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.64/0.98  
% 3.64/0.98  ------ Combination Options
% 3.64/0.98  
% 3.64/0.98  --comb_res_mult                         3
% 3.64/0.98  --comb_sup_mult                         2
% 3.64/0.98  --comb_inst_mult                        10
% 3.64/0.98  
% 3.64/0.98  ------ Debug Options
% 3.64/0.98  
% 3.64/0.98  --dbg_backtrace                         false
% 3.64/0.98  --dbg_dump_prop_clauses                 false
% 3.64/0.98  --dbg_dump_prop_clauses_file            -
% 3.64/0.98  --dbg_out_stat                          false
% 3.64/0.98  ------ Parsing...
% 3.64/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.64/0.98  
% 3.64/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.64/0.98  
% 3.64/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.64/0.98  
% 3.64/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.64/0.98  ------ Proving...
% 3.64/0.98  ------ Problem Properties 
% 3.64/0.98  
% 3.64/0.98  
% 3.64/0.98  clauses                                 26
% 3.64/0.98  conjectures                             2
% 3.64/0.98  EPR                                     0
% 3.64/0.98  Horn                                    18
% 3.64/0.98  unary                                   6
% 3.64/0.98  binary                                  9
% 3.64/0.98  lits                                    61
% 3.64/0.98  lits eq                                 28
% 3.64/0.98  fd_pure                                 0
% 3.64/0.98  fd_pseudo                               0
% 3.64/0.98  fd_cond                                 0
% 3.64/0.98  fd_pseudo_cond                          10
% 3.64/0.98  AC symbols                              0
% 3.64/0.98  
% 3.64/0.98  ------ Schedule dynamic 5 is on 
% 3.64/0.98  
% 3.64/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.64/0.98  
% 3.64/0.98  
% 3.64/0.98  ------ 
% 3.64/0.98  Current options:
% 3.64/0.98  ------ 
% 3.64/0.98  
% 3.64/0.98  ------ Input Options
% 3.64/0.98  
% 3.64/0.98  --out_options                           all
% 3.64/0.98  --tptp_safe_out                         true
% 3.64/0.98  --problem_path                          ""
% 3.64/0.98  --include_path                          ""
% 3.64/0.98  --clausifier                            res/vclausify_rel
% 3.64/0.98  --clausifier_options                    --mode clausify
% 3.64/0.98  --stdin                                 false
% 3.64/0.98  --stats_out                             all
% 3.64/0.98  
% 3.64/0.98  ------ General Options
% 3.64/0.98  
% 3.64/0.98  --fof                                   false
% 3.64/0.98  --time_out_real                         305.
% 3.64/0.98  --time_out_virtual                      -1.
% 3.64/0.98  --symbol_type_check                     false
% 3.64/0.98  --clausify_out                          false
% 3.64/0.98  --sig_cnt_out                           false
% 3.64/0.98  --trig_cnt_out                          false
% 3.64/0.98  --trig_cnt_out_tolerance                1.
% 3.64/0.98  --trig_cnt_out_sk_spl                   false
% 3.64/0.98  --abstr_cl_out                          false
% 3.64/0.98  
% 3.64/0.98  ------ Global Options
% 3.64/0.98  
% 3.64/0.98  --schedule                              default
% 3.64/0.98  --add_important_lit                     false
% 3.64/0.98  --prop_solver_per_cl                    1000
% 3.64/0.98  --min_unsat_core                        false
% 3.64/0.98  --soft_assumptions                      false
% 3.64/0.98  --soft_lemma_size                       3
% 3.64/0.98  --prop_impl_unit_size                   0
% 3.64/0.98  --prop_impl_unit                        []
% 3.64/0.98  --share_sel_clauses                     true
% 3.64/0.98  --reset_solvers                         false
% 3.64/0.98  --bc_imp_inh                            [conj_cone]
% 3.64/0.98  --conj_cone_tolerance                   3.
% 3.64/0.98  --extra_neg_conj                        none
% 3.64/0.98  --large_theory_mode                     true
% 3.64/0.98  --prolific_symb_bound                   200
% 3.64/0.98  --lt_threshold                          2000
% 3.64/0.98  --clause_weak_htbl                      true
% 3.64/0.98  --gc_record_bc_elim                     false
% 3.64/0.98  
% 3.64/0.98  ------ Preprocessing Options
% 3.64/0.98  
% 3.64/0.98  --preprocessing_flag                    true
% 3.64/0.98  --time_out_prep_mult                    0.1
% 3.64/0.98  --splitting_mode                        input
% 3.64/0.98  --splitting_grd                         true
% 3.64/0.98  --splitting_cvd                         false
% 3.64/0.98  --splitting_cvd_svl                     false
% 3.64/0.98  --splitting_nvd                         32
% 3.64/0.98  --sub_typing                            true
% 3.64/0.98  --prep_gs_sim                           true
% 3.64/0.98  --prep_unflatten                        true
% 3.64/0.98  --prep_res_sim                          true
% 3.64/0.98  --prep_upred                            true
% 3.64/0.98  --prep_sem_filter                       exhaustive
% 3.64/0.98  --prep_sem_filter_out                   false
% 3.64/0.98  --pred_elim                             true
% 3.64/0.98  --res_sim_input                         true
% 3.64/0.98  --eq_ax_congr_red                       true
% 3.64/0.98  --pure_diseq_elim                       true
% 3.64/0.98  --brand_transform                       false
% 3.64/0.98  --non_eq_to_eq                          false
% 3.64/0.98  --prep_def_merge                        true
% 3.64/0.98  --prep_def_merge_prop_impl              false
% 3.64/0.98  --prep_def_merge_mbd                    true
% 3.64/0.98  --prep_def_merge_tr_red                 false
% 3.64/0.98  --prep_def_merge_tr_cl                  false
% 3.64/0.98  --smt_preprocessing                     true
% 3.64/0.98  --smt_ac_axioms                         fast
% 3.64/0.98  --preprocessed_out                      false
% 3.64/0.98  --preprocessed_stats                    false
% 3.64/0.98  
% 3.64/0.98  ------ Abstraction refinement Options
% 3.64/0.98  
% 3.64/0.98  --abstr_ref                             []
% 3.64/0.98  --abstr_ref_prep                        false
% 3.64/0.98  --abstr_ref_until_sat                   false
% 3.64/0.98  --abstr_ref_sig_restrict                funpre
% 3.64/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.64/0.98  --abstr_ref_under                       []
% 3.64/0.98  
% 3.64/0.98  ------ SAT Options
% 3.64/0.98  
% 3.64/0.98  --sat_mode                              false
% 3.64/0.98  --sat_fm_restart_options                ""
% 3.64/0.98  --sat_gr_def                            false
% 3.64/0.98  --sat_epr_types                         true
% 3.64/0.98  --sat_non_cyclic_types                  false
% 3.64/0.98  --sat_finite_models                     false
% 3.64/0.98  --sat_fm_lemmas                         false
% 3.64/0.98  --sat_fm_prep                           false
% 3.64/0.98  --sat_fm_uc_incr                        true
% 3.64/0.98  --sat_out_model                         small
% 3.64/0.98  --sat_out_clauses                       false
% 3.64/0.98  
% 3.64/0.98  ------ QBF Options
% 3.64/0.98  
% 3.64/0.98  --qbf_mode                              false
% 3.64/0.98  --qbf_elim_univ                         false
% 3.64/0.98  --qbf_dom_inst                          none
% 3.64/0.98  --qbf_dom_pre_inst                      false
% 3.64/0.98  --qbf_sk_in                             false
% 3.64/0.98  --qbf_pred_elim                         true
% 3.64/0.98  --qbf_split                             512
% 3.64/0.98  
% 3.64/0.98  ------ BMC1 Options
% 3.64/0.98  
% 3.64/0.98  --bmc1_incremental                      false
% 3.64/0.98  --bmc1_axioms                           reachable_all
% 3.64/0.98  --bmc1_min_bound                        0
% 3.64/0.98  --bmc1_max_bound                        -1
% 3.64/0.98  --bmc1_max_bound_default                -1
% 3.64/0.98  --bmc1_symbol_reachability              true
% 3.64/0.98  --bmc1_property_lemmas                  false
% 3.64/0.98  --bmc1_k_induction                      false
% 3.64/0.98  --bmc1_non_equiv_states                 false
% 3.64/0.98  --bmc1_deadlock                         false
% 3.64/0.98  --bmc1_ucm                              false
% 3.64/0.98  --bmc1_add_unsat_core                   none
% 3.64/0.98  --bmc1_unsat_core_children              false
% 3.64/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.64/0.98  --bmc1_out_stat                         full
% 3.64/0.98  --bmc1_ground_init                      false
% 3.64/0.98  --bmc1_pre_inst_next_state              false
% 3.64/0.98  --bmc1_pre_inst_state                   false
% 3.64/0.98  --bmc1_pre_inst_reach_state             false
% 3.64/0.98  --bmc1_out_unsat_core                   false
% 3.64/0.98  --bmc1_aig_witness_out                  false
% 3.64/0.98  --bmc1_verbose                          false
% 3.64/0.98  --bmc1_dump_clauses_tptp                false
% 3.64/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.64/0.98  --bmc1_dump_file                        -
% 3.64/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.64/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.64/0.98  --bmc1_ucm_extend_mode                  1
% 3.64/0.98  --bmc1_ucm_init_mode                    2
% 3.64/0.98  --bmc1_ucm_cone_mode                    none
% 3.64/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.64/0.98  --bmc1_ucm_relax_model                  4
% 3.64/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.64/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.64/0.98  --bmc1_ucm_layered_model                none
% 3.64/0.98  --bmc1_ucm_max_lemma_size               10
% 3.64/0.98  
% 3.64/0.98  ------ AIG Options
% 3.64/0.98  
% 3.64/0.98  --aig_mode                              false
% 3.64/0.98  
% 3.64/0.98  ------ Instantiation Options
% 3.64/0.98  
% 3.64/0.98  --instantiation_flag                    true
% 3.64/0.98  --inst_sos_flag                         false
% 3.64/0.98  --inst_sos_phase                        true
% 3.64/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.64/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.64/0.98  --inst_lit_sel_side                     none
% 3.64/0.98  --inst_solver_per_active                1400
% 3.64/0.98  --inst_solver_calls_frac                1.
% 3.64/0.98  --inst_passive_queue_type               priority_queues
% 3.64/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.64/0.98  --inst_passive_queues_freq              [25;2]
% 3.64/0.98  --inst_dismatching                      true
% 3.64/0.98  --inst_eager_unprocessed_to_passive     true
% 3.64/0.98  --inst_prop_sim_given                   true
% 3.64/0.98  --inst_prop_sim_new                     false
% 3.64/0.98  --inst_subs_new                         false
% 3.64/0.98  --inst_eq_res_simp                      false
% 3.64/0.98  --inst_subs_given                       false
% 3.64/0.98  --inst_orphan_elimination               true
% 3.64/0.98  --inst_learning_loop_flag               true
% 3.64/0.98  --inst_learning_start                   3000
% 3.64/0.98  --inst_learning_factor                  2
% 3.64/0.98  --inst_start_prop_sim_after_learn       3
% 3.64/0.98  --inst_sel_renew                        solver
% 3.64/0.98  --inst_lit_activity_flag                true
% 3.64/0.98  --inst_restr_to_given                   false
% 3.64/0.98  --inst_activity_threshold               500
% 3.64/0.98  --inst_out_proof                        true
% 3.64/0.98  
% 3.64/0.98  ------ Resolution Options
% 3.64/0.98  
% 3.64/0.98  --resolution_flag                       false
% 3.64/0.98  --res_lit_sel                           adaptive
% 3.64/0.98  --res_lit_sel_side                      none
% 3.64/0.98  --res_ordering                          kbo
% 3.64/0.98  --res_to_prop_solver                    active
% 3.64/0.98  --res_prop_simpl_new                    false
% 3.64/0.98  --res_prop_simpl_given                  true
% 3.64/0.98  --res_passive_queue_type                priority_queues
% 3.64/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.64/0.98  --res_passive_queues_freq               [15;5]
% 3.64/0.98  --res_forward_subs                      full
% 3.64/0.98  --res_backward_subs                     full
% 3.64/0.98  --res_forward_subs_resolution           true
% 3.64/0.98  --res_backward_subs_resolution          true
% 3.64/0.98  --res_orphan_elimination                true
% 3.64/0.98  --res_time_limit                        2.
% 3.64/0.98  --res_out_proof                         true
% 3.64/0.98  
% 3.64/0.98  ------ Superposition Options
% 3.64/0.98  
% 3.64/0.98  --superposition_flag                    true
% 3.64/0.98  --sup_passive_queue_type                priority_queues
% 3.64/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.64/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.64/0.98  --demod_completeness_check              fast
% 3.64/0.98  --demod_use_ground                      true
% 3.64/0.98  --sup_to_prop_solver                    passive
% 3.64/0.98  --sup_prop_simpl_new                    true
% 3.64/0.98  --sup_prop_simpl_given                  true
% 3.64/0.98  --sup_fun_splitting                     false
% 3.64/0.98  --sup_smt_interval                      50000
% 3.64/0.98  
% 3.64/0.98  ------ Superposition Simplification Setup
% 3.64/0.98  
% 3.64/0.98  --sup_indices_passive                   []
% 3.64/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.64/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.64/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.64/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.64/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.64/0.98  --sup_full_bw                           [BwDemod]
% 3.64/0.98  --sup_immed_triv                        [TrivRules]
% 3.64/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.64/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.64/0.98  --sup_immed_bw_main                     []
% 3.64/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.64/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.64/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.64/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.64/0.98  
% 3.64/0.98  ------ Combination Options
% 3.64/0.98  
% 3.64/0.98  --comb_res_mult                         3
% 3.64/0.98  --comb_sup_mult                         2
% 3.64/0.98  --comb_inst_mult                        10
% 3.64/0.98  
% 3.64/0.98  ------ Debug Options
% 3.64/0.98  
% 3.64/0.98  --dbg_backtrace                         false
% 3.64/0.98  --dbg_dump_prop_clauses                 false
% 3.64/0.98  --dbg_dump_prop_clauses_file            -
% 3.64/0.98  --dbg_out_stat                          false
% 3.64/0.98  
% 3.64/0.98  
% 3.64/0.98  
% 3.64/0.98  
% 3.64/0.98  ------ Proving...
% 3.64/0.98  
% 3.64/0.98  
% 3.64/0.98  % SZS status Theorem for theBenchmark.p
% 3.64/0.98  
% 3.64/0.98   Resolution empty clause
% 3.64/0.98  
% 3.64/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.64/0.98  
% 3.64/0.98  fof(f7,axiom,(
% 3.64/0.98    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 3.64/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.98  
% 3.64/0.98  fof(f15,plain,(
% 3.64/0.98    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 3.64/0.98    inference(ennf_transformation,[],[f7])).
% 3.64/0.98  
% 3.64/0.98  fof(f34,plain,(
% 3.64/0.98    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK2(X0,X1) != X1 & r2_hidden(sK2(X0,X1),X0)))),
% 3.64/0.98    introduced(choice_axiom,[])).
% 3.64/0.98  
% 3.64/0.98  fof(f35,plain,(
% 3.64/0.98    ! [X0,X1] : ((sK2(X0,X1) != X1 & r2_hidden(sK2(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 3.64/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f34])).
% 3.64/0.98  
% 3.64/0.98  fof(f61,plain,(
% 3.64/0.98    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 3.64/0.98    inference(cnf_transformation,[],[f35])).
% 3.64/0.98  
% 3.64/0.98  fof(f4,axiom,(
% 3.64/0.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.64/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.98  
% 3.64/0.98  fof(f58,plain,(
% 3.64/0.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.64/0.98    inference(cnf_transformation,[],[f4])).
% 3.64/0.98  
% 3.64/0.98  fof(f5,axiom,(
% 3.64/0.98    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.64/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.98  
% 3.64/0.98  fof(f59,plain,(
% 3.64/0.98    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.64/0.98    inference(cnf_transformation,[],[f5])).
% 3.64/0.98  
% 3.64/0.98  fof(f6,axiom,(
% 3.64/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.64/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.98  
% 3.64/0.98  fof(f60,plain,(
% 3.64/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.64/0.98    inference(cnf_transformation,[],[f6])).
% 3.64/0.98  
% 3.64/0.98  fof(f75,plain,(
% 3.64/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.64/0.98    inference(definition_unfolding,[],[f59,f60])).
% 3.64/0.98  
% 3.64/0.98  fof(f76,plain,(
% 3.64/0.98    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.64/0.98    inference(definition_unfolding,[],[f58,f75])).
% 3.64/0.98  
% 3.64/0.98  fof(f86,plain,(
% 3.64/0.98    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | k1_xboole_0 = X0 | k2_enumset1(X1,X1,X1,X1) = X0) )),
% 3.64/0.98    inference(definition_unfolding,[],[f61,f76])).
% 3.64/0.98  
% 3.64/0.98  fof(f10,axiom,(
% 3.64/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 3.64/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.98  
% 3.64/0.98  fof(f18,plain,(
% 3.64/0.98    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 3.64/0.98    inference(ennf_transformation,[],[f10])).
% 3.64/0.98  
% 3.64/0.98  fof(f37,plain,(
% 3.64/0.98    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0))) & (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_relat_1(X2))),
% 3.64/0.98    inference(nnf_transformation,[],[f18])).
% 3.64/0.98  
% 3.64/0.98  fof(f67,plain,(
% 3.64/0.98    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0)) | ~v1_relat_1(X2)) )),
% 3.64/0.98    inference(cnf_transformation,[],[f37])).
% 3.64/0.98  
% 3.64/0.98  fof(f12,conjecture,(
% 3.64/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)))),
% 3.64/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.98  
% 3.64/0.98  fof(f13,negated_conjecture,(
% 3.64/0.98    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)))),
% 3.64/0.98    inference(negated_conjecture,[],[f12])).
% 3.64/0.98  
% 3.64/0.98  fof(f21,plain,(
% 3.64/0.98    ? [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) != k11_relat_1(X1,X0) & r2_hidden(X0,k1_relat_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 3.64/0.98    inference(ennf_transformation,[],[f13])).
% 3.64/0.98  
% 3.64/0.98  fof(f22,plain,(
% 3.64/0.98    ? [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) != k11_relat_1(X1,X0) & r2_hidden(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 3.64/0.98    inference(flattening,[],[f21])).
% 3.64/0.98  
% 3.64/0.98  fof(f40,plain,(
% 3.64/0.98    ? [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) != k11_relat_1(X1,X0) & r2_hidden(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(k1_funct_1(sK4,sK3)) != k11_relat_1(sK4,sK3) & r2_hidden(sK3,k1_relat_1(sK4)) & v1_funct_1(sK4) & v1_relat_1(sK4))),
% 3.64/0.98    introduced(choice_axiom,[])).
% 3.64/0.98  
% 3.64/0.98  fof(f41,plain,(
% 3.64/0.98    k1_tarski(k1_funct_1(sK4,sK3)) != k11_relat_1(sK4,sK3) & r2_hidden(sK3,k1_relat_1(sK4)) & v1_funct_1(sK4) & v1_relat_1(sK4)),
% 3.64/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f22,f40])).
% 3.64/0.98  
% 3.64/0.98  fof(f71,plain,(
% 3.64/0.98    v1_relat_1(sK4)),
% 3.64/0.98    inference(cnf_transformation,[],[f41])).
% 3.64/0.98  
% 3.64/0.98  fof(f11,axiom,(
% 3.64/0.98    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 3.64/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.98  
% 3.64/0.98  fof(f19,plain,(
% 3.64/0.98    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.64/0.98    inference(ennf_transformation,[],[f11])).
% 3.64/0.98  
% 3.64/0.98  fof(f20,plain,(
% 3.64/0.98    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.64/0.98    inference(flattening,[],[f19])).
% 3.64/0.98  
% 3.64/0.98  fof(f38,plain,(
% 3.64/0.98    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.64/0.98    inference(nnf_transformation,[],[f20])).
% 3.64/0.98  
% 3.64/0.98  fof(f39,plain,(
% 3.64/0.98    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.64/0.98    inference(flattening,[],[f38])).
% 3.64/0.98  
% 3.64/0.98  fof(f69,plain,(
% 3.64/0.98    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.64/0.98    inference(cnf_transformation,[],[f39])).
% 3.64/0.98  
% 3.64/0.98  fof(f72,plain,(
% 3.64/0.98    v1_funct_1(sK4)),
% 3.64/0.98    inference(cnf_transformation,[],[f41])).
% 3.64/0.98  
% 3.64/0.98  fof(f74,plain,(
% 3.64/0.98    k1_tarski(k1_funct_1(sK4,sK3)) != k11_relat_1(sK4,sK3)),
% 3.64/0.98    inference(cnf_transformation,[],[f41])).
% 3.64/0.98  
% 3.64/0.98  fof(f88,plain,(
% 3.64/0.98    k2_enumset1(k1_funct_1(sK4,sK3),k1_funct_1(sK4,sK3),k1_funct_1(sK4,sK3),k1_funct_1(sK4,sK3)) != k11_relat_1(sK4,sK3)),
% 3.64/0.98    inference(definition_unfolding,[],[f74,f76])).
% 3.64/0.98  
% 3.64/0.98  fof(f62,plain,(
% 3.64/0.98    ( ! [X0,X1] : (sK2(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 3.64/0.98    inference(cnf_transformation,[],[f35])).
% 3.64/0.98  
% 3.64/0.98  fof(f85,plain,(
% 3.64/0.98    ( ! [X0,X1] : (sK2(X0,X1) != X1 | k1_xboole_0 = X0 | k2_enumset1(X1,X1,X1,X1) = X0) )),
% 3.64/0.98    inference(definition_unfolding,[],[f62,f76])).
% 3.64/0.98  
% 3.64/0.98  fof(f70,plain,(
% 3.64/0.98    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.64/0.98    inference(cnf_transformation,[],[f39])).
% 3.64/0.98  
% 3.64/0.98  fof(f99,plain,(
% 3.64/0.98    ( ! [X2,X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.64/0.98    inference(equality_resolution,[],[f70])).
% 3.64/0.98  
% 3.64/0.98  fof(f66,plain,(
% 3.64/0.98    ( ! [X2,X0,X1] : (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 3.64/0.98    inference(cnf_transformation,[],[f37])).
% 3.64/0.98  
% 3.64/0.98  fof(f73,plain,(
% 3.64/0.98    r2_hidden(sK3,k1_relat_1(sK4))),
% 3.64/0.98    inference(cnf_transformation,[],[f41])).
% 3.64/0.98  
% 3.64/0.98  fof(f1,axiom,(
% 3.64/0.98    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.64/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.98  
% 3.64/0.98  fof(f23,plain,(
% 3.64/0.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.64/0.98    inference(nnf_transformation,[],[f1])).
% 3.64/0.98  
% 3.64/0.98  fof(f24,plain,(
% 3.64/0.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.64/0.98    inference(flattening,[],[f23])).
% 3.64/0.98  
% 3.64/0.98  fof(f25,plain,(
% 3.64/0.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.64/0.98    inference(rectify,[],[f24])).
% 3.64/0.98  
% 3.64/0.98  fof(f26,plain,(
% 3.64/0.98    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.64/0.98    introduced(choice_axiom,[])).
% 3.64/0.98  
% 3.64/0.98  fof(f27,plain,(
% 3.64/0.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.64/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).
% 3.64/0.98  
% 3.64/0.98  fof(f45,plain,(
% 3.64/0.98    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.64/0.98    inference(cnf_transformation,[],[f27])).
% 3.64/0.98  
% 3.64/0.98  fof(f46,plain,(
% 3.64/0.98    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.64/0.98    inference(cnf_transformation,[],[f27])).
% 3.64/0.98  
% 3.64/0.98  fof(f42,plain,(
% 3.64/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.64/0.98    inference(cnf_transformation,[],[f27])).
% 3.64/0.98  
% 3.64/0.98  fof(f91,plain,(
% 3.64/0.98    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 3.64/0.98    inference(equality_resolution,[],[f42])).
% 3.64/0.98  
% 3.64/0.98  fof(f43,plain,(
% 3.64/0.98    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.64/0.98    inference(cnf_transformation,[],[f27])).
% 3.64/0.98  
% 3.64/0.98  fof(f90,plain,(
% 3.64/0.98    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 3.64/0.98    inference(equality_resolution,[],[f43])).
% 3.64/0.98  
% 3.64/0.98  fof(f3,axiom,(
% 3.64/0.98    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 3.64/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.98  
% 3.64/0.98  fof(f14,plain,(
% 3.64/0.98    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 3.64/0.98    inference(ennf_transformation,[],[f3])).
% 3.64/0.98  
% 3.64/0.98  fof(f29,plain,(
% 3.64/0.98    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.64/0.98    inference(nnf_transformation,[],[f14])).
% 3.64/0.98  
% 3.64/0.98  fof(f30,plain,(
% 3.64/0.98    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.64/0.98    inference(flattening,[],[f29])).
% 3.64/0.98  
% 3.64/0.98  fof(f31,plain,(
% 3.64/0.98    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.64/0.98    inference(rectify,[],[f30])).
% 3.64/0.98  
% 3.64/0.98  fof(f32,plain,(
% 3.64/0.98    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3))))),
% 3.64/0.98    introduced(choice_axiom,[])).
% 3.64/0.98  
% 3.64/0.98  fof(f33,plain,(
% 3.64/0.98    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.64/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).
% 3.64/0.98  
% 3.64/0.98  fof(f51,plain,(
% 3.64/0.98    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.64/0.98    inference(cnf_transformation,[],[f33])).
% 3.64/0.98  
% 3.64/0.98  fof(f83,plain,(
% 3.64/0.98    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 3.64/0.98    inference(definition_unfolding,[],[f51,f60])).
% 3.64/0.98  
% 3.64/0.98  fof(f96,plain,(
% 3.64/0.98    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X5,X5,X1,X2) != X3) )),
% 3.64/0.98    inference(equality_resolution,[],[f83])).
% 3.64/0.98  
% 3.64/0.98  fof(f97,plain,(
% 3.64/0.98    ( ! [X2,X5,X1] : (r2_hidden(X5,k2_enumset1(X5,X5,X1,X2))) )),
% 3.64/0.98    inference(equality_resolution,[],[f96])).
% 3.64/0.98  
% 3.64/0.98  cnf(c_17,plain,
% 3.64/0.98      ( r2_hidden(sK2(X0,X1),X0)
% 3.64/0.98      | k2_enumset1(X1,X1,X1,X1) = X0
% 3.64/0.98      | k1_xboole_0 = X0 ),
% 3.64/0.98      inference(cnf_transformation,[],[f86]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_1248,plain,
% 3.64/0.98      ( k2_enumset1(X0,X0,X0,X0) = X1
% 3.64/0.98      | k1_xboole_0 = X1
% 3.64/0.98      | r2_hidden(sK2(X1,X0),X1) = iProver_top ),
% 3.64/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_21,plain,
% 3.64/0.98      ( ~ r2_hidden(X0,k11_relat_1(X1,X2))
% 3.64/0.98      | r2_hidden(k4_tarski(X2,X0),X1)
% 3.64/0.98      | ~ v1_relat_1(X1) ),
% 3.64/0.98      inference(cnf_transformation,[],[f67]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_29,negated_conjecture,
% 3.64/0.98      ( v1_relat_1(sK4) ),
% 3.64/0.98      inference(cnf_transformation,[],[f71]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_483,plain,
% 3.64/0.98      ( ~ r2_hidden(X0,k11_relat_1(X1,X2))
% 3.64/0.98      | r2_hidden(k4_tarski(X2,X0),X1)
% 3.64/0.98      | sK4 != X1 ),
% 3.64/0.98      inference(resolution_lifted,[status(thm)],[c_21,c_29]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_484,plain,
% 3.64/0.98      ( ~ r2_hidden(X0,k11_relat_1(sK4,X1)) | r2_hidden(k4_tarski(X1,X0),sK4) ),
% 3.64/0.98      inference(unflattening,[status(thm)],[c_483]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_602,plain,
% 3.64/0.98      ( r2_hidden(k4_tarski(X1,X0),sK4) | ~ r2_hidden(X0,k11_relat_1(sK4,X1)) ),
% 3.64/0.98      inference(prop_impl,[status(thm)],[c_484]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_603,plain,
% 3.64/0.98      ( ~ r2_hidden(X0,k11_relat_1(sK4,X1)) | r2_hidden(k4_tarski(X1,X0),sK4) ),
% 3.64/0.98      inference(renaming,[status(thm)],[c_602]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_1242,plain,
% 3.64/0.98      ( r2_hidden(X0,k11_relat_1(sK4,X1)) != iProver_top
% 3.64/0.98      | r2_hidden(k4_tarski(X1,X0),sK4) = iProver_top ),
% 3.64/0.98      inference(predicate_to_equality,[status(thm)],[c_603]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_2591,plain,
% 3.64/0.98      ( k2_enumset1(X0,X0,X0,X0) = k11_relat_1(sK4,X1)
% 3.64/0.98      | k11_relat_1(sK4,X1) = k1_xboole_0
% 3.64/0.98      | r2_hidden(k4_tarski(X1,sK2(k11_relat_1(sK4,X1),X0)),sK4) = iProver_top ),
% 3.64/0.98      inference(superposition,[status(thm)],[c_1248,c_1242]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_24,plain,
% 3.64/0.98      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.64/0.98      | ~ v1_funct_1(X2)
% 3.64/0.98      | ~ v1_relat_1(X2)
% 3.64/0.98      | k1_funct_1(X2,X0) = X1 ),
% 3.64/0.98      inference(cnf_transformation,[],[f69]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_28,negated_conjecture,
% 3.64/0.98      ( v1_funct_1(sK4) ),
% 3.64/0.98      inference(cnf_transformation,[],[f72]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_378,plain,
% 3.64/0.98      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.64/0.98      | ~ v1_relat_1(X2)
% 3.64/0.98      | k1_funct_1(X2,X0) = X1
% 3.64/0.98      | sK4 != X2 ),
% 3.64/0.98      inference(resolution_lifted,[status(thm)],[c_24,c_28]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_379,plain,
% 3.64/0.98      ( ~ r2_hidden(k4_tarski(X0,X1),sK4)
% 3.64/0.98      | ~ v1_relat_1(sK4)
% 3.64/0.98      | k1_funct_1(sK4,X0) = X1 ),
% 3.64/0.98      inference(unflattening,[status(thm)],[c_378]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_383,plain,
% 3.64/0.98      ( ~ r2_hidden(k4_tarski(X0,X1),sK4) | k1_funct_1(sK4,X0) = X1 ),
% 3.64/0.98      inference(global_propositional_subsumption,[status(thm)],[c_379,c_29]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_1246,plain,
% 3.64/0.98      ( k1_funct_1(sK4,X0) = X1
% 3.64/0.98      | r2_hidden(k4_tarski(X0,X1),sK4) != iProver_top ),
% 3.64/0.98      inference(predicate_to_equality,[status(thm)],[c_383]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_8178,plain,
% 3.64/0.98      ( k2_enumset1(X0,X0,X0,X0) = k11_relat_1(sK4,X1)
% 3.64/0.98      | k11_relat_1(sK4,X1) = k1_xboole_0
% 3.64/0.98      | sK2(k11_relat_1(sK4,X1),X0) = k1_funct_1(sK4,X1) ),
% 3.64/0.98      inference(superposition,[status(thm)],[c_2591,c_1246]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_26,negated_conjecture,
% 3.64/0.98      ( k2_enumset1(k1_funct_1(sK4,sK3),k1_funct_1(sK4,sK3),k1_funct_1(sK4,sK3),k1_funct_1(sK4,sK3)) != k11_relat_1(sK4,sK3) ),
% 3.64/0.98      inference(cnf_transformation,[],[f88]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_8726,plain,
% 3.64/0.98      ( k11_relat_1(sK4,X0) != k11_relat_1(sK4,sK3)
% 3.64/0.98      | k11_relat_1(sK4,X0) = k1_xboole_0
% 3.64/0.98      | sK2(k11_relat_1(sK4,X0),k1_funct_1(sK4,sK3)) = k1_funct_1(sK4,X0) ),
% 3.64/0.98      inference(superposition,[status(thm)],[c_8178,c_26]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_9116,plain,
% 3.64/0.98      ( k11_relat_1(sK4,sK3) = k1_xboole_0
% 3.64/0.98      | sK2(k11_relat_1(sK4,sK3),k1_funct_1(sK4,sK3)) = k1_funct_1(sK4,sK3) ),
% 3.64/0.98      inference(equality_resolution,[status(thm)],[c_8726]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_16,plain,
% 3.64/0.98      ( k2_enumset1(X0,X0,X0,X0) = X1 | sK2(X1,X0) != X0 | k1_xboole_0 = X1 ),
% 3.64/0.98      inference(cnf_transformation,[],[f85]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_1500,plain,
% 3.64/0.98      ( k2_enumset1(k1_funct_1(sK4,sK3),k1_funct_1(sK4,sK3),k1_funct_1(sK4,sK3),k1_funct_1(sK4,sK3)) = k11_relat_1(sK4,sK3)
% 3.64/0.98      | sK2(k11_relat_1(sK4,sK3),k1_funct_1(sK4,sK3)) != k1_funct_1(sK4,sK3)
% 3.64/0.98      | k1_xboole_0 = k11_relat_1(sK4,sK3) ),
% 3.64/0.98      inference(instantiation,[status(thm)],[c_16]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_740,plain,( X0 = X0 ),theory(equality) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_1787,plain,
% 3.64/0.98      ( k11_relat_1(sK4,sK3) = k11_relat_1(sK4,sK3) ),
% 3.64/0.98      inference(instantiation,[status(thm)],[c_740]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_741,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_1568,plain,
% 3.64/0.98      ( X0 != X1 | k11_relat_1(sK4,sK3) != X1 | k11_relat_1(sK4,sK3) = X0 ),
% 3.64/0.98      inference(instantiation,[status(thm)],[c_741]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_1786,plain,
% 3.64/0.98      ( X0 != k11_relat_1(sK4,sK3)
% 3.64/0.98      | k11_relat_1(sK4,sK3) = X0
% 3.64/0.98      | k11_relat_1(sK4,sK3) != k11_relat_1(sK4,sK3) ),
% 3.64/0.98      inference(instantiation,[status(thm)],[c_1568]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_2771,plain,
% 3.64/0.98      ( k11_relat_1(sK4,sK3) != k11_relat_1(sK4,sK3)
% 3.64/0.98      | k11_relat_1(sK4,sK3) = k1_xboole_0
% 3.64/0.98      | k1_xboole_0 != k11_relat_1(sK4,sK3) ),
% 3.64/0.98      inference(instantiation,[status(thm)],[c_1786]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_9134,plain,
% 3.64/0.98      ( k11_relat_1(sK4,sK3) = k1_xboole_0 ),
% 3.64/0.98      inference(global_propositional_subsumption,
% 3.64/0.98                [status(thm)],
% 3.64/0.98                [c_9116,c_26,c_1500,c_1787,c_2771]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_23,plain,
% 3.64/0.98      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.64/0.98      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 3.64/0.98      | ~ v1_funct_1(X1)
% 3.64/0.98      | ~ v1_relat_1(X1) ),
% 3.64/0.98      inference(cnf_transformation,[],[f99]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_414,plain,
% 3.64/0.98      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.64/0.98      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 3.64/0.98      | ~ v1_relat_1(X1)
% 3.64/0.98      | sK4 != X1 ),
% 3.64/0.98      inference(resolution_lifted,[status(thm)],[c_23,c_28]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_415,plain,
% 3.64/0.98      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 3.64/0.98      | r2_hidden(k4_tarski(X0,k1_funct_1(sK4,X0)),sK4)
% 3.64/0.98      | ~ v1_relat_1(sK4) ),
% 3.64/0.98      inference(unflattening,[status(thm)],[c_414]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_419,plain,
% 3.64/0.98      ( r2_hidden(k4_tarski(X0,k1_funct_1(sK4,X0)),sK4)
% 3.64/0.98      | ~ r2_hidden(X0,k1_relat_1(sK4)) ),
% 3.64/0.98      inference(global_propositional_subsumption,[status(thm)],[c_415,c_29]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_420,plain,
% 3.64/0.98      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 3.64/0.98      | r2_hidden(k4_tarski(X0,k1_funct_1(sK4,X0)),sK4) ),
% 3.64/0.98      inference(renaming,[status(thm)],[c_419]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_1244,plain,
% 3.64/0.98      ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 3.64/0.98      | r2_hidden(k4_tarski(X0,k1_funct_1(sK4,X0)),sK4) = iProver_top ),
% 3.64/0.98      inference(predicate_to_equality,[status(thm)],[c_420]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_22,plain,
% 3.64/0.98      ( r2_hidden(X0,k11_relat_1(X1,X2))
% 3.64/0.98      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 3.64/0.98      | ~ v1_relat_1(X1) ),
% 3.64/0.98      inference(cnf_transformation,[],[f66]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_471,plain,
% 3.64/0.98      ( r2_hidden(X0,k11_relat_1(X1,X2))
% 3.64/0.98      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 3.64/0.98      | sK4 != X1 ),
% 3.64/0.98      inference(resolution_lifted,[status(thm)],[c_22,c_29]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_472,plain,
% 3.64/0.98      ( r2_hidden(X0,k11_relat_1(sK4,X1)) | ~ r2_hidden(k4_tarski(X1,X0),sK4) ),
% 3.64/0.98      inference(unflattening,[status(thm)],[c_471]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_604,plain,
% 3.64/0.98      ( ~ r2_hidden(k4_tarski(X1,X0),sK4) | r2_hidden(X0,k11_relat_1(sK4,X1)) ),
% 3.64/0.98      inference(prop_impl,[status(thm)],[c_472]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_605,plain,
% 3.64/0.98      ( r2_hidden(X0,k11_relat_1(sK4,X1)) | ~ r2_hidden(k4_tarski(X1,X0),sK4) ),
% 3.64/0.98      inference(renaming,[status(thm)],[c_604]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_1243,plain,
% 3.64/0.98      ( r2_hidden(X0,k11_relat_1(sK4,X1)) = iProver_top
% 3.64/0.98      | r2_hidden(k4_tarski(X1,X0),sK4) != iProver_top ),
% 3.64/0.98      inference(predicate_to_equality,[status(thm)],[c_605]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_2214,plain,
% 3.64/0.98      ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 3.64/0.98      | r2_hidden(k1_funct_1(sK4,X0),k11_relat_1(sK4,X0)) = iProver_top ),
% 3.64/0.98      inference(superposition,[status(thm)],[c_1244,c_1243]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_9150,plain,
% 3.64/0.98      ( r2_hidden(k1_funct_1(sK4,sK3),k1_xboole_0) = iProver_top
% 3.64/0.98      | r2_hidden(sK3,k1_relat_1(sK4)) != iProver_top ),
% 3.64/0.98      inference(superposition,[status(thm)],[c_9134,c_2214]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_27,negated_conjecture,
% 3.64/0.98      ( r2_hidden(sK3,k1_relat_1(sK4)) ),
% 3.64/0.98      inference(cnf_transformation,[],[f73]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_32,plain,
% 3.64/0.98      ( r2_hidden(sK3,k1_relat_1(sK4)) = iProver_top ),
% 3.64/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_12937,plain,
% 3.64/0.98      ( r2_hidden(k1_funct_1(sK4,sK3),k1_xboole_0) = iProver_top ),
% 3.64/0.98      inference(global_propositional_subsumption,[status(thm)],[c_9150,c_32]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_2,plain,
% 3.64/0.98      ( r2_hidden(sK0(X0,X1,X2),X0)
% 3.64/0.98      | r2_hidden(sK0(X0,X1,X2),X2)
% 3.64/0.98      | k4_xboole_0(X0,X1) = X2 ),
% 3.64/0.98      inference(cnf_transformation,[],[f45]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_1260,plain,
% 3.64/0.98      ( k4_xboole_0(X0,X1) = X2
% 3.64/0.98      | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
% 3.64/0.98      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 3.64/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_1,plain,
% 3.64/0.98      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 3.64/0.98      | r2_hidden(sK0(X0,X1,X2),X2)
% 3.64/0.98      | k4_xboole_0(X0,X1) = X2 ),
% 3.64/0.98      inference(cnf_transformation,[],[f46]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_1261,plain,
% 3.64/0.98      ( k4_xboole_0(X0,X1) = X2
% 3.64/0.98      | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top
% 3.64/0.98      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 3.64/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_2927,plain,
% 3.64/0.98      ( k4_xboole_0(X0,X0) = X1 | r2_hidden(sK0(X0,X0,X1),X1) = iProver_top ),
% 3.64/0.98      inference(superposition,[status(thm)],[c_1260,c_1261]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_5,plain,
% 3.64/0.98      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 3.64/0.98      inference(cnf_transformation,[],[f91]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_1257,plain,
% 3.64/0.98      ( r2_hidden(X0,X1) = iProver_top
% 3.64/0.98      | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
% 3.64/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_3376,plain,
% 3.64/0.98      ( k4_xboole_0(X0,X0) = k4_xboole_0(X1,X2)
% 3.64/0.98      | r2_hidden(sK0(X0,X0,k4_xboole_0(X1,X2)),X1) = iProver_top ),
% 3.64/0.98      inference(superposition,[status(thm)],[c_2927,c_1257]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_4,plain,
% 3.64/0.98      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 3.64/0.98      inference(cnf_transformation,[],[f90]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_1258,plain,
% 3.64/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.64/0.98      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 3.64/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_3377,plain,
% 3.64/0.98      ( k4_xboole_0(X0,X0) = k4_xboole_0(X1,X2)
% 3.64/0.98      | r2_hidden(sK0(X0,X0,k4_xboole_0(X1,X2)),X2) != iProver_top ),
% 3.64/0.98      inference(superposition,[status(thm)],[c_2927,c_1258]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_3487,plain,
% 3.64/0.98      ( k4_xboole_0(X0,X0) = k4_xboole_0(X1,X1) ),
% 3.64/0.98      inference(superposition,[status(thm)],[c_3376,c_3377]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_3542,plain,
% 3.64/0.98      ( r2_hidden(X0,X1) = iProver_top
% 3.64/0.98      | r2_hidden(X0,k4_xboole_0(X2,X2)) != iProver_top ),
% 3.64/0.98      inference(superposition,[status(thm)],[c_3487,c_1257]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_3543,plain,
% 3.64/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.64/0.98      | r2_hidden(X0,k4_xboole_0(X2,X2)) != iProver_top ),
% 3.64/0.98      inference(superposition,[status(thm)],[c_3487,c_1258]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_3557,plain,
% 3.64/0.98      ( r2_hidden(X0,k4_xboole_0(X1,X1)) != iProver_top ),
% 3.64/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_3542,c_3543]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_3738,plain,
% 3.64/0.98      ( k2_enumset1(X0,X0,X0,X0) = k4_xboole_0(X1,X1)
% 3.64/0.98      | k4_xboole_0(X1,X1) = k1_xboole_0 ),
% 3.64/0.98      inference(superposition,[status(thm)],[c_1248,c_3557]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_4327,plain,
% 3.64/0.98      ( k4_xboole_0(X0,X0) != k11_relat_1(sK4,sK3)
% 3.64/0.98      | k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.64/0.98      inference(superposition,[status(thm)],[c_3738,c_26]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_4456,plain,
% 3.64/0.98      ( k4_xboole_0(X0,X0) != k11_relat_1(sK4,sK3)
% 3.64/0.98      | k4_xboole_0(X1,X1) = k1_xboole_0 ),
% 3.64/0.98      inference(superposition,[status(thm)],[c_3487,c_4327]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_3565,plain,
% 3.64/0.98      ( ~ r2_hidden(X0,k4_xboole_0(X1,X1)) ),
% 3.64/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_3557]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_14,plain,
% 3.64/0.98      ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
% 3.64/0.98      inference(cnf_transformation,[],[f97]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_1250,plain,
% 3.64/0.98      ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) = iProver_top ),
% 3.64/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_4321,plain,
% 3.64/0.98      ( k4_xboole_0(X0,X0) = k1_xboole_0
% 3.64/0.98      | r2_hidden(X1,k4_xboole_0(X0,X0)) = iProver_top ),
% 3.64/0.98      inference(superposition,[status(thm)],[c_3738,c_1250]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_4443,plain,
% 3.64/0.98      ( r2_hidden(X0,k4_xboole_0(X1,X1)) | k4_xboole_0(X1,X1) = k1_xboole_0 ),
% 3.64/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_4321]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_4511,plain,
% 3.64/0.98      ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
% 3.64/0.98      inference(global_propositional_subsumption,
% 3.64/0.98                [status(thm)],
% 3.64/0.98                [c_4456,c_3565,c_4443]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_4512,plain,
% 3.64/0.98      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.64/0.98      inference(renaming,[status(thm)],[c_4511]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_4522,plain,
% 3.64/0.98      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.64/0.98      inference(demodulation,[status(thm)],[c_4512,c_3557]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_12942,plain,
% 3.64/0.98      ( $false ),
% 3.64/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_12937,c_4522]) ).
% 3.64/0.98  
% 3.64/0.98  
% 3.64/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.64/0.98  
% 3.64/0.98  ------                               Statistics
% 3.64/0.98  
% 3.64/0.98  ------ General
% 3.64/0.98  
% 3.64/0.98  abstr_ref_over_cycles:                  0
% 3.64/0.98  abstr_ref_under_cycles:                 0
% 3.64/0.98  gc_basic_clause_elim:                   0
% 3.64/0.98  forced_gc_time:                         0
% 3.64/0.98  parsing_time:                           0.009
% 3.64/0.98  unif_index_cands_time:                  0.
% 3.64/0.98  unif_index_add_time:                    0.
% 3.64/0.98  orderings_time:                         0.
% 3.64/0.98  out_proof_time:                         0.008
% 3.64/0.98  total_time:                             0.368
% 3.64/0.98  num_of_symbols:                         48
% 3.64/0.98  num_of_terms:                           15039
% 3.64/0.98  
% 3.64/0.98  ------ Preprocessing
% 3.64/0.98  
% 3.64/0.98  num_of_splits:                          0
% 3.64/0.98  num_of_split_atoms:                     0
% 3.64/0.98  num_of_reused_defs:                     0
% 3.64/0.98  num_eq_ax_congr_red:                    36
% 3.64/0.98  num_of_sem_filtered_clauses:            1
% 3.64/0.98  num_of_subtypes:                        0
% 3.64/0.98  monotx_restored_types:                  0
% 3.64/0.98  sat_num_of_epr_types:                   0
% 3.64/0.98  sat_num_of_non_cyclic_types:            0
% 3.64/0.98  sat_guarded_non_collapsed_types:        0
% 3.64/0.98  num_pure_diseq_elim:                    0
% 3.64/0.98  simp_replaced_by:                       0
% 3.64/0.98  res_preprocessed:                       129
% 3.64/0.98  prep_upred:                             0
% 3.64/0.98  prep_unflattend:                        12
% 3.64/0.98  smt_new_axioms:                         0
% 3.64/0.98  pred_elim_cands:                        1
% 3.64/0.98  pred_elim:                              3
% 3.64/0.98  pred_elim_cl:                           4
% 3.64/0.98  pred_elim_cycles:                       5
% 3.64/0.98  merged_defs:                            14
% 3.64/0.98  merged_defs_ncl:                        0
% 3.64/0.98  bin_hyper_res:                          14
% 3.64/0.98  prep_cycles:                            4
% 3.64/0.98  pred_elim_time:                         0.003
% 3.64/0.98  splitting_time:                         0.
% 3.64/0.98  sem_filter_time:                        0.
% 3.64/0.98  monotx_time:                            0.
% 3.64/0.98  subtype_inf_time:                       0.
% 3.64/0.98  
% 3.64/0.98  ------ Problem properties
% 3.64/0.98  
% 3.64/0.98  clauses:                                26
% 3.64/0.98  conjectures:                            2
% 3.64/0.98  epr:                                    0
% 3.64/0.98  horn:                                   18
% 3.64/0.98  ground:                                 2
% 3.64/0.98  unary:                                  6
% 3.64/0.98  binary:                                 9
% 3.64/0.98  lits:                                   61
% 3.64/0.98  lits_eq:                                28
% 3.64/0.98  fd_pure:                                0
% 3.64/0.98  fd_pseudo:                              0
% 3.64/0.98  fd_cond:                                0
% 3.64/0.98  fd_pseudo_cond:                         10
% 3.64/0.98  ac_symbols:                             0
% 3.64/0.98  
% 3.64/0.98  ------ Propositional Solver
% 3.64/0.98  
% 3.64/0.98  prop_solver_calls:                      27
% 3.64/0.98  prop_fast_solver_calls:                 917
% 3.64/0.98  smt_solver_calls:                       0
% 3.64/0.98  smt_fast_solver_calls:                  0
% 3.64/0.98  prop_num_of_clauses:                    4051
% 3.64/0.98  prop_preprocess_simplified:             9690
% 3.64/0.98  prop_fo_subsumed:                       10
% 3.64/0.98  prop_solver_time:                       0.
% 3.64/0.98  smt_solver_time:                        0.
% 3.64/0.98  smt_fast_solver_time:                   0.
% 3.64/0.98  prop_fast_solver_time:                  0.
% 3.64/0.98  prop_unsat_core_time:                   0.
% 3.64/0.98  
% 3.64/0.98  ------ QBF
% 3.64/0.98  
% 3.64/0.98  qbf_q_res:                              0
% 3.64/0.98  qbf_num_tautologies:                    0
% 3.64/0.98  qbf_prep_cycles:                        0
% 3.64/0.98  
% 3.64/0.98  ------ BMC1
% 3.64/0.98  
% 3.64/0.98  bmc1_current_bound:                     -1
% 3.64/0.98  bmc1_last_solved_bound:                 -1
% 3.64/0.98  bmc1_unsat_core_size:                   -1
% 3.64/0.98  bmc1_unsat_core_parents_size:           -1
% 3.64/0.98  bmc1_merge_next_fun:                    0
% 3.64/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.64/0.98  
% 3.64/0.98  ------ Instantiation
% 3.64/0.98  
% 3.64/0.98  inst_num_of_clauses:                    996
% 3.64/0.98  inst_num_in_passive:                    296
% 3.64/0.98  inst_num_in_active:                     324
% 3.64/0.98  inst_num_in_unprocessed:                376
% 3.64/0.98  inst_num_of_loops:                      460
% 3.64/0.98  inst_num_of_learning_restarts:          0
% 3.64/0.98  inst_num_moves_active_passive:          135
% 3.64/0.98  inst_lit_activity:                      0
% 3.64/0.98  inst_lit_activity_moves:                0
% 3.64/0.98  inst_num_tautologies:                   0
% 3.64/0.98  inst_num_prop_implied:                  0
% 3.64/0.98  inst_num_existing_simplified:           0
% 3.64/0.98  inst_num_eq_res_simplified:             0
% 3.64/0.98  inst_num_child_elim:                    0
% 3.64/0.98  inst_num_of_dismatching_blockings:      909
% 3.64/0.98  inst_num_of_non_proper_insts:           950
% 3.64/0.98  inst_num_of_duplicates:                 0
% 3.64/0.98  inst_inst_num_from_inst_to_res:         0
% 3.64/0.98  inst_dismatching_checking_time:         0.
% 3.64/0.98  
% 3.64/0.98  ------ Resolution
% 3.64/0.98  
% 3.64/0.98  res_num_of_clauses:                     0
% 3.64/0.98  res_num_in_passive:                     0
% 3.64/0.98  res_num_in_active:                      0
% 3.64/0.98  res_num_of_loops:                       133
% 3.64/0.98  res_forward_subset_subsumed:            146
% 3.64/0.98  res_backward_subset_subsumed:           2
% 3.64/0.98  res_forward_subsumed:                   0
% 3.64/0.98  res_backward_subsumed:                  0
% 3.64/0.98  res_forward_subsumption_resolution:     0
% 3.64/0.98  res_backward_subsumption_resolution:    0
% 3.64/0.98  res_clause_to_clause_subsumption:       4469
% 3.64/0.98  res_orphan_elimination:                 0
% 3.64/0.98  res_tautology_del:                      55
% 3.64/0.98  res_num_eq_res_simplified:              0
% 3.64/0.98  res_num_sel_changes:                    0
% 3.64/0.98  res_moves_from_active_to_pass:          0
% 3.64/0.98  
% 3.64/0.98  ------ Superposition
% 3.64/0.98  
% 3.64/0.98  sup_time_total:                         0.
% 3.64/0.98  sup_time_generating:                    0.
% 3.64/0.98  sup_time_sim_full:                      0.
% 3.64/0.98  sup_time_sim_immed:                     0.
% 3.64/0.98  
% 3.64/0.98  sup_num_of_clauses:                     351
% 3.64/0.98  sup_num_in_active:                      79
% 3.64/0.98  sup_num_in_passive:                     272
% 3.64/0.98  sup_num_of_loops:                       91
% 3.64/0.98  sup_fw_superposition:                   360
% 3.64/0.98  sup_bw_superposition:                   550
% 3.64/0.98  sup_immediate_simplified:               304
% 3.64/0.98  sup_given_eliminated:                   2
% 3.64/0.98  comparisons_done:                       0
% 3.64/0.98  comparisons_avoided:                    74
% 3.64/0.98  
% 3.64/0.98  ------ Simplifications
% 3.64/0.98  
% 3.64/0.98  
% 3.64/0.98  sim_fw_subset_subsumed:                 64
% 3.64/0.98  sim_bw_subset_subsumed:                 3
% 3.64/0.98  sim_fw_subsumed:                        144
% 3.64/0.98  sim_bw_subsumed:                        7
% 3.64/0.98  sim_fw_subsumption_res:                 8
% 3.64/0.98  sim_bw_subsumption_res:                 0
% 3.64/0.98  sim_tautology_del:                      26
% 3.64/0.98  sim_eq_tautology_del:                   68
% 3.64/0.98  sim_eq_res_simp:                        1
% 3.64/0.98  sim_fw_demodulated:                     66
% 3.64/0.98  sim_bw_demodulated:                     10
% 3.64/0.98  sim_light_normalised:                   54
% 3.64/0.98  sim_joinable_taut:                      0
% 3.64/0.98  sim_joinable_simp:                      0
% 3.64/0.98  sim_ac_normalised:                      0
% 3.64/0.98  sim_smt_subsumption:                    0
% 3.64/0.98  
%------------------------------------------------------------------------------
