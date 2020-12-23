%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:49:53 EST 2020

% Result     : Theorem 7.97s
% Output     : CNFRefutation 7.97s
% Verified   : 
% Statistics : Number of formulae       :  150 (2494 expanded)
%              Number of clauses        :  100 ( 822 expanded)
%              Number of leaves         :   13 ( 431 expanded)
%              Depth                    :   38
%              Number of atoms          :  556 (14471 expanded)
%              Number of equality atoms :  279 (3613 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
       => k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
         => k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)
      & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)
      & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f32,plain,
    ( ? [X0,X1,X2] :
        ( k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)
        & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k1_funct_1(sK3,sK1) != k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1)
      & r2_hidden(sK1,k3_xboole_0(k1_relat_1(sK3),sK2))
      & v1_funct_1(sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( k1_funct_1(sK3,sK1) != k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1)
    & r2_hidden(sK1,k3_xboole_0(k1_relat_1(sK3),sK2))
    & v1_funct_1(sK3)
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f21,f32])).

fof(f58,plain,(
    r2_hidden(sK1,k3_xboole_0(k1_relat_1(sK3),sK2)) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f22])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).

fof(f35,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f61,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f60,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f34,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f62,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f66,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f55])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f56,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f57,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X0,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X0,X2) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
          | ~ r2_hidden(k4_tarski(X0,X1),X3)
          | ~ r2_hidden(X0,X2) )
        & ( ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X0,X2) )
          | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
          | ~ r2_hidden(k4_tarski(X0,X1),X3)
          | ~ r2_hidden(X0,X2) )
        & ( ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X0,X2) )
          | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(flattening,[],[f27])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      | ~ r2_hidden(k4_tarski(X0,X1),X3)
      | ~ r2_hidden(X0,X2)
      | ~ v1_relat_1(X3) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      | ~ v1_relat_1(X3) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f52,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f59,plain,(
    k1_funct_1(sK3,sK1) != k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_23,negated_conjecture,
    ( r2_hidden(sK1,k3_xboole_0(k1_relat_1(sK3),sK2)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_743,plain,
    ( r2_hidden(sK1,k3_xboole_0(k1_relat_1(sK3),sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_757,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1472,plain,
    ( r2_hidden(sK1,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_743,c_757])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_758,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X0,k3_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_755,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_15,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | v1_funct_1(k5_relat_1(X0,X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_748,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(k5_relat_1(X1,X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_756,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1359,plain,
    ( r2_hidden(sK1,k1_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_743,c_756])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_749,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_21,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_744,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1708,plain,
    ( r2_hidden(X0,k1_relat_1(k3_xboole_0(X1,X2))) = iProver_top
    | r2_hidden(k4_tarski(X0,X3),X2) != iProver_top
    | r2_hidden(k4_tarski(X0,X3),X1) != iProver_top
    | v1_funct_1(k3_xboole_0(X1,X2)) != iProver_top
    | v1_relat_1(k3_xboole_0(X1,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_758,c_744])).

cnf(c_2705,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(X0,k1_relat_1(k3_xboole_0(X2,X1))) = iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X2) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(k3_xboole_0(X2,X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k3_xboole_0(X2,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_749,c_1708])).

cnf(c_9260,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(X0,k1_relat_1(k3_xboole_0(X1,X1))) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(k3_xboole_0(X1,X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k3_xboole_0(X1,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_749,c_2705])).

cnf(c_2031,plain,
    ( r2_hidden(X0,k1_relat_1(k3_xboole_0(X1,X2))) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(k3_xboole_0(X1,X2),X0)),X1) = iProver_top
    | v1_funct_1(k3_xboole_0(X1,X2)) != iProver_top
    | v1_relat_1(k3_xboole_0(X1,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_749,c_756])).

cnf(c_20,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_745,plain,
    ( k1_funct_1(X0,X1) = X2
    | r2_hidden(k4_tarski(X1,X2),X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2572,plain,
    ( k1_funct_1(k3_xboole_0(X0,X1),X2) = k1_funct_1(X0,X2)
    | r2_hidden(X2,k1_relat_1(k3_xboole_0(X0,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k3_xboole_0(X0,X1)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k3_xboole_0(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2031,c_745])).

cnf(c_9390,plain,
    ( k1_funct_1(k3_xboole_0(X0,X0),X1) = k1_funct_1(X0,X1)
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k3_xboole_0(X0,X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k3_xboole_0(X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9260,c_2572])).

cnf(c_9442,plain,
    ( k1_funct_1(k3_xboole_0(sK3,sK3),sK1) = k1_funct_1(sK3,sK1)
    | v1_funct_1(k3_xboole_0(sK3,sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k3_xboole_0(sK3,sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1359,c_9390])).

cnf(c_25,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_26,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_27,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_79,plain,
    ( r2_hidden(sK0(sK3,sK3,sK3),sK3)
    | k3_xboole_0(sK3,sK3) = sK3 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_83,plain,
    ( ~ r2_hidden(sK0(sK3,sK3,sK3),sK3)
    | k3_xboole_0(sK3,sK3) = sK3 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_408,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1353,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k3_xboole_0(X1,sK3))
    | k3_xboole_0(X1,sK3) != X0 ),
    inference(instantiation,[status(thm)],[c_408])).

cnf(c_1354,plain,
    ( k3_xboole_0(X0,sK3) != X1
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k3_xboole_0(X0,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1353])).

cnf(c_1356,plain,
    ( k3_xboole_0(sK3,sK3) != sK3
    | v1_relat_1(k3_xboole_0(sK3,sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1354])).

cnf(c_413,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_4219,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k3_xboole_0(X1,sK3))
    | k3_xboole_0(X1,sK3) != X0 ),
    inference(instantiation,[status(thm)],[c_413])).

cnf(c_4220,plain,
    ( k3_xboole_0(X0,sK3) != X1
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(k3_xboole_0(X0,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4219])).

cnf(c_4222,plain,
    ( k3_xboole_0(sK3,sK3) != sK3
    | v1_funct_1(k3_xboole_0(sK3,sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4220])).

cnf(c_10425,plain,
    ( v1_relat_1(k3_xboole_0(sK3,sK3)) != iProver_top
    | k1_funct_1(k3_xboole_0(sK3,sK3),sK1) = k1_funct_1(sK3,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9442,c_26,c_27,c_79,c_83,c_1356,c_4222])).

cnf(c_10426,plain,
    ( k1_funct_1(k3_xboole_0(sK3,sK3),sK1) = k1_funct_1(sK3,sK1)
    | v1_relat_1(k3_xboole_0(sK3,sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_10425])).

cnf(c_10429,plain,
    ( k1_funct_1(k3_xboole_0(sK3,sK3),sK1) = k1_funct_1(sK3,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10426,c_26,c_27,c_79,c_83,c_1356,c_4222,c_9442])).

cnf(c_10432,plain,
    ( r2_hidden(k4_tarski(sK1,k1_funct_1(sK3,sK1)),k3_xboole_0(sK3,sK3)) = iProver_top
    | r2_hidden(sK1,k1_relat_1(k3_xboole_0(sK3,sK3))) != iProver_top
    | v1_funct_1(k3_xboole_0(sK3,sK3)) != iProver_top
    | v1_relat_1(k3_xboole_0(sK3,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10429,c_749])).

cnf(c_1266,plain,
    ( ~ r2_hidden(k4_tarski(sK1,X0),X1)
    | r2_hidden(k4_tarski(sK1,X0),k3_xboole_0(X1,sK3))
    | ~ r2_hidden(k4_tarski(sK1,X0),sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2436,plain,
    ( ~ r2_hidden(k4_tarski(sK1,k1_funct_1(sK3,sK1)),X0)
    | r2_hidden(k4_tarski(sK1,k1_funct_1(sK3,sK1)),k3_xboole_0(X0,sK3))
    | ~ r2_hidden(k4_tarski(sK1,k1_funct_1(sK3,sK1)),sK3) ),
    inference(instantiation,[status(thm)],[c_1266])).

cnf(c_2437,plain,
    ( r2_hidden(k4_tarski(sK1,k1_funct_1(sK3,sK1)),X0) != iProver_top
    | r2_hidden(k4_tarski(sK1,k1_funct_1(sK3,sK1)),k3_xboole_0(X0,sK3)) = iProver_top
    | r2_hidden(k4_tarski(sK1,k1_funct_1(sK3,sK1)),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2436])).

cnf(c_2439,plain,
    ( r2_hidden(k4_tarski(sK1,k1_funct_1(sK3,sK1)),k3_xboole_0(sK3,sK3)) = iProver_top
    | r2_hidden(k4_tarski(sK1,k1_funct_1(sK3,sK1)),sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2437])).

cnf(c_5175,plain,
    ( r2_hidden(k4_tarski(sK1,k1_funct_1(sK3,sK1)),sK3)
    | ~ r2_hidden(sK1,k1_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_5176,plain,
    ( r2_hidden(k4_tarski(sK1,k1_funct_1(sK3,sK1)),sK3) = iProver_top
    | r2_hidden(sK1,k1_relat_1(sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5175])).

cnf(c_10504,plain,
    ( r2_hidden(k4_tarski(sK1,k1_funct_1(sK3,sK1)),k3_xboole_0(sK3,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10432,c_26,c_27,c_1359,c_2439,c_5176])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),X3)
    | r2_hidden(k4_tarski(X0,X2),k5_relat_1(k6_relat_1(X1),X3))
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_753,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(k4_tarski(X0,X2),X3) != iProver_top
    | r2_hidden(k4_tarski(X0,X2),k5_relat_1(k6_relat_1(X1),X3)) = iProver_top
    | v1_relat_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2212,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_relat_1(k5_relat_1(k6_relat_1(X1),X2))) = iProver_top
    | r2_hidden(k4_tarski(X0,X3),X2) != iProver_top
    | v1_funct_1(k5_relat_1(k6_relat_1(X1),X2)) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(k5_relat_1(k6_relat_1(X1),X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_753,c_744])).

cnf(c_10512,plain,
    ( r2_hidden(sK1,X0) != iProver_top
    | r2_hidden(sK1,k1_relat_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3)))) = iProver_top
    | v1_funct_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3))) != iProver_top
    | v1_relat_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3))) != iProver_top
    | v1_relat_1(k3_xboole_0(sK3,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10504,c_2212])).

cnf(c_13267,plain,
    ( v1_relat_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3))) != iProver_top
    | v1_funct_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3))) != iProver_top
    | r2_hidden(sK1,k1_relat_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3)))) = iProver_top
    | r2_hidden(sK1,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10512,c_26,c_79,c_83,c_1356])).

cnf(c_13268,plain,
    ( r2_hidden(sK1,X0) != iProver_top
    | r2_hidden(sK1,k1_relat_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3)))) = iProver_top
    | v1_funct_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3))) != iProver_top
    | v1_relat_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_13267])).

cnf(c_9,plain,
    ( r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X3),X2))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_752,plain,
    ( r2_hidden(k4_tarski(X0,X1),X2) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X3),X2)) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2033,plain,
    ( r2_hidden(X0,k1_relat_1(k5_relat_1(k6_relat_1(X1),X2))) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)),X2) = iProver_top
    | v1_funct_1(k5_relat_1(k6_relat_1(X1),X2)) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(k5_relat_1(k6_relat_1(X1),X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_749,c_752])).

cnf(c_3084,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1(X0),X1),X2) = k1_funct_1(X1,X2)
    | r2_hidden(X2,k1_relat_1(k5_relat_1(k6_relat_1(X0),X1))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(k5_relat_1(k6_relat_1(X0),X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2033,c_745])).

cnf(c_13275,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3)),sK1) = k1_funct_1(k3_xboole_0(sK3,sK3),sK1)
    | r2_hidden(sK1,X0) != iProver_top
    | v1_funct_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3))) != iProver_top
    | v1_funct_1(k3_xboole_0(sK3,sK3)) != iProver_top
    | v1_relat_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3))) != iProver_top
    | v1_relat_1(k3_xboole_0(sK3,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13268,c_3084])).

cnf(c_13277,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3)),sK1) = k1_funct_1(sK3,sK1)
    | r2_hidden(sK1,X0) != iProver_top
    | v1_funct_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3))) != iProver_top
    | v1_funct_1(k3_xboole_0(sK3,sK3)) != iProver_top
    | v1_relat_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3))) != iProver_top
    | v1_relat_1(k3_xboole_0(sK3,sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13275,c_10429])).

cnf(c_2211,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1(X0),X1),X2) = X3
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(k4_tarski(X2,X3),X1) != iProver_top
    | v1_funct_1(k5_relat_1(k6_relat_1(X0),X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_753,c_745])).

cnf(c_10514,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3)),sK1) = k1_funct_1(sK3,sK1)
    | r2_hidden(sK1,X0) != iProver_top
    | v1_funct_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3))) != iProver_top
    | v1_relat_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3))) != iProver_top
    | v1_relat_1(k3_xboole_0(sK3,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10504,c_2211])).

cnf(c_13285,plain,
    ( v1_relat_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3))) != iProver_top
    | k1_funct_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3)),sK1) = k1_funct_1(sK3,sK1)
    | r2_hidden(sK1,X0) != iProver_top
    | v1_funct_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13277,c_26,c_79,c_83,c_1356,c_10514])).

cnf(c_13286,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3)),sK1) = k1_funct_1(sK3,sK1)
    | r2_hidden(sK1,X0) != iProver_top
    | v1_funct_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3))) != iProver_top
    | v1_relat_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_13285])).

cnf(c_13291,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3)),sK1) = k1_funct_1(sK3,sK1)
    | r2_hidden(sK1,X0) != iProver_top
    | v1_funct_1(k3_xboole_0(sK3,sK3)) != iProver_top
    | v1_funct_1(k6_relat_1(X0)) != iProver_top
    | v1_relat_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3))) != iProver_top
    | v1_relat_1(k3_xboole_0(sK3,sK3)) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_748,c_13286])).

cnf(c_18,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_38,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_17,plain,
    ( v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_41,plain,
    ( v1_funct_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_13812,plain,
    ( v1_relat_1(k3_xboole_0(sK3,sK3)) != iProver_top
    | v1_relat_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3))) != iProver_top
    | r2_hidden(sK1,X0) != iProver_top
    | k1_funct_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3)),sK1) = k1_funct_1(sK3,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13291,c_26,c_27,c_38,c_41,c_79,c_83,c_1356,c_4222])).

cnf(c_13813,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3)),sK1) = k1_funct_1(sK3,sK1)
    | r2_hidden(sK1,X0) != iProver_top
    | v1_relat_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3))) != iProver_top
    | v1_relat_1(k3_xboole_0(sK3,sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_13812])).

cnf(c_13818,plain,
    ( v1_relat_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3))) != iProver_top
    | r2_hidden(sK1,X0) != iProver_top
    | k1_funct_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3)),sK1) = k1_funct_1(sK3,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13813,c_26,c_27,c_38,c_41,c_79,c_83,c_1356,c_4222,c_13291])).

cnf(c_13819,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3)),sK1) = k1_funct_1(sK3,sK1)
    | r2_hidden(sK1,X0) != iProver_top
    | v1_relat_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_13818])).

cnf(c_13824,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3)),sK1) = k1_funct_1(sK3,sK1)
    | r2_hidden(sK1,X0) != iProver_top
    | v1_relat_1(k3_xboole_0(sK3,sK3)) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_755,c_13819])).

cnf(c_13829,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3)),sK1) = k1_funct_1(sK3,sK1)
    | r2_hidden(sK1,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13824,c_26,c_38,c_79,c_83,c_1356])).

cnf(c_13835,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(sK3,sK3)),sK1) = k1_funct_1(sK3,sK1)
    | r2_hidden(sK1,X1) != iProver_top
    | r2_hidden(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_758,c_13829])).

cnf(c_759,plain,
    ( k3_xboole_0(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2376,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r2_hidden(sK0(X0,X1,X0),X0) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_759])).

cnf(c_2378,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r2_hidden(sK0(X0,X1,X0),X0) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2376])).

cnf(c_761,plain,
    ( k3_xboole_0(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_14374,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r2_hidden(sK0(X0,X1,X0),X0) != iProver_top
    | r2_hidden(sK0(X0,X1,X0),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2378,c_761])).

cnf(c_14657,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r2_hidden(sK0(X0,X1,X0),X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14374,c_2378])).

cnf(c_14673,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_2378,c_14657])).

cnf(c_14766,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1(k3_xboole_0(X0,X1)),sK3),sK1) = k1_funct_1(sK3,sK1)
    | r2_hidden(sK1,X0) != iProver_top
    | r2_hidden(sK1,X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13835,c_14673])).

cnf(c_14773,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1(k3_xboole_0(sK2,X0)),sK3),sK1) = k1_funct_1(sK3,sK1)
    | r2_hidden(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1472,c_14766])).

cnf(c_14986,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1(k3_xboole_0(sK2,sK2)),sK3),sK1) = k1_funct_1(sK3,sK1) ),
    inference(superposition,[status(thm)],[c_1472,c_14773])).

cnf(c_15002,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1) = k1_funct_1(sK3,sK1) ),
    inference(demodulation,[status(thm)],[c_14986,c_14673])).

cnf(c_403,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_895,plain,
    ( k1_funct_1(sK3,sK1) = k1_funct_1(sK3,sK1) ),
    inference(instantiation,[status(thm)],[c_403])).

cnf(c_404,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_788,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1) != X0
    | k1_funct_1(sK3,sK1) != X0
    | k1_funct_1(sK3,sK1) = k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1) ),
    inference(instantiation,[status(thm)],[c_404])).

cnf(c_826,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1) != k1_funct_1(sK3,sK1)
    | k1_funct_1(sK3,sK1) = k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1)
    | k1_funct_1(sK3,sK1) != k1_funct_1(sK3,sK1) ),
    inference(instantiation,[status(thm)],[c_788])).

cnf(c_22,negated_conjecture,
    ( k1_funct_1(sK3,sK1) != k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_15002,c_895,c_826,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:18:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.97/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.97/1.49  
% 7.97/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.97/1.49  
% 7.97/1.49  ------  iProver source info
% 7.97/1.49  
% 7.97/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.97/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.97/1.49  git: non_committed_changes: false
% 7.97/1.49  git: last_make_outside_of_git: false
% 7.97/1.49  
% 7.97/1.49  ------ 
% 7.97/1.49  
% 7.97/1.49  ------ Input Options
% 7.97/1.49  
% 7.97/1.49  --out_options                           all
% 7.97/1.49  --tptp_safe_out                         true
% 7.97/1.49  --problem_path                          ""
% 7.97/1.49  --include_path                          ""
% 7.97/1.49  --clausifier                            res/vclausify_rel
% 7.97/1.49  --clausifier_options                    ""
% 7.97/1.49  --stdin                                 false
% 7.97/1.49  --stats_out                             all
% 7.97/1.49  
% 7.97/1.49  ------ General Options
% 7.97/1.49  
% 7.97/1.49  --fof                                   false
% 7.97/1.49  --time_out_real                         305.
% 7.97/1.49  --time_out_virtual                      -1.
% 7.97/1.49  --symbol_type_check                     false
% 7.97/1.49  --clausify_out                          false
% 7.97/1.49  --sig_cnt_out                           false
% 7.97/1.49  --trig_cnt_out                          false
% 7.97/1.49  --trig_cnt_out_tolerance                1.
% 7.97/1.49  --trig_cnt_out_sk_spl                   false
% 7.97/1.49  --abstr_cl_out                          false
% 7.97/1.49  
% 7.97/1.49  ------ Global Options
% 7.97/1.49  
% 7.97/1.49  --schedule                              default
% 7.97/1.49  --add_important_lit                     false
% 7.97/1.49  --prop_solver_per_cl                    1000
% 7.97/1.49  --min_unsat_core                        false
% 7.97/1.49  --soft_assumptions                      false
% 7.97/1.49  --soft_lemma_size                       3
% 7.97/1.49  --prop_impl_unit_size                   0
% 7.97/1.49  --prop_impl_unit                        []
% 7.97/1.49  --share_sel_clauses                     true
% 7.97/1.49  --reset_solvers                         false
% 7.97/1.49  --bc_imp_inh                            [conj_cone]
% 7.97/1.49  --conj_cone_tolerance                   3.
% 7.97/1.49  --extra_neg_conj                        none
% 7.97/1.49  --large_theory_mode                     true
% 7.97/1.49  --prolific_symb_bound                   200
% 7.97/1.49  --lt_threshold                          2000
% 7.97/1.49  --clause_weak_htbl                      true
% 7.97/1.49  --gc_record_bc_elim                     false
% 7.97/1.49  
% 7.97/1.49  ------ Preprocessing Options
% 7.97/1.49  
% 7.97/1.49  --preprocessing_flag                    true
% 7.97/1.49  --time_out_prep_mult                    0.1
% 7.97/1.49  --splitting_mode                        input
% 7.97/1.49  --splitting_grd                         true
% 7.97/1.49  --splitting_cvd                         false
% 7.97/1.49  --splitting_cvd_svl                     false
% 7.97/1.49  --splitting_nvd                         32
% 7.97/1.49  --sub_typing                            true
% 7.97/1.49  --prep_gs_sim                           true
% 7.97/1.49  --prep_unflatten                        true
% 7.97/1.49  --prep_res_sim                          true
% 7.97/1.49  --prep_upred                            true
% 7.97/1.49  --prep_sem_filter                       exhaustive
% 7.97/1.49  --prep_sem_filter_out                   false
% 7.97/1.49  --pred_elim                             true
% 7.97/1.49  --res_sim_input                         true
% 7.97/1.49  --eq_ax_congr_red                       true
% 7.97/1.49  --pure_diseq_elim                       true
% 7.97/1.49  --brand_transform                       false
% 7.97/1.49  --non_eq_to_eq                          false
% 7.97/1.49  --prep_def_merge                        true
% 7.97/1.49  --prep_def_merge_prop_impl              false
% 7.97/1.49  --prep_def_merge_mbd                    true
% 7.97/1.49  --prep_def_merge_tr_red                 false
% 7.97/1.49  --prep_def_merge_tr_cl                  false
% 7.97/1.49  --smt_preprocessing                     true
% 7.97/1.49  --smt_ac_axioms                         fast
% 7.97/1.49  --preprocessed_out                      false
% 7.97/1.49  --preprocessed_stats                    false
% 7.97/1.49  
% 7.97/1.49  ------ Abstraction refinement Options
% 7.97/1.49  
% 7.97/1.49  --abstr_ref                             []
% 7.97/1.49  --abstr_ref_prep                        false
% 7.97/1.49  --abstr_ref_until_sat                   false
% 7.97/1.49  --abstr_ref_sig_restrict                funpre
% 7.97/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.97/1.49  --abstr_ref_under                       []
% 7.97/1.49  
% 7.97/1.49  ------ SAT Options
% 7.97/1.49  
% 7.97/1.49  --sat_mode                              false
% 7.97/1.49  --sat_fm_restart_options                ""
% 7.97/1.49  --sat_gr_def                            false
% 7.97/1.49  --sat_epr_types                         true
% 7.97/1.49  --sat_non_cyclic_types                  false
% 7.97/1.49  --sat_finite_models                     false
% 7.97/1.49  --sat_fm_lemmas                         false
% 7.97/1.49  --sat_fm_prep                           false
% 7.97/1.49  --sat_fm_uc_incr                        true
% 7.97/1.49  --sat_out_model                         small
% 7.97/1.49  --sat_out_clauses                       false
% 7.97/1.49  
% 7.97/1.49  ------ QBF Options
% 7.97/1.49  
% 7.97/1.49  --qbf_mode                              false
% 7.97/1.49  --qbf_elim_univ                         false
% 7.97/1.49  --qbf_dom_inst                          none
% 7.97/1.49  --qbf_dom_pre_inst                      false
% 7.97/1.49  --qbf_sk_in                             false
% 7.97/1.49  --qbf_pred_elim                         true
% 7.97/1.49  --qbf_split                             512
% 7.97/1.49  
% 7.97/1.49  ------ BMC1 Options
% 7.97/1.49  
% 7.97/1.49  --bmc1_incremental                      false
% 7.97/1.49  --bmc1_axioms                           reachable_all
% 7.97/1.49  --bmc1_min_bound                        0
% 7.97/1.49  --bmc1_max_bound                        -1
% 7.97/1.49  --bmc1_max_bound_default                -1
% 7.97/1.49  --bmc1_symbol_reachability              true
% 7.97/1.49  --bmc1_property_lemmas                  false
% 7.97/1.49  --bmc1_k_induction                      false
% 7.97/1.49  --bmc1_non_equiv_states                 false
% 7.97/1.49  --bmc1_deadlock                         false
% 7.97/1.49  --bmc1_ucm                              false
% 7.97/1.49  --bmc1_add_unsat_core                   none
% 7.97/1.49  --bmc1_unsat_core_children              false
% 7.97/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.97/1.49  --bmc1_out_stat                         full
% 7.97/1.49  --bmc1_ground_init                      false
% 7.97/1.49  --bmc1_pre_inst_next_state              false
% 7.97/1.49  --bmc1_pre_inst_state                   false
% 7.97/1.49  --bmc1_pre_inst_reach_state             false
% 7.97/1.49  --bmc1_out_unsat_core                   false
% 7.97/1.49  --bmc1_aig_witness_out                  false
% 7.97/1.49  --bmc1_verbose                          false
% 7.97/1.49  --bmc1_dump_clauses_tptp                false
% 7.97/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.97/1.49  --bmc1_dump_file                        -
% 7.97/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.97/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.97/1.49  --bmc1_ucm_extend_mode                  1
% 7.97/1.49  --bmc1_ucm_init_mode                    2
% 7.97/1.49  --bmc1_ucm_cone_mode                    none
% 7.97/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.97/1.49  --bmc1_ucm_relax_model                  4
% 7.97/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.97/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.97/1.49  --bmc1_ucm_layered_model                none
% 7.97/1.49  --bmc1_ucm_max_lemma_size               10
% 7.97/1.49  
% 7.97/1.49  ------ AIG Options
% 7.97/1.49  
% 7.97/1.49  --aig_mode                              false
% 7.97/1.49  
% 7.97/1.49  ------ Instantiation Options
% 7.97/1.49  
% 7.97/1.49  --instantiation_flag                    true
% 7.97/1.49  --inst_sos_flag                         true
% 7.97/1.49  --inst_sos_phase                        true
% 7.97/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.97/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.97/1.49  --inst_lit_sel_side                     num_symb
% 7.97/1.49  --inst_solver_per_active                1400
% 7.97/1.49  --inst_solver_calls_frac                1.
% 7.97/1.49  --inst_passive_queue_type               priority_queues
% 7.97/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.97/1.49  --inst_passive_queues_freq              [25;2]
% 7.97/1.49  --inst_dismatching                      true
% 7.97/1.49  --inst_eager_unprocessed_to_passive     true
% 7.97/1.49  --inst_prop_sim_given                   true
% 7.97/1.49  --inst_prop_sim_new                     false
% 7.97/1.49  --inst_subs_new                         false
% 7.97/1.49  --inst_eq_res_simp                      false
% 7.97/1.49  --inst_subs_given                       false
% 7.97/1.49  --inst_orphan_elimination               true
% 7.97/1.49  --inst_learning_loop_flag               true
% 7.97/1.49  --inst_learning_start                   3000
% 7.97/1.49  --inst_learning_factor                  2
% 7.97/1.49  --inst_start_prop_sim_after_learn       3
% 7.97/1.49  --inst_sel_renew                        solver
% 7.97/1.49  --inst_lit_activity_flag                true
% 7.97/1.49  --inst_restr_to_given                   false
% 7.97/1.49  --inst_activity_threshold               500
% 7.97/1.49  --inst_out_proof                        true
% 7.97/1.49  
% 7.97/1.49  ------ Resolution Options
% 7.97/1.49  
% 7.97/1.49  --resolution_flag                       true
% 7.97/1.49  --res_lit_sel                           adaptive
% 7.97/1.49  --res_lit_sel_side                      none
% 7.97/1.49  --res_ordering                          kbo
% 7.97/1.49  --res_to_prop_solver                    active
% 7.97/1.49  --res_prop_simpl_new                    false
% 7.97/1.49  --res_prop_simpl_given                  true
% 7.97/1.49  --res_passive_queue_type                priority_queues
% 7.97/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.97/1.49  --res_passive_queues_freq               [15;5]
% 7.97/1.49  --res_forward_subs                      full
% 7.97/1.49  --res_backward_subs                     full
% 7.97/1.49  --res_forward_subs_resolution           true
% 7.97/1.49  --res_backward_subs_resolution          true
% 7.97/1.49  --res_orphan_elimination                true
% 7.97/1.49  --res_time_limit                        2.
% 7.97/1.49  --res_out_proof                         true
% 7.97/1.49  
% 7.97/1.49  ------ Superposition Options
% 7.97/1.49  
% 7.97/1.49  --superposition_flag                    true
% 7.97/1.49  --sup_passive_queue_type                priority_queues
% 7.97/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.97/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.97/1.49  --demod_completeness_check              fast
% 7.97/1.49  --demod_use_ground                      true
% 7.97/1.49  --sup_to_prop_solver                    passive
% 7.97/1.49  --sup_prop_simpl_new                    true
% 7.97/1.49  --sup_prop_simpl_given                  true
% 7.97/1.49  --sup_fun_splitting                     true
% 7.97/1.49  --sup_smt_interval                      50000
% 7.97/1.49  
% 7.97/1.49  ------ Superposition Simplification Setup
% 7.97/1.49  
% 7.97/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.97/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.97/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.97/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.97/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.97/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.97/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.97/1.49  --sup_immed_triv                        [TrivRules]
% 7.97/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.97/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.97/1.49  --sup_immed_bw_main                     []
% 7.97/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.97/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.97/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.97/1.49  --sup_input_bw                          []
% 7.97/1.49  
% 7.97/1.49  ------ Combination Options
% 7.97/1.49  
% 7.97/1.49  --comb_res_mult                         3
% 7.97/1.49  --comb_sup_mult                         2
% 7.97/1.49  --comb_inst_mult                        10
% 7.97/1.49  
% 7.97/1.49  ------ Debug Options
% 7.97/1.49  
% 7.97/1.49  --dbg_backtrace                         false
% 7.97/1.49  --dbg_dump_prop_clauses                 false
% 7.97/1.49  --dbg_dump_prop_clauses_file            -
% 7.97/1.49  --dbg_out_stat                          false
% 7.97/1.49  ------ Parsing...
% 7.97/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.97/1.49  
% 7.97/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.97/1.49  
% 7.97/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.97/1.49  
% 7.97/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.97/1.49  ------ Proving...
% 7.97/1.49  ------ Problem Properties 
% 7.97/1.49  
% 7.97/1.49  
% 7.97/1.49  clauses                                 22
% 7.97/1.49  conjectures                             4
% 7.97/1.49  EPR                                     2
% 7.97/1.49  Horn                                    19
% 7.97/1.49  unary                                   6
% 7.97/1.49  binary                                  2
% 7.97/1.49  lits                                    62
% 7.97/1.49  lits eq                                 6
% 7.97/1.49  fd_pure                                 0
% 7.97/1.49  fd_pseudo                               0
% 7.97/1.49  fd_cond                                 0
% 7.97/1.49  fd_pseudo_cond                          4
% 7.97/1.49  AC symbols                              0
% 7.97/1.49  
% 7.97/1.49  ------ Schedule dynamic 5 is on 
% 7.97/1.49  
% 7.97/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.97/1.49  
% 7.97/1.49  
% 7.97/1.49  ------ 
% 7.97/1.49  Current options:
% 7.97/1.49  ------ 
% 7.97/1.49  
% 7.97/1.49  ------ Input Options
% 7.97/1.49  
% 7.97/1.49  --out_options                           all
% 7.97/1.49  --tptp_safe_out                         true
% 7.97/1.49  --problem_path                          ""
% 7.97/1.49  --include_path                          ""
% 7.97/1.49  --clausifier                            res/vclausify_rel
% 7.97/1.49  --clausifier_options                    ""
% 7.97/1.49  --stdin                                 false
% 7.97/1.49  --stats_out                             all
% 7.97/1.49  
% 7.97/1.49  ------ General Options
% 7.97/1.49  
% 7.97/1.49  --fof                                   false
% 7.97/1.49  --time_out_real                         305.
% 7.97/1.49  --time_out_virtual                      -1.
% 7.97/1.49  --symbol_type_check                     false
% 7.97/1.49  --clausify_out                          false
% 7.97/1.49  --sig_cnt_out                           false
% 7.97/1.49  --trig_cnt_out                          false
% 7.97/1.49  --trig_cnt_out_tolerance                1.
% 7.97/1.49  --trig_cnt_out_sk_spl                   false
% 7.97/1.49  --abstr_cl_out                          false
% 7.97/1.49  
% 7.97/1.49  ------ Global Options
% 7.97/1.49  
% 7.97/1.49  --schedule                              default
% 7.97/1.49  --add_important_lit                     false
% 7.97/1.49  --prop_solver_per_cl                    1000
% 7.97/1.49  --min_unsat_core                        false
% 7.97/1.49  --soft_assumptions                      false
% 7.97/1.49  --soft_lemma_size                       3
% 7.97/1.49  --prop_impl_unit_size                   0
% 7.97/1.49  --prop_impl_unit                        []
% 7.97/1.49  --share_sel_clauses                     true
% 7.97/1.49  --reset_solvers                         false
% 7.97/1.49  --bc_imp_inh                            [conj_cone]
% 7.97/1.49  --conj_cone_tolerance                   3.
% 7.97/1.49  --extra_neg_conj                        none
% 7.97/1.49  --large_theory_mode                     true
% 7.97/1.49  --prolific_symb_bound                   200
% 7.97/1.49  --lt_threshold                          2000
% 7.97/1.49  --clause_weak_htbl                      true
% 7.97/1.49  --gc_record_bc_elim                     false
% 7.97/1.49  
% 7.97/1.49  ------ Preprocessing Options
% 7.97/1.49  
% 7.97/1.49  --preprocessing_flag                    true
% 7.97/1.49  --time_out_prep_mult                    0.1
% 7.97/1.49  --splitting_mode                        input
% 7.97/1.49  --splitting_grd                         true
% 7.97/1.49  --splitting_cvd                         false
% 7.97/1.49  --splitting_cvd_svl                     false
% 7.97/1.49  --splitting_nvd                         32
% 7.97/1.49  --sub_typing                            true
% 7.97/1.49  --prep_gs_sim                           true
% 7.97/1.49  --prep_unflatten                        true
% 7.97/1.49  --prep_res_sim                          true
% 7.97/1.49  --prep_upred                            true
% 7.97/1.49  --prep_sem_filter                       exhaustive
% 7.97/1.49  --prep_sem_filter_out                   false
% 7.97/1.49  --pred_elim                             true
% 7.97/1.49  --res_sim_input                         true
% 7.97/1.49  --eq_ax_congr_red                       true
% 7.97/1.49  --pure_diseq_elim                       true
% 7.97/1.49  --brand_transform                       false
% 7.97/1.49  --non_eq_to_eq                          false
% 7.97/1.49  --prep_def_merge                        true
% 7.97/1.49  --prep_def_merge_prop_impl              false
% 7.97/1.49  --prep_def_merge_mbd                    true
% 7.97/1.49  --prep_def_merge_tr_red                 false
% 7.97/1.49  --prep_def_merge_tr_cl                  false
% 7.97/1.49  --smt_preprocessing                     true
% 7.97/1.49  --smt_ac_axioms                         fast
% 7.97/1.49  --preprocessed_out                      false
% 7.97/1.49  --preprocessed_stats                    false
% 7.97/1.49  
% 7.97/1.49  ------ Abstraction refinement Options
% 7.97/1.49  
% 7.97/1.49  --abstr_ref                             []
% 7.97/1.49  --abstr_ref_prep                        false
% 7.97/1.49  --abstr_ref_until_sat                   false
% 7.97/1.49  --abstr_ref_sig_restrict                funpre
% 7.97/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.97/1.49  --abstr_ref_under                       []
% 7.97/1.49  
% 7.97/1.49  ------ SAT Options
% 7.97/1.49  
% 7.97/1.49  --sat_mode                              false
% 7.97/1.49  --sat_fm_restart_options                ""
% 7.97/1.49  --sat_gr_def                            false
% 7.97/1.49  --sat_epr_types                         true
% 7.97/1.49  --sat_non_cyclic_types                  false
% 7.97/1.49  --sat_finite_models                     false
% 7.97/1.49  --sat_fm_lemmas                         false
% 7.97/1.49  --sat_fm_prep                           false
% 7.97/1.49  --sat_fm_uc_incr                        true
% 7.97/1.49  --sat_out_model                         small
% 7.97/1.49  --sat_out_clauses                       false
% 7.97/1.49  
% 7.97/1.49  ------ QBF Options
% 7.97/1.49  
% 7.97/1.49  --qbf_mode                              false
% 7.97/1.49  --qbf_elim_univ                         false
% 7.97/1.49  --qbf_dom_inst                          none
% 7.97/1.49  --qbf_dom_pre_inst                      false
% 7.97/1.49  --qbf_sk_in                             false
% 7.97/1.49  --qbf_pred_elim                         true
% 7.97/1.49  --qbf_split                             512
% 7.97/1.49  
% 7.97/1.49  ------ BMC1 Options
% 7.97/1.49  
% 7.97/1.49  --bmc1_incremental                      false
% 7.97/1.49  --bmc1_axioms                           reachable_all
% 7.97/1.49  --bmc1_min_bound                        0
% 7.97/1.49  --bmc1_max_bound                        -1
% 7.97/1.49  --bmc1_max_bound_default                -1
% 7.97/1.49  --bmc1_symbol_reachability              true
% 7.97/1.49  --bmc1_property_lemmas                  false
% 7.97/1.49  --bmc1_k_induction                      false
% 7.97/1.49  --bmc1_non_equiv_states                 false
% 7.97/1.49  --bmc1_deadlock                         false
% 7.97/1.49  --bmc1_ucm                              false
% 7.97/1.49  --bmc1_add_unsat_core                   none
% 7.97/1.49  --bmc1_unsat_core_children              false
% 7.97/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.97/1.49  --bmc1_out_stat                         full
% 7.97/1.49  --bmc1_ground_init                      false
% 7.97/1.49  --bmc1_pre_inst_next_state              false
% 7.97/1.49  --bmc1_pre_inst_state                   false
% 7.97/1.49  --bmc1_pre_inst_reach_state             false
% 7.97/1.49  --bmc1_out_unsat_core                   false
% 7.97/1.49  --bmc1_aig_witness_out                  false
% 7.97/1.49  --bmc1_verbose                          false
% 7.97/1.49  --bmc1_dump_clauses_tptp                false
% 7.97/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.97/1.49  --bmc1_dump_file                        -
% 7.97/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.97/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.97/1.49  --bmc1_ucm_extend_mode                  1
% 7.97/1.49  --bmc1_ucm_init_mode                    2
% 7.97/1.49  --bmc1_ucm_cone_mode                    none
% 7.97/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.97/1.49  --bmc1_ucm_relax_model                  4
% 7.97/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.97/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.97/1.49  --bmc1_ucm_layered_model                none
% 7.97/1.49  --bmc1_ucm_max_lemma_size               10
% 7.97/1.49  
% 7.97/1.49  ------ AIG Options
% 7.97/1.49  
% 7.97/1.49  --aig_mode                              false
% 7.97/1.49  
% 7.97/1.49  ------ Instantiation Options
% 7.97/1.49  
% 7.97/1.49  --instantiation_flag                    true
% 7.97/1.49  --inst_sos_flag                         true
% 7.97/1.49  --inst_sos_phase                        true
% 7.97/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.97/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.97/1.49  --inst_lit_sel_side                     none
% 7.97/1.49  --inst_solver_per_active                1400
% 7.97/1.49  --inst_solver_calls_frac                1.
% 7.97/1.49  --inst_passive_queue_type               priority_queues
% 7.97/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.97/1.49  --inst_passive_queues_freq              [25;2]
% 7.97/1.49  --inst_dismatching                      true
% 7.97/1.49  --inst_eager_unprocessed_to_passive     true
% 7.97/1.49  --inst_prop_sim_given                   true
% 7.97/1.49  --inst_prop_sim_new                     false
% 7.97/1.49  --inst_subs_new                         false
% 7.97/1.49  --inst_eq_res_simp                      false
% 7.97/1.49  --inst_subs_given                       false
% 7.97/1.49  --inst_orphan_elimination               true
% 7.97/1.49  --inst_learning_loop_flag               true
% 7.97/1.49  --inst_learning_start                   3000
% 7.97/1.49  --inst_learning_factor                  2
% 7.97/1.49  --inst_start_prop_sim_after_learn       3
% 7.97/1.49  --inst_sel_renew                        solver
% 7.97/1.49  --inst_lit_activity_flag                true
% 7.97/1.49  --inst_restr_to_given                   false
% 7.97/1.49  --inst_activity_threshold               500
% 7.97/1.49  --inst_out_proof                        true
% 7.97/1.49  
% 7.97/1.49  ------ Resolution Options
% 7.97/1.49  
% 7.97/1.49  --resolution_flag                       false
% 7.97/1.49  --res_lit_sel                           adaptive
% 7.97/1.49  --res_lit_sel_side                      none
% 7.97/1.49  --res_ordering                          kbo
% 7.97/1.49  --res_to_prop_solver                    active
% 7.97/1.49  --res_prop_simpl_new                    false
% 7.97/1.49  --res_prop_simpl_given                  true
% 7.97/1.49  --res_passive_queue_type                priority_queues
% 7.97/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.97/1.49  --res_passive_queues_freq               [15;5]
% 7.97/1.49  --res_forward_subs                      full
% 7.97/1.49  --res_backward_subs                     full
% 7.97/1.49  --res_forward_subs_resolution           true
% 7.97/1.49  --res_backward_subs_resolution          true
% 7.97/1.49  --res_orphan_elimination                true
% 7.97/1.49  --res_time_limit                        2.
% 7.97/1.49  --res_out_proof                         true
% 7.97/1.49  
% 7.97/1.49  ------ Superposition Options
% 7.97/1.49  
% 7.97/1.49  --superposition_flag                    true
% 7.97/1.49  --sup_passive_queue_type                priority_queues
% 7.97/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.97/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.97/1.49  --demod_completeness_check              fast
% 7.97/1.49  --demod_use_ground                      true
% 7.97/1.49  --sup_to_prop_solver                    passive
% 7.97/1.49  --sup_prop_simpl_new                    true
% 7.97/1.49  --sup_prop_simpl_given                  true
% 7.97/1.49  --sup_fun_splitting                     true
% 7.97/1.49  --sup_smt_interval                      50000
% 7.97/1.49  
% 7.97/1.49  ------ Superposition Simplification Setup
% 7.97/1.49  
% 7.97/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.97/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.97/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.97/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.97/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.97/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.97/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.97/1.49  --sup_immed_triv                        [TrivRules]
% 7.97/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.97/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.97/1.49  --sup_immed_bw_main                     []
% 7.97/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.97/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.97/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.97/1.49  --sup_input_bw                          []
% 7.97/1.49  
% 7.97/1.49  ------ Combination Options
% 7.97/1.49  
% 7.97/1.49  --comb_res_mult                         3
% 7.97/1.49  --comb_sup_mult                         2
% 7.97/1.49  --comb_inst_mult                        10
% 7.97/1.49  
% 7.97/1.49  ------ Debug Options
% 7.97/1.49  
% 7.97/1.49  --dbg_backtrace                         false
% 7.97/1.49  --dbg_dump_prop_clauses                 false
% 7.97/1.49  --dbg_dump_prop_clauses_file            -
% 7.97/1.49  --dbg_out_stat                          false
% 7.97/1.49  
% 7.97/1.49  
% 7.97/1.49  
% 7.97/1.49  
% 7.97/1.49  ------ Proving...
% 7.97/1.49  
% 7.97/1.49  
% 7.97/1.49  % SZS status Theorem for theBenchmark.p
% 7.97/1.49  
% 7.97/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.97/1.49  
% 7.97/1.49  fof(f9,conjecture,(
% 7.97/1.49    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) => k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)))),
% 7.97/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.49  
% 7.97/1.49  fof(f10,negated_conjecture,(
% 7.97/1.49    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) => k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)))),
% 7.97/1.49    inference(negated_conjecture,[],[f9])).
% 7.97/1.49  
% 7.97/1.49  fof(f20,plain,(
% 7.97/1.49    ? [X0,X1,X2] : ((k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 7.97/1.49    inference(ennf_transformation,[],[f10])).
% 7.97/1.49  
% 7.97/1.49  fof(f21,plain,(
% 7.97/1.49    ? [X0,X1,X2] : (k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 7.97/1.49    inference(flattening,[],[f20])).
% 7.97/1.49  
% 7.97/1.49  fof(f32,plain,(
% 7.97/1.49    ? [X0,X1,X2] : (k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (k1_funct_1(sK3,sK1) != k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1) & r2_hidden(sK1,k3_xboole_0(k1_relat_1(sK3),sK2)) & v1_funct_1(sK3) & v1_relat_1(sK3))),
% 7.97/1.49    introduced(choice_axiom,[])).
% 7.97/1.49  
% 7.97/1.49  fof(f33,plain,(
% 7.97/1.49    k1_funct_1(sK3,sK1) != k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1) & r2_hidden(sK1,k3_xboole_0(k1_relat_1(sK3),sK2)) & v1_funct_1(sK3) & v1_relat_1(sK3)),
% 7.97/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f21,f32])).
% 7.97/1.49  
% 7.97/1.49  fof(f58,plain,(
% 7.97/1.49    r2_hidden(sK1,k3_xboole_0(k1_relat_1(sK3),sK2))),
% 7.97/1.49    inference(cnf_transformation,[],[f33])).
% 7.97/1.49  
% 7.97/1.49  fof(f1,axiom,(
% 7.97/1.49    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 7.97/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.49  
% 7.97/1.49  fof(f22,plain,(
% 7.97/1.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.97/1.49    inference(nnf_transformation,[],[f1])).
% 7.97/1.49  
% 7.97/1.49  fof(f23,plain,(
% 7.97/1.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.97/1.49    inference(flattening,[],[f22])).
% 7.97/1.49  
% 7.97/1.49  fof(f24,plain,(
% 7.97/1.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.97/1.49    inference(rectify,[],[f23])).
% 7.97/1.49  
% 7.97/1.49  fof(f25,plain,(
% 7.97/1.49    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 7.97/1.49    introduced(choice_axiom,[])).
% 7.97/1.49  
% 7.97/1.49  fof(f26,plain,(
% 7.97/1.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.97/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).
% 7.97/1.49  
% 7.97/1.49  fof(f35,plain,(
% 7.97/1.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 7.97/1.49    inference(cnf_transformation,[],[f26])).
% 7.97/1.49  
% 7.97/1.49  fof(f61,plain,(
% 7.97/1.49    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 7.97/1.49    inference(equality_resolution,[],[f35])).
% 7.97/1.49  
% 7.97/1.49  fof(f36,plain,(
% 7.97/1.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 7.97/1.49    inference(cnf_transformation,[],[f26])).
% 7.97/1.49  
% 7.97/1.49  fof(f60,plain,(
% 7.97/1.49    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_xboole_0(X0,X1)) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 7.97/1.49    inference(equality_resolution,[],[f36])).
% 7.97/1.49  
% 7.97/1.49  fof(f2,axiom,(
% 7.97/1.49    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 7.97/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.49  
% 7.97/1.49  fof(f11,plain,(
% 7.97/1.49    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 7.97/1.49    inference(ennf_transformation,[],[f2])).
% 7.97/1.49  
% 7.97/1.49  fof(f12,plain,(
% 7.97/1.49    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 7.97/1.49    inference(flattening,[],[f11])).
% 7.97/1.49  
% 7.97/1.49  fof(f40,plain,(
% 7.97/1.49    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.97/1.49    inference(cnf_transformation,[],[f12])).
% 7.97/1.49  
% 7.97/1.49  fof(f6,axiom,(
% 7.97/1.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1) & v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))))),
% 7.97/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.49  
% 7.97/1.49  fof(f16,plain,(
% 7.97/1.49    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.97/1.49    inference(ennf_transformation,[],[f6])).
% 7.97/1.49  
% 7.97/1.49  fof(f17,plain,(
% 7.97/1.49    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.97/1.49    inference(flattening,[],[f16])).
% 7.97/1.49  
% 7.97/1.49  fof(f50,plain,(
% 7.97/1.49    ( ! [X0,X1] : (v1_funct_1(k5_relat_1(X0,X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.97/1.49    inference(cnf_transformation,[],[f17])).
% 7.97/1.49  
% 7.97/1.49  fof(f34,plain,(
% 7.97/1.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 7.97/1.49    inference(cnf_transformation,[],[f26])).
% 7.97/1.49  
% 7.97/1.49  fof(f62,plain,(
% 7.97/1.49    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 7.97/1.49    inference(equality_resolution,[],[f34])).
% 7.97/1.49  
% 7.97/1.49  fof(f8,axiom,(
% 7.97/1.49    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 7.97/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.49  
% 7.97/1.49  fof(f18,plain,(
% 7.97/1.49    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 7.97/1.49    inference(ennf_transformation,[],[f8])).
% 7.97/1.49  
% 7.97/1.49  fof(f19,plain,(
% 7.97/1.49    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 7.97/1.49    inference(flattening,[],[f18])).
% 7.97/1.49  
% 7.97/1.49  fof(f30,plain,(
% 7.97/1.49    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 7.97/1.49    inference(nnf_transformation,[],[f19])).
% 7.97/1.49  
% 7.97/1.49  fof(f31,plain,(
% 7.97/1.49    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 7.97/1.49    inference(flattening,[],[f30])).
% 7.97/1.49  
% 7.97/1.49  fof(f55,plain,(
% 7.97/1.49    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.97/1.49    inference(cnf_transformation,[],[f31])).
% 7.97/1.49  
% 7.97/1.49  fof(f66,plain,(
% 7.97/1.49    ( ! [X2,X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.97/1.49    inference(equality_resolution,[],[f55])).
% 7.97/1.49  
% 7.97/1.49  fof(f53,plain,(
% 7.97/1.49    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.97/1.49    inference(cnf_transformation,[],[f31])).
% 7.97/1.49  
% 7.97/1.49  fof(f54,plain,(
% 7.97/1.49    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.97/1.49    inference(cnf_transformation,[],[f31])).
% 7.97/1.49  
% 7.97/1.49  fof(f56,plain,(
% 7.97/1.49    v1_relat_1(sK3)),
% 7.97/1.49    inference(cnf_transformation,[],[f33])).
% 7.97/1.49  
% 7.97/1.49  fof(f57,plain,(
% 7.97/1.49    v1_funct_1(sK3)),
% 7.97/1.49    inference(cnf_transformation,[],[f33])).
% 7.97/1.49  
% 7.97/1.49  fof(f37,plain,(
% 7.97/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 7.97/1.49    inference(cnf_transformation,[],[f26])).
% 7.97/1.49  
% 7.97/1.49  fof(f39,plain,(
% 7.97/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 7.97/1.49    inference(cnf_transformation,[],[f26])).
% 7.97/1.49  
% 7.97/1.49  fof(f4,axiom,(
% 7.97/1.49    ! [X0,X1,X2,X3] : (v1_relat_1(X3) => (r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) <=> (r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X0,X2))))),
% 7.97/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.49  
% 7.97/1.49  fof(f13,plain,(
% 7.97/1.49    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) <=> (r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X0,X2))) | ~v1_relat_1(X3))),
% 7.97/1.49    inference(ennf_transformation,[],[f4])).
% 7.97/1.49  
% 7.97/1.49  fof(f27,plain,(
% 7.97/1.49    ! [X0,X1,X2,X3] : (((r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) | (~r2_hidden(k4_tarski(X0,X1),X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)))) | ~v1_relat_1(X3))),
% 7.97/1.49    inference(nnf_transformation,[],[f13])).
% 7.97/1.49  
% 7.97/1.49  fof(f28,plain,(
% 7.97/1.49    ! [X0,X1,X2,X3] : (((r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) | ~r2_hidden(k4_tarski(X0,X1),X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)))) | ~v1_relat_1(X3))),
% 7.97/1.49    inference(flattening,[],[f27])).
% 7.97/1.49  
% 7.97/1.49  fof(f44,plain,(
% 7.97/1.49    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) | ~r2_hidden(k4_tarski(X0,X1),X3) | ~r2_hidden(X0,X2) | ~v1_relat_1(X3)) )),
% 7.97/1.49    inference(cnf_transformation,[],[f28])).
% 7.97/1.49  
% 7.97/1.49  fof(f43,plain,(
% 7.97/1.49    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),X3) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) | ~v1_relat_1(X3)) )),
% 7.97/1.49    inference(cnf_transformation,[],[f28])).
% 7.97/1.49  
% 7.97/1.49  fof(f7,axiom,(
% 7.97/1.49    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 7.97/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.49  
% 7.97/1.49  fof(f51,plain,(
% 7.97/1.49    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 7.97/1.49    inference(cnf_transformation,[],[f7])).
% 7.97/1.49  
% 7.97/1.49  fof(f52,plain,(
% 7.97/1.49    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 7.97/1.49    inference(cnf_transformation,[],[f7])).
% 7.97/1.49  
% 7.97/1.49  fof(f59,plain,(
% 7.97/1.49    k1_funct_1(sK3,sK1) != k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1)),
% 7.97/1.49    inference(cnf_transformation,[],[f33])).
% 7.97/1.49  
% 7.97/1.49  cnf(c_23,negated_conjecture,
% 7.97/1.49      ( r2_hidden(sK1,k3_xboole_0(k1_relat_1(sK3),sK2)) ),
% 7.97/1.49      inference(cnf_transformation,[],[f58]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_743,plain,
% 7.97/1.49      ( r2_hidden(sK1,k3_xboole_0(k1_relat_1(sK3),sK2)) = iProver_top ),
% 7.97/1.49      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_4,plain,
% 7.97/1.49      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
% 7.97/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_757,plain,
% 7.97/1.49      ( r2_hidden(X0,X1) = iProver_top
% 7.97/1.49      | r2_hidden(X0,k3_xboole_0(X2,X1)) != iProver_top ),
% 7.97/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_1472,plain,
% 7.97/1.49      ( r2_hidden(sK1,sK2) = iProver_top ),
% 7.97/1.49      inference(superposition,[status(thm)],[c_743,c_757]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_3,plain,
% 7.97/1.49      ( ~ r2_hidden(X0,X1)
% 7.97/1.49      | ~ r2_hidden(X0,X2)
% 7.97/1.49      | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
% 7.97/1.49      inference(cnf_transformation,[],[f60]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_758,plain,
% 7.97/1.49      ( r2_hidden(X0,X1) != iProver_top
% 7.97/1.49      | r2_hidden(X0,X2) != iProver_top
% 7.97/1.49      | r2_hidden(X0,k3_xboole_0(X2,X1)) = iProver_top ),
% 7.97/1.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_6,plain,
% 7.97/1.49      ( ~ v1_relat_1(X0)
% 7.97/1.49      | ~ v1_relat_1(X1)
% 7.97/1.49      | v1_relat_1(k5_relat_1(X1,X0)) ),
% 7.97/1.49      inference(cnf_transformation,[],[f40]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_755,plain,
% 7.97/1.49      ( v1_relat_1(X0) != iProver_top
% 7.97/1.49      | v1_relat_1(X1) != iProver_top
% 7.97/1.49      | v1_relat_1(k5_relat_1(X0,X1)) = iProver_top ),
% 7.97/1.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_15,plain,
% 7.97/1.49      ( ~ v1_funct_1(X0)
% 7.97/1.49      | ~ v1_funct_1(X1)
% 7.97/1.49      | v1_funct_1(k5_relat_1(X0,X1))
% 7.97/1.49      | ~ v1_relat_1(X1)
% 7.97/1.49      | ~ v1_relat_1(X0) ),
% 7.97/1.49      inference(cnf_transformation,[],[f50]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_748,plain,
% 7.97/1.49      ( v1_funct_1(X0) != iProver_top
% 7.97/1.49      | v1_funct_1(X1) != iProver_top
% 7.97/1.49      | v1_funct_1(k5_relat_1(X1,X0)) = iProver_top
% 7.97/1.49      | v1_relat_1(X0) != iProver_top
% 7.97/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.97/1.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_5,plain,
% 7.97/1.49      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
% 7.97/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_756,plain,
% 7.97/1.49      ( r2_hidden(X0,X1) = iProver_top
% 7.97/1.49      | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
% 7.97/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_1359,plain,
% 7.97/1.49      ( r2_hidden(sK1,k1_relat_1(sK3)) = iProver_top ),
% 7.97/1.49      inference(superposition,[status(thm)],[c_743,c_756]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_19,plain,
% 7.97/1.49      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 7.97/1.49      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 7.97/1.49      | ~ v1_funct_1(X1)
% 7.97/1.49      | ~ v1_relat_1(X1) ),
% 7.97/1.49      inference(cnf_transformation,[],[f66]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_749,plain,
% 7.97/1.49      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 7.97/1.49      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1) = iProver_top
% 7.97/1.49      | v1_funct_1(X1) != iProver_top
% 7.97/1.50      | v1_relat_1(X1) != iProver_top ),
% 7.97/1.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_21,plain,
% 7.97/1.50      ( r2_hidden(X0,k1_relat_1(X1))
% 7.97/1.50      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 7.97/1.50      | ~ v1_funct_1(X1)
% 7.97/1.50      | ~ v1_relat_1(X1) ),
% 7.97/1.50      inference(cnf_transformation,[],[f53]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_744,plain,
% 7.97/1.50      ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
% 7.97/1.50      | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top
% 7.97/1.50      | v1_funct_1(X1) != iProver_top
% 7.97/1.50      | v1_relat_1(X1) != iProver_top ),
% 7.97/1.50      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_1708,plain,
% 7.97/1.50      ( r2_hidden(X0,k1_relat_1(k3_xboole_0(X1,X2))) = iProver_top
% 7.97/1.50      | r2_hidden(k4_tarski(X0,X3),X2) != iProver_top
% 7.97/1.50      | r2_hidden(k4_tarski(X0,X3),X1) != iProver_top
% 7.97/1.50      | v1_funct_1(k3_xboole_0(X1,X2)) != iProver_top
% 7.97/1.50      | v1_relat_1(k3_xboole_0(X1,X2)) != iProver_top ),
% 7.97/1.50      inference(superposition,[status(thm)],[c_758,c_744]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_2705,plain,
% 7.97/1.50      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 7.97/1.50      | r2_hidden(X0,k1_relat_1(k3_xboole_0(X2,X1))) = iProver_top
% 7.97/1.50      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X2) != iProver_top
% 7.97/1.50      | v1_funct_1(X1) != iProver_top
% 7.97/1.50      | v1_funct_1(k3_xboole_0(X2,X1)) != iProver_top
% 7.97/1.50      | v1_relat_1(X1) != iProver_top
% 7.97/1.50      | v1_relat_1(k3_xboole_0(X2,X1)) != iProver_top ),
% 7.97/1.50      inference(superposition,[status(thm)],[c_749,c_1708]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_9260,plain,
% 7.97/1.50      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 7.97/1.50      | r2_hidden(X0,k1_relat_1(k3_xboole_0(X1,X1))) = iProver_top
% 7.97/1.50      | v1_funct_1(X1) != iProver_top
% 7.97/1.50      | v1_funct_1(k3_xboole_0(X1,X1)) != iProver_top
% 7.97/1.50      | v1_relat_1(X1) != iProver_top
% 7.97/1.50      | v1_relat_1(k3_xboole_0(X1,X1)) != iProver_top ),
% 7.97/1.50      inference(superposition,[status(thm)],[c_749,c_2705]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_2031,plain,
% 7.97/1.50      ( r2_hidden(X0,k1_relat_1(k3_xboole_0(X1,X2))) != iProver_top
% 7.97/1.50      | r2_hidden(k4_tarski(X0,k1_funct_1(k3_xboole_0(X1,X2),X0)),X1) = iProver_top
% 7.97/1.50      | v1_funct_1(k3_xboole_0(X1,X2)) != iProver_top
% 7.97/1.50      | v1_relat_1(k3_xboole_0(X1,X2)) != iProver_top ),
% 7.97/1.50      inference(superposition,[status(thm)],[c_749,c_756]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_20,plain,
% 7.97/1.50      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 7.97/1.50      | ~ v1_funct_1(X2)
% 7.97/1.50      | ~ v1_relat_1(X2)
% 7.97/1.50      | k1_funct_1(X2,X0) = X1 ),
% 7.97/1.50      inference(cnf_transformation,[],[f54]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_745,plain,
% 7.97/1.50      ( k1_funct_1(X0,X1) = X2
% 7.97/1.50      | r2_hidden(k4_tarski(X1,X2),X0) != iProver_top
% 7.97/1.50      | v1_funct_1(X0) != iProver_top
% 7.97/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.97/1.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_2572,plain,
% 7.97/1.50      ( k1_funct_1(k3_xboole_0(X0,X1),X2) = k1_funct_1(X0,X2)
% 7.97/1.50      | r2_hidden(X2,k1_relat_1(k3_xboole_0(X0,X1))) != iProver_top
% 7.97/1.50      | v1_funct_1(X0) != iProver_top
% 7.97/1.50      | v1_funct_1(k3_xboole_0(X0,X1)) != iProver_top
% 7.97/1.50      | v1_relat_1(X0) != iProver_top
% 7.97/1.50      | v1_relat_1(k3_xboole_0(X0,X1)) != iProver_top ),
% 7.97/1.50      inference(superposition,[status(thm)],[c_2031,c_745]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_9390,plain,
% 7.97/1.50      ( k1_funct_1(k3_xboole_0(X0,X0),X1) = k1_funct_1(X0,X1)
% 7.97/1.50      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 7.97/1.50      | v1_funct_1(X0) != iProver_top
% 7.97/1.50      | v1_funct_1(k3_xboole_0(X0,X0)) != iProver_top
% 7.97/1.50      | v1_relat_1(X0) != iProver_top
% 7.97/1.50      | v1_relat_1(k3_xboole_0(X0,X0)) != iProver_top ),
% 7.97/1.50      inference(superposition,[status(thm)],[c_9260,c_2572]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_9442,plain,
% 7.97/1.50      ( k1_funct_1(k3_xboole_0(sK3,sK3),sK1) = k1_funct_1(sK3,sK1)
% 7.97/1.50      | v1_funct_1(k3_xboole_0(sK3,sK3)) != iProver_top
% 7.97/1.50      | v1_funct_1(sK3) != iProver_top
% 7.97/1.50      | v1_relat_1(k3_xboole_0(sK3,sK3)) != iProver_top
% 7.97/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.97/1.50      inference(superposition,[status(thm)],[c_1359,c_9390]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_25,negated_conjecture,
% 7.97/1.50      ( v1_relat_1(sK3) ),
% 7.97/1.50      inference(cnf_transformation,[],[f56]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_26,plain,
% 7.97/1.50      ( v1_relat_1(sK3) = iProver_top ),
% 7.97/1.50      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_24,negated_conjecture,
% 7.97/1.50      ( v1_funct_1(sK3) ),
% 7.97/1.50      inference(cnf_transformation,[],[f57]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_27,plain,
% 7.97/1.50      ( v1_funct_1(sK3) = iProver_top ),
% 7.97/1.50      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_2,plain,
% 7.97/1.50      ( r2_hidden(sK0(X0,X1,X2),X0)
% 7.97/1.50      | r2_hidden(sK0(X0,X1,X2),X2)
% 7.97/1.50      | k3_xboole_0(X0,X1) = X2 ),
% 7.97/1.50      inference(cnf_transformation,[],[f37]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_79,plain,
% 7.97/1.50      ( r2_hidden(sK0(sK3,sK3,sK3),sK3) | k3_xboole_0(sK3,sK3) = sK3 ),
% 7.97/1.50      inference(instantiation,[status(thm)],[c_2]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_0,plain,
% 7.97/1.50      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 7.97/1.50      | ~ r2_hidden(sK0(X0,X1,X2),X0)
% 7.97/1.50      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 7.97/1.50      | k3_xboole_0(X0,X1) = X2 ),
% 7.97/1.50      inference(cnf_transformation,[],[f39]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_83,plain,
% 7.97/1.50      ( ~ r2_hidden(sK0(sK3,sK3,sK3),sK3) | k3_xboole_0(sK3,sK3) = sK3 ),
% 7.97/1.50      inference(instantiation,[status(thm)],[c_0]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_408,plain,
% 7.97/1.50      ( ~ v1_relat_1(X0) | v1_relat_1(X1) | X1 != X0 ),
% 7.97/1.50      theory(equality) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_1353,plain,
% 7.97/1.50      ( ~ v1_relat_1(X0)
% 7.97/1.50      | v1_relat_1(k3_xboole_0(X1,sK3))
% 7.97/1.50      | k3_xboole_0(X1,sK3) != X0 ),
% 7.97/1.50      inference(instantiation,[status(thm)],[c_408]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_1354,plain,
% 7.97/1.50      ( k3_xboole_0(X0,sK3) != X1
% 7.97/1.50      | v1_relat_1(X1) != iProver_top
% 7.97/1.50      | v1_relat_1(k3_xboole_0(X0,sK3)) = iProver_top ),
% 7.97/1.50      inference(predicate_to_equality,[status(thm)],[c_1353]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_1356,plain,
% 7.97/1.50      ( k3_xboole_0(sK3,sK3) != sK3
% 7.97/1.50      | v1_relat_1(k3_xboole_0(sK3,sK3)) = iProver_top
% 7.97/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.97/1.50      inference(instantiation,[status(thm)],[c_1354]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_413,plain,
% 7.97/1.50      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 7.97/1.50      theory(equality) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_4219,plain,
% 7.97/1.50      ( ~ v1_funct_1(X0)
% 7.97/1.50      | v1_funct_1(k3_xboole_0(X1,sK3))
% 7.97/1.50      | k3_xboole_0(X1,sK3) != X0 ),
% 7.97/1.50      inference(instantiation,[status(thm)],[c_413]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_4220,plain,
% 7.97/1.50      ( k3_xboole_0(X0,sK3) != X1
% 7.97/1.50      | v1_funct_1(X1) != iProver_top
% 7.97/1.50      | v1_funct_1(k3_xboole_0(X0,sK3)) = iProver_top ),
% 7.97/1.50      inference(predicate_to_equality,[status(thm)],[c_4219]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_4222,plain,
% 7.97/1.50      ( k3_xboole_0(sK3,sK3) != sK3
% 7.97/1.50      | v1_funct_1(k3_xboole_0(sK3,sK3)) = iProver_top
% 7.97/1.50      | v1_funct_1(sK3) != iProver_top ),
% 7.97/1.50      inference(instantiation,[status(thm)],[c_4220]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_10425,plain,
% 7.97/1.50      ( v1_relat_1(k3_xboole_0(sK3,sK3)) != iProver_top
% 7.97/1.50      | k1_funct_1(k3_xboole_0(sK3,sK3),sK1) = k1_funct_1(sK3,sK1) ),
% 7.97/1.50      inference(global_propositional_subsumption,
% 7.97/1.50                [status(thm)],
% 7.97/1.50                [c_9442,c_26,c_27,c_79,c_83,c_1356,c_4222]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_10426,plain,
% 7.97/1.50      ( k1_funct_1(k3_xboole_0(sK3,sK3),sK1) = k1_funct_1(sK3,sK1)
% 7.97/1.50      | v1_relat_1(k3_xboole_0(sK3,sK3)) != iProver_top ),
% 7.97/1.50      inference(renaming,[status(thm)],[c_10425]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_10429,plain,
% 7.97/1.50      ( k1_funct_1(k3_xboole_0(sK3,sK3),sK1) = k1_funct_1(sK3,sK1) ),
% 7.97/1.50      inference(global_propositional_subsumption,
% 7.97/1.50                [status(thm)],
% 7.97/1.50                [c_10426,c_26,c_27,c_79,c_83,c_1356,c_4222,c_9442]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_10432,plain,
% 7.97/1.50      ( r2_hidden(k4_tarski(sK1,k1_funct_1(sK3,sK1)),k3_xboole_0(sK3,sK3)) = iProver_top
% 7.97/1.50      | r2_hidden(sK1,k1_relat_1(k3_xboole_0(sK3,sK3))) != iProver_top
% 7.97/1.50      | v1_funct_1(k3_xboole_0(sK3,sK3)) != iProver_top
% 7.97/1.50      | v1_relat_1(k3_xboole_0(sK3,sK3)) != iProver_top ),
% 7.97/1.50      inference(superposition,[status(thm)],[c_10429,c_749]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_1266,plain,
% 7.97/1.50      ( ~ r2_hidden(k4_tarski(sK1,X0),X1)
% 7.97/1.50      | r2_hidden(k4_tarski(sK1,X0),k3_xboole_0(X1,sK3))
% 7.97/1.50      | ~ r2_hidden(k4_tarski(sK1,X0),sK3) ),
% 7.97/1.50      inference(instantiation,[status(thm)],[c_3]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_2436,plain,
% 7.97/1.50      ( ~ r2_hidden(k4_tarski(sK1,k1_funct_1(sK3,sK1)),X0)
% 7.97/1.50      | r2_hidden(k4_tarski(sK1,k1_funct_1(sK3,sK1)),k3_xboole_0(X0,sK3))
% 7.97/1.50      | ~ r2_hidden(k4_tarski(sK1,k1_funct_1(sK3,sK1)),sK3) ),
% 7.97/1.50      inference(instantiation,[status(thm)],[c_1266]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_2437,plain,
% 7.97/1.50      ( r2_hidden(k4_tarski(sK1,k1_funct_1(sK3,sK1)),X0) != iProver_top
% 7.97/1.50      | r2_hidden(k4_tarski(sK1,k1_funct_1(sK3,sK1)),k3_xboole_0(X0,sK3)) = iProver_top
% 7.97/1.50      | r2_hidden(k4_tarski(sK1,k1_funct_1(sK3,sK1)),sK3) != iProver_top ),
% 7.97/1.50      inference(predicate_to_equality,[status(thm)],[c_2436]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_2439,plain,
% 7.97/1.50      ( r2_hidden(k4_tarski(sK1,k1_funct_1(sK3,sK1)),k3_xboole_0(sK3,sK3)) = iProver_top
% 7.97/1.50      | r2_hidden(k4_tarski(sK1,k1_funct_1(sK3,sK1)),sK3) != iProver_top ),
% 7.97/1.50      inference(instantiation,[status(thm)],[c_2437]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_5175,plain,
% 7.97/1.50      ( r2_hidden(k4_tarski(sK1,k1_funct_1(sK3,sK1)),sK3)
% 7.97/1.50      | ~ r2_hidden(sK1,k1_relat_1(sK3))
% 7.97/1.50      | ~ v1_funct_1(sK3)
% 7.97/1.50      | ~ v1_relat_1(sK3) ),
% 7.97/1.50      inference(instantiation,[status(thm)],[c_19]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_5176,plain,
% 7.97/1.50      ( r2_hidden(k4_tarski(sK1,k1_funct_1(sK3,sK1)),sK3) = iProver_top
% 7.97/1.50      | r2_hidden(sK1,k1_relat_1(sK3)) != iProver_top
% 7.97/1.50      | v1_funct_1(sK3) != iProver_top
% 7.97/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.97/1.50      inference(predicate_to_equality,[status(thm)],[c_5175]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_10504,plain,
% 7.97/1.50      ( r2_hidden(k4_tarski(sK1,k1_funct_1(sK3,sK1)),k3_xboole_0(sK3,sK3)) = iProver_top ),
% 7.97/1.50      inference(global_propositional_subsumption,
% 7.97/1.50                [status(thm)],
% 7.97/1.50                [c_10432,c_26,c_27,c_1359,c_2439,c_5176]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_8,plain,
% 7.97/1.50      ( ~ r2_hidden(X0,X1)
% 7.97/1.50      | ~ r2_hidden(k4_tarski(X0,X2),X3)
% 7.97/1.50      | r2_hidden(k4_tarski(X0,X2),k5_relat_1(k6_relat_1(X1),X3))
% 7.97/1.50      | ~ v1_relat_1(X3) ),
% 7.97/1.50      inference(cnf_transformation,[],[f44]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_753,plain,
% 7.97/1.50      ( r2_hidden(X0,X1) != iProver_top
% 7.97/1.50      | r2_hidden(k4_tarski(X0,X2),X3) != iProver_top
% 7.97/1.50      | r2_hidden(k4_tarski(X0,X2),k5_relat_1(k6_relat_1(X1),X3)) = iProver_top
% 7.97/1.50      | v1_relat_1(X3) != iProver_top ),
% 7.97/1.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_2212,plain,
% 7.97/1.50      ( r2_hidden(X0,X1) != iProver_top
% 7.97/1.50      | r2_hidden(X0,k1_relat_1(k5_relat_1(k6_relat_1(X1),X2))) = iProver_top
% 7.97/1.50      | r2_hidden(k4_tarski(X0,X3),X2) != iProver_top
% 7.97/1.50      | v1_funct_1(k5_relat_1(k6_relat_1(X1),X2)) != iProver_top
% 7.97/1.50      | v1_relat_1(X2) != iProver_top
% 7.97/1.50      | v1_relat_1(k5_relat_1(k6_relat_1(X1),X2)) != iProver_top ),
% 7.97/1.50      inference(superposition,[status(thm)],[c_753,c_744]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_10512,plain,
% 7.97/1.50      ( r2_hidden(sK1,X0) != iProver_top
% 7.97/1.50      | r2_hidden(sK1,k1_relat_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3)))) = iProver_top
% 7.97/1.50      | v1_funct_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3))) != iProver_top
% 7.97/1.50      | v1_relat_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3))) != iProver_top
% 7.97/1.50      | v1_relat_1(k3_xboole_0(sK3,sK3)) != iProver_top ),
% 7.97/1.50      inference(superposition,[status(thm)],[c_10504,c_2212]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_13267,plain,
% 7.97/1.50      ( v1_relat_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3))) != iProver_top
% 7.97/1.50      | v1_funct_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3))) != iProver_top
% 7.97/1.50      | r2_hidden(sK1,k1_relat_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3)))) = iProver_top
% 7.97/1.50      | r2_hidden(sK1,X0) != iProver_top ),
% 7.97/1.50      inference(global_propositional_subsumption,
% 7.97/1.50                [status(thm)],
% 7.97/1.50                [c_10512,c_26,c_79,c_83,c_1356]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_13268,plain,
% 7.97/1.50      ( r2_hidden(sK1,X0) != iProver_top
% 7.97/1.50      | r2_hidden(sK1,k1_relat_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3)))) = iProver_top
% 7.97/1.50      | v1_funct_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3))) != iProver_top
% 7.97/1.50      | v1_relat_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3))) != iProver_top ),
% 7.97/1.50      inference(renaming,[status(thm)],[c_13267]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_9,plain,
% 7.97/1.50      ( r2_hidden(k4_tarski(X0,X1),X2)
% 7.97/1.50      | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X3),X2))
% 7.97/1.50      | ~ v1_relat_1(X2) ),
% 7.97/1.50      inference(cnf_transformation,[],[f43]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_752,plain,
% 7.97/1.50      ( r2_hidden(k4_tarski(X0,X1),X2) = iProver_top
% 7.97/1.50      | r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X3),X2)) != iProver_top
% 7.97/1.50      | v1_relat_1(X2) != iProver_top ),
% 7.97/1.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_2033,plain,
% 7.97/1.50      ( r2_hidden(X0,k1_relat_1(k5_relat_1(k6_relat_1(X1),X2))) != iProver_top
% 7.97/1.50      | r2_hidden(k4_tarski(X0,k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)),X2) = iProver_top
% 7.97/1.50      | v1_funct_1(k5_relat_1(k6_relat_1(X1),X2)) != iProver_top
% 7.97/1.50      | v1_relat_1(X2) != iProver_top
% 7.97/1.50      | v1_relat_1(k5_relat_1(k6_relat_1(X1),X2)) != iProver_top ),
% 7.97/1.50      inference(superposition,[status(thm)],[c_749,c_752]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_3084,plain,
% 7.97/1.50      ( k1_funct_1(k5_relat_1(k6_relat_1(X0),X1),X2) = k1_funct_1(X1,X2)
% 7.97/1.50      | r2_hidden(X2,k1_relat_1(k5_relat_1(k6_relat_1(X0),X1))) != iProver_top
% 7.97/1.50      | v1_funct_1(X1) != iProver_top
% 7.97/1.50      | v1_funct_1(k5_relat_1(k6_relat_1(X0),X1)) != iProver_top
% 7.97/1.50      | v1_relat_1(X1) != iProver_top
% 7.97/1.50      | v1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) != iProver_top ),
% 7.97/1.50      inference(superposition,[status(thm)],[c_2033,c_745]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_13275,plain,
% 7.97/1.50      ( k1_funct_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3)),sK1) = k1_funct_1(k3_xboole_0(sK3,sK3),sK1)
% 7.97/1.50      | r2_hidden(sK1,X0) != iProver_top
% 7.97/1.50      | v1_funct_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3))) != iProver_top
% 7.97/1.50      | v1_funct_1(k3_xboole_0(sK3,sK3)) != iProver_top
% 7.97/1.50      | v1_relat_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3))) != iProver_top
% 7.97/1.50      | v1_relat_1(k3_xboole_0(sK3,sK3)) != iProver_top ),
% 7.97/1.50      inference(superposition,[status(thm)],[c_13268,c_3084]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_13277,plain,
% 7.97/1.50      ( k1_funct_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3)),sK1) = k1_funct_1(sK3,sK1)
% 7.97/1.50      | r2_hidden(sK1,X0) != iProver_top
% 7.97/1.50      | v1_funct_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3))) != iProver_top
% 7.97/1.50      | v1_funct_1(k3_xboole_0(sK3,sK3)) != iProver_top
% 7.97/1.50      | v1_relat_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3))) != iProver_top
% 7.97/1.50      | v1_relat_1(k3_xboole_0(sK3,sK3)) != iProver_top ),
% 7.97/1.50      inference(light_normalisation,[status(thm)],[c_13275,c_10429]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_2211,plain,
% 7.97/1.50      ( k1_funct_1(k5_relat_1(k6_relat_1(X0),X1),X2) = X3
% 7.97/1.50      | r2_hidden(X2,X0) != iProver_top
% 7.97/1.50      | r2_hidden(k4_tarski(X2,X3),X1) != iProver_top
% 7.97/1.50      | v1_funct_1(k5_relat_1(k6_relat_1(X0),X1)) != iProver_top
% 7.97/1.50      | v1_relat_1(X1) != iProver_top
% 7.97/1.50      | v1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) != iProver_top ),
% 7.97/1.50      inference(superposition,[status(thm)],[c_753,c_745]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_10514,plain,
% 7.97/1.50      ( k1_funct_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3)),sK1) = k1_funct_1(sK3,sK1)
% 7.97/1.50      | r2_hidden(sK1,X0) != iProver_top
% 7.97/1.50      | v1_funct_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3))) != iProver_top
% 7.97/1.50      | v1_relat_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3))) != iProver_top
% 7.97/1.50      | v1_relat_1(k3_xboole_0(sK3,sK3)) != iProver_top ),
% 7.97/1.50      inference(superposition,[status(thm)],[c_10504,c_2211]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_13285,plain,
% 7.97/1.50      ( v1_relat_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3))) != iProver_top
% 7.97/1.50      | k1_funct_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3)),sK1) = k1_funct_1(sK3,sK1)
% 7.97/1.50      | r2_hidden(sK1,X0) != iProver_top
% 7.97/1.50      | v1_funct_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3))) != iProver_top ),
% 7.97/1.50      inference(global_propositional_subsumption,
% 7.97/1.50                [status(thm)],
% 7.97/1.50                [c_13277,c_26,c_79,c_83,c_1356,c_10514]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_13286,plain,
% 7.97/1.50      ( k1_funct_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3)),sK1) = k1_funct_1(sK3,sK1)
% 7.97/1.50      | r2_hidden(sK1,X0) != iProver_top
% 7.97/1.50      | v1_funct_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3))) != iProver_top
% 7.97/1.50      | v1_relat_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3))) != iProver_top ),
% 7.97/1.50      inference(renaming,[status(thm)],[c_13285]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_13291,plain,
% 7.97/1.50      ( k1_funct_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3)),sK1) = k1_funct_1(sK3,sK1)
% 7.97/1.50      | r2_hidden(sK1,X0) != iProver_top
% 7.97/1.50      | v1_funct_1(k3_xboole_0(sK3,sK3)) != iProver_top
% 7.97/1.50      | v1_funct_1(k6_relat_1(X0)) != iProver_top
% 7.97/1.50      | v1_relat_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3))) != iProver_top
% 7.97/1.50      | v1_relat_1(k3_xboole_0(sK3,sK3)) != iProver_top
% 7.97/1.50      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 7.97/1.50      inference(superposition,[status(thm)],[c_748,c_13286]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_18,plain,
% 7.97/1.50      ( v1_relat_1(k6_relat_1(X0)) ),
% 7.97/1.50      inference(cnf_transformation,[],[f51]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_38,plain,
% 7.97/1.50      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 7.97/1.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_17,plain,
% 7.97/1.50      ( v1_funct_1(k6_relat_1(X0)) ),
% 7.97/1.50      inference(cnf_transformation,[],[f52]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_41,plain,
% 7.97/1.50      ( v1_funct_1(k6_relat_1(X0)) = iProver_top ),
% 7.97/1.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_13812,plain,
% 7.97/1.50      ( v1_relat_1(k3_xboole_0(sK3,sK3)) != iProver_top
% 7.97/1.50      | v1_relat_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3))) != iProver_top
% 7.97/1.50      | r2_hidden(sK1,X0) != iProver_top
% 7.97/1.50      | k1_funct_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3)),sK1) = k1_funct_1(sK3,sK1) ),
% 7.97/1.50      inference(global_propositional_subsumption,
% 7.97/1.50                [status(thm)],
% 7.97/1.50                [c_13291,c_26,c_27,c_38,c_41,c_79,c_83,c_1356,c_4222]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_13813,plain,
% 7.97/1.50      ( k1_funct_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3)),sK1) = k1_funct_1(sK3,sK1)
% 7.97/1.50      | r2_hidden(sK1,X0) != iProver_top
% 7.97/1.50      | v1_relat_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3))) != iProver_top
% 7.97/1.50      | v1_relat_1(k3_xboole_0(sK3,sK3)) != iProver_top ),
% 7.97/1.50      inference(renaming,[status(thm)],[c_13812]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_13818,plain,
% 7.97/1.50      ( v1_relat_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3))) != iProver_top
% 7.97/1.50      | r2_hidden(sK1,X0) != iProver_top
% 7.97/1.50      | k1_funct_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3)),sK1) = k1_funct_1(sK3,sK1) ),
% 7.97/1.50      inference(global_propositional_subsumption,
% 7.97/1.50                [status(thm)],
% 7.97/1.50                [c_13813,c_26,c_27,c_38,c_41,c_79,c_83,c_1356,c_4222,
% 7.97/1.50                 c_13291]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_13819,plain,
% 7.97/1.50      ( k1_funct_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3)),sK1) = k1_funct_1(sK3,sK1)
% 7.97/1.50      | r2_hidden(sK1,X0) != iProver_top
% 7.97/1.50      | v1_relat_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3))) != iProver_top ),
% 7.97/1.50      inference(renaming,[status(thm)],[c_13818]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_13824,plain,
% 7.97/1.50      ( k1_funct_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3)),sK1) = k1_funct_1(sK3,sK1)
% 7.97/1.50      | r2_hidden(sK1,X0) != iProver_top
% 7.97/1.50      | v1_relat_1(k3_xboole_0(sK3,sK3)) != iProver_top
% 7.97/1.50      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 7.97/1.50      inference(superposition,[status(thm)],[c_755,c_13819]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_13829,plain,
% 7.97/1.50      ( k1_funct_1(k5_relat_1(k6_relat_1(X0),k3_xboole_0(sK3,sK3)),sK1) = k1_funct_1(sK3,sK1)
% 7.97/1.50      | r2_hidden(sK1,X0) != iProver_top ),
% 7.97/1.50      inference(global_propositional_subsumption,
% 7.97/1.50                [status(thm)],
% 7.97/1.50                [c_13824,c_26,c_38,c_79,c_83,c_1356]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_13835,plain,
% 7.97/1.50      ( k1_funct_1(k5_relat_1(k6_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(sK3,sK3)),sK1) = k1_funct_1(sK3,sK1)
% 7.97/1.50      | r2_hidden(sK1,X1) != iProver_top
% 7.97/1.50      | r2_hidden(sK1,X0) != iProver_top ),
% 7.97/1.50      inference(superposition,[status(thm)],[c_758,c_13829]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_759,plain,
% 7.97/1.50      ( k3_xboole_0(X0,X1) = X2
% 7.97/1.50      | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
% 7.97/1.50      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 7.97/1.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_2376,plain,
% 7.97/1.50      ( k3_xboole_0(X0,X1) = X0
% 7.97/1.50      | r2_hidden(sK0(X0,X1,X0),X0) = iProver_top
% 7.97/1.50      | iProver_top != iProver_top ),
% 7.97/1.50      inference(equality_factoring,[status(thm)],[c_759]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_2378,plain,
% 7.97/1.50      ( k3_xboole_0(X0,X1) = X0
% 7.97/1.50      | r2_hidden(sK0(X0,X1,X0),X0) = iProver_top ),
% 7.97/1.50      inference(equality_resolution_simp,[status(thm)],[c_2376]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_761,plain,
% 7.97/1.50      ( k3_xboole_0(X0,X1) = X2
% 7.97/1.50      | r2_hidden(sK0(X0,X1,X2),X0) != iProver_top
% 7.97/1.50      | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top
% 7.97/1.50      | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top ),
% 7.97/1.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_14374,plain,
% 7.97/1.50      ( k3_xboole_0(X0,X1) = X0
% 7.97/1.50      | r2_hidden(sK0(X0,X1,X0),X0) != iProver_top
% 7.97/1.50      | r2_hidden(sK0(X0,X1,X0),X1) != iProver_top ),
% 7.97/1.50      inference(superposition,[status(thm)],[c_2378,c_761]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_14657,plain,
% 7.97/1.50      ( k3_xboole_0(X0,X1) = X0
% 7.97/1.50      | r2_hidden(sK0(X0,X1,X0),X1) != iProver_top ),
% 7.97/1.50      inference(global_propositional_subsumption,
% 7.97/1.50                [status(thm)],
% 7.97/1.50                [c_14374,c_2378]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_14673,plain,
% 7.97/1.50      ( k3_xboole_0(X0,X0) = X0 ),
% 7.97/1.50      inference(superposition,[status(thm)],[c_2378,c_14657]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_14766,plain,
% 7.97/1.50      ( k1_funct_1(k5_relat_1(k6_relat_1(k3_xboole_0(X0,X1)),sK3),sK1) = k1_funct_1(sK3,sK1)
% 7.97/1.50      | r2_hidden(sK1,X0) != iProver_top
% 7.97/1.50      | r2_hidden(sK1,X1) != iProver_top ),
% 7.97/1.50      inference(demodulation,[status(thm)],[c_13835,c_14673]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_14773,plain,
% 7.97/1.50      ( k1_funct_1(k5_relat_1(k6_relat_1(k3_xboole_0(sK2,X0)),sK3),sK1) = k1_funct_1(sK3,sK1)
% 7.97/1.50      | r2_hidden(sK1,X0) != iProver_top ),
% 7.97/1.50      inference(superposition,[status(thm)],[c_1472,c_14766]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_14986,plain,
% 7.97/1.50      ( k1_funct_1(k5_relat_1(k6_relat_1(k3_xboole_0(sK2,sK2)),sK3),sK1) = k1_funct_1(sK3,sK1) ),
% 7.97/1.50      inference(superposition,[status(thm)],[c_1472,c_14773]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_15002,plain,
% 7.97/1.50      ( k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1) = k1_funct_1(sK3,sK1) ),
% 7.97/1.50      inference(demodulation,[status(thm)],[c_14986,c_14673]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_403,plain,( X0 = X0 ),theory(equality) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_895,plain,
% 7.97/1.50      ( k1_funct_1(sK3,sK1) = k1_funct_1(sK3,sK1) ),
% 7.97/1.50      inference(instantiation,[status(thm)],[c_403]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_404,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_788,plain,
% 7.97/1.50      ( k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1) != X0
% 7.97/1.50      | k1_funct_1(sK3,sK1) != X0
% 7.97/1.50      | k1_funct_1(sK3,sK1) = k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1) ),
% 7.97/1.50      inference(instantiation,[status(thm)],[c_404]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_826,plain,
% 7.97/1.50      ( k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1) != k1_funct_1(sK3,sK1)
% 7.97/1.50      | k1_funct_1(sK3,sK1) = k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1)
% 7.97/1.50      | k1_funct_1(sK3,sK1) != k1_funct_1(sK3,sK1) ),
% 7.97/1.50      inference(instantiation,[status(thm)],[c_788]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_22,negated_conjecture,
% 7.97/1.50      ( k1_funct_1(sK3,sK1) != k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1) ),
% 7.97/1.50      inference(cnf_transformation,[],[f59]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(contradiction,plain,
% 7.97/1.50      ( $false ),
% 7.97/1.50      inference(minisat,[status(thm)],[c_15002,c_895,c_826,c_22]) ).
% 7.97/1.50  
% 7.97/1.50  
% 7.97/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.97/1.50  
% 7.97/1.50  ------                               Statistics
% 7.97/1.50  
% 7.97/1.50  ------ General
% 7.97/1.50  
% 7.97/1.50  abstr_ref_over_cycles:                  0
% 7.97/1.50  abstr_ref_under_cycles:                 0
% 7.97/1.50  gc_basic_clause_elim:                   0
% 7.97/1.50  forced_gc_time:                         0
% 7.97/1.50  parsing_time:                           0.016
% 7.97/1.50  unif_index_cands_time:                  0.
% 7.97/1.50  unif_index_add_time:                    0.
% 7.97/1.50  orderings_time:                         0.
% 7.97/1.50  out_proof_time:                         0.023
% 7.97/1.50  total_time:                             0.861
% 7.97/1.50  num_of_symbols:                         45
% 7.97/1.50  num_of_terms:                           46626
% 7.97/1.50  
% 7.97/1.50  ------ Preprocessing
% 7.97/1.50  
% 7.97/1.50  num_of_splits:                          0
% 7.97/1.50  num_of_split_atoms:                     0
% 7.97/1.50  num_of_reused_defs:                     0
% 7.97/1.50  num_eq_ax_congr_red:                    12
% 7.97/1.50  num_of_sem_filtered_clauses:            1
% 7.97/1.50  num_of_subtypes:                        0
% 7.97/1.50  monotx_restored_types:                  0
% 7.97/1.50  sat_num_of_epr_types:                   0
% 7.97/1.50  sat_num_of_non_cyclic_types:            0
% 7.97/1.50  sat_guarded_non_collapsed_types:        0
% 7.97/1.50  num_pure_diseq_elim:                    0
% 7.97/1.50  simp_replaced_by:                       0
% 7.97/1.50  res_preprocessed:                       111
% 7.97/1.50  prep_upred:                             0
% 7.97/1.50  prep_unflattend:                        0
% 7.97/1.50  smt_new_axioms:                         0
% 7.97/1.50  pred_elim_cands:                        3
% 7.97/1.50  pred_elim:                              0
% 7.97/1.50  pred_elim_cl:                           0
% 7.97/1.50  pred_elim_cycles:                       2
% 7.97/1.50  merged_defs:                            0
% 7.97/1.50  merged_defs_ncl:                        0
% 7.97/1.50  bin_hyper_res:                          0
% 7.97/1.50  prep_cycles:                            4
% 7.97/1.50  pred_elim_time:                         0.001
% 7.97/1.50  splitting_time:                         0.
% 7.97/1.50  sem_filter_time:                        0.
% 7.97/1.50  monotx_time:                            0.
% 7.97/1.50  subtype_inf_time:                       0.
% 7.97/1.50  
% 7.97/1.50  ------ Problem properties
% 7.97/1.50  
% 7.97/1.50  clauses:                                22
% 7.97/1.50  conjectures:                            4
% 7.97/1.50  epr:                                    2
% 7.97/1.50  horn:                                   19
% 7.97/1.50  ground:                                 4
% 7.97/1.50  unary:                                  6
% 7.97/1.50  binary:                                 2
% 7.97/1.50  lits:                                   62
% 7.97/1.50  lits_eq:                                6
% 7.97/1.50  fd_pure:                                0
% 7.97/1.50  fd_pseudo:                              0
% 7.97/1.50  fd_cond:                                0
% 7.97/1.50  fd_pseudo_cond:                         4
% 7.97/1.50  ac_symbols:                             0
% 7.97/1.50  
% 7.97/1.50  ------ Propositional Solver
% 7.97/1.50  
% 7.97/1.50  prop_solver_calls:                      30
% 7.97/1.50  prop_fast_solver_calls:                 1206
% 7.97/1.50  smt_solver_calls:                       0
% 7.97/1.50  smt_fast_solver_calls:                  0
% 7.97/1.50  prop_num_of_clauses:                    10879
% 7.97/1.50  prop_preprocess_simplified:             12184
% 7.97/1.50  prop_fo_subsumed:                       42
% 7.97/1.50  prop_solver_time:                       0.
% 7.97/1.50  smt_solver_time:                        0.
% 7.97/1.50  smt_fast_solver_time:                   0.
% 7.97/1.50  prop_fast_solver_time:                  0.
% 7.97/1.50  prop_unsat_core_time:                   0.001
% 7.97/1.50  
% 7.97/1.50  ------ QBF
% 7.97/1.50  
% 7.97/1.50  qbf_q_res:                              0
% 7.97/1.50  qbf_num_tautologies:                    0
% 7.97/1.50  qbf_prep_cycles:                        0
% 7.97/1.50  
% 7.97/1.50  ------ BMC1
% 7.97/1.50  
% 7.97/1.50  bmc1_current_bound:                     -1
% 7.97/1.50  bmc1_last_solved_bound:                 -1
% 7.97/1.50  bmc1_unsat_core_size:                   -1
% 7.97/1.50  bmc1_unsat_core_parents_size:           -1
% 7.97/1.50  bmc1_merge_next_fun:                    0
% 7.97/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.97/1.50  
% 7.97/1.50  ------ Instantiation
% 7.97/1.50  
% 7.97/1.50  inst_num_of_clauses:                    1348
% 7.97/1.50  inst_num_in_passive:                    477
% 7.97/1.50  inst_num_in_active:                     575
% 7.97/1.50  inst_num_in_unprocessed:                296
% 7.97/1.50  inst_num_of_loops:                      640
% 7.97/1.50  inst_num_of_learning_restarts:          0
% 7.97/1.50  inst_num_moves_active_passive:          62
% 7.97/1.50  inst_lit_activity:                      0
% 7.97/1.50  inst_lit_activity_moves:                0
% 7.97/1.50  inst_num_tautologies:                   0
% 7.97/1.50  inst_num_prop_implied:                  0
% 7.97/1.50  inst_num_existing_simplified:           0
% 7.97/1.50  inst_num_eq_res_simplified:             0
% 7.97/1.50  inst_num_child_elim:                    0
% 7.97/1.50  inst_num_of_dismatching_blockings:      559
% 7.97/1.50  inst_num_of_non_proper_insts:           914
% 7.97/1.50  inst_num_of_duplicates:                 0
% 7.97/1.50  inst_inst_num_from_inst_to_res:         0
% 7.97/1.50  inst_dismatching_checking_time:         0.
% 7.97/1.50  
% 7.97/1.50  ------ Resolution
% 7.97/1.50  
% 7.97/1.50  res_num_of_clauses:                     0
% 7.97/1.50  res_num_in_passive:                     0
% 7.97/1.50  res_num_in_active:                      0
% 7.97/1.50  res_num_of_loops:                       115
% 7.97/1.50  res_forward_subset_subsumed:            69
% 7.97/1.50  res_backward_subset_subsumed:           0
% 7.97/1.50  res_forward_subsumed:                   0
% 7.97/1.50  res_backward_subsumed:                  0
% 7.97/1.50  res_forward_subsumption_resolution:     0
% 7.97/1.50  res_backward_subsumption_resolution:    0
% 7.97/1.50  res_clause_to_clause_subsumption:       27630
% 7.97/1.50  res_orphan_elimination:                 0
% 7.97/1.50  res_tautology_del:                      37
% 7.97/1.50  res_num_eq_res_simplified:              0
% 7.97/1.50  res_num_sel_changes:                    0
% 7.97/1.50  res_moves_from_active_to_pass:          0
% 7.97/1.50  
% 7.97/1.50  ------ Superposition
% 7.97/1.50  
% 7.97/1.50  sup_time_total:                         0.
% 7.97/1.50  sup_time_generating:                    0.
% 7.97/1.50  sup_time_sim_full:                      0.
% 7.97/1.50  sup_time_sim_immed:                     0.
% 7.97/1.50  
% 7.97/1.50  sup_num_of_clauses:                     2237
% 7.97/1.50  sup_num_in_active:                      126
% 7.97/1.50  sup_num_in_passive:                     2111
% 7.97/1.50  sup_num_of_loops:                       127
% 7.97/1.50  sup_fw_superposition:                   879
% 7.97/1.50  sup_bw_superposition:                   1551
% 7.97/1.50  sup_immediate_simplified:               133
% 7.97/1.50  sup_given_eliminated:                   0
% 7.97/1.50  comparisons_done:                       0
% 7.97/1.50  comparisons_avoided:                    2
% 7.97/1.50  
% 7.97/1.50  ------ Simplifications
% 7.97/1.50  
% 7.97/1.50  
% 7.97/1.50  sim_fw_subset_subsumed:                 21
% 7.97/1.50  sim_bw_subset_subsumed:                 10
% 7.97/1.50  sim_fw_subsumed:                        79
% 7.97/1.50  sim_bw_subsumed:                        1
% 7.97/1.50  sim_fw_subsumption_res:                 0
% 7.97/1.50  sim_bw_subsumption_res:                 0
% 7.97/1.50  sim_tautology_del:                      45
% 7.97/1.50  sim_eq_tautology_del:                   10
% 7.97/1.50  sim_eq_res_simp:                        31
% 7.97/1.50  sim_fw_demodulated:                     21
% 7.97/1.50  sim_bw_demodulated:                     9
% 7.97/1.50  sim_light_normalised:                   7
% 7.97/1.50  sim_joinable_taut:                      0
% 7.97/1.50  sim_joinable_simp:                      0
% 7.97/1.50  sim_ac_normalised:                      0
% 7.97/1.50  sim_smt_subsumption:                    0
% 7.97/1.50  
%------------------------------------------------------------------------------
