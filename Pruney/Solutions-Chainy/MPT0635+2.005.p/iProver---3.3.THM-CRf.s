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
% DateTime   : Thu Dec  3 11:49:52 EST 2020

% Result     : Theorem 3.81s
% Output     : CNFRefutation 3.81s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 180 expanded)
%              Number of clauses        :   49 (  55 expanded)
%              Number of leaves         :   14 (  39 expanded)
%              Depth                    :   19
%              Number of atoms          :  385 ( 657 expanded)
%              Number of equality atoms :  140 ( 214 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f63,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f38,f39,f39])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
       => k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
         => k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)
      & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)
      & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f30,plain,
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

fof(f31,plain,
    ( k1_funct_1(sK3,sK1) != k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1)
    & r2_hidden(sK1,k3_xboole_0(k1_relat_1(sK3),sK2))
    & v1_funct_1(sK3)
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f20,f30])).

fof(f54,plain,(
    r2_hidden(sK1,k3_xboole_0(k1_relat_1(sK3),sK2)) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f56,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f40,f39])).

fof(f64,plain,(
    r2_hidden(sK1,k1_setfam_1(k1_enumset1(k1_relat_1(sK3),k1_relat_1(sK3),sK2))) ),
    inference(definition_unfolding,[],[f54,f56])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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
    inference(flattening,[],[f21])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f22])).

fof(f24,plain,(
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

fof(f25,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).

fof(f32,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f62,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k1_setfam_1(k1_enumset1(X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f32,f56])).

fof(f67,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k1_setfam_1(k1_enumset1(X0,X0,X1))) ) ),
    inference(equality_resolution,[],[f62])).

fof(f33,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f61,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k1_setfam_1(k1_enumset1(X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f33,f56])).

fof(f66,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k1_setfam_1(k1_enumset1(X0,X0,X1))) ) ),
    inference(equality_resolution,[],[f61])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f68,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f51])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X0,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X0,X2) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
          | ~ r2_hidden(k4_tarski(X0,X1),X3)
          | ~ r2_hidden(X0,X2) )
        & ( ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X0,X2) )
          | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
          | ~ r2_hidden(k4_tarski(X0,X1),X3)
          | ~ r2_hidden(X0,X2) )
        & ( ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X0,X2) )
          | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(flattening,[],[f26])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      | ~ r2_hidden(k4_tarski(X0,X1),X3)
      | ~ r2_hidden(X0,X2)
      | ~ v1_relat_1(X3) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f48,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f52,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f53,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f55,plain,(
    k1_funct_1(sK3,sK1) != k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_6,plain,
    ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_19,negated_conjecture,
    ( r2_hidden(sK1,k1_setfam_1(k1_enumset1(k1_relat_1(sK3),k1_relat_1(sK3),sK2))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_562,plain,
    ( r2_hidden(sK1,k1_setfam_1(k1_enumset1(k1_relat_1(sK3),k1_relat_1(sK3),sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1155,plain,
    ( r2_hidden(sK1,k1_setfam_1(k1_enumset1(sK2,sK2,k1_relat_1(sK3)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6,c_562])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_573,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1324,plain,
    ( r2_hidden(sK1,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1155,c_573])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_setfam_1(k1_enumset1(X2,X2,X1))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_574,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_setfam_1(k1_enumset1(X2,X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1493,plain,
    ( r2_hidden(sK1,k1_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1155,c_574])).

cnf(c_12,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_122,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12,c_7])).

cnf(c_123,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X0,X1)) ),
    inference(renaming,[status(thm)],[c_122])).

cnf(c_559,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_123])).

cnf(c_11,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | v1_funct_1(k5_relat_1(X1,X0))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_568,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(k5_relat_1(X0,X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_565,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),X3)
    | r2_hidden(k4_tarski(X0,X2),k5_relat_1(k6_relat_1(X1),X3))
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_571,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(k4_tarski(X0,X2),X3) != iProver_top
    | r2_hidden(k4_tarski(X0,X2),k5_relat_1(k6_relat_1(X1),X3)) = iProver_top
    | v1_relat_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_16,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_564,plain,
    ( k1_funct_1(X0,X1) = X2
    | r2_hidden(k4_tarski(X1,X2),X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2137,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1(X0),X1),X2) = X3
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(k4_tarski(X2,X3),X1) != iProver_top
    | v1_funct_1(k5_relat_1(k6_relat_1(X0),X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_571,c_564])).

cnf(c_3289,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1(X0),X1),X2) = k1_funct_1(X1,X2)
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(k5_relat_1(k6_relat_1(X0),X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_565,c_2137])).

cnf(c_4885,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1(X0),X1),X2) = k1_funct_1(X1,X2)
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(k6_relat_1(X0)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_568,c_3289])).

cnf(c_14,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_34,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_13,plain,
    ( v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_37,plain,
    ( v1_funct_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_5784,plain,
    ( v1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | k1_funct_1(k5_relat_1(k6_relat_1(X0),X1),X2) = k1_funct_1(X1,X2)
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4885,c_34,c_37])).

cnf(c_5785,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1(X0),X1),X2) = k1_funct_1(X1,X2)
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5784])).

cnf(c_5790,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1(X0),X1),X2) = k1_funct_1(X1,X2)
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_559,c_5785])).

cnf(c_5795,plain,
    ( v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | k1_funct_1(k5_relat_1(k6_relat_1(X0),X1),X2) = k1_funct_1(X1,X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5790,c_34])).

cnf(c_5796,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1(X0),X1),X2) = k1_funct_1(X1,X2)
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_5795])).

cnf(c_5806,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1(X0),sK3),sK1) = k1_funct_1(sK3,sK1)
    | r2_hidden(sK1,X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1493,c_5796])).

cnf(c_21,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_22,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_23,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_5914,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1(X0),sK3),sK1) = k1_funct_1(sK3,sK1)
    | r2_hidden(sK1,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5806,c_22,c_23])).

cnf(c_5921,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1) = k1_funct_1(sK3,sK1) ),
    inference(superposition,[status(thm)],[c_1324,c_5914])).

cnf(c_233,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_727,plain,
    ( k1_funct_1(sK3,sK1) = k1_funct_1(sK3,sK1) ),
    inference(instantiation,[status(thm)],[c_233])).

cnf(c_234,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_604,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1) != X0
    | k1_funct_1(sK3,sK1) != X0
    | k1_funct_1(sK3,sK1) = k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1) ),
    inference(instantiation,[status(thm)],[c_234])).

cnf(c_642,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1) != k1_funct_1(sK3,sK1)
    | k1_funct_1(sK3,sK1) = k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1)
    | k1_funct_1(sK3,sK1) != k1_funct_1(sK3,sK1) ),
    inference(instantiation,[status(thm)],[c_604])).

cnf(c_18,negated_conjecture,
    ( k1_funct_1(sK3,sK1) != k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1) ),
    inference(cnf_transformation,[],[f55])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5921,c_727,c_642,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:49:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.81/1.06  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.81/1.06  
% 3.81/1.06  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.81/1.06  
% 3.81/1.06  ------  iProver source info
% 3.81/1.06  
% 3.81/1.06  git: date: 2020-06-30 10:37:57 +0100
% 3.81/1.06  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.81/1.06  git: non_committed_changes: false
% 3.81/1.06  git: last_make_outside_of_git: false
% 3.81/1.06  
% 3.81/1.06  ------ 
% 3.81/1.06  
% 3.81/1.06  ------ Input Options
% 3.81/1.06  
% 3.81/1.06  --out_options                           all
% 3.81/1.06  --tptp_safe_out                         true
% 3.81/1.06  --problem_path                          ""
% 3.81/1.06  --include_path                          ""
% 3.81/1.06  --clausifier                            res/vclausify_rel
% 3.81/1.06  --clausifier_options                    ""
% 3.81/1.06  --stdin                                 false
% 3.81/1.06  --stats_out                             all
% 3.81/1.06  
% 3.81/1.06  ------ General Options
% 3.81/1.06  
% 3.81/1.06  --fof                                   false
% 3.81/1.06  --time_out_real                         305.
% 3.81/1.06  --time_out_virtual                      -1.
% 3.81/1.06  --symbol_type_check                     false
% 3.81/1.06  --clausify_out                          false
% 3.81/1.06  --sig_cnt_out                           false
% 3.81/1.06  --trig_cnt_out                          false
% 3.81/1.06  --trig_cnt_out_tolerance                1.
% 3.81/1.06  --trig_cnt_out_sk_spl                   false
% 3.81/1.06  --abstr_cl_out                          false
% 3.81/1.06  
% 3.81/1.06  ------ Global Options
% 3.81/1.06  
% 3.81/1.06  --schedule                              default
% 3.81/1.06  --add_important_lit                     false
% 3.81/1.06  --prop_solver_per_cl                    1000
% 3.81/1.06  --min_unsat_core                        false
% 3.81/1.06  --soft_assumptions                      false
% 3.81/1.06  --soft_lemma_size                       3
% 3.81/1.06  --prop_impl_unit_size                   0
% 3.81/1.06  --prop_impl_unit                        []
% 3.81/1.06  --share_sel_clauses                     true
% 3.81/1.06  --reset_solvers                         false
% 3.81/1.06  --bc_imp_inh                            [conj_cone]
% 3.81/1.06  --conj_cone_tolerance                   3.
% 3.81/1.06  --extra_neg_conj                        none
% 3.81/1.06  --large_theory_mode                     true
% 3.81/1.06  --prolific_symb_bound                   200
% 3.81/1.06  --lt_threshold                          2000
% 3.81/1.06  --clause_weak_htbl                      true
% 3.81/1.06  --gc_record_bc_elim                     false
% 3.81/1.06  
% 3.81/1.06  ------ Preprocessing Options
% 3.81/1.06  
% 3.81/1.06  --preprocessing_flag                    true
% 3.81/1.06  --time_out_prep_mult                    0.1
% 3.81/1.06  --splitting_mode                        input
% 3.81/1.06  --splitting_grd                         true
% 3.81/1.06  --splitting_cvd                         false
% 3.81/1.06  --splitting_cvd_svl                     false
% 3.81/1.06  --splitting_nvd                         32
% 3.81/1.06  --sub_typing                            true
% 3.81/1.06  --prep_gs_sim                           true
% 3.81/1.06  --prep_unflatten                        true
% 3.81/1.06  --prep_res_sim                          true
% 3.81/1.06  --prep_upred                            true
% 3.81/1.06  --prep_sem_filter                       exhaustive
% 3.81/1.06  --prep_sem_filter_out                   false
% 3.81/1.06  --pred_elim                             true
% 3.81/1.06  --res_sim_input                         true
% 3.81/1.06  --eq_ax_congr_red                       true
% 3.81/1.06  --pure_diseq_elim                       true
% 3.81/1.06  --brand_transform                       false
% 3.81/1.06  --non_eq_to_eq                          false
% 3.81/1.06  --prep_def_merge                        true
% 3.81/1.06  --prep_def_merge_prop_impl              false
% 3.81/1.06  --prep_def_merge_mbd                    true
% 3.81/1.06  --prep_def_merge_tr_red                 false
% 3.81/1.06  --prep_def_merge_tr_cl                  false
% 3.81/1.06  --smt_preprocessing                     true
% 3.81/1.06  --smt_ac_axioms                         fast
% 3.81/1.06  --preprocessed_out                      false
% 3.81/1.06  --preprocessed_stats                    false
% 3.81/1.06  
% 3.81/1.06  ------ Abstraction refinement Options
% 3.81/1.06  
% 3.81/1.06  --abstr_ref                             []
% 3.81/1.06  --abstr_ref_prep                        false
% 3.81/1.06  --abstr_ref_until_sat                   false
% 3.81/1.06  --abstr_ref_sig_restrict                funpre
% 3.81/1.06  --abstr_ref_af_restrict_to_split_sk     false
% 3.81/1.06  --abstr_ref_under                       []
% 3.81/1.06  
% 3.81/1.06  ------ SAT Options
% 3.81/1.06  
% 3.81/1.06  --sat_mode                              false
% 3.81/1.06  --sat_fm_restart_options                ""
% 3.81/1.06  --sat_gr_def                            false
% 3.81/1.06  --sat_epr_types                         true
% 3.81/1.06  --sat_non_cyclic_types                  false
% 3.81/1.06  --sat_finite_models                     false
% 3.81/1.06  --sat_fm_lemmas                         false
% 3.81/1.06  --sat_fm_prep                           false
% 3.81/1.06  --sat_fm_uc_incr                        true
% 3.81/1.06  --sat_out_model                         small
% 3.81/1.06  --sat_out_clauses                       false
% 3.81/1.06  
% 3.81/1.06  ------ QBF Options
% 3.81/1.06  
% 3.81/1.06  --qbf_mode                              false
% 3.81/1.06  --qbf_elim_univ                         false
% 3.81/1.06  --qbf_dom_inst                          none
% 3.81/1.06  --qbf_dom_pre_inst                      false
% 3.81/1.06  --qbf_sk_in                             false
% 3.81/1.06  --qbf_pred_elim                         true
% 3.81/1.06  --qbf_split                             512
% 3.81/1.06  
% 3.81/1.06  ------ BMC1 Options
% 3.81/1.06  
% 3.81/1.06  --bmc1_incremental                      false
% 3.81/1.06  --bmc1_axioms                           reachable_all
% 3.81/1.06  --bmc1_min_bound                        0
% 3.81/1.06  --bmc1_max_bound                        -1
% 3.81/1.06  --bmc1_max_bound_default                -1
% 3.81/1.06  --bmc1_symbol_reachability              true
% 3.81/1.06  --bmc1_property_lemmas                  false
% 3.81/1.06  --bmc1_k_induction                      false
% 3.81/1.06  --bmc1_non_equiv_states                 false
% 3.81/1.06  --bmc1_deadlock                         false
% 3.81/1.06  --bmc1_ucm                              false
% 3.81/1.06  --bmc1_add_unsat_core                   none
% 3.81/1.06  --bmc1_unsat_core_children              false
% 3.81/1.06  --bmc1_unsat_core_extrapolate_axioms    false
% 3.81/1.06  --bmc1_out_stat                         full
% 3.81/1.06  --bmc1_ground_init                      false
% 3.81/1.06  --bmc1_pre_inst_next_state              false
% 3.81/1.06  --bmc1_pre_inst_state                   false
% 3.81/1.06  --bmc1_pre_inst_reach_state             false
% 3.81/1.06  --bmc1_out_unsat_core                   false
% 3.81/1.06  --bmc1_aig_witness_out                  false
% 3.81/1.06  --bmc1_verbose                          false
% 3.81/1.06  --bmc1_dump_clauses_tptp                false
% 3.81/1.06  --bmc1_dump_unsat_core_tptp             false
% 3.81/1.06  --bmc1_dump_file                        -
% 3.81/1.06  --bmc1_ucm_expand_uc_limit              128
% 3.81/1.06  --bmc1_ucm_n_expand_iterations          6
% 3.81/1.06  --bmc1_ucm_extend_mode                  1
% 3.81/1.06  --bmc1_ucm_init_mode                    2
% 3.81/1.06  --bmc1_ucm_cone_mode                    none
% 3.81/1.06  --bmc1_ucm_reduced_relation_type        0
% 3.81/1.06  --bmc1_ucm_relax_model                  4
% 3.81/1.06  --bmc1_ucm_full_tr_after_sat            true
% 3.81/1.06  --bmc1_ucm_expand_neg_assumptions       false
% 3.81/1.06  --bmc1_ucm_layered_model                none
% 3.81/1.06  --bmc1_ucm_max_lemma_size               10
% 3.81/1.06  
% 3.81/1.06  ------ AIG Options
% 3.81/1.06  
% 3.81/1.06  --aig_mode                              false
% 3.81/1.06  
% 3.81/1.06  ------ Instantiation Options
% 3.81/1.06  
% 3.81/1.06  --instantiation_flag                    true
% 3.81/1.06  --inst_sos_flag                         true
% 3.81/1.06  --inst_sos_phase                        true
% 3.81/1.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.81/1.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.81/1.06  --inst_lit_sel_side                     num_symb
% 3.81/1.06  --inst_solver_per_active                1400
% 3.81/1.06  --inst_solver_calls_frac                1.
% 3.81/1.06  --inst_passive_queue_type               priority_queues
% 3.81/1.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.81/1.06  --inst_passive_queues_freq              [25;2]
% 3.81/1.06  --inst_dismatching                      true
% 3.81/1.06  --inst_eager_unprocessed_to_passive     true
% 3.81/1.06  --inst_prop_sim_given                   true
% 3.81/1.06  --inst_prop_sim_new                     false
% 3.81/1.06  --inst_subs_new                         false
% 3.81/1.06  --inst_eq_res_simp                      false
% 3.81/1.06  --inst_subs_given                       false
% 3.81/1.06  --inst_orphan_elimination               true
% 3.81/1.06  --inst_learning_loop_flag               true
% 3.81/1.06  --inst_learning_start                   3000
% 3.81/1.06  --inst_learning_factor                  2
% 3.81/1.06  --inst_start_prop_sim_after_learn       3
% 3.81/1.06  --inst_sel_renew                        solver
% 3.81/1.06  --inst_lit_activity_flag                true
% 3.81/1.06  --inst_restr_to_given                   false
% 3.81/1.06  --inst_activity_threshold               500
% 3.81/1.06  --inst_out_proof                        true
% 3.81/1.06  
% 3.81/1.06  ------ Resolution Options
% 3.81/1.06  
% 3.81/1.06  --resolution_flag                       true
% 3.81/1.06  --res_lit_sel                           adaptive
% 3.81/1.06  --res_lit_sel_side                      none
% 3.81/1.06  --res_ordering                          kbo
% 3.81/1.06  --res_to_prop_solver                    active
% 3.81/1.06  --res_prop_simpl_new                    false
% 3.81/1.06  --res_prop_simpl_given                  true
% 3.81/1.06  --res_passive_queue_type                priority_queues
% 3.81/1.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.81/1.06  --res_passive_queues_freq               [15;5]
% 3.81/1.06  --res_forward_subs                      full
% 3.81/1.06  --res_backward_subs                     full
% 3.81/1.06  --res_forward_subs_resolution           true
% 3.81/1.06  --res_backward_subs_resolution          true
% 3.81/1.06  --res_orphan_elimination                true
% 3.81/1.06  --res_time_limit                        2.
% 3.81/1.06  --res_out_proof                         true
% 3.81/1.06  
% 3.81/1.06  ------ Superposition Options
% 3.81/1.06  
% 3.81/1.06  --superposition_flag                    true
% 3.81/1.06  --sup_passive_queue_type                priority_queues
% 3.81/1.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.81/1.06  --sup_passive_queues_freq               [8;1;4]
% 3.81/1.06  --demod_completeness_check              fast
% 3.81/1.06  --demod_use_ground                      true
% 3.81/1.06  --sup_to_prop_solver                    passive
% 3.81/1.06  --sup_prop_simpl_new                    true
% 3.81/1.06  --sup_prop_simpl_given                  true
% 3.81/1.06  --sup_fun_splitting                     true
% 3.81/1.06  --sup_smt_interval                      50000
% 3.81/1.06  
% 3.81/1.06  ------ Superposition Simplification Setup
% 3.81/1.06  
% 3.81/1.06  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.81/1.06  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.81/1.06  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.81/1.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.81/1.06  --sup_full_triv                         [TrivRules;PropSubs]
% 3.81/1.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.81/1.06  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.81/1.06  --sup_immed_triv                        [TrivRules]
% 3.81/1.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.81/1.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.81/1.06  --sup_immed_bw_main                     []
% 3.81/1.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.81/1.06  --sup_input_triv                        [Unflattening;TrivRules]
% 3.81/1.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.81/1.06  --sup_input_bw                          []
% 3.81/1.06  
% 3.81/1.06  ------ Combination Options
% 3.81/1.06  
% 3.81/1.06  --comb_res_mult                         3
% 3.81/1.06  --comb_sup_mult                         2
% 3.81/1.06  --comb_inst_mult                        10
% 3.81/1.06  
% 3.81/1.06  ------ Debug Options
% 3.81/1.06  
% 3.81/1.06  --dbg_backtrace                         false
% 3.81/1.06  --dbg_dump_prop_clauses                 false
% 3.81/1.06  --dbg_dump_prop_clauses_file            -
% 3.81/1.06  --dbg_out_stat                          false
% 3.81/1.06  ------ Parsing...
% 3.81/1.06  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.81/1.06  
% 3.81/1.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.81/1.06  
% 3.81/1.06  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.81/1.06  
% 3.81/1.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.81/1.06  ------ Proving...
% 3.81/1.06  ------ Problem Properties 
% 3.81/1.06  
% 3.81/1.06  
% 3.81/1.06  clauses                                 22
% 3.81/1.06  conjectures                             4
% 3.81/1.06  EPR                                     2
% 3.81/1.06  Horn                                    20
% 3.81/1.06  unary                                   7
% 3.81/1.06  binary                                  2
% 3.81/1.06  lits                                    57
% 3.81/1.06  lits eq                                 6
% 3.81/1.06  fd_pure                                 0
% 3.81/1.06  fd_pseudo                               0
% 3.81/1.06  fd_cond                                 0
% 3.81/1.06  fd_pseudo_cond                          4
% 3.81/1.06  AC symbols                              0
% 3.81/1.06  
% 3.81/1.06  ------ Schedule dynamic 5 is on 
% 3.81/1.06  
% 3.81/1.06  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.81/1.06  
% 3.81/1.06  
% 3.81/1.06  ------ 
% 3.81/1.06  Current options:
% 3.81/1.06  ------ 
% 3.81/1.06  
% 3.81/1.06  ------ Input Options
% 3.81/1.06  
% 3.81/1.06  --out_options                           all
% 3.81/1.06  --tptp_safe_out                         true
% 3.81/1.06  --problem_path                          ""
% 3.81/1.06  --include_path                          ""
% 3.81/1.06  --clausifier                            res/vclausify_rel
% 3.81/1.06  --clausifier_options                    ""
% 3.81/1.06  --stdin                                 false
% 3.81/1.06  --stats_out                             all
% 3.81/1.06  
% 3.81/1.06  ------ General Options
% 3.81/1.06  
% 3.81/1.06  --fof                                   false
% 3.81/1.06  --time_out_real                         305.
% 3.81/1.06  --time_out_virtual                      -1.
% 3.81/1.06  --symbol_type_check                     false
% 3.81/1.06  --clausify_out                          false
% 3.81/1.06  --sig_cnt_out                           false
% 3.81/1.06  --trig_cnt_out                          false
% 3.81/1.06  --trig_cnt_out_tolerance                1.
% 3.81/1.06  --trig_cnt_out_sk_spl                   false
% 3.81/1.06  --abstr_cl_out                          false
% 3.81/1.06  
% 3.81/1.06  ------ Global Options
% 3.81/1.06  
% 3.81/1.06  --schedule                              default
% 3.81/1.06  --add_important_lit                     false
% 3.81/1.06  --prop_solver_per_cl                    1000
% 3.81/1.06  --min_unsat_core                        false
% 3.81/1.06  --soft_assumptions                      false
% 3.81/1.06  --soft_lemma_size                       3
% 3.81/1.06  --prop_impl_unit_size                   0
% 3.81/1.06  --prop_impl_unit                        []
% 3.81/1.06  --share_sel_clauses                     true
% 3.81/1.06  --reset_solvers                         false
% 3.81/1.06  --bc_imp_inh                            [conj_cone]
% 3.81/1.06  --conj_cone_tolerance                   3.
% 3.81/1.06  --extra_neg_conj                        none
% 3.81/1.06  --large_theory_mode                     true
% 3.81/1.06  --prolific_symb_bound                   200
% 3.81/1.06  --lt_threshold                          2000
% 3.81/1.06  --clause_weak_htbl                      true
% 3.81/1.06  --gc_record_bc_elim                     false
% 3.81/1.06  
% 3.81/1.06  ------ Preprocessing Options
% 3.81/1.06  
% 3.81/1.06  --preprocessing_flag                    true
% 3.81/1.06  --time_out_prep_mult                    0.1
% 3.81/1.06  --splitting_mode                        input
% 3.81/1.06  --splitting_grd                         true
% 3.81/1.06  --splitting_cvd                         false
% 3.81/1.06  --splitting_cvd_svl                     false
% 3.81/1.06  --splitting_nvd                         32
% 3.81/1.06  --sub_typing                            true
% 3.81/1.06  --prep_gs_sim                           true
% 3.81/1.06  --prep_unflatten                        true
% 3.81/1.06  --prep_res_sim                          true
% 3.81/1.06  --prep_upred                            true
% 3.81/1.06  --prep_sem_filter                       exhaustive
% 3.81/1.06  --prep_sem_filter_out                   false
% 3.81/1.06  --pred_elim                             true
% 3.81/1.06  --res_sim_input                         true
% 3.81/1.06  --eq_ax_congr_red                       true
% 3.81/1.06  --pure_diseq_elim                       true
% 3.81/1.06  --brand_transform                       false
% 3.81/1.06  --non_eq_to_eq                          false
% 3.81/1.06  --prep_def_merge                        true
% 3.81/1.06  --prep_def_merge_prop_impl              false
% 3.81/1.06  --prep_def_merge_mbd                    true
% 3.81/1.06  --prep_def_merge_tr_red                 false
% 3.81/1.06  --prep_def_merge_tr_cl                  false
% 3.81/1.06  --smt_preprocessing                     true
% 3.81/1.06  --smt_ac_axioms                         fast
% 3.81/1.06  --preprocessed_out                      false
% 3.81/1.06  --preprocessed_stats                    false
% 3.81/1.06  
% 3.81/1.06  ------ Abstraction refinement Options
% 3.81/1.06  
% 3.81/1.06  --abstr_ref                             []
% 3.81/1.06  --abstr_ref_prep                        false
% 3.81/1.06  --abstr_ref_until_sat                   false
% 3.81/1.06  --abstr_ref_sig_restrict                funpre
% 3.81/1.06  --abstr_ref_af_restrict_to_split_sk     false
% 3.81/1.06  --abstr_ref_under                       []
% 3.81/1.06  
% 3.81/1.06  ------ SAT Options
% 3.81/1.06  
% 3.81/1.06  --sat_mode                              false
% 3.81/1.06  --sat_fm_restart_options                ""
% 3.81/1.06  --sat_gr_def                            false
% 3.81/1.06  --sat_epr_types                         true
% 3.81/1.06  --sat_non_cyclic_types                  false
% 3.81/1.06  --sat_finite_models                     false
% 3.81/1.06  --sat_fm_lemmas                         false
% 3.81/1.06  --sat_fm_prep                           false
% 3.81/1.06  --sat_fm_uc_incr                        true
% 3.81/1.06  --sat_out_model                         small
% 3.81/1.06  --sat_out_clauses                       false
% 3.81/1.06  
% 3.81/1.06  ------ QBF Options
% 3.81/1.06  
% 3.81/1.06  --qbf_mode                              false
% 3.81/1.06  --qbf_elim_univ                         false
% 3.81/1.06  --qbf_dom_inst                          none
% 3.81/1.06  --qbf_dom_pre_inst                      false
% 3.81/1.06  --qbf_sk_in                             false
% 3.81/1.06  --qbf_pred_elim                         true
% 3.81/1.06  --qbf_split                             512
% 3.81/1.06  
% 3.81/1.06  ------ BMC1 Options
% 3.81/1.06  
% 3.81/1.06  --bmc1_incremental                      false
% 3.81/1.06  --bmc1_axioms                           reachable_all
% 3.81/1.06  --bmc1_min_bound                        0
% 3.81/1.06  --bmc1_max_bound                        -1
% 3.81/1.06  --bmc1_max_bound_default                -1
% 3.81/1.06  --bmc1_symbol_reachability              true
% 3.81/1.06  --bmc1_property_lemmas                  false
% 3.81/1.06  --bmc1_k_induction                      false
% 3.81/1.06  --bmc1_non_equiv_states                 false
% 3.81/1.06  --bmc1_deadlock                         false
% 3.81/1.06  --bmc1_ucm                              false
% 3.81/1.06  --bmc1_add_unsat_core                   none
% 3.81/1.06  --bmc1_unsat_core_children              false
% 3.81/1.06  --bmc1_unsat_core_extrapolate_axioms    false
% 3.81/1.06  --bmc1_out_stat                         full
% 3.81/1.06  --bmc1_ground_init                      false
% 3.81/1.06  --bmc1_pre_inst_next_state              false
% 3.81/1.06  --bmc1_pre_inst_state                   false
% 3.81/1.06  --bmc1_pre_inst_reach_state             false
% 3.81/1.06  --bmc1_out_unsat_core                   false
% 3.81/1.06  --bmc1_aig_witness_out                  false
% 3.81/1.06  --bmc1_verbose                          false
% 3.81/1.06  --bmc1_dump_clauses_tptp                false
% 3.81/1.06  --bmc1_dump_unsat_core_tptp             false
% 3.81/1.06  --bmc1_dump_file                        -
% 3.81/1.06  --bmc1_ucm_expand_uc_limit              128
% 3.81/1.06  --bmc1_ucm_n_expand_iterations          6
% 3.81/1.06  --bmc1_ucm_extend_mode                  1
% 3.81/1.06  --bmc1_ucm_init_mode                    2
% 3.81/1.06  --bmc1_ucm_cone_mode                    none
% 3.81/1.06  --bmc1_ucm_reduced_relation_type        0
% 3.81/1.06  --bmc1_ucm_relax_model                  4
% 3.81/1.06  --bmc1_ucm_full_tr_after_sat            true
% 3.81/1.06  --bmc1_ucm_expand_neg_assumptions       false
% 3.81/1.06  --bmc1_ucm_layered_model                none
% 3.81/1.06  --bmc1_ucm_max_lemma_size               10
% 3.81/1.06  
% 3.81/1.06  ------ AIG Options
% 3.81/1.06  
% 3.81/1.06  --aig_mode                              false
% 3.81/1.06  
% 3.81/1.06  ------ Instantiation Options
% 3.81/1.06  
% 3.81/1.06  --instantiation_flag                    true
% 3.81/1.06  --inst_sos_flag                         true
% 3.81/1.06  --inst_sos_phase                        true
% 3.81/1.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.81/1.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.81/1.06  --inst_lit_sel_side                     none
% 3.81/1.06  --inst_solver_per_active                1400
% 3.81/1.06  --inst_solver_calls_frac                1.
% 3.81/1.06  --inst_passive_queue_type               priority_queues
% 3.81/1.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.81/1.06  --inst_passive_queues_freq              [25;2]
% 3.81/1.06  --inst_dismatching                      true
% 3.81/1.06  --inst_eager_unprocessed_to_passive     true
% 3.81/1.06  --inst_prop_sim_given                   true
% 3.81/1.06  --inst_prop_sim_new                     false
% 3.81/1.06  --inst_subs_new                         false
% 3.81/1.06  --inst_eq_res_simp                      false
% 3.81/1.06  --inst_subs_given                       false
% 3.81/1.06  --inst_orphan_elimination               true
% 3.81/1.06  --inst_learning_loop_flag               true
% 3.81/1.06  --inst_learning_start                   3000
% 3.81/1.06  --inst_learning_factor                  2
% 3.81/1.06  --inst_start_prop_sim_after_learn       3
% 3.81/1.06  --inst_sel_renew                        solver
% 3.81/1.06  --inst_lit_activity_flag                true
% 3.81/1.06  --inst_restr_to_given                   false
% 3.81/1.06  --inst_activity_threshold               500
% 3.81/1.06  --inst_out_proof                        true
% 3.81/1.06  
% 3.81/1.06  ------ Resolution Options
% 3.81/1.06  
% 3.81/1.06  --resolution_flag                       false
% 3.81/1.06  --res_lit_sel                           adaptive
% 3.81/1.06  --res_lit_sel_side                      none
% 3.81/1.06  --res_ordering                          kbo
% 3.81/1.06  --res_to_prop_solver                    active
% 3.81/1.06  --res_prop_simpl_new                    false
% 3.81/1.06  --res_prop_simpl_given                  true
% 3.81/1.06  --res_passive_queue_type                priority_queues
% 3.81/1.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.81/1.06  --res_passive_queues_freq               [15;5]
% 3.81/1.06  --res_forward_subs                      full
% 3.81/1.06  --res_backward_subs                     full
% 3.81/1.06  --res_forward_subs_resolution           true
% 3.81/1.06  --res_backward_subs_resolution          true
% 3.81/1.06  --res_orphan_elimination                true
% 3.81/1.06  --res_time_limit                        2.
% 3.81/1.06  --res_out_proof                         true
% 3.81/1.06  
% 3.81/1.06  ------ Superposition Options
% 3.81/1.06  
% 3.81/1.06  --superposition_flag                    true
% 3.81/1.06  --sup_passive_queue_type                priority_queues
% 3.81/1.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.81/1.06  --sup_passive_queues_freq               [8;1;4]
% 3.81/1.06  --demod_completeness_check              fast
% 3.81/1.06  --demod_use_ground                      true
% 3.81/1.06  --sup_to_prop_solver                    passive
% 3.81/1.06  --sup_prop_simpl_new                    true
% 3.81/1.06  --sup_prop_simpl_given                  true
% 3.81/1.06  --sup_fun_splitting                     true
% 3.81/1.06  --sup_smt_interval                      50000
% 3.81/1.06  
% 3.81/1.06  ------ Superposition Simplification Setup
% 3.81/1.06  
% 3.81/1.06  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.81/1.06  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.81/1.06  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.81/1.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.81/1.06  --sup_full_triv                         [TrivRules;PropSubs]
% 3.81/1.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.81/1.06  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.81/1.06  --sup_immed_triv                        [TrivRules]
% 3.81/1.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.81/1.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.81/1.06  --sup_immed_bw_main                     []
% 3.81/1.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.81/1.06  --sup_input_triv                        [Unflattening;TrivRules]
% 3.81/1.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.81/1.06  --sup_input_bw                          []
% 3.81/1.06  
% 3.81/1.06  ------ Combination Options
% 3.81/1.06  
% 3.81/1.06  --comb_res_mult                         3
% 3.81/1.06  --comb_sup_mult                         2
% 3.81/1.06  --comb_inst_mult                        10
% 3.81/1.06  
% 3.81/1.06  ------ Debug Options
% 3.81/1.06  
% 3.81/1.06  --dbg_backtrace                         false
% 3.81/1.06  --dbg_dump_prop_clauses                 false
% 3.81/1.06  --dbg_dump_prop_clauses_file            -
% 3.81/1.06  --dbg_out_stat                          false
% 3.81/1.06  
% 3.81/1.06  
% 3.81/1.06  
% 3.81/1.06  
% 3.81/1.06  ------ Proving...
% 3.81/1.06  
% 3.81/1.06  
% 3.81/1.06  % SZS status Theorem for theBenchmark.p
% 3.81/1.06  
% 3.81/1.06  % SZS output start CNFRefutation for theBenchmark.p
% 3.81/1.06  
% 3.81/1.06  fof(f2,axiom,(
% 3.81/1.06    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.81/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/1.06  
% 3.81/1.06  fof(f38,plain,(
% 3.81/1.06    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.81/1.06    inference(cnf_transformation,[],[f2])).
% 3.81/1.06  
% 3.81/1.06  fof(f3,axiom,(
% 3.81/1.06    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.81/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/1.06  
% 3.81/1.06  fof(f39,plain,(
% 3.81/1.06    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.81/1.06    inference(cnf_transformation,[],[f3])).
% 3.81/1.06  
% 3.81/1.06  fof(f63,plain,(
% 3.81/1.06    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 3.81/1.06    inference(definition_unfolding,[],[f38,f39,f39])).
% 3.81/1.06  
% 3.81/1.06  fof(f10,conjecture,(
% 3.81/1.06    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) => k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)))),
% 3.81/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/1.06  
% 3.81/1.06  fof(f11,negated_conjecture,(
% 3.81/1.06    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) => k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)))),
% 3.81/1.06    inference(negated_conjecture,[],[f10])).
% 3.81/1.06  
% 3.81/1.06  fof(f19,plain,(
% 3.81/1.06    ? [X0,X1,X2] : ((k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 3.81/1.06    inference(ennf_transformation,[],[f11])).
% 3.81/1.06  
% 3.81/1.06  fof(f20,plain,(
% 3.81/1.06    ? [X0,X1,X2] : (k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 3.81/1.06    inference(flattening,[],[f19])).
% 3.81/1.06  
% 3.81/1.06  fof(f30,plain,(
% 3.81/1.06    ? [X0,X1,X2] : (k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (k1_funct_1(sK3,sK1) != k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1) & r2_hidden(sK1,k3_xboole_0(k1_relat_1(sK3),sK2)) & v1_funct_1(sK3) & v1_relat_1(sK3))),
% 3.81/1.06    introduced(choice_axiom,[])).
% 3.81/1.06  
% 3.81/1.06  fof(f31,plain,(
% 3.81/1.06    k1_funct_1(sK3,sK1) != k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1) & r2_hidden(sK1,k3_xboole_0(k1_relat_1(sK3),sK2)) & v1_funct_1(sK3) & v1_relat_1(sK3)),
% 3.81/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f20,f30])).
% 3.81/1.06  
% 3.81/1.06  fof(f54,plain,(
% 3.81/1.06    r2_hidden(sK1,k3_xboole_0(k1_relat_1(sK3),sK2))),
% 3.81/1.06    inference(cnf_transformation,[],[f31])).
% 3.81/1.06  
% 3.81/1.06  fof(f4,axiom,(
% 3.81/1.06    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.81/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/1.06  
% 3.81/1.06  fof(f40,plain,(
% 3.81/1.06    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.81/1.06    inference(cnf_transformation,[],[f4])).
% 3.81/1.06  
% 3.81/1.06  fof(f56,plain,(
% 3.81/1.06    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 3.81/1.06    inference(definition_unfolding,[],[f40,f39])).
% 3.81/1.06  
% 3.81/1.06  fof(f64,plain,(
% 3.81/1.06    r2_hidden(sK1,k1_setfam_1(k1_enumset1(k1_relat_1(sK3),k1_relat_1(sK3),sK2)))),
% 3.81/1.06    inference(definition_unfolding,[],[f54,f56])).
% 3.81/1.06  
% 3.81/1.06  fof(f1,axiom,(
% 3.81/1.06    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.81/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/1.06  
% 3.81/1.06  fof(f21,plain,(
% 3.81/1.06    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.81/1.06    inference(nnf_transformation,[],[f1])).
% 3.81/1.06  
% 3.81/1.06  fof(f22,plain,(
% 3.81/1.06    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.81/1.06    inference(flattening,[],[f21])).
% 3.81/1.06  
% 3.81/1.06  fof(f23,plain,(
% 3.81/1.06    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.81/1.06    inference(rectify,[],[f22])).
% 3.81/1.06  
% 3.81/1.06  fof(f24,plain,(
% 3.81/1.06    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.81/1.06    introduced(choice_axiom,[])).
% 3.81/1.06  
% 3.81/1.06  fof(f25,plain,(
% 3.81/1.06    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.81/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).
% 3.81/1.06  
% 3.81/1.06  fof(f32,plain,(
% 3.81/1.06    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 3.81/1.06    inference(cnf_transformation,[],[f25])).
% 3.81/1.06  
% 3.81/1.06  fof(f62,plain,(
% 3.81/1.06    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k1_setfam_1(k1_enumset1(X0,X0,X1)) != X2) )),
% 3.81/1.06    inference(definition_unfolding,[],[f32,f56])).
% 3.81/1.06  
% 3.81/1.06  fof(f67,plain,(
% 3.81/1.06    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k1_setfam_1(k1_enumset1(X0,X0,X1)))) )),
% 3.81/1.06    inference(equality_resolution,[],[f62])).
% 3.81/1.06  
% 3.81/1.06  fof(f33,plain,(
% 3.81/1.06    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 3.81/1.06    inference(cnf_transformation,[],[f25])).
% 3.81/1.06  
% 3.81/1.06  fof(f61,plain,(
% 3.81/1.06    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k1_setfam_1(k1_enumset1(X0,X0,X1)) != X2) )),
% 3.81/1.06    inference(definition_unfolding,[],[f33,f56])).
% 3.81/1.06  
% 3.81/1.06  fof(f66,plain,(
% 3.81/1.06    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k1_setfam_1(k1_enumset1(X0,X0,X1)))) )),
% 3.81/1.06    inference(equality_resolution,[],[f61])).
% 3.81/1.06  
% 3.81/1.06  fof(f7,axiom,(
% 3.81/1.06    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1) & v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))))),
% 3.81/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/1.06  
% 3.81/1.06  fof(f15,plain,(
% 3.81/1.06    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.81/1.06    inference(ennf_transformation,[],[f7])).
% 3.81/1.06  
% 3.81/1.06  fof(f16,plain,(
% 3.81/1.06    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.81/1.06    inference(flattening,[],[f15])).
% 3.81/1.06  
% 3.81/1.06  fof(f45,plain,(
% 3.81/1.06    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.81/1.06    inference(cnf_transformation,[],[f16])).
% 3.81/1.06  
% 3.81/1.06  fof(f5,axiom,(
% 3.81/1.06    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 3.81/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/1.06  
% 3.81/1.06  fof(f12,plain,(
% 3.81/1.06    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 3.81/1.06    inference(ennf_transformation,[],[f5])).
% 3.81/1.06  
% 3.81/1.06  fof(f13,plain,(
% 3.81/1.06    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 3.81/1.06    inference(flattening,[],[f12])).
% 3.81/1.06  
% 3.81/1.06  fof(f41,plain,(
% 3.81/1.06    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.81/1.06    inference(cnf_transformation,[],[f13])).
% 3.81/1.06  
% 3.81/1.06  fof(f46,plain,(
% 3.81/1.06    ( ! [X0,X1] : (v1_funct_1(k5_relat_1(X0,X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.81/1.06    inference(cnf_transformation,[],[f16])).
% 3.81/1.06  
% 3.81/1.06  fof(f9,axiom,(
% 3.81/1.06    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 3.81/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/1.06  
% 3.81/1.06  fof(f17,plain,(
% 3.81/1.06    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.81/1.06    inference(ennf_transformation,[],[f9])).
% 3.81/1.06  
% 3.81/1.06  fof(f18,plain,(
% 3.81/1.06    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.81/1.06    inference(flattening,[],[f17])).
% 3.81/1.06  
% 3.81/1.06  fof(f28,plain,(
% 3.81/1.06    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.81/1.06    inference(nnf_transformation,[],[f18])).
% 3.81/1.06  
% 3.81/1.06  fof(f29,plain,(
% 3.81/1.06    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.81/1.06    inference(flattening,[],[f28])).
% 3.81/1.06  
% 3.81/1.06  fof(f51,plain,(
% 3.81/1.06    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.81/1.06    inference(cnf_transformation,[],[f29])).
% 3.81/1.06  
% 3.81/1.06  fof(f68,plain,(
% 3.81/1.06    ( ! [X2,X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.81/1.06    inference(equality_resolution,[],[f51])).
% 3.81/1.06  
% 3.81/1.06  fof(f6,axiom,(
% 3.81/1.06    ! [X0,X1,X2,X3] : (v1_relat_1(X3) => (r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) <=> (r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X0,X2))))),
% 3.81/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/1.06  
% 3.81/1.06  fof(f14,plain,(
% 3.81/1.06    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) <=> (r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X0,X2))) | ~v1_relat_1(X3))),
% 3.81/1.06    inference(ennf_transformation,[],[f6])).
% 3.81/1.06  
% 3.81/1.06  fof(f26,plain,(
% 3.81/1.06    ! [X0,X1,X2,X3] : (((r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) | (~r2_hidden(k4_tarski(X0,X1),X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)))) | ~v1_relat_1(X3))),
% 3.81/1.06    inference(nnf_transformation,[],[f14])).
% 3.81/1.06  
% 3.81/1.06  fof(f27,plain,(
% 3.81/1.06    ! [X0,X1,X2,X3] : (((r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) | ~r2_hidden(k4_tarski(X0,X1),X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)))) | ~v1_relat_1(X3))),
% 3.81/1.06    inference(flattening,[],[f26])).
% 3.81/1.06  
% 3.81/1.06  fof(f44,plain,(
% 3.81/1.06    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) | ~r2_hidden(k4_tarski(X0,X1),X3) | ~r2_hidden(X0,X2) | ~v1_relat_1(X3)) )),
% 3.81/1.06    inference(cnf_transformation,[],[f27])).
% 3.81/1.06  
% 3.81/1.06  fof(f50,plain,(
% 3.81/1.06    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.81/1.06    inference(cnf_transformation,[],[f29])).
% 3.81/1.06  
% 3.81/1.06  fof(f8,axiom,(
% 3.81/1.06    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.81/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/1.06  
% 3.81/1.06  fof(f47,plain,(
% 3.81/1.06    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 3.81/1.06    inference(cnf_transformation,[],[f8])).
% 3.81/1.06  
% 3.81/1.06  fof(f48,plain,(
% 3.81/1.06    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 3.81/1.06    inference(cnf_transformation,[],[f8])).
% 3.81/1.06  
% 3.81/1.06  fof(f52,plain,(
% 3.81/1.06    v1_relat_1(sK3)),
% 3.81/1.06    inference(cnf_transformation,[],[f31])).
% 3.81/1.06  
% 3.81/1.06  fof(f53,plain,(
% 3.81/1.06    v1_funct_1(sK3)),
% 3.81/1.06    inference(cnf_transformation,[],[f31])).
% 3.81/1.06  
% 3.81/1.06  fof(f55,plain,(
% 3.81/1.06    k1_funct_1(sK3,sK1) != k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1)),
% 3.81/1.06    inference(cnf_transformation,[],[f31])).
% 3.81/1.06  
% 3.81/1.06  cnf(c_6,plain,
% 3.81/1.06      ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
% 3.81/1.06      inference(cnf_transformation,[],[f63]) ).
% 3.81/1.06  
% 3.81/1.06  cnf(c_19,negated_conjecture,
% 3.81/1.06      ( r2_hidden(sK1,k1_setfam_1(k1_enumset1(k1_relat_1(sK3),k1_relat_1(sK3),sK2))) ),
% 3.81/1.06      inference(cnf_transformation,[],[f64]) ).
% 3.81/1.06  
% 3.81/1.06  cnf(c_562,plain,
% 3.81/1.06      ( r2_hidden(sK1,k1_setfam_1(k1_enumset1(k1_relat_1(sK3),k1_relat_1(sK3),sK2))) = iProver_top ),
% 3.81/1.06      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.81/1.06  
% 3.81/1.06  cnf(c_1155,plain,
% 3.81/1.06      ( r2_hidden(sK1,k1_setfam_1(k1_enumset1(sK2,sK2,k1_relat_1(sK3)))) = iProver_top ),
% 3.81/1.06      inference(demodulation,[status(thm)],[c_6,c_562]) ).
% 3.81/1.06  
% 3.81/1.06  cnf(c_5,plain,
% 3.81/1.06      ( r2_hidden(X0,X1)
% 3.81/1.06      | ~ r2_hidden(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
% 3.81/1.06      inference(cnf_transformation,[],[f67]) ).
% 3.81/1.06  
% 3.81/1.06  cnf(c_573,plain,
% 3.81/1.06      ( r2_hidden(X0,X1) = iProver_top
% 3.81/1.06      | r2_hidden(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) != iProver_top ),
% 3.81/1.06      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.81/1.06  
% 3.81/1.06  cnf(c_1324,plain,
% 3.81/1.06      ( r2_hidden(sK1,sK2) = iProver_top ),
% 3.81/1.06      inference(superposition,[status(thm)],[c_1155,c_573]) ).
% 3.81/1.06  
% 3.81/1.06  cnf(c_4,plain,
% 3.81/1.06      ( r2_hidden(X0,X1)
% 3.81/1.06      | ~ r2_hidden(X0,k1_setfam_1(k1_enumset1(X2,X2,X1))) ),
% 3.81/1.06      inference(cnf_transformation,[],[f66]) ).
% 3.81/1.06  
% 3.81/1.06  cnf(c_574,plain,
% 3.81/1.06      ( r2_hidden(X0,X1) = iProver_top
% 3.81/1.06      | r2_hidden(X0,k1_setfam_1(k1_enumset1(X2,X2,X1))) != iProver_top ),
% 3.81/1.06      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.81/1.06  
% 3.81/1.06  cnf(c_1493,plain,
% 3.81/1.06      ( r2_hidden(sK1,k1_relat_1(sK3)) = iProver_top ),
% 3.81/1.06      inference(superposition,[status(thm)],[c_1155,c_574]) ).
% 3.81/1.06  
% 3.81/1.06  cnf(c_12,plain,
% 3.81/1.06      ( ~ v1_funct_1(X0)
% 3.81/1.06      | ~ v1_funct_1(X1)
% 3.81/1.06      | ~ v1_relat_1(X0)
% 3.81/1.06      | ~ v1_relat_1(X1)
% 3.81/1.06      | v1_relat_1(k5_relat_1(X1,X0)) ),
% 3.81/1.06      inference(cnf_transformation,[],[f45]) ).
% 3.81/1.06  
% 3.81/1.06  cnf(c_7,plain,
% 3.81/1.06      ( ~ v1_relat_1(X0)
% 3.81/1.06      | ~ v1_relat_1(X1)
% 3.81/1.06      | v1_relat_1(k5_relat_1(X1,X0)) ),
% 3.81/1.06      inference(cnf_transformation,[],[f41]) ).
% 3.81/1.06  
% 3.81/1.06  cnf(c_122,plain,
% 3.81/1.06      ( ~ v1_relat_1(X0)
% 3.81/1.06      | ~ v1_relat_1(X1)
% 3.81/1.06      | v1_relat_1(k5_relat_1(X1,X0)) ),
% 3.81/1.06      inference(global_propositional_subsumption,
% 3.81/1.06                [status(thm)],
% 3.81/1.06                [c_12,c_7]) ).
% 3.81/1.06  
% 3.81/1.06  cnf(c_123,plain,
% 3.81/1.06      ( ~ v1_relat_1(X0)
% 3.81/1.06      | ~ v1_relat_1(X1)
% 3.81/1.06      | v1_relat_1(k5_relat_1(X0,X1)) ),
% 3.81/1.06      inference(renaming,[status(thm)],[c_122]) ).
% 3.81/1.06  
% 3.81/1.06  cnf(c_559,plain,
% 3.81/1.06      ( v1_relat_1(X0) != iProver_top
% 3.81/1.06      | v1_relat_1(X1) != iProver_top
% 3.81/1.06      | v1_relat_1(k5_relat_1(X1,X0)) = iProver_top ),
% 3.81/1.06      inference(predicate_to_equality,[status(thm)],[c_123]) ).
% 3.81/1.06  
% 3.81/1.06  cnf(c_11,plain,
% 3.81/1.06      ( ~ v1_funct_1(X0)
% 3.81/1.06      | ~ v1_funct_1(X1)
% 3.81/1.06      | v1_funct_1(k5_relat_1(X1,X0))
% 3.81/1.06      | ~ v1_relat_1(X0)
% 3.81/1.06      | ~ v1_relat_1(X1) ),
% 3.81/1.06      inference(cnf_transformation,[],[f46]) ).
% 3.81/1.06  
% 3.81/1.06  cnf(c_568,plain,
% 3.81/1.06      ( v1_funct_1(X0) != iProver_top
% 3.81/1.06      | v1_funct_1(X1) != iProver_top
% 3.81/1.06      | v1_funct_1(k5_relat_1(X0,X1)) = iProver_top
% 3.81/1.06      | v1_relat_1(X0) != iProver_top
% 3.81/1.06      | v1_relat_1(X1) != iProver_top ),
% 3.81/1.06      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.81/1.06  
% 3.81/1.06  cnf(c_15,plain,
% 3.81/1.06      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.81/1.06      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 3.81/1.06      | ~ v1_funct_1(X1)
% 3.81/1.06      | ~ v1_relat_1(X1) ),
% 3.81/1.06      inference(cnf_transformation,[],[f68]) ).
% 3.81/1.06  
% 3.81/1.06  cnf(c_565,plain,
% 3.81/1.06      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 3.81/1.06      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1) = iProver_top
% 3.81/1.06      | v1_funct_1(X1) != iProver_top
% 3.81/1.06      | v1_relat_1(X1) != iProver_top ),
% 3.81/1.06      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.81/1.06  
% 3.81/1.06  cnf(c_8,plain,
% 3.81/1.06      ( ~ r2_hidden(X0,X1)
% 3.81/1.06      | ~ r2_hidden(k4_tarski(X0,X2),X3)
% 3.81/1.06      | r2_hidden(k4_tarski(X0,X2),k5_relat_1(k6_relat_1(X1),X3))
% 3.81/1.06      | ~ v1_relat_1(X3) ),
% 3.81/1.06      inference(cnf_transformation,[],[f44]) ).
% 3.81/1.06  
% 3.81/1.06  cnf(c_571,plain,
% 3.81/1.06      ( r2_hidden(X0,X1) != iProver_top
% 3.81/1.06      | r2_hidden(k4_tarski(X0,X2),X3) != iProver_top
% 3.81/1.06      | r2_hidden(k4_tarski(X0,X2),k5_relat_1(k6_relat_1(X1),X3)) = iProver_top
% 3.81/1.06      | v1_relat_1(X3) != iProver_top ),
% 3.81/1.06      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.81/1.06  
% 3.81/1.06  cnf(c_16,plain,
% 3.81/1.06      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.81/1.06      | ~ v1_funct_1(X2)
% 3.81/1.06      | ~ v1_relat_1(X2)
% 3.81/1.06      | k1_funct_1(X2,X0) = X1 ),
% 3.81/1.06      inference(cnf_transformation,[],[f50]) ).
% 3.81/1.06  
% 3.81/1.06  cnf(c_564,plain,
% 3.81/1.06      ( k1_funct_1(X0,X1) = X2
% 3.81/1.06      | r2_hidden(k4_tarski(X1,X2),X0) != iProver_top
% 3.81/1.06      | v1_funct_1(X0) != iProver_top
% 3.81/1.06      | v1_relat_1(X0) != iProver_top ),
% 3.81/1.06      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.81/1.06  
% 3.81/1.06  cnf(c_2137,plain,
% 3.81/1.06      ( k1_funct_1(k5_relat_1(k6_relat_1(X0),X1),X2) = X3
% 3.81/1.06      | r2_hidden(X2,X0) != iProver_top
% 3.81/1.06      | r2_hidden(k4_tarski(X2,X3),X1) != iProver_top
% 3.81/1.06      | v1_funct_1(k5_relat_1(k6_relat_1(X0),X1)) != iProver_top
% 3.81/1.06      | v1_relat_1(X1) != iProver_top
% 3.81/1.06      | v1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) != iProver_top ),
% 3.81/1.06      inference(superposition,[status(thm)],[c_571,c_564]) ).
% 3.81/1.06  
% 3.81/1.06  cnf(c_3289,plain,
% 3.81/1.06      ( k1_funct_1(k5_relat_1(k6_relat_1(X0),X1),X2) = k1_funct_1(X1,X2)
% 3.81/1.06      | r2_hidden(X2,X0) != iProver_top
% 3.81/1.06      | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
% 3.81/1.06      | v1_funct_1(X1) != iProver_top
% 3.81/1.06      | v1_funct_1(k5_relat_1(k6_relat_1(X0),X1)) != iProver_top
% 3.81/1.06      | v1_relat_1(X1) != iProver_top
% 3.81/1.06      | v1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) != iProver_top ),
% 3.81/1.06      inference(superposition,[status(thm)],[c_565,c_2137]) ).
% 3.81/1.06  
% 3.81/1.06  cnf(c_4885,plain,
% 3.81/1.06      ( k1_funct_1(k5_relat_1(k6_relat_1(X0),X1),X2) = k1_funct_1(X1,X2)
% 3.81/1.06      | r2_hidden(X2,X0) != iProver_top
% 3.81/1.06      | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
% 3.81/1.06      | v1_funct_1(X1) != iProver_top
% 3.81/1.06      | v1_funct_1(k6_relat_1(X0)) != iProver_top
% 3.81/1.06      | v1_relat_1(X1) != iProver_top
% 3.81/1.06      | v1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) != iProver_top
% 3.81/1.06      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 3.81/1.06      inference(superposition,[status(thm)],[c_568,c_3289]) ).
% 3.81/1.06  
% 3.81/1.06  cnf(c_14,plain,
% 3.81/1.06      ( v1_relat_1(k6_relat_1(X0)) ),
% 3.81/1.06      inference(cnf_transformation,[],[f47]) ).
% 3.81/1.06  
% 3.81/1.06  cnf(c_34,plain,
% 3.81/1.06      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 3.81/1.06      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.81/1.06  
% 3.81/1.06  cnf(c_13,plain,
% 3.81/1.06      ( v1_funct_1(k6_relat_1(X0)) ),
% 3.81/1.06      inference(cnf_transformation,[],[f48]) ).
% 3.81/1.06  
% 3.81/1.06  cnf(c_37,plain,
% 3.81/1.06      ( v1_funct_1(k6_relat_1(X0)) = iProver_top ),
% 3.81/1.06      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.81/1.06  
% 3.81/1.06  cnf(c_5784,plain,
% 3.81/1.06      ( v1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) != iProver_top
% 3.81/1.06      | v1_relat_1(X1) != iProver_top
% 3.81/1.06      | k1_funct_1(k5_relat_1(k6_relat_1(X0),X1),X2) = k1_funct_1(X1,X2)
% 3.81/1.06      | r2_hidden(X2,X0) != iProver_top
% 3.81/1.06      | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
% 3.81/1.06      | v1_funct_1(X1) != iProver_top ),
% 3.81/1.06      inference(global_propositional_subsumption,
% 3.81/1.06                [status(thm)],
% 3.81/1.06                [c_4885,c_34,c_37]) ).
% 3.81/1.06  
% 3.81/1.06  cnf(c_5785,plain,
% 3.81/1.06      ( k1_funct_1(k5_relat_1(k6_relat_1(X0),X1),X2) = k1_funct_1(X1,X2)
% 3.81/1.06      | r2_hidden(X2,X0) != iProver_top
% 3.81/1.06      | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
% 3.81/1.06      | v1_funct_1(X1) != iProver_top
% 3.81/1.06      | v1_relat_1(X1) != iProver_top
% 3.81/1.06      | v1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) != iProver_top ),
% 3.81/1.06      inference(renaming,[status(thm)],[c_5784]) ).
% 3.81/1.06  
% 3.81/1.06  cnf(c_5790,plain,
% 3.81/1.06      ( k1_funct_1(k5_relat_1(k6_relat_1(X0),X1),X2) = k1_funct_1(X1,X2)
% 3.81/1.06      | r2_hidden(X2,X0) != iProver_top
% 3.81/1.06      | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
% 3.81/1.06      | v1_funct_1(X1) != iProver_top
% 3.81/1.06      | v1_relat_1(X1) != iProver_top
% 3.81/1.06      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 3.81/1.06      inference(superposition,[status(thm)],[c_559,c_5785]) ).
% 3.81/1.06  
% 3.81/1.06  cnf(c_5795,plain,
% 3.81/1.06      ( v1_relat_1(X1) != iProver_top
% 3.81/1.06      | v1_funct_1(X1) != iProver_top
% 3.81/1.06      | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
% 3.81/1.06      | r2_hidden(X2,X0) != iProver_top
% 3.81/1.06      | k1_funct_1(k5_relat_1(k6_relat_1(X0),X1),X2) = k1_funct_1(X1,X2) ),
% 3.81/1.06      inference(global_propositional_subsumption,
% 3.81/1.06                [status(thm)],
% 3.81/1.06                [c_5790,c_34]) ).
% 3.81/1.06  
% 3.81/1.06  cnf(c_5796,plain,
% 3.81/1.06      ( k1_funct_1(k5_relat_1(k6_relat_1(X0),X1),X2) = k1_funct_1(X1,X2)
% 3.81/1.06      | r2_hidden(X2,X0) != iProver_top
% 3.81/1.06      | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
% 3.81/1.06      | v1_funct_1(X1) != iProver_top
% 3.81/1.06      | v1_relat_1(X1) != iProver_top ),
% 3.81/1.06      inference(renaming,[status(thm)],[c_5795]) ).
% 3.81/1.06  
% 3.81/1.06  cnf(c_5806,plain,
% 3.81/1.06      ( k1_funct_1(k5_relat_1(k6_relat_1(X0),sK3),sK1) = k1_funct_1(sK3,sK1)
% 3.81/1.06      | r2_hidden(sK1,X0) != iProver_top
% 3.81/1.06      | v1_funct_1(sK3) != iProver_top
% 3.81/1.06      | v1_relat_1(sK3) != iProver_top ),
% 3.81/1.06      inference(superposition,[status(thm)],[c_1493,c_5796]) ).
% 3.81/1.06  
% 3.81/1.06  cnf(c_21,negated_conjecture,
% 3.81/1.06      ( v1_relat_1(sK3) ),
% 3.81/1.06      inference(cnf_transformation,[],[f52]) ).
% 3.81/1.06  
% 3.81/1.06  cnf(c_22,plain,
% 3.81/1.06      ( v1_relat_1(sK3) = iProver_top ),
% 3.81/1.06      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.81/1.06  
% 3.81/1.06  cnf(c_20,negated_conjecture,
% 3.81/1.06      ( v1_funct_1(sK3) ),
% 3.81/1.06      inference(cnf_transformation,[],[f53]) ).
% 3.81/1.06  
% 3.81/1.06  cnf(c_23,plain,
% 3.81/1.06      ( v1_funct_1(sK3) = iProver_top ),
% 3.81/1.06      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.81/1.06  
% 3.81/1.06  cnf(c_5914,plain,
% 3.81/1.06      ( k1_funct_1(k5_relat_1(k6_relat_1(X0),sK3),sK1) = k1_funct_1(sK3,sK1)
% 3.81/1.06      | r2_hidden(sK1,X0) != iProver_top ),
% 3.81/1.06      inference(global_propositional_subsumption,
% 3.81/1.06                [status(thm)],
% 3.81/1.06                [c_5806,c_22,c_23]) ).
% 3.81/1.06  
% 3.81/1.06  cnf(c_5921,plain,
% 3.81/1.06      ( k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1) = k1_funct_1(sK3,sK1) ),
% 3.81/1.06      inference(superposition,[status(thm)],[c_1324,c_5914]) ).
% 3.81/1.06  
% 3.81/1.06  cnf(c_233,plain,( X0 = X0 ),theory(equality) ).
% 3.81/1.06  
% 3.81/1.06  cnf(c_727,plain,
% 3.81/1.06      ( k1_funct_1(sK3,sK1) = k1_funct_1(sK3,sK1) ),
% 3.81/1.06      inference(instantiation,[status(thm)],[c_233]) ).
% 3.81/1.06  
% 3.81/1.06  cnf(c_234,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.81/1.06  
% 3.81/1.06  cnf(c_604,plain,
% 3.81/1.06      ( k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1) != X0
% 3.81/1.06      | k1_funct_1(sK3,sK1) != X0
% 3.81/1.06      | k1_funct_1(sK3,sK1) = k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1) ),
% 3.81/1.06      inference(instantiation,[status(thm)],[c_234]) ).
% 3.81/1.06  
% 3.81/1.06  cnf(c_642,plain,
% 3.81/1.06      ( k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1) != k1_funct_1(sK3,sK1)
% 3.81/1.06      | k1_funct_1(sK3,sK1) = k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1)
% 3.81/1.06      | k1_funct_1(sK3,sK1) != k1_funct_1(sK3,sK1) ),
% 3.81/1.06      inference(instantiation,[status(thm)],[c_604]) ).
% 3.81/1.06  
% 3.81/1.06  cnf(c_18,negated_conjecture,
% 3.81/1.06      ( k1_funct_1(sK3,sK1) != k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1) ),
% 3.81/1.06      inference(cnf_transformation,[],[f55]) ).
% 3.81/1.06  
% 3.81/1.06  cnf(contradiction,plain,
% 3.81/1.06      ( $false ),
% 3.81/1.06      inference(minisat,[status(thm)],[c_5921,c_727,c_642,c_18]) ).
% 3.81/1.06  
% 3.81/1.06  
% 3.81/1.06  % SZS output end CNFRefutation for theBenchmark.p
% 3.81/1.06  
% 3.81/1.06  ------                               Statistics
% 3.81/1.06  
% 3.81/1.06  ------ General
% 3.81/1.06  
% 3.81/1.06  abstr_ref_over_cycles:                  0
% 3.81/1.06  abstr_ref_under_cycles:                 0
% 3.81/1.06  gc_basic_clause_elim:                   0
% 3.81/1.06  forced_gc_time:                         0
% 3.81/1.06  parsing_time:                           0.01
% 3.81/1.06  unif_index_cands_time:                  0.
% 3.81/1.06  unif_index_add_time:                    0.
% 3.81/1.06  orderings_time:                         0.
% 3.81/1.06  out_proof_time:                         0.01
% 3.81/1.06  total_time:                             0.383
% 3.81/1.06  num_of_symbols:                         45
% 3.81/1.06  num_of_terms:                           12375
% 3.81/1.06  
% 3.81/1.06  ------ Preprocessing
% 3.81/1.06  
% 3.81/1.06  num_of_splits:                          0
% 3.81/1.06  num_of_split_atoms:                     0
% 3.81/1.06  num_of_reused_defs:                     0
% 3.81/1.06  num_eq_ax_congr_red:                    8
% 3.81/1.06  num_of_sem_filtered_clauses:            1
% 3.81/1.06  num_of_subtypes:                        0
% 3.81/1.06  monotx_restored_types:                  0
% 3.81/1.06  sat_num_of_epr_types:                   0
% 3.81/1.06  sat_num_of_non_cyclic_types:            0
% 3.81/1.06  sat_guarded_non_collapsed_types:        0
% 3.81/1.06  num_pure_diseq_elim:                    0
% 3.81/1.06  simp_replaced_by:                       0
% 3.81/1.06  res_preprocessed:                       91
% 3.81/1.06  prep_upred:                             0
% 3.81/1.06  prep_unflattend:                        0
% 3.81/1.06  smt_new_axioms:                         0
% 3.81/1.06  pred_elim_cands:                        3
% 3.81/1.06  pred_elim:                              0
% 3.81/1.06  pred_elim_cl:                           0
% 3.81/1.06  pred_elim_cycles:                       1
% 3.81/1.06  merged_defs:                            0
% 3.81/1.06  merged_defs_ncl:                        0
% 3.81/1.06  bin_hyper_res:                          0
% 3.81/1.06  prep_cycles:                            3
% 3.81/1.06  pred_elim_time:                         0.
% 3.81/1.06  splitting_time:                         0.
% 3.81/1.06  sem_filter_time:                        0.
% 3.81/1.06  monotx_time:                            0.
% 3.81/1.06  subtype_inf_time:                       0.
% 3.81/1.06  
% 3.81/1.06  ------ Problem properties
% 3.81/1.06  
% 3.81/1.06  clauses:                                22
% 3.81/1.06  conjectures:                            4
% 3.81/1.06  epr:                                    2
% 3.81/1.06  horn:                                   20
% 3.81/1.06  ground:                                 4
% 3.81/1.06  unary:                                  7
% 3.81/1.06  binary:                                 2
% 3.81/1.06  lits:                                   57
% 3.81/1.06  lits_eq:                                6
% 3.81/1.06  fd_pure:                                0
% 3.81/1.06  fd_pseudo:                              0
% 3.81/1.06  fd_cond:                                0
% 3.81/1.06  fd_pseudo_cond:                         4
% 3.81/1.06  ac_symbols:                             0
% 3.81/1.06  
% 3.81/1.06  ------ Propositional Solver
% 3.81/1.06  
% 3.81/1.06  prop_solver_calls:                      25
% 3.81/1.06  prop_fast_solver_calls:                 774
% 3.81/1.06  smt_solver_calls:                       0
% 3.81/1.06  smt_fast_solver_calls:                  0
% 3.81/1.06  prop_num_of_clauses:                    4001
% 3.81/1.06  prop_preprocess_simplified:             7063
% 3.81/1.06  prop_fo_subsumed:                       7
% 3.81/1.06  prop_solver_time:                       0.
% 3.81/1.06  smt_solver_time:                        0.
% 3.81/1.06  smt_fast_solver_time:                   0.
% 3.81/1.06  prop_fast_solver_time:                  0.
% 3.81/1.06  prop_unsat_core_time:                   0.
% 3.81/1.06  
% 3.81/1.06  ------ QBF
% 3.81/1.06  
% 3.81/1.06  qbf_q_res:                              0
% 3.81/1.06  qbf_num_tautologies:                    0
% 3.81/1.06  qbf_prep_cycles:                        0
% 3.81/1.06  
% 3.81/1.06  ------ BMC1
% 3.81/1.06  
% 3.81/1.06  bmc1_current_bound:                     -1
% 3.81/1.06  bmc1_last_solved_bound:                 -1
% 3.81/1.06  bmc1_unsat_core_size:                   -1
% 3.81/1.06  bmc1_unsat_core_parents_size:           -1
% 3.81/1.06  bmc1_merge_next_fun:                    0
% 3.81/1.06  bmc1_unsat_core_clauses_time:           0.
% 3.81/1.06  
% 3.81/1.06  ------ Instantiation
% 3.81/1.06  
% 3.81/1.06  inst_num_of_clauses:                    612
% 3.81/1.06  inst_num_in_passive:                    198
% 3.81/1.06  inst_num_in_active:                     349
% 3.81/1.06  inst_num_in_unprocessed:                65
% 3.81/1.06  inst_num_of_loops:                      360
% 3.81/1.06  inst_num_of_learning_restarts:          0
% 3.81/1.06  inst_num_moves_active_passive:          9
% 3.81/1.06  inst_lit_activity:                      0
% 3.81/1.06  inst_lit_activity_moves:                0
% 3.81/1.06  inst_num_tautologies:                   0
% 3.81/1.06  inst_num_prop_implied:                  0
% 3.81/1.06  inst_num_existing_simplified:           0
% 3.81/1.06  inst_num_eq_res_simplified:             0
% 3.81/1.06  inst_num_child_elim:                    0
% 3.81/1.06  inst_num_of_dismatching_blockings:      143
% 3.81/1.06  inst_num_of_non_proper_insts:           501
% 3.81/1.06  inst_num_of_duplicates:                 0
% 3.81/1.06  inst_inst_num_from_inst_to_res:         0
% 3.81/1.06  inst_dismatching_checking_time:         0.
% 3.81/1.06  
% 3.81/1.06  ------ Resolution
% 3.81/1.06  
% 3.81/1.06  res_num_of_clauses:                     0
% 3.81/1.06  res_num_in_passive:                     0
% 3.81/1.06  res_num_in_active:                      0
% 3.81/1.06  res_num_of_loops:                       94
% 3.81/1.06  res_forward_subset_subsumed:            31
% 3.81/1.06  res_backward_subset_subsumed:           0
% 3.81/1.06  res_forward_subsumed:                   0
% 3.81/1.06  res_backward_subsumed:                  0
% 3.81/1.06  res_forward_subsumption_resolution:     0
% 3.81/1.06  res_backward_subsumption_resolution:    0
% 3.81/1.06  res_clause_to_clause_subsumption:       6270
% 3.81/1.06  res_orphan_elimination:                 0
% 3.81/1.06  res_tautology_del:                      22
% 3.81/1.06  res_num_eq_res_simplified:              0
% 3.81/1.06  res_num_sel_changes:                    0
% 3.81/1.06  res_moves_from_active_to_pass:          0
% 3.81/1.06  
% 3.81/1.06  ------ Superposition
% 3.81/1.06  
% 3.81/1.06  sup_time_total:                         0.
% 3.81/1.06  sup_time_generating:                    0.
% 3.81/1.06  sup_time_sim_full:                      0.
% 3.81/1.06  sup_time_sim_immed:                     0.
% 3.81/1.06  
% 3.81/1.06  sup_num_of_clauses:                     773
% 3.81/1.06  sup_num_in_active:                      68
% 3.81/1.06  sup_num_in_passive:                     705
% 3.81/1.06  sup_num_of_loops:                       70
% 3.81/1.06  sup_fw_superposition:                   565
% 3.81/1.06  sup_bw_superposition:                   288
% 3.81/1.06  sup_immediate_simplified:               23
% 3.81/1.06  sup_given_eliminated:                   0
% 3.81/1.06  comparisons_done:                       0
% 3.81/1.06  comparisons_avoided:                    0
% 3.81/1.06  
% 3.81/1.06  ------ Simplifications
% 3.81/1.06  
% 3.81/1.06  
% 3.81/1.06  sim_fw_subset_subsumed:                 5
% 3.81/1.06  sim_bw_subset_subsumed:                 1
% 3.81/1.06  sim_fw_subsumed:                        19
% 3.81/1.06  sim_bw_subsumed:                        1
% 3.81/1.06  sim_fw_subsumption_res:                 0
% 3.81/1.06  sim_bw_subsumption_res:                 0
% 3.81/1.06  sim_tautology_del:                      11
% 3.81/1.06  sim_eq_tautology_del:                   1
% 3.81/1.06  sim_eq_res_simp:                        14
% 3.81/1.06  sim_fw_demodulated:                     0
% 3.81/1.06  sim_bw_demodulated:                     1
% 3.81/1.06  sim_light_normalised:                   0
% 3.81/1.06  sim_joinable_taut:                      0
% 3.81/1.06  sim_joinable_simp:                      0
% 3.81/1.06  sim_ac_normalised:                      0
% 3.81/1.06  sim_smt_subsumption:                    0
% 3.81/1.06  
%------------------------------------------------------------------------------
