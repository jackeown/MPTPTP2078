%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:51:22 EST 2020

% Result     : Theorem 3.29s
% Output     : CNFRefutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 252 expanded)
%              Number of clauses        :   40 (  42 expanded)
%              Number of leaves         :   19 (  70 expanded)
%              Depth                    :   14
%              Number of atoms          :  256 ( 586 expanded)
%              Number of equality atoms :   80 ( 185 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_xboole_0(X0,X1) )
       => r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( v2_funct_1(X2)
            & r1_xboole_0(X0,X1) )
         => r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v2_funct_1(X2)
      & r1_xboole_0(X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v2_funct_1(X2)
      & r1_xboole_0(X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f33,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        & v2_funct_1(X2)
        & r1_xboole_0(X0,X1)
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_xboole_0(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))
      & v2_funct_1(sK4)
      & r1_xboole_0(sK2,sK3)
      & v1_funct_1(sK4)
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ~ r1_xboole_0(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))
    & v2_funct_1(sK4)
    & r1_xboole_0(sK2,sK3)
    & v1_funct_1(sK4)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f26,f33])).

fof(f57,plain,(
    r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f27])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f29])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f12])).

fof(f60,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f49,f50])).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f48,f60])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f47,f61])).

fof(f63,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f46,f62])).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f45,f63])).

fof(f65,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f51,f64])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f39,f65])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k9_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k9_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k9_relat_1(X1,X0)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f55,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k6_enumset1(k9_relat_1(X2,X0),k9_relat_1(X2,X0),k9_relat_1(X2,X0),k9_relat_1(X2,X0),k9_relat_1(X2,X0),k9_relat_1(X2,X0),k9_relat_1(X2,X0),k9_relat_1(X2,X1))) = k9_relat_1(X2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f54,f65,f65])).

fof(f58,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f56,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f38,f65])).

fof(f59,plain,(
    ~ r1_xboole_0(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f66,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f40,f65])).

fof(f70,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) = X0 ),
    inference(definition_unfolding,[],[f42,f66])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) != X0 ) ),
    inference(definition_unfolding,[],[f44,f66])).

cnf(c_14,negated_conjecture,
    ( r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1364,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1371,plain,
    ( r2_hidden(sK0(X0,X1),X1) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1369,plain,
    ( r2_hidden(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2109,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1371,c_1369])).

cnf(c_9,plain,
    ( ~ r1_xboole_0(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k9_relat_1(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_16,negated_conjecture,
    ( v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_232,plain,
    ( ~ r1_xboole_0(k1_relat_1(X0),X1)
    | k9_relat_1(X0,X1) = k1_xboole_0
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_16])).

cnf(c_233,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK4),X0)
    | k9_relat_1(sK4,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_232])).

cnf(c_641,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK4),X0)
    | k9_relat_1(sK4,X0) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_233])).

cnf(c_1362,plain,
    ( k9_relat_1(sK4,X0) = k1_xboole_0
    | r1_xboole_0(k1_relat_1(sK4),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_641])).

cnf(c_3530,plain,
    ( k9_relat_1(sK4,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2109,c_1362])).

cnf(c_4235,plain,
    ( k9_relat_1(sK4,k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1364,c_3530])).

cnf(c_1030,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2698,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k9_relat_1(sK4,k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))),k9_relat_1(sK4,k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))))
    | k9_relat_1(sK4,k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))) != X0
    | k9_relat_1(sK4,k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))) != X1 ),
    inference(instantiation,[status(thm)],[c_1030])).

cnf(c_2700,plain,
    ( r1_xboole_0(k9_relat_1(sK4,k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))),k9_relat_1(sK4,k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))))
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | k9_relat_1(sK4,k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2698])).

cnf(c_1816,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k1_setfam_1(k6_enumset1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))),k1_setfam_1(k6_enumset1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))))
    | k1_setfam_1(k6_enumset1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))) != X0
    | k1_setfam_1(k6_enumset1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))) != X1 ),
    inference(instantiation,[status(thm)],[c_1030])).

cnf(c_2561,plain,
    ( ~ r1_xboole_0(X0,k9_relat_1(sK4,k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))))
    | r1_xboole_0(k1_setfam_1(k6_enumset1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))),k1_setfam_1(k6_enumset1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))))
    | k1_setfam_1(k6_enumset1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))) != X0
    | k1_setfam_1(k6_enumset1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))) != k9_relat_1(sK4,k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_1816])).

cnf(c_2575,plain,
    ( ~ r1_xboole_0(k9_relat_1(sK4,k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))),k9_relat_1(sK4,k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))))
    | r1_xboole_0(k1_setfam_1(k6_enumset1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))),k1_setfam_1(k6_enumset1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))))
    | k1_setfam_1(k6_enumset1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))) != k9_relat_1(sK4,k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_2561])).

cnf(c_11,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_setfam_1(k6_enumset1(k9_relat_1(X0,X1),k9_relat_1(X0,X1),k9_relat_1(X0,X1),k9_relat_1(X0,X1),k9_relat_1(X0,X1),k9_relat_1(X0,X1),k9_relat_1(X0,X1),k9_relat_1(X0,X2))) = k9_relat_1(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_13,negated_conjecture,
    ( v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_208,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_setfam_1(k6_enumset1(k9_relat_1(X0,X1),k9_relat_1(X0,X1),k9_relat_1(X0,X1),k9_relat_1(X0,X1),k9_relat_1(X0,X1),k9_relat_1(X0,X1),k9_relat_1(X0,X1),k9_relat_1(X0,X2))) = k9_relat_1(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_13])).

cnf(c_209,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k1_setfam_1(k6_enumset1(k9_relat_1(sK4,X0),k9_relat_1(sK4,X0),k9_relat_1(sK4,X0),k9_relat_1(sK4,X0),k9_relat_1(sK4,X0),k9_relat_1(sK4,X0),k9_relat_1(sK4,X0),k9_relat_1(sK4,X1))) = k9_relat_1(sK4,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(unflattening,[status(thm)],[c_208])).

cnf(c_15,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_213,plain,
    ( k1_setfam_1(k6_enumset1(k9_relat_1(sK4,X0),k9_relat_1(sK4,X0),k9_relat_1(sK4,X0),k9_relat_1(sK4,X0),k9_relat_1(sK4,X0),k9_relat_1(sK4,X0),k9_relat_1(sK4,X0),k9_relat_1(sK4,X1))) = k9_relat_1(sK4,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_209,c_16,c_15])).

cnf(c_2562,plain,
    ( k1_setfam_1(k6_enumset1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))) = k9_relat_1(sK4,k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_213])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1520,plain,
    ( ~ r2_hidden(sK1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)),X0)
    | ~ r2_hidden(sK1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)),k1_setfam_1(k6_enumset1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))))
    | ~ r1_xboole_0(k1_setfam_1(k6_enumset1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))),X0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1611,plain,
    ( ~ r2_hidden(sK1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)),k1_setfam_1(k6_enumset1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))))
    | ~ r1_xboole_0(k1_setfam_1(k6_enumset1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))),k1_setfam_1(k6_enumset1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)))) ),
    inference(instantiation,[status(thm)],[c_1520])).

cnf(c_4,plain,
    ( r2_hidden(sK1(X0,X1),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_12,negated_conjecture,
    ( ~ r1_xboole_0(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_388,plain,
    ( r2_hidden(sK1(X0,X1),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
    | k9_relat_1(sK4,sK3) != X1
    | k9_relat_1(sK4,sK2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_12])).

cnf(c_389,plain,
    ( r2_hidden(sK1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)),k1_setfam_1(k6_enumset1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)))) ),
    inference(unflattening,[status(thm)],[c_388])).

cnf(c_6,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_37,plain,
    ( k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_7,plain,
    ( r1_xboole_0(X0,X1)
    | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) != X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_35,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4235,c_2700,c_2575,c_2562,c_1611,c_389,c_37,c_35])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:36:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.34  % Running in FOF mode
% 3.29/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.29/0.99  
% 3.29/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.29/0.99  
% 3.29/0.99  ------  iProver source info
% 3.29/0.99  
% 3.29/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.29/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.29/0.99  git: non_committed_changes: false
% 3.29/0.99  git: last_make_outside_of_git: false
% 3.29/0.99  
% 3.29/0.99  ------ 
% 3.29/0.99  ------ Parsing...
% 3.29/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.29/0.99  
% 3.29/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.29/0.99  
% 3.29/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.29/0.99  
% 3.29/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.29/0.99  ------ Proving...
% 3.29/0.99  ------ Problem Properties 
% 3.29/0.99  
% 3.29/0.99  
% 3.29/0.99  clauses                                 14
% 3.29/0.99  conjectures                             2
% 3.29/0.99  EPR                                     2
% 3.29/0.99  Horn                                    11
% 3.29/0.99  unary                                   5
% 3.29/0.99  binary                                  8
% 3.29/0.99  lits                                    24
% 3.29/0.99  lits eq                                 7
% 3.29/0.99  fd_pure                                 0
% 3.29/0.99  fd_pseudo                               0
% 3.29/0.99  fd_cond                                 0
% 3.29/0.99  fd_pseudo_cond                          0
% 3.29/0.99  AC symbols                              0
% 3.29/0.99  
% 3.29/0.99  ------ Input Options Time Limit: Unbounded
% 3.29/0.99  
% 3.29/0.99  
% 3.29/0.99  ------ 
% 3.29/0.99  Current options:
% 3.29/0.99  ------ 
% 3.29/0.99  
% 3.29/0.99  
% 3.29/0.99  
% 3.29/0.99  
% 3.29/0.99  ------ Proving...
% 3.29/0.99  
% 3.29/0.99  
% 3.29/0.99  % SZS status Theorem for theBenchmark.p
% 3.29/0.99  
% 3.29/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.29/0.99  
% 3.29/0.99  fof(f16,conjecture,(
% 3.29/0.99    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_xboole_0(X0,X1)) => r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 3.29/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f17,negated_conjecture,(
% 3.29/0.99    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_xboole_0(X0,X1)) => r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 3.29/0.99    inference(negated_conjecture,[],[f16])).
% 3.29/0.99  
% 3.29/0.99  fof(f25,plain,(
% 3.29/0.99    ? [X0,X1,X2] : ((~r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & (v2_funct_1(X2) & r1_xboole_0(X0,X1))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 3.29/0.99    inference(ennf_transformation,[],[f17])).
% 3.29/0.99  
% 3.29/0.99  fof(f26,plain,(
% 3.29/0.99    ? [X0,X1,X2] : (~r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v2_funct_1(X2) & r1_xboole_0(X0,X1) & v1_funct_1(X2) & v1_relat_1(X2))),
% 3.29/0.99    inference(flattening,[],[f25])).
% 3.29/0.99  
% 3.29/0.99  fof(f33,plain,(
% 3.29/0.99    ? [X0,X1,X2] : (~r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v2_funct_1(X2) & r1_xboole_0(X0,X1) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_xboole_0(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)) & v2_funct_1(sK4) & r1_xboole_0(sK2,sK3) & v1_funct_1(sK4) & v1_relat_1(sK4))),
% 3.29/0.99    introduced(choice_axiom,[])).
% 3.29/0.99  
% 3.29/0.99  fof(f34,plain,(
% 3.29/0.99    ~r1_xboole_0(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)) & v2_funct_1(sK4) & r1_xboole_0(sK2,sK3) & v1_funct_1(sK4) & v1_relat_1(sK4)),
% 3.29/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f26,f33])).
% 3.29/0.99  
% 3.29/0.99  fof(f57,plain,(
% 3.29/0.99    r1_xboole_0(sK2,sK3)),
% 3.29/0.99    inference(cnf_transformation,[],[f34])).
% 3.29/0.99  
% 3.29/0.99  fof(f1,axiom,(
% 3.29/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.29/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f18,plain,(
% 3.29/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.29/0.99    inference(rectify,[],[f1])).
% 3.29/0.99  
% 3.29/0.99  fof(f20,plain,(
% 3.29/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.29/0.99    inference(ennf_transformation,[],[f18])).
% 3.29/0.99  
% 3.29/0.99  fof(f27,plain,(
% 3.29/0.99    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.29/0.99    introduced(choice_axiom,[])).
% 3.29/0.99  
% 3.29/0.99  fof(f28,plain,(
% 3.29/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 3.29/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f27])).
% 3.29/0.99  
% 3.29/0.99  fof(f36,plain,(
% 3.29/0.99    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 3.29/0.99    inference(cnf_transformation,[],[f28])).
% 3.29/0.99  
% 3.29/0.99  fof(f2,axiom,(
% 3.29/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.29/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f19,plain,(
% 3.29/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.29/0.99    inference(rectify,[],[f2])).
% 3.29/0.99  
% 3.29/0.99  fof(f21,plain,(
% 3.29/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.29/0.99    inference(ennf_transformation,[],[f19])).
% 3.29/0.99  
% 3.29/0.99  fof(f29,plain,(
% 3.29/0.99    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 3.29/0.99    introduced(choice_axiom,[])).
% 3.29/0.99  
% 3.29/0.99  fof(f30,plain,(
% 3.29/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.29/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f29])).
% 3.29/0.99  
% 3.29/0.99  fof(f39,plain,(
% 3.29/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 3.29/0.99    inference(cnf_transformation,[],[f30])).
% 3.29/0.99  
% 3.29/0.99  fof(f13,axiom,(
% 3.29/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.29/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f51,plain,(
% 3.29/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.29/0.99    inference(cnf_transformation,[],[f13])).
% 3.29/0.99  
% 3.29/0.99  fof(f7,axiom,(
% 3.29/0.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.29/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f45,plain,(
% 3.29/0.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.29/0.99    inference(cnf_transformation,[],[f7])).
% 3.29/0.99  
% 3.29/0.99  fof(f8,axiom,(
% 3.29/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.29/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f46,plain,(
% 3.29/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.29/0.99    inference(cnf_transformation,[],[f8])).
% 3.29/0.99  
% 3.29/0.99  fof(f9,axiom,(
% 3.29/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.29/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f47,plain,(
% 3.29/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.29/0.99    inference(cnf_transformation,[],[f9])).
% 3.29/0.99  
% 3.29/0.99  fof(f10,axiom,(
% 3.29/0.99    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.29/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f48,plain,(
% 3.29/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.29/0.99    inference(cnf_transformation,[],[f10])).
% 3.29/0.99  
% 3.29/0.99  fof(f11,axiom,(
% 3.29/0.99    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.29/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f49,plain,(
% 3.29/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.29/0.99    inference(cnf_transformation,[],[f11])).
% 3.29/0.99  
% 3.29/0.99  fof(f12,axiom,(
% 3.29/0.99    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.29/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f50,plain,(
% 3.29/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.29/0.99    inference(cnf_transformation,[],[f12])).
% 3.29/0.99  
% 3.29/0.99  fof(f60,plain,(
% 3.29/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.29/0.99    inference(definition_unfolding,[],[f49,f50])).
% 3.29/0.99  
% 3.29/0.99  fof(f61,plain,(
% 3.29/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.29/0.99    inference(definition_unfolding,[],[f48,f60])).
% 3.29/0.99  
% 3.29/0.99  fof(f62,plain,(
% 3.29/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.29/0.99    inference(definition_unfolding,[],[f47,f61])).
% 3.29/0.99  
% 3.29/0.99  fof(f63,plain,(
% 3.29/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.29/0.99    inference(definition_unfolding,[],[f46,f62])).
% 3.29/0.99  
% 3.29/0.99  fof(f64,plain,(
% 3.29/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.29/0.99    inference(definition_unfolding,[],[f45,f63])).
% 3.29/0.99  
% 3.29/0.99  fof(f65,plain,(
% 3.29/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 3.29/0.99    inference(definition_unfolding,[],[f51,f64])).
% 3.29/0.99  
% 3.29/0.99  fof(f67,plain,(
% 3.29/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 3.29/0.99    inference(definition_unfolding,[],[f39,f65])).
% 3.29/0.99  
% 3.29/0.99  fof(f14,axiom,(
% 3.29/0.99    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 3.29/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f22,plain,(
% 3.29/0.99    ! [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.29/0.99    inference(ennf_transformation,[],[f14])).
% 3.29/0.99  
% 3.29/0.99  fof(f32,plain,(
% 3.29/0.99    ! [X0,X1] : (((k1_xboole_0 = k9_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.29/0.99    inference(nnf_transformation,[],[f22])).
% 3.29/0.99  
% 3.29/0.99  fof(f53,plain,(
% 3.29/0.99    ( ! [X0,X1] : (k1_xboole_0 = k9_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.29/0.99    inference(cnf_transformation,[],[f32])).
% 3.29/0.99  
% 3.29/0.99  fof(f55,plain,(
% 3.29/0.99    v1_relat_1(sK4)),
% 3.29/0.99    inference(cnf_transformation,[],[f34])).
% 3.29/0.99  
% 3.29/0.99  fof(f15,axiom,(
% 3.29/0.99    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1))))),
% 3.29/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f23,plain,(
% 3.29/0.99    ! [X0,X1,X2] : ((k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.29/0.99    inference(ennf_transformation,[],[f15])).
% 3.29/0.99  
% 3.29/0.99  fof(f24,plain,(
% 3.29/0.99    ! [X0,X1,X2] : (k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.29/0.99    inference(flattening,[],[f23])).
% 3.29/0.99  
% 3.29/0.99  fof(f54,plain,(
% 3.29/0.99    ( ! [X2,X0,X1] : (k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.29/0.99    inference(cnf_transformation,[],[f24])).
% 3.29/0.99  
% 3.29/0.99  fof(f73,plain,(
% 3.29/0.99    ( ! [X2,X0,X1] : (k1_setfam_1(k6_enumset1(k9_relat_1(X2,X0),k9_relat_1(X2,X0),k9_relat_1(X2,X0),k9_relat_1(X2,X0),k9_relat_1(X2,X0),k9_relat_1(X2,X0),k9_relat_1(X2,X0),k9_relat_1(X2,X1))) = k9_relat_1(X2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.29/0.99    inference(definition_unfolding,[],[f54,f65,f65])).
% 3.29/0.99  
% 3.29/0.99  fof(f58,plain,(
% 3.29/0.99    v2_funct_1(sK4)),
% 3.29/0.99    inference(cnf_transformation,[],[f34])).
% 3.29/0.99  
% 3.29/0.99  fof(f56,plain,(
% 3.29/0.99    v1_funct_1(sK4)),
% 3.29/0.99    inference(cnf_transformation,[],[f34])).
% 3.29/0.99  
% 3.29/0.99  fof(f37,plain,(
% 3.29/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 3.29/0.99    inference(cnf_transformation,[],[f28])).
% 3.29/0.99  
% 3.29/0.99  fof(f38,plain,(
% 3.29/0.99    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 3.29/0.99    inference(cnf_transformation,[],[f30])).
% 3.29/0.99  
% 3.29/0.99  fof(f68,plain,(
% 3.29/0.99    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | r1_xboole_0(X0,X1)) )),
% 3.29/0.99    inference(definition_unfolding,[],[f38,f65])).
% 3.29/0.99  
% 3.29/0.99  fof(f59,plain,(
% 3.29/0.99    ~r1_xboole_0(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))),
% 3.29/0.99    inference(cnf_transformation,[],[f34])).
% 3.29/0.99  
% 3.29/0.99  fof(f5,axiom,(
% 3.29/0.99    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.29/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f42,plain,(
% 3.29/0.99    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.29/0.99    inference(cnf_transformation,[],[f5])).
% 3.29/0.99  
% 3.29/0.99  fof(f3,axiom,(
% 3.29/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.29/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f40,plain,(
% 3.29/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.29/0.99    inference(cnf_transformation,[],[f3])).
% 3.29/0.99  
% 3.29/0.99  fof(f66,plain,(
% 3.29/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 3.29/0.99    inference(definition_unfolding,[],[f40,f65])).
% 3.29/0.99  
% 3.29/0.99  fof(f70,plain,(
% 3.29/0.99    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) = X0) )),
% 3.29/0.99    inference(definition_unfolding,[],[f42,f66])).
% 3.29/0.99  
% 3.29/0.99  fof(f6,axiom,(
% 3.29/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 3.29/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f31,plain,(
% 3.29/0.99    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 3.29/0.99    inference(nnf_transformation,[],[f6])).
% 3.29/0.99  
% 3.29/0.99  fof(f44,plain,(
% 3.29/0.99    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 3.29/0.99    inference(cnf_transformation,[],[f31])).
% 3.29/0.99  
% 3.29/0.99  fof(f71,plain,(
% 3.29/0.99    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) != X0) )),
% 3.29/0.99    inference(definition_unfolding,[],[f44,f66])).
% 3.29/0.99  
% 3.29/0.99  cnf(c_14,negated_conjecture,
% 3.29/0.99      ( r1_xboole_0(sK2,sK3) ),
% 3.29/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_1364,plain,
% 3.29/0.99      ( r1_xboole_0(sK2,sK3) = iProver_top ),
% 3.29/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_1,plain,
% 3.29/0.99      ( r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1) ),
% 3.29/0.99      inference(cnf_transformation,[],[f36]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_1371,plain,
% 3.29/0.99      ( r2_hidden(sK0(X0,X1),X1) = iProver_top
% 3.29/0.99      | r1_xboole_0(X0,X1) = iProver_top ),
% 3.29/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_3,plain,
% 3.29/0.99      ( ~ r2_hidden(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))
% 3.29/0.99      | ~ r1_xboole_0(X1,X2) ),
% 3.29/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_1369,plain,
% 3.29/0.99      ( r2_hidden(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) != iProver_top
% 3.29/0.99      | r1_xboole_0(X1,X2) != iProver_top ),
% 3.29/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_2109,plain,
% 3.29/0.99      ( r1_xboole_0(X0,X1) != iProver_top
% 3.29/0.99      | r1_xboole_0(X2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
% 3.29/0.99      inference(superposition,[status(thm)],[c_1371,c_1369]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_9,plain,
% 3.29/0.99      ( ~ r1_xboole_0(k1_relat_1(X0),X1)
% 3.29/0.99      | ~ v1_relat_1(X0)
% 3.29/0.99      | k9_relat_1(X0,X1) = k1_xboole_0 ),
% 3.29/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_16,negated_conjecture,
% 3.29/0.99      ( v1_relat_1(sK4) ),
% 3.29/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_232,plain,
% 3.29/0.99      ( ~ r1_xboole_0(k1_relat_1(X0),X1)
% 3.29/0.99      | k9_relat_1(X0,X1) = k1_xboole_0
% 3.29/0.99      | sK4 != X0 ),
% 3.29/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_16]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_233,plain,
% 3.29/0.99      ( ~ r1_xboole_0(k1_relat_1(sK4),X0)
% 3.29/0.99      | k9_relat_1(sK4,X0) = k1_xboole_0 ),
% 3.29/0.99      inference(unflattening,[status(thm)],[c_232]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_641,plain,
% 3.29/0.99      ( ~ r1_xboole_0(k1_relat_1(sK4),X0)
% 3.29/0.99      | k9_relat_1(sK4,X0) = k1_xboole_0 ),
% 3.29/0.99      inference(prop_impl,[status(thm)],[c_233]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_1362,plain,
% 3.29/0.99      ( k9_relat_1(sK4,X0) = k1_xboole_0
% 3.29/0.99      | r1_xboole_0(k1_relat_1(sK4),X0) != iProver_top ),
% 3.29/0.99      inference(predicate_to_equality,[status(thm)],[c_641]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_3530,plain,
% 3.29/0.99      ( k9_relat_1(sK4,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k1_xboole_0
% 3.29/0.99      | r1_xboole_0(X0,X1) != iProver_top ),
% 3.29/0.99      inference(superposition,[status(thm)],[c_2109,c_1362]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_4235,plain,
% 3.29/0.99      ( k9_relat_1(sK4,k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))) = k1_xboole_0 ),
% 3.29/0.99      inference(superposition,[status(thm)],[c_1364,c_3530]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_1030,plain,
% 3.29/0.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.29/0.99      theory(equality) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_2698,plain,
% 3.29/0.99      ( ~ r1_xboole_0(X0,X1)
% 3.29/0.99      | r1_xboole_0(k9_relat_1(sK4,k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))),k9_relat_1(sK4,k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))))
% 3.29/0.99      | k9_relat_1(sK4,k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))) != X0
% 3.29/0.99      | k9_relat_1(sK4,k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))) != X1 ),
% 3.29/0.99      inference(instantiation,[status(thm)],[c_1030]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_2700,plain,
% 3.29/0.99      ( r1_xboole_0(k9_relat_1(sK4,k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))),k9_relat_1(sK4,k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))))
% 3.29/0.99      | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 3.29/0.99      | k9_relat_1(sK4,k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))) != k1_xboole_0 ),
% 3.29/0.99      inference(instantiation,[status(thm)],[c_2698]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_1816,plain,
% 3.29/0.99      ( ~ r1_xboole_0(X0,X1)
% 3.29/0.99      | r1_xboole_0(k1_setfam_1(k6_enumset1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))),k1_setfam_1(k6_enumset1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))))
% 3.29/0.99      | k1_setfam_1(k6_enumset1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))) != X0
% 3.29/0.99      | k1_setfam_1(k6_enumset1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))) != X1 ),
% 3.29/0.99      inference(instantiation,[status(thm)],[c_1030]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_2561,plain,
% 3.29/0.99      ( ~ r1_xboole_0(X0,k9_relat_1(sK4,k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))))
% 3.29/0.99      | r1_xboole_0(k1_setfam_1(k6_enumset1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))),k1_setfam_1(k6_enumset1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))))
% 3.29/0.99      | k1_setfam_1(k6_enumset1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))) != X0
% 3.29/0.99      | k1_setfam_1(k6_enumset1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))) != k9_relat_1(sK4,k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))) ),
% 3.29/0.99      inference(instantiation,[status(thm)],[c_1816]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_2575,plain,
% 3.29/0.99      ( ~ r1_xboole_0(k9_relat_1(sK4,k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))),k9_relat_1(sK4,k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))))
% 3.29/0.99      | r1_xboole_0(k1_setfam_1(k6_enumset1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))),k1_setfam_1(k6_enumset1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))))
% 3.29/0.99      | k1_setfam_1(k6_enumset1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))) != k9_relat_1(sK4,k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))) ),
% 3.29/0.99      inference(instantiation,[status(thm)],[c_2561]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_11,plain,
% 3.29/0.99      ( ~ v1_funct_1(X0)
% 3.29/0.99      | ~ v2_funct_1(X0)
% 3.29/0.99      | ~ v1_relat_1(X0)
% 3.29/0.99      | k1_setfam_1(k6_enumset1(k9_relat_1(X0,X1),k9_relat_1(X0,X1),k9_relat_1(X0,X1),k9_relat_1(X0,X1),k9_relat_1(X0,X1),k9_relat_1(X0,X1),k9_relat_1(X0,X1),k9_relat_1(X0,X2))) = k9_relat_1(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
% 3.29/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_13,negated_conjecture,
% 3.29/0.99      ( v2_funct_1(sK4) ),
% 3.29/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_208,plain,
% 3.29/0.99      ( ~ v1_funct_1(X0)
% 3.29/0.99      | ~ v1_relat_1(X0)
% 3.29/0.99      | k1_setfam_1(k6_enumset1(k9_relat_1(X0,X1),k9_relat_1(X0,X1),k9_relat_1(X0,X1),k9_relat_1(X0,X1),k9_relat_1(X0,X1),k9_relat_1(X0,X1),k9_relat_1(X0,X1),k9_relat_1(X0,X2))) = k9_relat_1(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))
% 3.29/0.99      | sK4 != X0 ),
% 3.29/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_13]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_209,plain,
% 3.29/0.99      ( ~ v1_funct_1(sK4)
% 3.29/0.99      | ~ v1_relat_1(sK4)
% 3.29/0.99      | k1_setfam_1(k6_enumset1(k9_relat_1(sK4,X0),k9_relat_1(sK4,X0),k9_relat_1(sK4,X0),k9_relat_1(sK4,X0),k9_relat_1(sK4,X0),k9_relat_1(sK4,X0),k9_relat_1(sK4,X0),k9_relat_1(sK4,X1))) = k9_relat_1(sK4,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
% 3.29/0.99      inference(unflattening,[status(thm)],[c_208]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_15,negated_conjecture,
% 3.29/0.99      ( v1_funct_1(sK4) ),
% 3.29/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_213,plain,
% 3.29/0.99      ( k1_setfam_1(k6_enumset1(k9_relat_1(sK4,X0),k9_relat_1(sK4,X0),k9_relat_1(sK4,X0),k9_relat_1(sK4,X0),k9_relat_1(sK4,X0),k9_relat_1(sK4,X0),k9_relat_1(sK4,X0),k9_relat_1(sK4,X1))) = k9_relat_1(sK4,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
% 3.29/0.99      inference(global_propositional_subsumption,
% 3.29/0.99                [status(thm)],
% 3.29/0.99                [c_209,c_16,c_15]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_2562,plain,
% 3.29/0.99      ( k1_setfam_1(k6_enumset1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))) = k9_relat_1(sK4,k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))) ),
% 3.29/0.99      inference(instantiation,[status(thm)],[c_213]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_0,plain,
% 3.29/0.99      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 3.29/0.99      inference(cnf_transformation,[],[f37]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_1520,plain,
% 3.29/0.99      ( ~ r2_hidden(sK1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)),X0)
% 3.29/0.99      | ~ r2_hidden(sK1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)),k1_setfam_1(k6_enumset1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))))
% 3.29/0.99      | ~ r1_xboole_0(k1_setfam_1(k6_enumset1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))),X0) ),
% 3.29/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_1611,plain,
% 3.29/0.99      ( ~ r2_hidden(sK1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)),k1_setfam_1(k6_enumset1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))))
% 3.29/0.99      | ~ r1_xboole_0(k1_setfam_1(k6_enumset1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))),k1_setfam_1(k6_enumset1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)))) ),
% 3.29/0.99      inference(instantiation,[status(thm)],[c_1520]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_4,plain,
% 3.29/0.99      ( r2_hidden(sK1(X0,X1),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
% 3.29/0.99      | r1_xboole_0(X0,X1) ),
% 3.29/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_12,negated_conjecture,
% 3.29/0.99      ( ~ r1_xboole_0(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)) ),
% 3.29/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_388,plain,
% 3.29/0.99      ( r2_hidden(sK1(X0,X1),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
% 3.29/0.99      | k9_relat_1(sK4,sK3) != X1
% 3.29/0.99      | k9_relat_1(sK4,sK2) != X0 ),
% 3.29/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_12]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_389,plain,
% 3.29/0.99      ( r2_hidden(sK1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)),k1_setfam_1(k6_enumset1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)))) ),
% 3.29/0.99      inference(unflattening,[status(thm)],[c_388]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_6,plain,
% 3.29/0.99      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) = X0 ),
% 3.29/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_37,plain,
% 3.29/0.99      ( k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k1_xboole_0 ),
% 3.29/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_7,plain,
% 3.29/0.99      ( r1_xboole_0(X0,X1)
% 3.29/0.99      | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) != X0 ),
% 3.29/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_35,plain,
% 3.29/0.99      ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 3.29/0.99      | k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) != k1_xboole_0 ),
% 3.29/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(contradiction,plain,
% 3.29/0.99      ( $false ),
% 3.29/0.99      inference(minisat,
% 3.29/0.99                [status(thm)],
% 3.29/0.99                [c_4235,c_2700,c_2575,c_2562,c_1611,c_389,c_37,c_35]) ).
% 3.29/0.99  
% 3.29/0.99  
% 3.29/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.29/0.99  
% 3.29/0.99  ------                               Statistics
% 3.29/0.99  
% 3.29/0.99  ------ Selected
% 3.29/0.99  
% 3.29/0.99  total_time:                             0.18
% 3.29/0.99  
%------------------------------------------------------------------------------
