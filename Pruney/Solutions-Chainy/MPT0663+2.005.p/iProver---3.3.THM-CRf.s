%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:51:00 EST 2020

% Result     : Theorem 3.69s
% Output     : CNFRefutation 3.69s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 616 expanded)
%              Number of clauses        :   67 ( 143 expanded)
%              Number of leaves         :   21 ( 173 expanded)
%              Depth                    :   21
%              Number of atoms          :  337 (1006 expanded)
%              Number of equality atoms :  208 ( 689 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f15,axiom,(
    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f8,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f7])).

fof(f61,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f40,f41])).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f39,f61])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f38,f62])).

fof(f64,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f37,f63])).

fof(f65,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f36,f64])).

fof(f66,plain,(
    ! [X0,X1] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f42,f65])).

fof(f68,plain,(
    ! [X0,X1] : k6_relat_1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(definition_unfolding,[],[f56,f66])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f43,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f67,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f35,f65,f65])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
       => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
         => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0)
      & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0)
      & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f33,plain,
    ( ? [X0,X1,X2] :
        ( k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0)
        & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k1_funct_1(sK3,sK1) != k1_funct_1(k7_relat_1(sK3,sK2),sK1)
      & r2_hidden(sK1,k3_xboole_0(k1_relat_1(sK3),sK2))
      & v1_funct_1(sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( k1_funct_1(sK3,sK1) != k1_funct_1(k7_relat_1(sK3,sK2),sK1)
    & r2_hidden(sK1,k3_xboole_0(k1_relat_1(sK3),sK2))
    & v1_funct_1(sK3)
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f25,f33])).

fof(f59,plain,(
    r2_hidden(sK1,k3_xboole_0(k1_relat_1(sK3),sK2)) ),
    inference(cnf_transformation,[],[f34])).

fof(f69,plain,(
    r2_hidden(sK1,k1_setfam_1(k6_enumset1(k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),sK2))) ),
    inference(definition_unfolding,[],[f59,f66])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X1,X2) != X2
          & r2_hidden(X2,X0) )
     => ( k1_funct_1(X1,sK0(X0,X1)) != sK0(X0,X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( k1_funct_1(X1,sK0(X0,X1)) != sK0(X0,X1)
            & r2_hidden(sK0(X0,X1),X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(X1,X3) = X3
      | ~ r2_hidden(X3,X0)
      | k6_relat_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f72,plain,(
    ! [X0,X3] :
      ( k1_funct_1(k6_relat_1(X0),X3) = X3
      | ~ r2_hidden(X3,X0)
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f53])).

fof(f50,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f60,plain,(
    k1_funct_1(sK3,sK1) != k1_funct_1(k7_relat_1(sK3,sK2),sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f58,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f57,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_267,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_736,plain,
    ( X0 != X1
    | k1_funct_1(sK3,sK1) != X1
    | k1_funct_1(sK3,sK1) = X0 ),
    inference(instantiation,[status(thm)],[c_267])).

cnf(c_969,plain,
    ( X0 != k1_funct_1(sK3,sK1)
    | k1_funct_1(sK3,sK1) = X0
    | k1_funct_1(sK3,sK1) != k1_funct_1(sK3,sK1) ),
    inference(instantiation,[status(thm)],[c_736])).

cnf(c_1439,plain,
    ( k1_funct_1(X0,X1) != k1_funct_1(sK3,sK1)
    | k1_funct_1(sK3,sK1) = k1_funct_1(X0,X1)
    | k1_funct_1(sK3,sK1) != k1_funct_1(sK3,sK1) ),
    inference(instantiation,[status(thm)],[c_969])).

cnf(c_2886,plain,
    ( k1_funct_1(X0,sK1) != k1_funct_1(sK3,sK1)
    | k1_funct_1(sK3,sK1) = k1_funct_1(X0,sK1)
    | k1_funct_1(sK3,sK1) != k1_funct_1(sK3,sK1) ),
    inference(instantiation,[status(thm)],[c_1439])).

cnf(c_11341,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1) != k1_funct_1(sK3,sK1)
    | k1_funct_1(sK3,sK1) = k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1)
    | k1_funct_1(sK3,sK1) != k1_funct_1(sK3,sK1) ),
    inference(instantiation,[status(thm)],[c_2886])).

cnf(c_814,plain,
    ( k1_funct_1(k7_relat_1(sK3,sK2),sK1) != X0
    | k1_funct_1(k7_relat_1(sK3,sK2),sK1) = k1_funct_1(sK3,sK1)
    | k1_funct_1(sK3,sK1) != X0 ),
    inference(instantiation,[status(thm)],[c_267])).

cnf(c_7566,plain,
    ( k1_funct_1(k7_relat_1(sK3,sK2),sK1) != k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1)
    | k1_funct_1(k7_relat_1(sK3,sK2),sK1) = k1_funct_1(sK3,sK1)
    | k1_funct_1(sK3,sK1) != k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1) ),
    inference(instantiation,[status(thm)],[c_814])).

cnf(c_8,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_539,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_541,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1840,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_539,c_541])).

cnf(c_14,plain,
    ( k6_relat_1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_891,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_14,c_1])).

cnf(c_893,plain,
    ( k6_relat_1(k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ),
    inference(demodulation,[status(thm)],[c_891,c_14])).

cnf(c_2,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1307,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
    inference(superposition,[status(thm)],[c_893,c_2])).

cnf(c_890,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_14,c_2])).

cnf(c_0,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_16,negated_conjecture,
    ( r2_hidden(sK1,k1_setfam_1(k6_enumset1(k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),sK2))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_534,plain,
    ( r2_hidden(sK1,k1_setfam_1(k6_enumset1(k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_993,plain,
    ( r2_hidden(sK1,k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k1_relat_1(sK3)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_0,c_534])).

cnf(c_997,plain,
    ( r2_hidden(sK1,k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK3)),k6_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_890,c_993])).

cnf(c_1805,plain,
    ( r2_hidden(sK1,k2_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK3)),k6_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1307,c_997])).

cnf(c_4719,plain,
    ( r2_hidden(sK1,k2_relat_1(k7_relat_1(k6_relat_1(sK2),k1_relat_1(sK3)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1840,c_1805])).

cnf(c_4711,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(demodulation,[status(thm)],[c_1840,c_1307])).

cnf(c_4,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_543,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
    | r2_hidden(X0,k1_relat_1(k7_relat_1(X1,X2))) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_6097,plain,
    ( r2_hidden(X0,k1_relat_1(k6_relat_1(X1))) = iProver_top
    | r2_hidden(X0,k2_relat_1(k7_relat_1(k6_relat_1(X1),X2))) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4711,c_543])).

cnf(c_6127,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k2_relat_1(k7_relat_1(k6_relat_1(X1),X2))) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6097,c_2])).

cnf(c_6160,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k2_relat_1(k7_relat_1(k6_relat_1(X1),X2))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6127,c_539])).

cnf(c_6164,plain,
    ( r2_hidden(sK1,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4719,c_6160])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_funct_1(k6_relat_1(X1))
    | ~ v1_relat_1(k6_relat_1(X1))
    | k1_funct_1(k6_relat_1(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_535,plain,
    ( k1_funct_1(k6_relat_1(X0),X1) = X1
    | r2_hidden(X1,X0) != iProver_top
    | v1_funct_1(k6_relat_1(X0)) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_7,plain,
    ( v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_540,plain,
    ( v1_funct_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_585,plain,
    ( k1_funct_1(k6_relat_1(X0),X1) = X1
    | r2_hidden(X1,X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_535,c_539,c_540])).

cnf(c_6874,plain,
    ( k1_funct_1(k6_relat_1(sK2),sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_6164,c_585])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_538,plain,
    ( k1_funct_1(k5_relat_1(X0,X1),X2) = k1_funct_1(X1,k1_funct_1(X0,X2))
    | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2742,plain,
    ( k1_funct_1(X0,k1_funct_1(k6_relat_1(X1),X2)) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X0),X2)
    | r2_hidden(X2,X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k6_relat_1(X1)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_538])).

cnf(c_4473,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1(X0),X1),X2) = k1_funct_1(X1,k1_funct_1(k6_relat_1(X0),X2))
    | r2_hidden(X2,X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2742,c_539,c_540])).

cnf(c_6875,plain,
    ( k1_funct_1(X0,k1_funct_1(k6_relat_1(sK2),sK1)) = k1_funct_1(k5_relat_1(k6_relat_1(sK2),X0),sK1)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6164,c_4473])).

cnf(c_6883,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1(sK2),X0),sK1) = k1_funct_1(X0,sK1)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6874,c_6875])).

cnf(c_6892,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1) = k1_funct_1(sK3,sK1)
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6883])).

cnf(c_277,plain,
    ( X0 != X1
    | X2 != X3
    | k1_funct_1(X0,X2) = k1_funct_1(X1,X3) ),
    theory(equality)).

cnf(c_978,plain,
    ( k1_funct_1(k7_relat_1(sK3,sK2),sK1) = k1_funct_1(X0,X1)
    | k7_relat_1(sK3,sK2) != X0
    | sK1 != X1 ),
    inference(instantiation,[status(thm)],[c_277])).

cnf(c_1661,plain,
    ( k1_funct_1(k7_relat_1(sK3,sK2),sK1) = k1_funct_1(X0,sK1)
    | k7_relat_1(sK3,sK2) != X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_978])).

cnf(c_4370,plain,
    ( k1_funct_1(k7_relat_1(sK3,sK2),sK1) = k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1)
    | k7_relat_1(sK3,sK2) != k5_relat_1(k6_relat_1(sK2),sK3)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1661])).

cnf(c_1949,plain,
    ( ~ v1_relat_1(sK3)
    | k5_relat_1(k6_relat_1(sK2),sK3) = k7_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_959,plain,
    ( X0 != X1
    | k7_relat_1(sK3,sK2) != X1
    | k7_relat_1(sK3,sK2) = X0 ),
    inference(instantiation,[status(thm)],[c_267])).

cnf(c_1250,plain,
    ( X0 != k7_relat_1(sK3,sK2)
    | k7_relat_1(sK3,sK2) = X0
    | k7_relat_1(sK3,sK2) != k7_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_959])).

cnf(c_1948,plain,
    ( k5_relat_1(k6_relat_1(sK2),sK3) != k7_relat_1(sK3,sK2)
    | k7_relat_1(sK3,sK2) = k5_relat_1(k6_relat_1(sK2),sK3)
    | k7_relat_1(sK3,sK2) != k7_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_1250])).

cnf(c_266,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1251,plain,
    ( k7_relat_1(sK3,sK2) = k7_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_266])).

cnf(c_735,plain,
    ( k1_funct_1(sK3,sK1) = k1_funct_1(sK3,sK1) ),
    inference(instantiation,[status(thm)],[c_266])).

cnf(c_684,plain,
    ( k1_funct_1(k7_relat_1(sK3,sK2),sK1) != X0
    | k1_funct_1(sK3,sK1) != X0
    | k1_funct_1(sK3,sK1) = k1_funct_1(k7_relat_1(sK3,sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_267])).

cnf(c_734,plain,
    ( k1_funct_1(k7_relat_1(sK3,sK2),sK1) != k1_funct_1(sK3,sK1)
    | k1_funct_1(sK3,sK1) = k1_funct_1(k7_relat_1(sK3,sK2),sK1)
    | k1_funct_1(sK3,sK1) != k1_funct_1(sK3,sK1) ),
    inference(instantiation,[status(thm)],[c_684])).

cnf(c_732,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_266])).

cnf(c_15,negated_conjecture,
    ( k1_funct_1(sK3,sK1) != k1_funct_1(k7_relat_1(sK3,sK2),sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_17,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_20,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_18,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_19,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11341,c_7566,c_6892,c_4370,c_1949,c_1948,c_1251,c_735,c_734,c_732,c_15,c_20,c_19,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:44:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.69/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.69/0.99  
% 3.69/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.69/0.99  
% 3.69/0.99  ------  iProver source info
% 3.69/0.99  
% 3.69/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.69/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.69/0.99  git: non_committed_changes: false
% 3.69/0.99  git: last_make_outside_of_git: false
% 3.69/0.99  
% 3.69/0.99  ------ 
% 3.69/0.99  ------ Parsing...
% 3.69/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.69/0.99  
% 3.69/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.69/0.99  
% 3.69/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.69/0.99  
% 3.69/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.69/0.99  ------ Proving...
% 3.69/0.99  ------ Problem Properties 
% 3.69/0.99  
% 3.69/0.99  
% 3.69/0.99  clauses                                 18
% 3.69/0.99  conjectures                             4
% 3.69/0.99  EPR                                     2
% 3.69/0.99  Horn                                    17
% 3.69/0.99  unary                                   10
% 3.69/0.99  binary                                  1
% 3.69/0.99  lits                                    40
% 3.69/0.99  lits eq                                 11
% 3.69/0.99  fd_pure                                 0
% 3.69/0.99  fd_pseudo                               0
% 3.69/0.99  fd_cond                                 0
% 3.69/0.99  fd_pseudo_cond                          0
% 3.69/0.99  AC symbols                              0
% 3.69/0.99  
% 3.69/0.99  ------ Input Options Time Limit: Unbounded
% 3.69/0.99  
% 3.69/0.99  
% 3.69/0.99  ------ 
% 3.69/0.99  Current options:
% 3.69/0.99  ------ 
% 3.69/0.99  
% 3.69/0.99  
% 3.69/0.99  
% 3.69/0.99  
% 3.69/0.99  ------ Proving...
% 3.69/0.99  
% 3.69/0.99  
% 3.69/0.99  % SZS status Theorem for theBenchmark.p
% 3.69/0.99  
% 3.69/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.69/0.99  
% 3.69/0.99  fof(f12,axiom,(
% 3.69/0.99    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.69/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.99  
% 3.69/0.99  fof(f49,plain,(
% 3.69/0.99    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 3.69/0.99    inference(cnf_transformation,[],[f12])).
% 3.69/0.99  
% 3.69/0.99  fof(f11,axiom,(
% 3.69/0.99    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 3.69/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.99  
% 3.69/0.99  fof(f19,plain,(
% 3.69/0.99    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 3.69/0.99    inference(ennf_transformation,[],[f11])).
% 3.69/0.99  
% 3.69/0.99  fof(f48,plain,(
% 3.69/0.99    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 3.69/0.99    inference(cnf_transformation,[],[f19])).
% 3.69/0.99  
% 3.69/0.99  fof(f15,axiom,(
% 3.69/0.99    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))),
% 3.69/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.99  
% 3.69/0.99  fof(f56,plain,(
% 3.69/0.99    ( ! [X0,X1] : (k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) )),
% 3.69/0.99    inference(cnf_transformation,[],[f15])).
% 3.69/0.99  
% 3.69/0.99  fof(f8,axiom,(
% 3.69/0.99    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 3.69/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.99  
% 3.69/0.99  fof(f42,plain,(
% 3.69/0.99    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 3.69/0.99    inference(cnf_transformation,[],[f8])).
% 3.69/0.99  
% 3.69/0.99  fof(f2,axiom,(
% 3.69/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.69/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.99  
% 3.69/0.99  fof(f36,plain,(
% 3.69/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.69/0.99    inference(cnf_transformation,[],[f2])).
% 3.69/0.99  
% 3.69/0.99  fof(f3,axiom,(
% 3.69/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.69/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.99  
% 3.69/0.99  fof(f37,plain,(
% 3.69/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.69/0.99    inference(cnf_transformation,[],[f3])).
% 3.69/0.99  
% 3.69/0.99  fof(f4,axiom,(
% 3.69/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.69/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.99  
% 3.69/0.99  fof(f38,plain,(
% 3.69/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.69/0.99    inference(cnf_transformation,[],[f4])).
% 3.69/0.99  
% 3.69/0.99  fof(f5,axiom,(
% 3.69/0.99    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.69/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.99  
% 3.69/0.99  fof(f39,plain,(
% 3.69/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.69/0.99    inference(cnf_transformation,[],[f5])).
% 3.69/0.99  
% 3.69/0.99  fof(f6,axiom,(
% 3.69/0.99    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.69/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.99  
% 3.69/0.99  fof(f40,plain,(
% 3.69/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.69/0.99    inference(cnf_transformation,[],[f6])).
% 3.69/0.99  
% 3.69/0.99  fof(f7,axiom,(
% 3.69/0.99    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.69/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.99  
% 3.69/0.99  fof(f41,plain,(
% 3.69/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.69/0.99    inference(cnf_transformation,[],[f7])).
% 3.69/0.99  
% 3.69/0.99  fof(f61,plain,(
% 3.69/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.69/0.99    inference(definition_unfolding,[],[f40,f41])).
% 3.69/0.99  
% 3.69/0.99  fof(f62,plain,(
% 3.69/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.69/0.99    inference(definition_unfolding,[],[f39,f61])).
% 3.69/0.99  
% 3.69/0.99  fof(f63,plain,(
% 3.69/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.69/0.99    inference(definition_unfolding,[],[f38,f62])).
% 3.69/0.99  
% 3.69/0.99  fof(f64,plain,(
% 3.69/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.69/0.99    inference(definition_unfolding,[],[f37,f63])).
% 3.69/0.99  
% 3.69/0.99  fof(f65,plain,(
% 3.69/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.69/0.99    inference(definition_unfolding,[],[f36,f64])).
% 3.69/0.99  
% 3.69/0.99  fof(f66,plain,(
% 3.69/0.99    ( ! [X0,X1] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k3_xboole_0(X0,X1)) )),
% 3.69/0.99    inference(definition_unfolding,[],[f42,f65])).
% 3.69/0.99  
% 3.69/0.99  fof(f68,plain,(
% 3.69/0.99    ( ! [X0,X1] : (k6_relat_1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) )),
% 3.69/0.99    inference(definition_unfolding,[],[f56,f66])).
% 3.69/0.99  
% 3.69/0.99  fof(f9,axiom,(
% 3.69/0.99    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.69/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.99  
% 3.69/0.99  fof(f44,plain,(
% 3.69/0.99    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.69/0.99    inference(cnf_transformation,[],[f9])).
% 3.69/0.99  
% 3.69/0.99  fof(f43,plain,(
% 3.69/0.99    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.69/0.99    inference(cnf_transformation,[],[f9])).
% 3.69/0.99  
% 3.69/0.99  fof(f1,axiom,(
% 3.69/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.69/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.99  
% 3.69/0.99  fof(f35,plain,(
% 3.69/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.69/0.99    inference(cnf_transformation,[],[f1])).
% 3.69/0.99  
% 3.69/0.99  fof(f67,plain,(
% 3.69/0.99    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) )),
% 3.69/0.99    inference(definition_unfolding,[],[f35,f65,f65])).
% 3.69/0.99  
% 3.69/0.99  fof(f16,conjecture,(
% 3.69/0.99    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)))),
% 3.69/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.99  
% 3.69/0.99  fof(f17,negated_conjecture,(
% 3.69/0.99    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)))),
% 3.69/0.99    inference(negated_conjecture,[],[f16])).
% 3.69/0.99  
% 3.69/0.99  fof(f24,plain,(
% 3.69/0.99    ? [X0,X1,X2] : ((k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0) & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 3.69/0.99    inference(ennf_transformation,[],[f17])).
% 3.69/0.99  
% 3.69/0.99  fof(f25,plain,(
% 3.69/0.99    ? [X0,X1,X2] : (k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0) & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 3.69/0.99    inference(flattening,[],[f24])).
% 3.69/0.99  
% 3.69/0.99  fof(f33,plain,(
% 3.69/0.99    ? [X0,X1,X2] : (k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0) & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (k1_funct_1(sK3,sK1) != k1_funct_1(k7_relat_1(sK3,sK2),sK1) & r2_hidden(sK1,k3_xboole_0(k1_relat_1(sK3),sK2)) & v1_funct_1(sK3) & v1_relat_1(sK3))),
% 3.69/0.99    introduced(choice_axiom,[])).
% 3.69/0.99  
% 3.69/0.99  fof(f34,plain,(
% 3.69/0.99    k1_funct_1(sK3,sK1) != k1_funct_1(k7_relat_1(sK3,sK2),sK1) & r2_hidden(sK1,k3_xboole_0(k1_relat_1(sK3),sK2)) & v1_funct_1(sK3) & v1_relat_1(sK3)),
% 3.69/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f25,f33])).
% 3.69/0.99  
% 3.69/0.99  fof(f59,plain,(
% 3.69/0.99    r2_hidden(sK1,k3_xboole_0(k1_relat_1(sK3),sK2))),
% 3.69/0.99    inference(cnf_transformation,[],[f34])).
% 3.69/0.99  
% 3.69/0.99  fof(f69,plain,(
% 3.69/0.99    r2_hidden(sK1,k1_setfam_1(k6_enumset1(k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),sK2)))),
% 3.69/0.99    inference(definition_unfolding,[],[f59,f66])).
% 3.69/0.99  
% 3.69/0.99  fof(f10,axiom,(
% 3.69/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 3.69/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.99  
% 3.69/0.99  fof(f18,plain,(
% 3.69/0.99    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 3.69/0.99    inference(ennf_transformation,[],[f10])).
% 3.69/0.99  
% 3.69/0.99  fof(f26,plain,(
% 3.69/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | (~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1))) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 3.69/0.99    inference(nnf_transformation,[],[f18])).
% 3.69/0.99  
% 3.69/0.99  fof(f27,plain,(
% 3.69/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1)) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 3.69/0.99    inference(flattening,[],[f26])).
% 3.69/0.99  
% 3.69/0.99  fof(f46,plain,(
% 3.69/0.99    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~v1_relat_1(X2)) )),
% 3.69/0.99    inference(cnf_transformation,[],[f27])).
% 3.69/0.99  
% 3.69/0.99  fof(f14,axiom,(
% 3.69/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 3.69/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.99  
% 3.69/0.99  fof(f22,plain,(
% 3.69/0.99    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.69/0.99    inference(ennf_transformation,[],[f14])).
% 3.69/0.99  
% 3.69/0.99  fof(f23,plain,(
% 3.69/0.99    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.69/0.99    inference(flattening,[],[f22])).
% 3.69/0.99  
% 3.69/0.99  fof(f28,plain,(
% 3.69/0.99    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0)) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.69/0.99    inference(nnf_transformation,[],[f23])).
% 3.69/0.99  
% 3.69/0.99  fof(f29,plain,(
% 3.69/0.99    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.69/0.99    inference(flattening,[],[f28])).
% 3.69/0.99  
% 3.69/0.99  fof(f30,plain,(
% 3.69/0.99    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.69/0.99    inference(rectify,[],[f29])).
% 3.69/0.99  
% 3.69/0.99  fof(f31,plain,(
% 3.69/0.99    ! [X1,X0] : (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) => (k1_funct_1(X1,sK0(X0,X1)) != sK0(X0,X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.69/0.99    introduced(choice_axiom,[])).
% 3.69/0.99  
% 3.69/0.99  fof(f32,plain,(
% 3.69/0.99    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (k1_funct_1(X1,sK0(X0,X1)) != sK0(X0,X1) & r2_hidden(sK0(X0,X1),X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.69/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).
% 3.69/0.99  
% 3.69/0.99  fof(f53,plain,(
% 3.69/0.99    ( ! [X0,X3,X1] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0) | k6_relat_1(X0) != X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.69/0.99    inference(cnf_transformation,[],[f32])).
% 3.69/0.99  
% 3.69/0.99  fof(f72,plain,(
% 3.69/0.99    ( ! [X0,X3] : (k1_funct_1(k6_relat_1(X0),X3) = X3 | ~r2_hidden(X3,X0) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 3.69/0.99    inference(equality_resolution,[],[f53])).
% 3.69/0.99  
% 3.69/0.99  fof(f50,plain,(
% 3.69/0.99    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 3.69/0.99    inference(cnf_transformation,[],[f12])).
% 3.69/0.99  
% 3.69/0.99  fof(f13,axiom,(
% 3.69/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0))))),
% 3.69/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.99  
% 3.69/0.99  fof(f20,plain,(
% 3.69/0.99    ! [X0,X1] : (! [X2] : ((k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.69/0.99    inference(ennf_transformation,[],[f13])).
% 3.69/0.99  
% 3.69/0.99  fof(f21,plain,(
% 3.69/0.99    ! [X0,X1] : (! [X2] : (k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.69/0.99    inference(flattening,[],[f20])).
% 3.69/0.99  
% 3.69/0.99  fof(f51,plain,(
% 3.69/0.99    ( ! [X2,X0,X1] : (k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.69/0.99    inference(cnf_transformation,[],[f21])).
% 3.69/0.99  
% 3.69/0.99  fof(f60,plain,(
% 3.69/0.99    k1_funct_1(sK3,sK1) != k1_funct_1(k7_relat_1(sK3,sK2),sK1)),
% 3.69/0.99    inference(cnf_transformation,[],[f34])).
% 3.69/0.99  
% 3.69/0.99  fof(f58,plain,(
% 3.69/0.99    v1_funct_1(sK3)),
% 3.69/0.99    inference(cnf_transformation,[],[f34])).
% 3.69/0.99  
% 3.69/0.99  fof(f57,plain,(
% 3.69/0.99    v1_relat_1(sK3)),
% 3.69/0.99    inference(cnf_transformation,[],[f34])).
% 3.69/0.99  
% 3.69/0.99  cnf(c_267,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_736,plain,
% 3.69/0.99      ( X0 != X1 | k1_funct_1(sK3,sK1) != X1 | k1_funct_1(sK3,sK1) = X0 ),
% 3.69/0.99      inference(instantiation,[status(thm)],[c_267]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_969,plain,
% 3.69/0.99      ( X0 != k1_funct_1(sK3,sK1)
% 3.69/0.99      | k1_funct_1(sK3,sK1) = X0
% 3.69/0.99      | k1_funct_1(sK3,sK1) != k1_funct_1(sK3,sK1) ),
% 3.69/0.99      inference(instantiation,[status(thm)],[c_736]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_1439,plain,
% 3.69/0.99      ( k1_funct_1(X0,X1) != k1_funct_1(sK3,sK1)
% 3.69/0.99      | k1_funct_1(sK3,sK1) = k1_funct_1(X0,X1)
% 3.69/0.99      | k1_funct_1(sK3,sK1) != k1_funct_1(sK3,sK1) ),
% 3.69/0.99      inference(instantiation,[status(thm)],[c_969]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_2886,plain,
% 3.69/0.99      ( k1_funct_1(X0,sK1) != k1_funct_1(sK3,sK1)
% 3.69/0.99      | k1_funct_1(sK3,sK1) = k1_funct_1(X0,sK1)
% 3.69/0.99      | k1_funct_1(sK3,sK1) != k1_funct_1(sK3,sK1) ),
% 3.69/0.99      inference(instantiation,[status(thm)],[c_1439]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_11341,plain,
% 3.69/0.99      ( k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1) != k1_funct_1(sK3,sK1)
% 3.69/0.99      | k1_funct_1(sK3,sK1) = k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1)
% 3.69/0.99      | k1_funct_1(sK3,sK1) != k1_funct_1(sK3,sK1) ),
% 3.69/0.99      inference(instantiation,[status(thm)],[c_2886]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_814,plain,
% 3.69/0.99      ( k1_funct_1(k7_relat_1(sK3,sK2),sK1) != X0
% 3.69/0.99      | k1_funct_1(k7_relat_1(sK3,sK2),sK1) = k1_funct_1(sK3,sK1)
% 3.69/0.99      | k1_funct_1(sK3,sK1) != X0 ),
% 3.69/0.99      inference(instantiation,[status(thm)],[c_267]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_7566,plain,
% 3.69/0.99      ( k1_funct_1(k7_relat_1(sK3,sK2),sK1) != k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1)
% 3.69/0.99      | k1_funct_1(k7_relat_1(sK3,sK2),sK1) = k1_funct_1(sK3,sK1)
% 3.69/0.99      | k1_funct_1(sK3,sK1) != k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1) ),
% 3.69/0.99      inference(instantiation,[status(thm)],[c_814]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_8,plain,
% 3.69/0.99      ( v1_relat_1(k6_relat_1(X0)) ),
% 3.69/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_539,plain,
% 3.69/0.99      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 3.69/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_6,plain,
% 3.69/0.99      ( ~ v1_relat_1(X0)
% 3.69/0.99      | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
% 3.69/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_541,plain,
% 3.69/0.99      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
% 3.69/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.69/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_1840,plain,
% 3.69/0.99      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_539,c_541]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_14,plain,
% 3.69/0.99      ( k6_relat_1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
% 3.69/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_1,plain,
% 3.69/0.99      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 3.69/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_891,plain,
% 3.69/0.99      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_14,c_1]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_893,plain,
% 3.69/0.99      ( k6_relat_1(k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ),
% 3.69/0.99      inference(demodulation,[status(thm)],[c_891,c_14]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_2,plain,
% 3.69/0.99      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 3.69/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_1307,plain,
% 3.69/0.99      ( k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_893,c_2]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_890,plain,
% 3.69/0.99      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_14,c_2]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_0,plain,
% 3.69/0.99      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
% 3.69/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_16,negated_conjecture,
% 3.69/0.99      ( r2_hidden(sK1,k1_setfam_1(k6_enumset1(k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),sK2))) ),
% 3.69/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_534,plain,
% 3.69/0.99      ( r2_hidden(sK1,k1_setfam_1(k6_enumset1(k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),sK2))) = iProver_top ),
% 3.69/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_993,plain,
% 3.69/0.99      ( r2_hidden(sK1,k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k1_relat_1(sK3)))) = iProver_top ),
% 3.69/0.99      inference(demodulation,[status(thm)],[c_0,c_534]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_997,plain,
% 3.69/0.99      ( r2_hidden(sK1,k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK3)),k6_relat_1(sK2)))) = iProver_top ),
% 3.69/0.99      inference(demodulation,[status(thm)],[c_890,c_993]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_1805,plain,
% 3.69/0.99      ( r2_hidden(sK1,k2_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK3)),k6_relat_1(sK2)))) = iProver_top ),
% 3.69/0.99      inference(demodulation,[status(thm)],[c_1307,c_997]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_4719,plain,
% 3.69/0.99      ( r2_hidden(sK1,k2_relat_1(k7_relat_1(k6_relat_1(sK2),k1_relat_1(sK3)))) = iProver_top ),
% 3.69/0.99      inference(demodulation,[status(thm)],[c_1840,c_1805]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_4711,plain,
% 3.69/0.99      ( k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 3.69/0.99      inference(demodulation,[status(thm)],[c_1840,c_1307]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_4,plain,
% 3.69/0.99      ( r2_hidden(X0,k1_relat_1(X1))
% 3.69/0.99      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X1,X2)))
% 3.69/0.99      | ~ v1_relat_1(X1) ),
% 3.69/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_543,plain,
% 3.69/0.99      ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
% 3.69/0.99      | r2_hidden(X0,k1_relat_1(k7_relat_1(X1,X2))) != iProver_top
% 3.69/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.69/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_6097,plain,
% 3.69/0.99      ( r2_hidden(X0,k1_relat_1(k6_relat_1(X1))) = iProver_top
% 3.69/0.99      | r2_hidden(X0,k2_relat_1(k7_relat_1(k6_relat_1(X1),X2))) != iProver_top
% 3.69/0.99      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_4711,c_543]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_6127,plain,
% 3.69/0.99      ( r2_hidden(X0,X1) = iProver_top
% 3.69/0.99      | r2_hidden(X0,k2_relat_1(k7_relat_1(k6_relat_1(X1),X2))) != iProver_top
% 3.69/0.99      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 3.69/0.99      inference(demodulation,[status(thm)],[c_6097,c_2]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_6160,plain,
% 3.69/0.99      ( r2_hidden(X0,X1) = iProver_top
% 3.69/0.99      | r2_hidden(X0,k2_relat_1(k7_relat_1(k6_relat_1(X1),X2))) != iProver_top ),
% 3.69/0.99      inference(forward_subsumption_resolution,
% 3.69/0.99                [status(thm)],
% 3.69/0.99                [c_6127,c_539]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_6164,plain,
% 3.69/0.99      ( r2_hidden(sK1,sK2) = iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_4719,c_6160]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_12,plain,
% 3.69/0.99      ( ~ r2_hidden(X0,X1)
% 3.69/0.99      | ~ v1_funct_1(k6_relat_1(X1))
% 3.69/0.99      | ~ v1_relat_1(k6_relat_1(X1))
% 3.69/0.99      | k1_funct_1(k6_relat_1(X1),X0) = X0 ),
% 3.69/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_535,plain,
% 3.69/0.99      ( k1_funct_1(k6_relat_1(X0),X1) = X1
% 3.69/0.99      | r2_hidden(X1,X0) != iProver_top
% 3.69/0.99      | v1_funct_1(k6_relat_1(X0)) != iProver_top
% 3.69/0.99      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 3.69/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_7,plain,
% 3.69/0.99      ( v1_funct_1(k6_relat_1(X0)) ),
% 3.69/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_540,plain,
% 3.69/0.99      ( v1_funct_1(k6_relat_1(X0)) = iProver_top ),
% 3.69/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_585,plain,
% 3.69/0.99      ( k1_funct_1(k6_relat_1(X0),X1) = X1
% 3.69/0.99      | r2_hidden(X1,X0) != iProver_top ),
% 3.69/0.99      inference(forward_subsumption_resolution,
% 3.69/0.99                [status(thm)],
% 3.69/0.99                [c_535,c_539,c_540]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_6874,plain,
% 3.69/0.99      ( k1_funct_1(k6_relat_1(sK2),sK1) = sK1 ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_6164,c_585]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_9,plain,
% 3.69/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.69/0.99      | ~ v1_funct_1(X2)
% 3.69/0.99      | ~ v1_funct_1(X1)
% 3.69/0.99      | ~ v1_relat_1(X2)
% 3.69/0.99      | ~ v1_relat_1(X1)
% 3.69/0.99      | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ),
% 3.69/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_538,plain,
% 3.69/0.99      ( k1_funct_1(k5_relat_1(X0,X1),X2) = k1_funct_1(X1,k1_funct_1(X0,X2))
% 3.69/0.99      | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
% 3.69/0.99      | v1_funct_1(X1) != iProver_top
% 3.69/0.99      | v1_funct_1(X0) != iProver_top
% 3.69/0.99      | v1_relat_1(X1) != iProver_top
% 3.69/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.69/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_2742,plain,
% 3.69/0.99      ( k1_funct_1(X0,k1_funct_1(k6_relat_1(X1),X2)) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X0),X2)
% 3.69/0.99      | r2_hidden(X2,X1) != iProver_top
% 3.69/0.99      | v1_funct_1(X0) != iProver_top
% 3.69/0.99      | v1_funct_1(k6_relat_1(X1)) != iProver_top
% 3.69/0.99      | v1_relat_1(X0) != iProver_top
% 3.69/0.99      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_2,c_538]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_4473,plain,
% 3.69/0.99      ( k1_funct_1(k5_relat_1(k6_relat_1(X0),X1),X2) = k1_funct_1(X1,k1_funct_1(k6_relat_1(X0),X2))
% 3.69/0.99      | r2_hidden(X2,X0) != iProver_top
% 3.69/0.99      | v1_funct_1(X1) != iProver_top
% 3.69/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.69/0.99      inference(forward_subsumption_resolution,
% 3.69/0.99                [status(thm)],
% 3.69/0.99                [c_2742,c_539,c_540]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_6875,plain,
% 3.69/0.99      ( k1_funct_1(X0,k1_funct_1(k6_relat_1(sK2),sK1)) = k1_funct_1(k5_relat_1(k6_relat_1(sK2),X0),sK1)
% 3.69/0.99      | v1_funct_1(X0) != iProver_top
% 3.69/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_6164,c_4473]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_6883,plain,
% 3.69/0.99      ( k1_funct_1(k5_relat_1(k6_relat_1(sK2),X0),sK1) = k1_funct_1(X0,sK1)
% 3.69/0.99      | v1_funct_1(X0) != iProver_top
% 3.69/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.69/0.99      inference(demodulation,[status(thm)],[c_6874,c_6875]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_6892,plain,
% 3.69/0.99      ( k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1) = k1_funct_1(sK3,sK1)
% 3.69/0.99      | v1_funct_1(sK3) != iProver_top
% 3.69/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.69/0.99      inference(instantiation,[status(thm)],[c_6883]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_277,plain,
% 3.69/0.99      ( X0 != X1 | X2 != X3 | k1_funct_1(X0,X2) = k1_funct_1(X1,X3) ),
% 3.69/0.99      theory(equality) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_978,plain,
% 3.69/0.99      ( k1_funct_1(k7_relat_1(sK3,sK2),sK1) = k1_funct_1(X0,X1)
% 3.69/0.99      | k7_relat_1(sK3,sK2) != X0
% 3.69/0.99      | sK1 != X1 ),
% 3.69/0.99      inference(instantiation,[status(thm)],[c_277]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_1661,plain,
% 3.69/0.99      ( k1_funct_1(k7_relat_1(sK3,sK2),sK1) = k1_funct_1(X0,sK1)
% 3.69/0.99      | k7_relat_1(sK3,sK2) != X0
% 3.69/0.99      | sK1 != sK1 ),
% 3.69/0.99      inference(instantiation,[status(thm)],[c_978]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_4370,plain,
% 3.69/0.99      ( k1_funct_1(k7_relat_1(sK3,sK2),sK1) = k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1)
% 3.69/0.99      | k7_relat_1(sK3,sK2) != k5_relat_1(k6_relat_1(sK2),sK3)
% 3.69/0.99      | sK1 != sK1 ),
% 3.69/0.99      inference(instantiation,[status(thm)],[c_1661]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_1949,plain,
% 3.69/0.99      ( ~ v1_relat_1(sK3)
% 3.69/0.99      | k5_relat_1(k6_relat_1(sK2),sK3) = k7_relat_1(sK3,sK2) ),
% 3.69/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_959,plain,
% 3.69/0.99      ( X0 != X1 | k7_relat_1(sK3,sK2) != X1 | k7_relat_1(sK3,sK2) = X0 ),
% 3.69/0.99      inference(instantiation,[status(thm)],[c_267]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_1250,plain,
% 3.69/0.99      ( X0 != k7_relat_1(sK3,sK2)
% 3.69/0.99      | k7_relat_1(sK3,sK2) = X0
% 3.69/0.99      | k7_relat_1(sK3,sK2) != k7_relat_1(sK3,sK2) ),
% 3.69/0.99      inference(instantiation,[status(thm)],[c_959]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_1948,plain,
% 3.69/0.99      ( k5_relat_1(k6_relat_1(sK2),sK3) != k7_relat_1(sK3,sK2)
% 3.69/0.99      | k7_relat_1(sK3,sK2) = k5_relat_1(k6_relat_1(sK2),sK3)
% 3.69/0.99      | k7_relat_1(sK3,sK2) != k7_relat_1(sK3,sK2) ),
% 3.69/0.99      inference(instantiation,[status(thm)],[c_1250]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_266,plain,( X0 = X0 ),theory(equality) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_1251,plain,
% 3.69/0.99      ( k7_relat_1(sK3,sK2) = k7_relat_1(sK3,sK2) ),
% 3.69/0.99      inference(instantiation,[status(thm)],[c_266]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_735,plain,
% 3.69/0.99      ( k1_funct_1(sK3,sK1) = k1_funct_1(sK3,sK1) ),
% 3.69/0.99      inference(instantiation,[status(thm)],[c_266]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_684,plain,
% 3.69/0.99      ( k1_funct_1(k7_relat_1(sK3,sK2),sK1) != X0
% 3.69/0.99      | k1_funct_1(sK3,sK1) != X0
% 3.69/0.99      | k1_funct_1(sK3,sK1) = k1_funct_1(k7_relat_1(sK3,sK2),sK1) ),
% 3.69/0.99      inference(instantiation,[status(thm)],[c_267]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_734,plain,
% 3.69/0.99      ( k1_funct_1(k7_relat_1(sK3,sK2),sK1) != k1_funct_1(sK3,sK1)
% 3.69/0.99      | k1_funct_1(sK3,sK1) = k1_funct_1(k7_relat_1(sK3,sK2),sK1)
% 3.69/0.99      | k1_funct_1(sK3,sK1) != k1_funct_1(sK3,sK1) ),
% 3.69/0.99      inference(instantiation,[status(thm)],[c_684]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_732,plain,
% 3.69/0.99      ( sK1 = sK1 ),
% 3.69/0.99      inference(instantiation,[status(thm)],[c_266]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_15,negated_conjecture,
% 3.69/0.99      ( k1_funct_1(sK3,sK1) != k1_funct_1(k7_relat_1(sK3,sK2),sK1) ),
% 3.69/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_17,negated_conjecture,
% 3.69/0.99      ( v1_funct_1(sK3) ),
% 3.69/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_20,plain,
% 3.69/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 3.69/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_18,negated_conjecture,
% 3.69/0.99      ( v1_relat_1(sK3) ),
% 3.69/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_19,plain,
% 3.69/0.99      ( v1_relat_1(sK3) = iProver_top ),
% 3.69/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(contradiction,plain,
% 3.69/0.99      ( $false ),
% 3.69/0.99      inference(minisat,
% 3.69/0.99                [status(thm)],
% 3.69/0.99                [c_11341,c_7566,c_6892,c_4370,c_1949,c_1948,c_1251,c_735,
% 3.69/0.99                 c_734,c_732,c_15,c_20,c_19,c_18]) ).
% 3.69/0.99  
% 3.69/0.99  
% 3.69/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.69/0.99  
% 3.69/0.99  ------                               Statistics
% 3.69/0.99  
% 3.69/0.99  ------ Selected
% 3.69/0.99  
% 3.69/0.99  total_time:                             0.405
% 3.69/0.99  
%------------------------------------------------------------------------------
