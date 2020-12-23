%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:45:40 EST 2020

% Result     : Theorem 11.51s
% Output     : CNFRefutation 11.51s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 240 expanded)
%              Number of clauses        :   73 (  96 expanded)
%              Number of leaves         :   14 (  57 expanded)
%              Depth                    :   12
%              Number of atoms          :  275 ( 862 expanded)
%              Number of equality atoms :  121 ( 149 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => ( ( r1_tarski(X0,X1)
                & r1_tarski(X2,X3) )
             => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
     => ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,sK3))
        & r1_tarski(X0,X1)
        & r1_tarski(X2,sK3)
        & v1_relat_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3))
            & r1_tarski(X0,X1)
            & r1_tarski(X2,X3)
            & v1_relat_1(X3) )
        & v1_relat_1(X2) )
   => ( ? [X3] :
          ( ~ r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,X3))
          & r1_tarski(sK0,sK1)
          & r1_tarski(sK2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ~ r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))
    & r1_tarski(sK0,sK1)
    & r1_tarski(sK2,sK3)
    & v1_relat_1(sK3)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f23,f22])).

fof(f34,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k8_relat_1(X0,X1),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f35,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f33,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f36,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f37,plain,(
    ~ r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_11,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_342,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_5,plain,
    ( r1_tarski(k8_relat_1(X0,X1),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_348,plain,
    ( r1_tarski(k8_relat_1(X0,X1),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_350,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_840,plain,
    ( k3_xboole_0(k8_relat_1(X0,X1),X1) = k8_relat_1(X0,X1)
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_348,c_350])).

cnf(c_3596,plain,
    ( k3_xboole_0(k8_relat_1(X0,sK3),sK3) = k8_relat_1(X0,sK3) ),
    inference(superposition,[status(thm)],[c_342,c_840])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_349,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k3_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_650,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k3_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_349])).

cnf(c_3810,plain,
    ( v1_relat_1(k8_relat_1(X0,sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3596,c_650])).

cnf(c_14,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4203,plain,
    ( v1_relat_1(k8_relat_1(X0,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3810,c_14])).

cnf(c_10,negated_conjecture,
    ( r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_343,plain,
    ( r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k8_relat_1(X2,X0),k8_relat_1(X2,X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_346,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k8_relat_1(X2,X0),k8_relat_1(X2,X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_724,plain,
    ( k3_xboole_0(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) = k8_relat_1(X0,X1)
    | r1_tarski(X1,X2) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_346,c_350])).

cnf(c_1923,plain,
    ( k3_xboole_0(k8_relat_1(X0,sK2),k8_relat_1(X0,sK3)) = k8_relat_1(X0,sK2)
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_343,c_724])).

cnf(c_12,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_13,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2134,plain,
    ( k3_xboole_0(k8_relat_1(X0,sK2),k8_relat_1(X0,sK3)) = k8_relat_1(X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1923,c_13,c_14])).

cnf(c_2138,plain,
    ( v1_relat_1(k8_relat_1(X0,sK3)) != iProver_top
    | v1_relat_1(k8_relat_1(X0,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2134,c_650])).

cnf(c_4215,plain,
    ( v1_relat_1(k8_relat_1(X0,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4203,c_2138])).

cnf(c_341,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_9,negated_conjecture,
    ( r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_344,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X2)
    | k8_relat_1(X1,k8_relat_1(X0,X2)) = k8_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_347,plain,
    ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X1,X2)
    | r1_tarski(X1,X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1225,plain,
    ( k8_relat_1(sK1,k8_relat_1(sK0,X0)) = k8_relat_1(sK0,X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_344,c_347])).

cnf(c_1495,plain,
    ( k8_relat_1(sK1,k8_relat_1(sK0,sK2)) = k8_relat_1(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_341,c_1225])).

cnf(c_1651,plain,
    ( r1_tarski(k8_relat_1(sK0,sK2),X0) != iProver_top
    | r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k8_relat_1(sK0,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1495,c_346])).

cnf(c_15,plain,
    ( r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_8,negated_conjecture,
    ( ~ r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_17,plain,
    ( r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_136,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_405,plain,
    ( k8_relat_1(sK1,sK3) = k8_relat_1(sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_136])).

cnf(c_520,plain,
    ( k8_relat_1(sK0,sK2) = k8_relat_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_136])).

cnf(c_892,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_136])).

cnf(c_854,plain,
    ( ~ r1_tarski(sK0,X0)
    | ~ v1_relat_1(sK2)
    | k8_relat_1(X0,k8_relat_1(sK0,sK2)) = k8_relat_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1172,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ v1_relat_1(sK2)
    | k8_relat_1(sK1,k8_relat_1(sK0,sK2)) = k8_relat_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_854])).

cnf(c_137,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_441,plain,
    ( X0 != X1
    | k8_relat_1(sK0,sK2) != X1
    | k8_relat_1(sK0,sK2) = X0 ),
    inference(instantiation,[status(thm)],[c_137])).

cnf(c_523,plain,
    ( X0 != k8_relat_1(sK0,sK2)
    | k8_relat_1(sK0,sK2) = X0
    | k8_relat_1(sK0,sK2) != k8_relat_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_441])).

cnf(c_621,plain,
    ( k8_relat_1(X0,k8_relat_1(sK0,sK2)) != k8_relat_1(sK0,sK2)
    | k8_relat_1(sK0,sK2) = k8_relat_1(X0,k8_relat_1(sK0,sK2))
    | k8_relat_1(sK0,sK2) != k8_relat_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_523])).

cnf(c_1383,plain,
    ( k8_relat_1(sK1,k8_relat_1(sK0,sK2)) != k8_relat_1(sK0,sK2)
    | k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2))
    | k8_relat_1(sK0,sK2) != k8_relat_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_621])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_1515,plain,
    ( ~ r1_tarski(k8_relat_1(sK0,sK2),X0)
    | k2_xboole_0(k8_relat_1(sK0,sK2),X0) = X0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1517,plain,
    ( ~ r1_tarski(k8_relat_1(sK0,sK2),sK2)
    | k2_xboole_0(k8_relat_1(sK0,sK2),sK2) = sK2 ),
    inference(instantiation,[status(thm)],[c_1515])).

cnf(c_138,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_375,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))
    | k8_relat_1(sK1,sK3) != X1
    | k8_relat_1(sK0,sK2) != X0 ),
    inference(instantiation,[status(thm)],[c_138])).

cnf(c_390,plain,
    ( ~ r1_tarski(X0,k8_relat_1(sK1,sK3))
    | r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))
    | k8_relat_1(sK1,sK3) != k8_relat_1(sK1,sK3)
    | k8_relat_1(sK0,sK2) != X0 ),
    inference(instantiation,[status(thm)],[c_375])).

cnf(c_460,plain,
    ( ~ r1_tarski(k8_relat_1(sK1,X0),k8_relat_1(sK1,sK3))
    | r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))
    | k8_relat_1(sK1,sK3) != k8_relat_1(sK1,sK3)
    | k8_relat_1(sK0,sK2) != k8_relat_1(sK1,X0) ),
    inference(instantiation,[status(thm)],[c_390])).

cnf(c_1681,plain,
    ( ~ r1_tarski(k8_relat_1(sK1,k8_relat_1(sK0,sK2)),k8_relat_1(sK1,sK3))
    | r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))
    | k8_relat_1(sK1,sK3) != k8_relat_1(sK1,sK3)
    | k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_460])).

cnf(c_1682,plain,
    ( k8_relat_1(sK1,sK3) != k8_relat_1(sK1,sK3)
    | k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2))
    | r1_tarski(k8_relat_1(sK1,k8_relat_1(sK0,sK2)),k8_relat_1(sK1,sK3)) != iProver_top
    | r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1681])).

cnf(c_1814,plain,
    ( r1_tarski(k8_relat_1(sK0,sK2),sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_498,plain,
    ( ~ r1_tarski(X0,sK3)
    | r1_tarski(k8_relat_1(sK1,X0),k8_relat_1(sK1,sK3))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_3307,plain,
    ( r1_tarski(k8_relat_1(sK1,k8_relat_1(sK0,sK2)),k8_relat_1(sK1,sK3))
    | ~ r1_tarski(k8_relat_1(sK0,sK2),sK3)
    | ~ v1_relat_1(k8_relat_1(sK0,sK2))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_498])).

cnf(c_3308,plain,
    ( r1_tarski(k8_relat_1(sK1,k8_relat_1(sK0,sK2)),k8_relat_1(sK1,sK3)) = iProver_top
    | r1_tarski(k8_relat_1(sK0,sK2),sK3) != iProver_top
    | v1_relat_1(k8_relat_1(sK0,sK2)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3307])).

cnf(c_1,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_1062,plain,
    ( r1_tarski(k8_relat_1(sK0,sK2),X0)
    | ~ r1_tarski(k2_xboole_0(k8_relat_1(sK0,sK2),X1),X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_8344,plain,
    ( r1_tarski(k8_relat_1(sK0,sK2),sK3)
    | ~ r1_tarski(k2_xboole_0(k8_relat_1(sK0,sK2),X0),sK3) ),
    inference(instantiation,[status(thm)],[c_1062])).

cnf(c_8349,plain,
    ( r1_tarski(k8_relat_1(sK0,sK2),sK3) = iProver_top
    | r1_tarski(k2_xboole_0(k8_relat_1(sK0,sK2),X0),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8344])).

cnf(c_8351,plain,
    ( r1_tarski(k8_relat_1(sK0,sK2),sK3) = iProver_top
    | r1_tarski(k2_xboole_0(k8_relat_1(sK0,sK2),sK2),sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8349])).

cnf(c_1476,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(sK2,sK3)
    | X1 != sK3
    | X0 != sK2 ),
    inference(instantiation,[status(thm)],[c_138])).

cnf(c_1660,plain,
    ( r1_tarski(X0,sK3)
    | ~ r1_tarski(sK2,sK3)
    | X0 != sK2
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1476])).

cnf(c_3005,plain,
    ( r1_tarski(k2_xboole_0(X0,X1),sK3)
    | ~ r1_tarski(sK2,sK3)
    | k2_xboole_0(X0,X1) != sK2
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1660])).

cnf(c_8458,plain,
    ( r1_tarski(k2_xboole_0(k8_relat_1(sK0,sK2),sK2),sK3)
    | ~ r1_tarski(sK2,sK3)
    | k2_xboole_0(k8_relat_1(sK0,sK2),sK2) != sK2
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_3005])).

cnf(c_8459,plain,
    ( k2_xboole_0(k8_relat_1(sK0,sK2),sK2) != sK2
    | sK3 != sK3
    | r1_tarski(k2_xboole_0(k8_relat_1(sK0,sK2),sK2),sK3) = iProver_top
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8458])).

cnf(c_13546,plain,
    ( v1_relat_1(k8_relat_1(sK0,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1651,c_12,c_14,c_15,c_9,c_17,c_405,c_520,c_892,c_1172,c_1383,c_1517,c_1682,c_1814,c_3308,c_8351,c_8459])).

cnf(c_40481,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_4215,c_13546])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:57:32 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 11.51/1.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.51/1.99  
% 11.51/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.51/1.99  
% 11.51/1.99  ------  iProver source info
% 11.51/1.99  
% 11.51/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.51/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.51/1.99  git: non_committed_changes: false
% 11.51/1.99  git: last_make_outside_of_git: false
% 11.51/1.99  
% 11.51/1.99  ------ 
% 11.51/1.99  
% 11.51/1.99  ------ Input Options
% 11.51/1.99  
% 11.51/1.99  --out_options                           all
% 11.51/1.99  --tptp_safe_out                         true
% 11.51/1.99  --problem_path                          ""
% 11.51/1.99  --include_path                          ""
% 11.51/1.99  --clausifier                            res/vclausify_rel
% 11.51/1.99  --clausifier_options                    ""
% 11.51/1.99  --stdin                                 false
% 11.51/1.99  --stats_out                             all
% 11.51/1.99  
% 11.51/1.99  ------ General Options
% 11.51/1.99  
% 11.51/1.99  --fof                                   false
% 11.51/1.99  --time_out_real                         305.
% 11.51/1.99  --time_out_virtual                      -1.
% 11.51/1.99  --symbol_type_check                     false
% 11.51/1.99  --clausify_out                          false
% 11.51/1.99  --sig_cnt_out                           false
% 11.51/1.99  --trig_cnt_out                          false
% 11.51/1.99  --trig_cnt_out_tolerance                1.
% 11.51/1.99  --trig_cnt_out_sk_spl                   false
% 11.51/1.99  --abstr_cl_out                          false
% 11.51/1.99  
% 11.51/1.99  ------ Global Options
% 11.51/1.99  
% 11.51/1.99  --schedule                              default
% 11.51/1.99  --add_important_lit                     false
% 11.51/1.99  --prop_solver_per_cl                    1000
% 11.51/1.99  --min_unsat_core                        false
% 11.51/1.99  --soft_assumptions                      false
% 11.51/1.99  --soft_lemma_size                       3
% 11.51/1.99  --prop_impl_unit_size                   0
% 11.51/1.99  --prop_impl_unit                        []
% 11.51/1.99  --share_sel_clauses                     true
% 11.51/1.99  --reset_solvers                         false
% 11.51/1.99  --bc_imp_inh                            [conj_cone]
% 11.51/1.99  --conj_cone_tolerance                   3.
% 11.51/1.99  --extra_neg_conj                        none
% 11.51/1.99  --large_theory_mode                     true
% 11.51/1.99  --prolific_symb_bound                   200
% 11.51/1.99  --lt_threshold                          2000
% 11.51/1.99  --clause_weak_htbl                      true
% 11.51/1.99  --gc_record_bc_elim                     false
% 11.51/1.99  
% 11.51/1.99  ------ Preprocessing Options
% 11.51/1.99  
% 11.51/1.99  --preprocessing_flag                    true
% 11.51/1.99  --time_out_prep_mult                    0.1
% 11.51/1.99  --splitting_mode                        input
% 11.51/1.99  --splitting_grd                         true
% 11.51/1.99  --splitting_cvd                         false
% 11.51/1.99  --splitting_cvd_svl                     false
% 11.51/1.99  --splitting_nvd                         32
% 11.51/1.99  --sub_typing                            true
% 11.51/1.99  --prep_gs_sim                           true
% 11.51/1.99  --prep_unflatten                        true
% 11.51/1.99  --prep_res_sim                          true
% 11.51/1.99  --prep_upred                            true
% 11.51/1.99  --prep_sem_filter                       exhaustive
% 11.51/1.99  --prep_sem_filter_out                   false
% 11.51/1.99  --pred_elim                             true
% 11.51/1.99  --res_sim_input                         true
% 11.51/1.99  --eq_ax_congr_red                       true
% 11.51/1.99  --pure_diseq_elim                       true
% 11.51/1.99  --brand_transform                       false
% 11.51/1.99  --non_eq_to_eq                          false
% 11.51/1.99  --prep_def_merge                        true
% 11.51/1.99  --prep_def_merge_prop_impl              false
% 11.51/1.99  --prep_def_merge_mbd                    true
% 11.51/1.99  --prep_def_merge_tr_red                 false
% 11.51/1.99  --prep_def_merge_tr_cl                  false
% 11.51/1.99  --smt_preprocessing                     true
% 11.51/1.99  --smt_ac_axioms                         fast
% 11.51/1.99  --preprocessed_out                      false
% 11.51/1.99  --preprocessed_stats                    false
% 11.51/1.99  
% 11.51/1.99  ------ Abstraction refinement Options
% 11.51/1.99  
% 11.51/1.99  --abstr_ref                             []
% 11.51/1.99  --abstr_ref_prep                        false
% 11.51/1.99  --abstr_ref_until_sat                   false
% 11.51/1.99  --abstr_ref_sig_restrict                funpre
% 11.51/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.51/1.99  --abstr_ref_under                       []
% 11.51/1.99  
% 11.51/1.99  ------ SAT Options
% 11.51/1.99  
% 11.51/1.99  --sat_mode                              false
% 11.51/1.99  --sat_fm_restart_options                ""
% 11.51/1.99  --sat_gr_def                            false
% 11.51/1.99  --sat_epr_types                         true
% 11.51/1.99  --sat_non_cyclic_types                  false
% 11.51/1.99  --sat_finite_models                     false
% 11.51/1.99  --sat_fm_lemmas                         false
% 11.51/1.99  --sat_fm_prep                           false
% 11.51/1.99  --sat_fm_uc_incr                        true
% 11.51/1.99  --sat_out_model                         small
% 11.51/1.99  --sat_out_clauses                       false
% 11.51/1.99  
% 11.51/1.99  ------ QBF Options
% 11.51/1.99  
% 11.51/1.99  --qbf_mode                              false
% 11.51/1.99  --qbf_elim_univ                         false
% 11.51/1.99  --qbf_dom_inst                          none
% 11.51/1.99  --qbf_dom_pre_inst                      false
% 11.51/1.99  --qbf_sk_in                             false
% 11.51/1.99  --qbf_pred_elim                         true
% 11.51/1.99  --qbf_split                             512
% 11.51/1.99  
% 11.51/1.99  ------ BMC1 Options
% 11.51/1.99  
% 11.51/1.99  --bmc1_incremental                      false
% 11.51/1.99  --bmc1_axioms                           reachable_all
% 11.51/1.99  --bmc1_min_bound                        0
% 11.51/1.99  --bmc1_max_bound                        -1
% 11.51/1.99  --bmc1_max_bound_default                -1
% 11.51/1.99  --bmc1_symbol_reachability              true
% 11.51/1.99  --bmc1_property_lemmas                  false
% 11.51/1.99  --bmc1_k_induction                      false
% 11.51/1.99  --bmc1_non_equiv_states                 false
% 11.51/1.99  --bmc1_deadlock                         false
% 11.51/1.99  --bmc1_ucm                              false
% 11.51/1.99  --bmc1_add_unsat_core                   none
% 11.51/1.99  --bmc1_unsat_core_children              false
% 11.51/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.51/1.99  --bmc1_out_stat                         full
% 11.51/1.99  --bmc1_ground_init                      false
% 11.51/1.99  --bmc1_pre_inst_next_state              false
% 11.51/1.99  --bmc1_pre_inst_state                   false
% 11.51/1.99  --bmc1_pre_inst_reach_state             false
% 11.51/1.99  --bmc1_out_unsat_core                   false
% 11.51/1.99  --bmc1_aig_witness_out                  false
% 11.51/1.99  --bmc1_verbose                          false
% 11.51/1.99  --bmc1_dump_clauses_tptp                false
% 11.51/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.51/1.99  --bmc1_dump_file                        -
% 11.51/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.51/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.51/1.99  --bmc1_ucm_extend_mode                  1
% 11.51/1.99  --bmc1_ucm_init_mode                    2
% 11.51/1.99  --bmc1_ucm_cone_mode                    none
% 11.51/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.51/1.99  --bmc1_ucm_relax_model                  4
% 11.51/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.51/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.51/1.99  --bmc1_ucm_layered_model                none
% 11.51/1.99  --bmc1_ucm_max_lemma_size               10
% 11.51/1.99  
% 11.51/1.99  ------ AIG Options
% 11.51/1.99  
% 11.51/1.99  --aig_mode                              false
% 11.51/1.99  
% 11.51/1.99  ------ Instantiation Options
% 11.51/1.99  
% 11.51/1.99  --instantiation_flag                    true
% 11.51/1.99  --inst_sos_flag                         true
% 11.51/1.99  --inst_sos_phase                        true
% 11.51/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.51/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.51/1.99  --inst_lit_sel_side                     num_symb
% 11.51/1.99  --inst_solver_per_active                1400
% 11.51/1.99  --inst_solver_calls_frac                1.
% 11.51/1.99  --inst_passive_queue_type               priority_queues
% 11.51/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.51/1.99  --inst_passive_queues_freq              [25;2]
% 11.51/1.99  --inst_dismatching                      true
% 11.51/1.99  --inst_eager_unprocessed_to_passive     true
% 11.51/1.99  --inst_prop_sim_given                   true
% 11.51/1.99  --inst_prop_sim_new                     false
% 11.51/1.99  --inst_subs_new                         false
% 11.51/1.99  --inst_eq_res_simp                      false
% 11.51/1.99  --inst_subs_given                       false
% 11.51/1.99  --inst_orphan_elimination               true
% 11.51/1.99  --inst_learning_loop_flag               true
% 11.51/1.99  --inst_learning_start                   3000
% 11.51/1.99  --inst_learning_factor                  2
% 11.51/1.99  --inst_start_prop_sim_after_learn       3
% 11.51/1.99  --inst_sel_renew                        solver
% 11.51/1.99  --inst_lit_activity_flag                true
% 11.51/1.99  --inst_restr_to_given                   false
% 11.51/1.99  --inst_activity_threshold               500
% 11.51/1.99  --inst_out_proof                        true
% 11.51/1.99  
% 11.51/1.99  ------ Resolution Options
% 11.51/1.99  
% 11.51/1.99  --resolution_flag                       true
% 11.51/1.99  --res_lit_sel                           adaptive
% 11.51/1.99  --res_lit_sel_side                      none
% 11.51/1.99  --res_ordering                          kbo
% 11.51/1.99  --res_to_prop_solver                    active
% 11.51/1.99  --res_prop_simpl_new                    false
% 11.51/1.99  --res_prop_simpl_given                  true
% 11.51/1.99  --res_passive_queue_type                priority_queues
% 11.51/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.51/1.99  --res_passive_queues_freq               [15;5]
% 11.51/1.99  --res_forward_subs                      full
% 11.51/1.99  --res_backward_subs                     full
% 11.51/1.99  --res_forward_subs_resolution           true
% 11.51/1.99  --res_backward_subs_resolution          true
% 11.51/1.99  --res_orphan_elimination                true
% 11.51/1.99  --res_time_limit                        2.
% 11.51/1.99  --res_out_proof                         true
% 11.51/1.99  
% 11.51/1.99  ------ Superposition Options
% 11.51/1.99  
% 11.51/1.99  --superposition_flag                    true
% 11.51/1.99  --sup_passive_queue_type                priority_queues
% 11.51/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.51/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.51/1.99  --demod_completeness_check              fast
% 11.51/1.99  --demod_use_ground                      true
% 11.51/1.99  --sup_to_prop_solver                    passive
% 11.51/1.99  --sup_prop_simpl_new                    true
% 11.51/1.99  --sup_prop_simpl_given                  true
% 11.51/1.99  --sup_fun_splitting                     true
% 11.51/1.99  --sup_smt_interval                      50000
% 11.51/1.99  
% 11.51/1.99  ------ Superposition Simplification Setup
% 11.51/1.99  
% 11.51/1.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.51/1.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.51/1.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.51/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.51/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.51/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.51/1.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.51/1.99  --sup_immed_triv                        [TrivRules]
% 11.51/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.51/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.51/1.99  --sup_immed_bw_main                     []
% 11.51/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.51/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.51/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.51/1.99  --sup_input_bw                          []
% 11.51/1.99  
% 11.51/1.99  ------ Combination Options
% 11.51/1.99  
% 11.51/1.99  --comb_res_mult                         3
% 11.51/1.99  --comb_sup_mult                         2
% 11.51/1.99  --comb_inst_mult                        10
% 11.51/1.99  
% 11.51/1.99  ------ Debug Options
% 11.51/1.99  
% 11.51/1.99  --dbg_backtrace                         false
% 11.51/1.99  --dbg_dump_prop_clauses                 false
% 11.51/1.99  --dbg_dump_prop_clauses_file            -
% 11.51/1.99  --dbg_out_stat                          false
% 11.51/1.99  ------ Parsing...
% 11.51/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.51/1.99  
% 11.51/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 11.51/1.99  
% 11.51/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.51/1.99  
% 11.51/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.51/1.99  ------ Proving...
% 11.51/1.99  ------ Problem Properties 
% 11.51/1.99  
% 11.51/1.99  
% 11.51/1.99  clauses                                 13
% 11.51/1.99  conjectures                             5
% 11.51/1.99  EPR                                     4
% 11.51/1.99  Horn                                    13
% 11.51/1.99  unary                                   6
% 11.51/1.99  binary                                  5
% 11.51/1.99  lits                                    23
% 11.51/1.99  lits eq                                 4
% 11.51/1.99  fd_pure                                 0
% 11.51/1.99  fd_pseudo                               0
% 11.51/1.99  fd_cond                                 0
% 11.51/1.99  fd_pseudo_cond                          0
% 11.51/1.99  AC symbols                              0
% 11.51/1.99  
% 11.51/1.99  ------ Schedule dynamic 5 is on 
% 11.51/1.99  
% 11.51/1.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.51/1.99  
% 11.51/1.99  
% 11.51/1.99  ------ 
% 11.51/1.99  Current options:
% 11.51/1.99  ------ 
% 11.51/1.99  
% 11.51/1.99  ------ Input Options
% 11.51/1.99  
% 11.51/1.99  --out_options                           all
% 11.51/1.99  --tptp_safe_out                         true
% 11.51/1.99  --problem_path                          ""
% 11.51/1.99  --include_path                          ""
% 11.51/1.99  --clausifier                            res/vclausify_rel
% 11.51/1.99  --clausifier_options                    ""
% 11.51/1.99  --stdin                                 false
% 11.51/1.99  --stats_out                             all
% 11.51/1.99  
% 11.51/1.99  ------ General Options
% 11.51/1.99  
% 11.51/1.99  --fof                                   false
% 11.51/1.99  --time_out_real                         305.
% 11.51/1.99  --time_out_virtual                      -1.
% 11.51/1.99  --symbol_type_check                     false
% 11.51/1.99  --clausify_out                          false
% 11.51/1.99  --sig_cnt_out                           false
% 11.51/1.99  --trig_cnt_out                          false
% 11.51/1.99  --trig_cnt_out_tolerance                1.
% 11.51/1.99  --trig_cnt_out_sk_spl                   false
% 11.51/1.99  --abstr_cl_out                          false
% 11.51/1.99  
% 11.51/1.99  ------ Global Options
% 11.51/1.99  
% 11.51/1.99  --schedule                              default
% 11.51/1.99  --add_important_lit                     false
% 11.51/1.99  --prop_solver_per_cl                    1000
% 11.51/1.99  --min_unsat_core                        false
% 11.51/1.99  --soft_assumptions                      false
% 11.51/1.99  --soft_lemma_size                       3
% 11.51/1.99  --prop_impl_unit_size                   0
% 11.51/1.99  --prop_impl_unit                        []
% 11.51/1.99  --share_sel_clauses                     true
% 11.51/1.99  --reset_solvers                         false
% 11.51/1.99  --bc_imp_inh                            [conj_cone]
% 11.51/1.99  --conj_cone_tolerance                   3.
% 11.51/1.99  --extra_neg_conj                        none
% 11.51/1.99  --large_theory_mode                     true
% 11.51/1.99  --prolific_symb_bound                   200
% 11.51/1.99  --lt_threshold                          2000
% 11.51/1.99  --clause_weak_htbl                      true
% 11.51/1.99  --gc_record_bc_elim                     false
% 11.51/1.99  
% 11.51/1.99  ------ Preprocessing Options
% 11.51/1.99  
% 11.51/1.99  --preprocessing_flag                    true
% 11.51/1.99  --time_out_prep_mult                    0.1
% 11.51/1.99  --splitting_mode                        input
% 11.51/1.99  --splitting_grd                         true
% 11.51/1.99  --splitting_cvd                         false
% 11.51/1.99  --splitting_cvd_svl                     false
% 11.51/1.99  --splitting_nvd                         32
% 11.51/1.99  --sub_typing                            true
% 11.51/1.99  --prep_gs_sim                           true
% 11.51/1.99  --prep_unflatten                        true
% 11.51/1.99  --prep_res_sim                          true
% 11.51/1.99  --prep_upred                            true
% 11.51/1.99  --prep_sem_filter                       exhaustive
% 11.51/1.99  --prep_sem_filter_out                   false
% 11.51/1.99  --pred_elim                             true
% 11.51/1.99  --res_sim_input                         true
% 11.51/1.99  --eq_ax_congr_red                       true
% 11.51/1.99  --pure_diseq_elim                       true
% 11.51/1.99  --brand_transform                       false
% 11.51/1.99  --non_eq_to_eq                          false
% 11.51/1.99  --prep_def_merge                        true
% 11.51/1.99  --prep_def_merge_prop_impl              false
% 11.51/1.99  --prep_def_merge_mbd                    true
% 11.51/1.99  --prep_def_merge_tr_red                 false
% 11.51/1.99  --prep_def_merge_tr_cl                  false
% 11.51/1.99  --smt_preprocessing                     true
% 11.51/1.99  --smt_ac_axioms                         fast
% 11.51/1.99  --preprocessed_out                      false
% 11.51/1.99  --preprocessed_stats                    false
% 11.51/1.99  
% 11.51/1.99  ------ Abstraction refinement Options
% 11.51/1.99  
% 11.51/1.99  --abstr_ref                             []
% 11.51/1.99  --abstr_ref_prep                        false
% 11.51/1.99  --abstr_ref_until_sat                   false
% 11.51/1.99  --abstr_ref_sig_restrict                funpre
% 11.51/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.51/1.99  --abstr_ref_under                       []
% 11.51/1.99  
% 11.51/1.99  ------ SAT Options
% 11.51/1.99  
% 11.51/1.99  --sat_mode                              false
% 11.51/1.99  --sat_fm_restart_options                ""
% 11.51/1.99  --sat_gr_def                            false
% 11.51/1.99  --sat_epr_types                         true
% 11.51/1.99  --sat_non_cyclic_types                  false
% 11.51/1.99  --sat_finite_models                     false
% 11.51/1.99  --sat_fm_lemmas                         false
% 11.51/1.99  --sat_fm_prep                           false
% 11.51/1.99  --sat_fm_uc_incr                        true
% 11.51/1.99  --sat_out_model                         small
% 11.51/1.99  --sat_out_clauses                       false
% 11.51/1.99  
% 11.51/1.99  ------ QBF Options
% 11.51/1.99  
% 11.51/1.99  --qbf_mode                              false
% 11.51/1.99  --qbf_elim_univ                         false
% 11.51/1.99  --qbf_dom_inst                          none
% 11.51/1.99  --qbf_dom_pre_inst                      false
% 11.51/1.99  --qbf_sk_in                             false
% 11.51/1.99  --qbf_pred_elim                         true
% 11.51/1.99  --qbf_split                             512
% 11.51/1.99  
% 11.51/1.99  ------ BMC1 Options
% 11.51/1.99  
% 11.51/1.99  --bmc1_incremental                      false
% 11.51/1.99  --bmc1_axioms                           reachable_all
% 11.51/1.99  --bmc1_min_bound                        0
% 11.51/1.99  --bmc1_max_bound                        -1
% 11.51/1.99  --bmc1_max_bound_default                -1
% 11.51/1.99  --bmc1_symbol_reachability              true
% 11.51/1.99  --bmc1_property_lemmas                  false
% 11.51/1.99  --bmc1_k_induction                      false
% 11.51/1.99  --bmc1_non_equiv_states                 false
% 11.51/1.99  --bmc1_deadlock                         false
% 11.51/1.99  --bmc1_ucm                              false
% 11.51/1.99  --bmc1_add_unsat_core                   none
% 11.51/1.99  --bmc1_unsat_core_children              false
% 11.51/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.51/1.99  --bmc1_out_stat                         full
% 11.51/1.99  --bmc1_ground_init                      false
% 11.51/1.99  --bmc1_pre_inst_next_state              false
% 11.51/1.99  --bmc1_pre_inst_state                   false
% 11.51/1.99  --bmc1_pre_inst_reach_state             false
% 11.51/1.99  --bmc1_out_unsat_core                   false
% 11.51/1.99  --bmc1_aig_witness_out                  false
% 11.51/1.99  --bmc1_verbose                          false
% 11.51/1.99  --bmc1_dump_clauses_tptp                false
% 11.51/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.51/1.99  --bmc1_dump_file                        -
% 11.51/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.51/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.51/1.99  --bmc1_ucm_extend_mode                  1
% 11.51/1.99  --bmc1_ucm_init_mode                    2
% 11.51/1.99  --bmc1_ucm_cone_mode                    none
% 11.51/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.51/1.99  --bmc1_ucm_relax_model                  4
% 11.51/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.51/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.51/1.99  --bmc1_ucm_layered_model                none
% 11.51/1.99  --bmc1_ucm_max_lemma_size               10
% 11.51/1.99  
% 11.51/1.99  ------ AIG Options
% 11.51/1.99  
% 11.51/1.99  --aig_mode                              false
% 11.51/1.99  
% 11.51/1.99  ------ Instantiation Options
% 11.51/1.99  
% 11.51/1.99  --instantiation_flag                    true
% 11.51/1.99  --inst_sos_flag                         true
% 11.51/1.99  --inst_sos_phase                        true
% 11.51/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.51/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.51/1.99  --inst_lit_sel_side                     none
% 11.51/1.99  --inst_solver_per_active                1400
% 11.51/1.99  --inst_solver_calls_frac                1.
% 11.51/1.99  --inst_passive_queue_type               priority_queues
% 11.51/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.51/1.99  --inst_passive_queues_freq              [25;2]
% 11.51/1.99  --inst_dismatching                      true
% 11.51/1.99  --inst_eager_unprocessed_to_passive     true
% 11.51/1.99  --inst_prop_sim_given                   true
% 11.51/1.99  --inst_prop_sim_new                     false
% 11.51/1.99  --inst_subs_new                         false
% 11.51/1.99  --inst_eq_res_simp                      false
% 11.51/1.99  --inst_subs_given                       false
% 11.51/1.99  --inst_orphan_elimination               true
% 11.51/1.99  --inst_learning_loop_flag               true
% 11.51/1.99  --inst_learning_start                   3000
% 11.51/1.99  --inst_learning_factor                  2
% 11.51/1.99  --inst_start_prop_sim_after_learn       3
% 11.51/1.99  --inst_sel_renew                        solver
% 11.51/1.99  --inst_lit_activity_flag                true
% 11.51/1.99  --inst_restr_to_given                   false
% 11.51/1.99  --inst_activity_threshold               500
% 11.51/1.99  --inst_out_proof                        true
% 11.51/1.99  
% 11.51/1.99  ------ Resolution Options
% 11.51/1.99  
% 11.51/1.99  --resolution_flag                       false
% 11.51/1.99  --res_lit_sel                           adaptive
% 11.51/1.99  --res_lit_sel_side                      none
% 11.51/1.99  --res_ordering                          kbo
% 11.51/1.99  --res_to_prop_solver                    active
% 11.51/1.99  --res_prop_simpl_new                    false
% 11.51/1.99  --res_prop_simpl_given                  true
% 11.51/1.99  --res_passive_queue_type                priority_queues
% 11.51/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.51/1.99  --res_passive_queues_freq               [15;5]
% 11.51/1.99  --res_forward_subs                      full
% 11.51/1.99  --res_backward_subs                     full
% 11.51/1.99  --res_forward_subs_resolution           true
% 11.51/1.99  --res_backward_subs_resolution          true
% 11.51/1.99  --res_orphan_elimination                true
% 11.51/1.99  --res_time_limit                        2.
% 11.51/1.99  --res_out_proof                         true
% 11.51/1.99  
% 11.51/1.99  ------ Superposition Options
% 11.51/1.99  
% 11.51/1.99  --superposition_flag                    true
% 11.51/1.99  --sup_passive_queue_type                priority_queues
% 11.51/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.51/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.51/1.99  --demod_completeness_check              fast
% 11.51/1.99  --demod_use_ground                      true
% 11.51/1.99  --sup_to_prop_solver                    passive
% 11.51/1.99  --sup_prop_simpl_new                    true
% 11.51/1.99  --sup_prop_simpl_given                  true
% 11.51/1.99  --sup_fun_splitting                     true
% 11.51/1.99  --sup_smt_interval                      50000
% 11.51/1.99  
% 11.51/1.99  ------ Superposition Simplification Setup
% 11.51/1.99  
% 11.51/1.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.51/1.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.51/1.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.51/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.51/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.51/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.51/1.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.51/1.99  --sup_immed_triv                        [TrivRules]
% 11.51/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.51/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.51/1.99  --sup_immed_bw_main                     []
% 11.51/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.51/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.51/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.51/1.99  --sup_input_bw                          []
% 11.51/1.99  
% 11.51/1.99  ------ Combination Options
% 11.51/1.99  
% 11.51/1.99  --comb_res_mult                         3
% 11.51/1.99  --comb_sup_mult                         2
% 11.51/1.99  --comb_inst_mult                        10
% 11.51/1.99  
% 11.51/1.99  ------ Debug Options
% 11.51/1.99  
% 11.51/1.99  --dbg_backtrace                         false
% 11.51/1.99  --dbg_dump_prop_clauses                 false
% 11.51/1.99  --dbg_dump_prop_clauses_file            -
% 11.51/1.99  --dbg_out_stat                          false
% 11.51/1.99  
% 11.51/1.99  
% 11.51/1.99  
% 11.51/1.99  
% 11.51/1.99  ------ Proving...
% 11.51/1.99  
% 11.51/1.99  
% 11.51/1.99  % SZS status Theorem for theBenchmark.p
% 11.51/1.99  
% 11.51/1.99   Resolution empty clause
% 11.51/1.99  
% 11.51/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.51/1.99  
% 11.51/1.99  fof(f9,conjecture,(
% 11.51/1.99    ! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)))))),
% 11.51/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.51/1.99  
% 11.51/1.99  fof(f10,negated_conjecture,(
% 11.51/1.99    ~! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)))))),
% 11.51/1.99    inference(negated_conjecture,[],[f9])).
% 11.51/1.99  
% 11.51/1.99  fof(f20,plain,(
% 11.51/1.99    ? [X0,X1,X2] : (? [X3] : ((~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) & (r1_tarski(X0,X1) & r1_tarski(X2,X3))) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 11.51/1.99    inference(ennf_transformation,[],[f10])).
% 11.51/1.99  
% 11.51/1.99  fof(f21,plain,(
% 11.51/1.99    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 11.51/1.99    inference(flattening,[],[f20])).
% 11.51/1.99  
% 11.51/1.99  fof(f23,plain,(
% 11.51/1.99    ( ! [X2,X0,X1] : (? [X3] : (~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) => (~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,sK3)) & r1_tarski(X0,X1) & r1_tarski(X2,sK3) & v1_relat_1(sK3))) )),
% 11.51/1.99    introduced(choice_axiom,[])).
% 11.51/1.99  
% 11.51/1.99  fof(f22,plain,(
% 11.51/1.99    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2)) => (? [X3] : (~r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,X3)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,X3) & v1_relat_1(X3)) & v1_relat_1(sK2))),
% 11.51/1.99    introduced(choice_axiom,[])).
% 11.51/1.99  
% 11.51/1.99  fof(f24,plain,(
% 11.51/1.99    (~r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,sK3) & v1_relat_1(sK3)) & v1_relat_1(sK2)),
% 11.51/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f23,f22])).
% 11.51/1.99  
% 11.51/1.99  fof(f34,plain,(
% 11.51/1.99    v1_relat_1(sK3)),
% 11.51/1.99    inference(cnf_transformation,[],[f24])).
% 11.51/1.99  
% 11.51/1.99  fof(f6,axiom,(
% 11.51/1.99    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k8_relat_1(X0,X1),X1))),
% 11.51/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.51/1.99  
% 11.51/1.99  fof(f15,plain,(
% 11.51/1.99    ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1))),
% 11.51/1.99    inference(ennf_transformation,[],[f6])).
% 11.51/1.99  
% 11.51/1.99  fof(f30,plain,(
% 11.51/1.99    ( ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1)) )),
% 11.51/1.99    inference(cnf_transformation,[],[f15])).
% 11.51/1.99  
% 11.51/1.99  fof(f4,axiom,(
% 11.51/1.99    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 11.51/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.51/1.99  
% 11.51/1.99  fof(f13,plain,(
% 11.51/1.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 11.51/1.99    inference(ennf_transformation,[],[f4])).
% 11.51/1.99  
% 11.51/1.99  fof(f28,plain,(
% 11.51/1.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 11.51/1.99    inference(cnf_transformation,[],[f13])).
% 11.51/1.99  
% 11.51/1.99  fof(f1,axiom,(
% 11.51/1.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 11.51/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.51/1.99  
% 11.51/1.99  fof(f25,plain,(
% 11.51/1.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 11.51/1.99    inference(cnf_transformation,[],[f1])).
% 11.51/1.99  
% 11.51/1.99  fof(f5,axiom,(
% 11.51/1.99    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 11.51/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.51/1.99  
% 11.51/1.99  fof(f14,plain,(
% 11.51/1.99    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 11.51/1.99    inference(ennf_transformation,[],[f5])).
% 11.51/1.99  
% 11.51/1.99  fof(f29,plain,(
% 11.51/1.99    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 11.51/1.99    inference(cnf_transformation,[],[f14])).
% 11.51/1.99  
% 11.51/1.99  fof(f35,plain,(
% 11.51/1.99    r1_tarski(sK2,sK3)),
% 11.51/1.99    inference(cnf_transformation,[],[f24])).
% 11.51/1.99  
% 11.51/1.99  fof(f8,axiom,(
% 11.51/1.99    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)))))),
% 11.51/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.51/1.99  
% 11.51/1.99  fof(f18,plain,(
% 11.51/1.99    ! [X0,X1] : (! [X2] : ((r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 11.51/1.99    inference(ennf_transformation,[],[f8])).
% 11.51/1.99  
% 11.51/1.99  fof(f19,plain,(
% 11.51/1.99    ! [X0,X1] : (! [X2] : (r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 11.51/1.99    inference(flattening,[],[f18])).
% 11.51/1.99  
% 11.51/1.99  fof(f32,plain,(
% 11.51/1.99    ( ! [X2,X0,X1] : (r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 11.51/1.99    inference(cnf_transformation,[],[f19])).
% 11.51/1.99  
% 11.51/1.99  fof(f33,plain,(
% 11.51/1.99    v1_relat_1(sK2)),
% 11.51/1.99    inference(cnf_transformation,[],[f24])).
% 11.51/1.99  
% 11.51/1.99  fof(f36,plain,(
% 11.51/1.99    r1_tarski(sK0,sK1)),
% 11.51/1.99    inference(cnf_transformation,[],[f24])).
% 11.51/1.99  
% 11.51/1.99  fof(f7,axiom,(
% 11.51/1.99    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))))),
% 11.51/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.51/1.99  
% 11.51/1.99  fof(f16,plain,(
% 11.51/1.99    ! [X0,X1,X2] : ((k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 11.51/1.99    inference(ennf_transformation,[],[f7])).
% 11.51/1.99  
% 11.51/1.99  fof(f17,plain,(
% 11.51/1.99    ! [X0,X1,X2] : (k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 11.51/1.99    inference(flattening,[],[f16])).
% 11.51/1.99  
% 11.51/1.99  fof(f31,plain,(
% 11.51/1.99    ( ! [X2,X0,X1] : (k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 11.51/1.99    inference(cnf_transformation,[],[f17])).
% 11.51/1.99  
% 11.51/1.99  fof(f37,plain,(
% 11.51/1.99    ~r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),
% 11.51/1.99    inference(cnf_transformation,[],[f24])).
% 11.51/1.99  
% 11.51/1.99  fof(f3,axiom,(
% 11.51/1.99    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 11.51/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.51/1.99  
% 11.51/1.99  fof(f12,plain,(
% 11.51/1.99    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 11.51/1.99    inference(ennf_transformation,[],[f3])).
% 11.51/1.99  
% 11.51/1.99  fof(f27,plain,(
% 11.51/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 11.51/1.99    inference(cnf_transformation,[],[f12])).
% 11.51/1.99  
% 11.51/1.99  fof(f2,axiom,(
% 11.51/1.99    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 11.51/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.51/1.99  
% 11.51/1.99  fof(f11,plain,(
% 11.51/1.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 11.51/1.99    inference(ennf_transformation,[],[f2])).
% 11.51/1.99  
% 11.51/1.99  fof(f26,plain,(
% 11.51/1.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 11.51/1.99    inference(cnf_transformation,[],[f11])).
% 11.51/1.99  
% 11.51/1.99  cnf(c_11,negated_conjecture,
% 11.51/1.99      ( v1_relat_1(sK3) ),
% 11.51/1.99      inference(cnf_transformation,[],[f34]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_342,plain,
% 11.51/1.99      ( v1_relat_1(sK3) = iProver_top ),
% 11.51/1.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_5,plain,
% 11.51/1.99      ( r1_tarski(k8_relat_1(X0,X1),X1) | ~ v1_relat_1(X1) ),
% 11.51/1.99      inference(cnf_transformation,[],[f30]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_348,plain,
% 11.51/1.99      ( r1_tarski(k8_relat_1(X0,X1),X1) = iProver_top
% 11.51/1.99      | v1_relat_1(X1) != iProver_top ),
% 11.51/1.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_3,plain,
% 11.51/1.99      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 11.51/1.99      inference(cnf_transformation,[],[f28]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_350,plain,
% 11.51/1.99      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 11.51/1.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_840,plain,
% 11.51/1.99      ( k3_xboole_0(k8_relat_1(X0,X1),X1) = k8_relat_1(X0,X1)
% 11.51/1.99      | v1_relat_1(X1) != iProver_top ),
% 11.51/1.99      inference(superposition,[status(thm)],[c_348,c_350]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_3596,plain,
% 11.51/1.99      ( k3_xboole_0(k8_relat_1(X0,sK3),sK3) = k8_relat_1(X0,sK3) ),
% 11.51/1.99      inference(superposition,[status(thm)],[c_342,c_840]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_0,plain,
% 11.51/1.99      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 11.51/1.99      inference(cnf_transformation,[],[f25]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_4,plain,
% 11.51/1.99      ( ~ v1_relat_1(X0) | v1_relat_1(k3_xboole_0(X0,X1)) ),
% 11.51/1.99      inference(cnf_transformation,[],[f29]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_349,plain,
% 11.51/1.99      ( v1_relat_1(X0) != iProver_top
% 11.51/1.99      | v1_relat_1(k3_xboole_0(X0,X1)) = iProver_top ),
% 11.51/1.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_650,plain,
% 11.51/1.99      ( v1_relat_1(X0) != iProver_top
% 11.51/1.99      | v1_relat_1(k3_xboole_0(X1,X0)) = iProver_top ),
% 11.51/1.99      inference(superposition,[status(thm)],[c_0,c_349]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_3810,plain,
% 11.51/1.99      ( v1_relat_1(k8_relat_1(X0,sK3)) = iProver_top
% 11.51/1.99      | v1_relat_1(sK3) != iProver_top ),
% 11.51/1.99      inference(superposition,[status(thm)],[c_3596,c_650]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_14,plain,
% 11.51/1.99      ( v1_relat_1(sK3) = iProver_top ),
% 11.51/1.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_4203,plain,
% 11.51/1.99      ( v1_relat_1(k8_relat_1(X0,sK3)) = iProver_top ),
% 11.51/1.99      inference(global_propositional_subsumption,[status(thm)],[c_3810,c_14]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_10,negated_conjecture,
% 11.51/1.99      ( r1_tarski(sK2,sK3) ),
% 11.51/1.99      inference(cnf_transformation,[],[f35]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_343,plain,
% 11.51/1.99      ( r1_tarski(sK2,sK3) = iProver_top ),
% 11.51/1.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_7,plain,
% 11.51/1.99      ( ~ r1_tarski(X0,X1)
% 11.51/1.99      | r1_tarski(k8_relat_1(X2,X0),k8_relat_1(X2,X1))
% 11.51/1.99      | ~ v1_relat_1(X0)
% 11.51/1.99      | ~ v1_relat_1(X1) ),
% 11.51/1.99      inference(cnf_transformation,[],[f32]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_346,plain,
% 11.51/1.99      ( r1_tarski(X0,X1) != iProver_top
% 11.51/1.99      | r1_tarski(k8_relat_1(X2,X0),k8_relat_1(X2,X1)) = iProver_top
% 11.51/1.99      | v1_relat_1(X0) != iProver_top
% 11.51/1.99      | v1_relat_1(X1) != iProver_top ),
% 11.51/1.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_724,plain,
% 11.51/1.99      ( k3_xboole_0(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) = k8_relat_1(X0,X1)
% 11.51/1.99      | r1_tarski(X1,X2) != iProver_top
% 11.51/1.99      | v1_relat_1(X1) != iProver_top
% 11.51/1.99      | v1_relat_1(X2) != iProver_top ),
% 11.51/1.99      inference(superposition,[status(thm)],[c_346,c_350]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_1923,plain,
% 11.51/1.99      ( k3_xboole_0(k8_relat_1(X0,sK2),k8_relat_1(X0,sK3)) = k8_relat_1(X0,sK2)
% 11.51/1.99      | v1_relat_1(sK3) != iProver_top
% 11.51/1.99      | v1_relat_1(sK2) != iProver_top ),
% 11.51/1.99      inference(superposition,[status(thm)],[c_343,c_724]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_12,negated_conjecture,
% 11.51/1.99      ( v1_relat_1(sK2) ),
% 11.51/1.99      inference(cnf_transformation,[],[f33]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_13,plain,
% 11.51/1.99      ( v1_relat_1(sK2) = iProver_top ),
% 11.51/1.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_2134,plain,
% 11.51/1.99      ( k3_xboole_0(k8_relat_1(X0,sK2),k8_relat_1(X0,sK3)) = k8_relat_1(X0,sK2) ),
% 11.51/1.99      inference(global_propositional_subsumption,
% 11.51/1.99                [status(thm)],
% 11.51/1.99                [c_1923,c_13,c_14]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_2138,plain,
% 11.51/1.99      ( v1_relat_1(k8_relat_1(X0,sK3)) != iProver_top
% 11.51/1.99      | v1_relat_1(k8_relat_1(X0,sK2)) = iProver_top ),
% 11.51/1.99      inference(superposition,[status(thm)],[c_2134,c_650]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_4215,plain,
% 11.51/1.99      ( v1_relat_1(k8_relat_1(X0,sK2)) = iProver_top ),
% 11.51/1.99      inference(superposition,[status(thm)],[c_4203,c_2138]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_341,plain,
% 11.51/1.99      ( v1_relat_1(sK2) = iProver_top ),
% 11.51/1.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_9,negated_conjecture,
% 11.51/1.99      ( r1_tarski(sK0,sK1) ),
% 11.51/1.99      inference(cnf_transformation,[],[f36]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_344,plain,
% 11.51/1.99      ( r1_tarski(sK0,sK1) = iProver_top ),
% 11.51/1.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_6,plain,
% 11.51/1.99      ( ~ r1_tarski(X0,X1)
% 11.51/1.99      | ~ v1_relat_1(X2)
% 11.51/1.99      | k8_relat_1(X1,k8_relat_1(X0,X2)) = k8_relat_1(X0,X2) ),
% 11.51/1.99      inference(cnf_transformation,[],[f31]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_347,plain,
% 11.51/1.99      ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X1,X2)
% 11.51/1.99      | r1_tarski(X1,X0) != iProver_top
% 11.51/1.99      | v1_relat_1(X2) != iProver_top ),
% 11.51/1.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_1225,plain,
% 11.51/1.99      ( k8_relat_1(sK1,k8_relat_1(sK0,X0)) = k8_relat_1(sK0,X0)
% 11.51/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.51/1.99      inference(superposition,[status(thm)],[c_344,c_347]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_1495,plain,
% 11.51/1.99      ( k8_relat_1(sK1,k8_relat_1(sK0,sK2)) = k8_relat_1(sK0,sK2) ),
% 11.51/1.99      inference(superposition,[status(thm)],[c_341,c_1225]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_1651,plain,
% 11.51/1.99      ( r1_tarski(k8_relat_1(sK0,sK2),X0) != iProver_top
% 11.51/1.99      | r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,X0)) = iProver_top
% 11.51/1.99      | v1_relat_1(X0) != iProver_top
% 11.51/1.99      | v1_relat_1(k8_relat_1(sK0,sK2)) != iProver_top ),
% 11.51/1.99      inference(superposition,[status(thm)],[c_1495,c_346]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_15,plain,
% 11.51/1.99      ( r1_tarski(sK2,sK3) = iProver_top ),
% 11.51/1.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_8,negated_conjecture,
% 11.51/1.99      ( ~ r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)) ),
% 11.51/1.99      inference(cnf_transformation,[],[f37]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_17,plain,
% 11.51/1.99      ( r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)) != iProver_top ),
% 11.51/1.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_136,plain,( X0 = X0 ),theory(equality) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_405,plain,
% 11.51/1.99      ( k8_relat_1(sK1,sK3) = k8_relat_1(sK1,sK3) ),
% 11.51/1.99      inference(instantiation,[status(thm)],[c_136]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_520,plain,
% 11.51/1.99      ( k8_relat_1(sK0,sK2) = k8_relat_1(sK0,sK2) ),
% 11.51/1.99      inference(instantiation,[status(thm)],[c_136]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_892,plain,
% 11.51/1.99      ( sK3 = sK3 ),
% 11.51/1.99      inference(instantiation,[status(thm)],[c_136]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_854,plain,
% 11.51/1.99      ( ~ r1_tarski(sK0,X0)
% 11.51/1.99      | ~ v1_relat_1(sK2)
% 11.51/1.99      | k8_relat_1(X0,k8_relat_1(sK0,sK2)) = k8_relat_1(sK0,sK2) ),
% 11.51/1.99      inference(instantiation,[status(thm)],[c_6]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_1172,plain,
% 11.51/1.99      ( ~ r1_tarski(sK0,sK1)
% 11.51/1.99      | ~ v1_relat_1(sK2)
% 11.51/1.99      | k8_relat_1(sK1,k8_relat_1(sK0,sK2)) = k8_relat_1(sK0,sK2) ),
% 11.51/1.99      inference(instantiation,[status(thm)],[c_854]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_137,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_441,plain,
% 11.51/1.99      ( X0 != X1 | k8_relat_1(sK0,sK2) != X1 | k8_relat_1(sK0,sK2) = X0 ),
% 11.51/1.99      inference(instantiation,[status(thm)],[c_137]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_523,plain,
% 11.51/1.99      ( X0 != k8_relat_1(sK0,sK2)
% 11.51/1.99      | k8_relat_1(sK0,sK2) = X0
% 11.51/1.99      | k8_relat_1(sK0,sK2) != k8_relat_1(sK0,sK2) ),
% 11.51/1.99      inference(instantiation,[status(thm)],[c_441]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_621,plain,
% 11.51/1.99      ( k8_relat_1(X0,k8_relat_1(sK0,sK2)) != k8_relat_1(sK0,sK2)
% 11.51/1.99      | k8_relat_1(sK0,sK2) = k8_relat_1(X0,k8_relat_1(sK0,sK2))
% 11.51/1.99      | k8_relat_1(sK0,sK2) != k8_relat_1(sK0,sK2) ),
% 11.51/1.99      inference(instantiation,[status(thm)],[c_523]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_1383,plain,
% 11.51/1.99      ( k8_relat_1(sK1,k8_relat_1(sK0,sK2)) != k8_relat_1(sK0,sK2)
% 11.51/1.99      | k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2))
% 11.51/1.99      | k8_relat_1(sK0,sK2) != k8_relat_1(sK0,sK2) ),
% 11.51/1.99      inference(instantiation,[status(thm)],[c_621]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_2,plain,
% 11.51/1.99      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 11.51/1.99      inference(cnf_transformation,[],[f27]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_1515,plain,
% 11.51/1.99      ( ~ r1_tarski(k8_relat_1(sK0,sK2),X0)
% 11.51/1.99      | k2_xboole_0(k8_relat_1(sK0,sK2),X0) = X0 ),
% 11.51/1.99      inference(instantiation,[status(thm)],[c_2]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_1517,plain,
% 11.51/1.99      ( ~ r1_tarski(k8_relat_1(sK0,sK2),sK2)
% 11.51/1.99      | k2_xboole_0(k8_relat_1(sK0,sK2),sK2) = sK2 ),
% 11.51/1.99      inference(instantiation,[status(thm)],[c_1515]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_138,plain,
% 11.51/1.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.51/1.99      theory(equality) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_375,plain,
% 11.51/1.99      ( ~ r1_tarski(X0,X1)
% 11.51/1.99      | r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))
% 11.51/1.99      | k8_relat_1(sK1,sK3) != X1
% 11.51/1.99      | k8_relat_1(sK0,sK2) != X0 ),
% 11.51/1.99      inference(instantiation,[status(thm)],[c_138]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_390,plain,
% 11.51/1.99      ( ~ r1_tarski(X0,k8_relat_1(sK1,sK3))
% 11.51/1.99      | r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))
% 11.51/1.99      | k8_relat_1(sK1,sK3) != k8_relat_1(sK1,sK3)
% 11.51/1.99      | k8_relat_1(sK0,sK2) != X0 ),
% 11.51/1.99      inference(instantiation,[status(thm)],[c_375]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_460,plain,
% 11.51/1.99      ( ~ r1_tarski(k8_relat_1(sK1,X0),k8_relat_1(sK1,sK3))
% 11.51/1.99      | r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))
% 11.51/1.99      | k8_relat_1(sK1,sK3) != k8_relat_1(sK1,sK3)
% 11.51/1.99      | k8_relat_1(sK0,sK2) != k8_relat_1(sK1,X0) ),
% 11.51/1.99      inference(instantiation,[status(thm)],[c_390]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_1681,plain,
% 11.51/1.99      ( ~ r1_tarski(k8_relat_1(sK1,k8_relat_1(sK0,sK2)),k8_relat_1(sK1,sK3))
% 11.51/1.99      | r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))
% 11.51/1.99      | k8_relat_1(sK1,sK3) != k8_relat_1(sK1,sK3)
% 11.51/1.99      | k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2)) ),
% 11.51/1.99      inference(instantiation,[status(thm)],[c_460]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_1682,plain,
% 11.51/1.99      ( k8_relat_1(sK1,sK3) != k8_relat_1(sK1,sK3)
% 11.51/1.99      | k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2))
% 11.51/1.99      | r1_tarski(k8_relat_1(sK1,k8_relat_1(sK0,sK2)),k8_relat_1(sK1,sK3)) != iProver_top
% 11.51/1.99      | r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)) = iProver_top ),
% 11.51/1.99      inference(predicate_to_equality,[status(thm)],[c_1681]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_1814,plain,
% 11.51/1.99      ( r1_tarski(k8_relat_1(sK0,sK2),sK2) | ~ v1_relat_1(sK2) ),
% 11.51/1.99      inference(instantiation,[status(thm)],[c_5]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_498,plain,
% 11.51/1.99      ( ~ r1_tarski(X0,sK3)
% 11.51/1.99      | r1_tarski(k8_relat_1(sK1,X0),k8_relat_1(sK1,sK3))
% 11.51/1.99      | ~ v1_relat_1(X0)
% 11.51/1.99      | ~ v1_relat_1(sK3) ),
% 11.51/1.99      inference(instantiation,[status(thm)],[c_7]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_3307,plain,
% 11.51/1.99      ( r1_tarski(k8_relat_1(sK1,k8_relat_1(sK0,sK2)),k8_relat_1(sK1,sK3))
% 11.51/1.99      | ~ r1_tarski(k8_relat_1(sK0,sK2),sK3)
% 11.51/1.99      | ~ v1_relat_1(k8_relat_1(sK0,sK2))
% 11.51/1.99      | ~ v1_relat_1(sK3) ),
% 11.51/1.99      inference(instantiation,[status(thm)],[c_498]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_3308,plain,
% 11.51/1.99      ( r1_tarski(k8_relat_1(sK1,k8_relat_1(sK0,sK2)),k8_relat_1(sK1,sK3)) = iProver_top
% 11.51/1.99      | r1_tarski(k8_relat_1(sK0,sK2),sK3) != iProver_top
% 11.51/1.99      | v1_relat_1(k8_relat_1(sK0,sK2)) != iProver_top
% 11.51/1.99      | v1_relat_1(sK3) != iProver_top ),
% 11.51/1.99      inference(predicate_to_equality,[status(thm)],[c_3307]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_1,plain,
% 11.51/1.99      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 11.51/1.99      inference(cnf_transformation,[],[f26]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_1062,plain,
% 11.51/1.99      ( r1_tarski(k8_relat_1(sK0,sK2),X0)
% 11.51/1.99      | ~ r1_tarski(k2_xboole_0(k8_relat_1(sK0,sK2),X1),X0) ),
% 11.51/1.99      inference(instantiation,[status(thm)],[c_1]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_8344,plain,
% 11.51/1.99      ( r1_tarski(k8_relat_1(sK0,sK2),sK3)
% 11.51/1.99      | ~ r1_tarski(k2_xboole_0(k8_relat_1(sK0,sK2),X0),sK3) ),
% 11.51/1.99      inference(instantiation,[status(thm)],[c_1062]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_8349,plain,
% 11.51/1.99      ( r1_tarski(k8_relat_1(sK0,sK2),sK3) = iProver_top
% 11.51/1.99      | r1_tarski(k2_xboole_0(k8_relat_1(sK0,sK2),X0),sK3) != iProver_top ),
% 11.51/1.99      inference(predicate_to_equality,[status(thm)],[c_8344]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_8351,plain,
% 11.51/1.99      ( r1_tarski(k8_relat_1(sK0,sK2),sK3) = iProver_top
% 11.51/1.99      | r1_tarski(k2_xboole_0(k8_relat_1(sK0,sK2),sK2),sK3) != iProver_top ),
% 11.51/1.99      inference(instantiation,[status(thm)],[c_8349]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_1476,plain,
% 11.51/1.99      ( r1_tarski(X0,X1) | ~ r1_tarski(sK2,sK3) | X1 != sK3 | X0 != sK2 ),
% 11.51/1.99      inference(instantiation,[status(thm)],[c_138]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_1660,plain,
% 11.51/1.99      ( r1_tarski(X0,sK3) | ~ r1_tarski(sK2,sK3) | X0 != sK2 | sK3 != sK3 ),
% 11.51/1.99      inference(instantiation,[status(thm)],[c_1476]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_3005,plain,
% 11.51/1.99      ( r1_tarski(k2_xboole_0(X0,X1),sK3)
% 11.51/1.99      | ~ r1_tarski(sK2,sK3)
% 11.51/1.99      | k2_xboole_0(X0,X1) != sK2
% 11.51/1.99      | sK3 != sK3 ),
% 11.51/1.99      inference(instantiation,[status(thm)],[c_1660]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_8458,plain,
% 11.51/1.99      ( r1_tarski(k2_xboole_0(k8_relat_1(sK0,sK2),sK2),sK3)
% 11.51/1.99      | ~ r1_tarski(sK2,sK3)
% 11.51/1.99      | k2_xboole_0(k8_relat_1(sK0,sK2),sK2) != sK2
% 11.51/1.99      | sK3 != sK3 ),
% 11.51/1.99      inference(instantiation,[status(thm)],[c_3005]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_8459,plain,
% 11.51/1.99      ( k2_xboole_0(k8_relat_1(sK0,sK2),sK2) != sK2
% 11.51/1.99      | sK3 != sK3
% 11.51/1.99      | r1_tarski(k2_xboole_0(k8_relat_1(sK0,sK2),sK2),sK3) = iProver_top
% 11.51/1.99      | r1_tarski(sK2,sK3) != iProver_top ),
% 11.51/1.99      inference(predicate_to_equality,[status(thm)],[c_8458]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_13546,plain,
% 11.51/1.99      ( v1_relat_1(k8_relat_1(sK0,sK2)) != iProver_top ),
% 11.51/1.99      inference(global_propositional_subsumption,
% 11.51/1.99                [status(thm)],
% 11.51/1.99                [c_1651,c_12,c_14,c_15,c_9,c_17,c_405,c_520,c_892,c_1172,
% 11.51/1.99                 c_1383,c_1517,c_1682,c_1814,c_3308,c_8351,c_8459]) ).
% 11.51/1.99  
% 11.51/1.99  cnf(c_40481,plain,
% 11.51/1.99      ( $false ),
% 11.51/1.99      inference(superposition,[status(thm)],[c_4215,c_13546]) ).
% 11.51/1.99  
% 11.51/1.99  
% 11.51/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.51/1.99  
% 11.51/1.99  ------                               Statistics
% 11.51/1.99  
% 11.51/1.99  ------ General
% 11.51/1.99  
% 11.51/1.99  abstr_ref_over_cycles:                  0
% 11.51/1.99  abstr_ref_under_cycles:                 0
% 11.51/1.99  gc_basic_clause_elim:                   0
% 11.51/1.99  forced_gc_time:                         0
% 11.51/1.99  parsing_time:                           0.02
% 11.51/1.99  unif_index_cands_time:                  0.
% 11.51/1.99  unif_index_add_time:                    0.
% 11.51/1.99  orderings_time:                         0.
% 11.51/1.99  out_proof_time:                         0.009
% 11.51/1.99  total_time:                             1.247
% 11.51/1.99  num_of_symbols:                         40
% 11.51/1.99  num_of_terms:                           35277
% 11.51/1.99  
% 11.51/1.99  ------ Preprocessing
% 11.51/1.99  
% 11.51/1.99  num_of_splits:                          0
% 11.51/1.99  num_of_split_atoms:                     0
% 11.51/1.99  num_of_reused_defs:                     0
% 11.51/1.99  num_eq_ax_congr_red:                    8
% 11.51/1.99  num_of_sem_filtered_clauses:            1
% 11.51/1.99  num_of_subtypes:                        0
% 11.51/1.99  monotx_restored_types:                  0
% 11.51/1.99  sat_num_of_epr_types:                   0
% 11.51/1.99  sat_num_of_non_cyclic_types:            0
% 11.51/1.99  sat_guarded_non_collapsed_types:        0
% 11.51/1.99  num_pure_diseq_elim:                    0
% 11.51/1.99  simp_replaced_by:                       0
% 11.51/1.99  res_preprocessed:                       50
% 11.51/1.99  prep_upred:                             0
% 11.51/1.99  prep_unflattend:                        0
% 11.51/1.99  smt_new_axioms:                         0
% 11.51/1.99  pred_elim_cands:                        2
% 11.51/1.99  pred_elim:                              0
% 11.51/1.99  pred_elim_cl:                           0
% 11.51/1.99  pred_elim_cycles:                       1
% 11.51/1.99  merged_defs:                            0
% 11.51/1.99  merged_defs_ncl:                        0
% 11.51/1.99  bin_hyper_res:                          0
% 11.51/1.99  prep_cycles:                            3
% 11.51/1.99  pred_elim_time:                         0.
% 11.51/1.99  splitting_time:                         0.
% 11.51/1.99  sem_filter_time:                        0.
% 11.51/1.99  monotx_time:                            0.
% 11.51/1.99  subtype_inf_time:                       0.
% 11.51/1.99  
% 11.51/1.99  ------ Problem properties
% 11.51/1.99  
% 11.51/1.99  clauses:                                13
% 11.51/1.99  conjectures:                            5
% 11.51/1.99  epr:                                    4
% 11.51/1.99  horn:                                   13
% 11.51/1.99  ground:                                 5
% 11.51/1.99  unary:                                  6
% 11.51/1.99  binary:                                 5
% 11.51/1.99  lits:                                   23
% 11.51/1.99  lits_eq:                                4
% 11.51/1.99  fd_pure:                                0
% 11.51/1.99  fd_pseudo:                              0
% 11.51/1.99  fd_cond:                                0
% 11.51/1.99  fd_pseudo_cond:                         0
% 11.51/1.99  ac_symbols:                             0
% 11.51/1.99  
% 11.51/1.99  ------ Propositional Solver
% 11.51/1.99  
% 11.51/1.99  prop_solver_calls:                      32
% 11.51/1.99  prop_fast_solver_calls:                 979
% 11.51/1.99  smt_solver_calls:                       0
% 11.51/1.99  smt_fast_solver_calls:                  0
% 11.51/1.99  prop_num_of_clauses:                    16529
% 11.51/1.99  prop_preprocess_simplified:             30211
% 11.51/1.99  prop_fo_subsumed:                       28
% 11.51/1.99  prop_solver_time:                       0.
% 11.51/1.99  smt_solver_time:                        0.
% 11.51/1.99  smt_fast_solver_time:                   0.
% 11.51/1.99  prop_fast_solver_time:                  0.
% 11.51/1.99  prop_unsat_core_time:                   0.
% 11.51/1.99  
% 11.51/1.99  ------ QBF
% 11.51/1.99  
% 11.51/1.99  qbf_q_res:                              0
% 11.51/1.99  qbf_num_tautologies:                    0
% 11.51/1.99  qbf_prep_cycles:                        0
% 11.51/1.99  
% 11.51/1.99  ------ BMC1
% 11.51/1.99  
% 11.51/1.99  bmc1_current_bound:                     -1
% 11.51/1.99  bmc1_last_solved_bound:                 -1
% 11.51/1.99  bmc1_unsat_core_size:                   -1
% 11.51/1.99  bmc1_unsat_core_parents_size:           -1
% 11.51/1.99  bmc1_merge_next_fun:                    0
% 11.51/1.99  bmc1_unsat_core_clauses_time:           0.
% 11.51/1.99  
% 11.51/1.99  ------ Instantiation
% 11.51/1.99  
% 11.51/1.99  inst_num_of_clauses:                    4133
% 11.51/1.99  inst_num_in_passive:                    2448
% 11.51/1.99  inst_num_in_active:                     1662
% 11.51/1.99  inst_num_in_unprocessed:                23
% 11.51/1.99  inst_num_of_loops:                      1720
% 11.51/1.99  inst_num_of_learning_restarts:          0
% 11.51/1.99  inst_num_moves_active_passive:          52
% 11.51/1.99  inst_lit_activity:                      0
% 11.51/1.99  inst_lit_activity_moves:                0
% 11.51/1.99  inst_num_tautologies:                   0
% 11.51/1.99  inst_num_prop_implied:                  0
% 11.51/1.99  inst_num_existing_simplified:           0
% 11.51/1.99  inst_num_eq_res_simplified:             0
% 11.51/1.99  inst_num_child_elim:                    0
% 11.51/1.99  inst_num_of_dismatching_blockings:      4955
% 11.51/1.99  inst_num_of_non_proper_insts:           6446
% 11.51/1.99  inst_num_of_duplicates:                 0
% 11.51/1.99  inst_inst_num_from_inst_to_res:         0
% 11.51/1.99  inst_dismatching_checking_time:         0.
% 11.51/1.99  
% 11.51/1.99  ------ Resolution
% 11.51/1.99  
% 11.51/1.99  res_num_of_clauses:                     0
% 11.51/1.99  res_num_in_passive:                     0
% 11.51/1.99  res_num_in_active:                      0
% 11.51/1.99  res_num_of_loops:                       53
% 11.51/1.99  res_forward_subset_subsumed:            233
% 11.51/1.99  res_backward_subset_subsumed:           0
% 11.51/1.99  res_forward_subsumed:                   0
% 11.51/1.99  res_backward_subsumed:                  0
% 11.51/1.99  res_forward_subsumption_resolution:     0
% 11.51/1.99  res_backward_subsumption_resolution:    0
% 11.51/1.99  res_clause_to_clause_subsumption:       10247
% 11.51/1.99  res_orphan_elimination:                 0
% 11.51/1.99  res_tautology_del:                      461
% 11.51/1.99  res_num_eq_res_simplified:              0
% 11.51/1.99  res_num_sel_changes:                    0
% 11.51/1.99  res_moves_from_active_to_pass:          0
% 11.51/1.99  
% 11.51/1.99  ------ Superposition
% 11.51/1.99  
% 11.51/1.99  sup_time_total:                         0.
% 11.51/1.99  sup_time_generating:                    0.
% 11.51/1.99  sup_time_sim_full:                      0.
% 11.51/1.99  sup_time_sim_immed:                     0.
% 11.51/1.99  
% 11.51/1.99  sup_num_of_clauses:                     1727
% 11.51/1.99  sup_num_in_active:                      328
% 11.51/1.99  sup_num_in_passive:                     1399
% 11.51/1.99  sup_num_of_loops:                       343
% 11.51/1.99  sup_fw_superposition:                   3033
% 11.51/1.99  sup_bw_superposition:                   1282
% 11.51/1.99  sup_immediate_simplified:               850
% 11.51/1.99  sup_given_eliminated:                   1
% 11.51/1.99  comparisons_done:                       0
% 11.51/1.99  comparisons_avoided:                    0
% 11.51/1.99  
% 11.51/1.99  ------ Simplifications
% 11.51/1.99  
% 11.51/1.99  
% 11.51/1.99  sim_fw_subset_subsumed:                 20
% 11.51/1.99  sim_bw_subset_subsumed:                 26
% 11.51/1.99  sim_fw_subsumed:                        311
% 11.51/1.99  sim_bw_subsumed:                        68
% 11.51/1.99  sim_fw_subsumption_res:                 0
% 11.51/1.99  sim_bw_subsumption_res:                 0
% 11.51/1.99  sim_tautology_del:                      689
% 11.51/1.99  sim_eq_tautology_del:                   133
% 11.51/1.99  sim_eq_res_simp:                        0
% 11.51/1.99  sim_fw_demodulated:                     307
% 11.51/1.99  sim_bw_demodulated:                     10
% 11.51/1.99  sim_light_normalised:                   275
% 11.51/1.99  sim_joinable_taut:                      0
% 11.51/1.99  sim_joinable_simp:                      0
% 11.51/1.99  sim_ac_normalised:                      0
% 11.51/1.99  sim_smt_subsumption:                    0
% 11.51/1.99  
%------------------------------------------------------------------------------
