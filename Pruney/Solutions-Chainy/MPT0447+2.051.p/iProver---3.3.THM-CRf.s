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
% DateTime   : Thu Dec  3 11:43:17 EST 2020

% Result     : Theorem 11.28s
% Output     : CNFRefutation 11.28s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 198 expanded)
%              Number of clauses        :   57 (  80 expanded)
%              Number of leaves         :   15 (  48 expanded)
%              Depth                    :   15
%              Number of atoms          :  211 ( 573 expanded)
%              Number of equality atoms :   84 ( 110 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f9,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
             => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
     => ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(sK1))
        & r1_tarski(X0,sK1)
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
            & r1_tarski(X0,X1)
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(X1))
          & r1_tarski(sK0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f23,f22])).

fof(f34,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f30,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f33,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f35,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f36,plain,(
    ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_1124,plain,
    ( r1_tarski(k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)),X0)
    | ~ r1_tarski(k2_relat_1(sK0),X0)
    | ~ r1_tarski(k1_relat_1(sK0),X0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_41479,plain,
    ( r1_tarski(k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)),k3_relat_1(sK1))
    | ~ r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_1124])).

cnf(c_10,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_340,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_345,plain,
    ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_716,plain,
    ( k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1)) = k3_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_340,c_345])).

cnf(c_3,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_347,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_882,plain,
    ( r1_tarski(k1_relat_1(sK1),k3_relat_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_716,c_347])).

cnf(c_11,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_339,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_344,plain,
    ( k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1268,plain,
    ( k2_xboole_0(k1_relat_1(sK0),k1_relat_1(X0)) = k1_relat_1(k2_xboole_0(sK0,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_339,c_344])).

cnf(c_1689,plain,
    ( k2_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) = k1_relat_1(k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_340,c_1268])).

cnf(c_9,negated_conjecture,
    ( r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_341,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_349,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_542,plain,
    ( k2_xboole_0(sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_341,c_349])).

cnf(c_1691,plain,
    ( k2_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) = k1_relat_1(sK1) ),
    inference(light_normalisation,[status(thm)],[c_1689,c_542])).

cnf(c_2147,plain,
    ( r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1691,c_347])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_348,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2616,plain,
    ( r1_tarski(k1_relat_1(sK1),X0) != iProver_top
    | r1_tarski(k1_relat_1(sK0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2147,c_348])).

cnf(c_6240,plain,
    ( r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_882,c_2616])).

cnf(c_6252,plain,
    ( r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6240])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_343,plain,
    ( k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_710,plain,
    ( k2_xboole_0(k2_relat_1(sK0),k2_relat_1(X0)) = k2_relat_1(k2_xboole_0(sK0,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_339,c_343])).

cnf(c_1161,plain,
    ( k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)) = k2_relat_1(k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_340,c_710])).

cnf(c_1163,plain,
    ( k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)) = k2_relat_1(sK1) ),
    inference(light_normalisation,[status(thm)],[c_1161,c_542])).

cnf(c_1842,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1163,c_347])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_350,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k2_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_879,plain,
    ( r1_tarski(X0,k3_relat_1(sK1)) = iProver_top
    | r1_tarski(X0,k2_relat_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_716,c_350])).

cnf(c_4041,plain,
    ( r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1842,c_879])).

cnf(c_4045,plain,
    ( r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4041])).

cnf(c_136,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_372,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
    | k3_relat_1(sK1) != X1
    | k3_relat_1(sK0) != X0 ),
    inference(instantiation,[status(thm)],[c_136])).

cnf(c_396,plain,
    ( ~ r1_tarski(X0,k3_relat_1(X1))
    | r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
    | k3_relat_1(sK1) != k3_relat_1(X1)
    | k3_relat_1(sK0) != X0 ),
    inference(instantiation,[status(thm)],[c_372])).

cnf(c_660,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)),k3_relat_1(X0))
    | r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
    | k3_relat_1(sK1) != k3_relat_1(X0)
    | k3_relat_1(sK0) != k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_396])).

cnf(c_852,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)),k3_relat_1(sK1))
    | r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
    | k3_relat_1(sK1) != k3_relat_1(sK1)
    | k3_relat_1(sK0) != k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_660])).

cnf(c_134,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_435,plain,
    ( X0 != X1
    | k3_relat_1(sK0) != X1
    | k3_relat_1(sK0) = X0 ),
    inference(instantiation,[status(thm)],[c_134])).

cnf(c_492,plain,
    ( X0 != k3_relat_1(sK0)
    | k3_relat_1(sK0) = X0
    | k3_relat_1(sK0) != k3_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_435])).

cnf(c_548,plain,
    ( k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)) != k3_relat_1(sK0)
    | k3_relat_1(sK0) = k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0))
    | k3_relat_1(sK0) != k3_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_492])).

cnf(c_133,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_406,plain,
    ( k3_relat_1(sK1) = k3_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_133])).

cnf(c_148,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_133])).

cnf(c_139,plain,
    ( X0 != X1
    | k3_relat_1(X0) = k3_relat_1(X1) ),
    theory(equality)).

cnf(c_145,plain,
    ( k3_relat_1(sK0) = k3_relat_1(sK0)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_139])).

cnf(c_23,plain,
    ( ~ v1_relat_1(sK0)
    | k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)) = k3_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_8,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_41479,c_6252,c_4045,c_852,c_548,c_406,c_148,c_145,c_23,c_8,c_11])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:40:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 11.28/2.04  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.28/2.04  
% 11.28/2.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.28/2.04  
% 11.28/2.04  ------  iProver source info
% 11.28/2.04  
% 11.28/2.04  git: date: 2020-06-30 10:37:57 +0100
% 11.28/2.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.28/2.04  git: non_committed_changes: false
% 11.28/2.04  git: last_make_outside_of_git: false
% 11.28/2.04  
% 11.28/2.04  ------ 
% 11.28/2.04  
% 11.28/2.04  ------ Input Options
% 11.28/2.04  
% 11.28/2.04  --out_options                           all
% 11.28/2.04  --tptp_safe_out                         true
% 11.28/2.04  --problem_path                          ""
% 11.28/2.04  --include_path                          ""
% 11.28/2.04  --clausifier                            res/vclausify_rel
% 11.28/2.04  --clausifier_options                    ""
% 11.28/2.04  --stdin                                 false
% 11.28/2.04  --stats_out                             all
% 11.28/2.04  
% 11.28/2.04  ------ General Options
% 11.28/2.04  
% 11.28/2.04  --fof                                   false
% 11.28/2.04  --time_out_real                         305.
% 11.28/2.04  --time_out_virtual                      -1.
% 11.28/2.04  --symbol_type_check                     false
% 11.28/2.04  --clausify_out                          false
% 11.28/2.04  --sig_cnt_out                           false
% 11.28/2.04  --trig_cnt_out                          false
% 11.28/2.04  --trig_cnt_out_tolerance                1.
% 11.28/2.04  --trig_cnt_out_sk_spl                   false
% 11.28/2.04  --abstr_cl_out                          false
% 11.28/2.04  
% 11.28/2.04  ------ Global Options
% 11.28/2.04  
% 11.28/2.04  --schedule                              default
% 11.28/2.04  --add_important_lit                     false
% 11.28/2.04  --prop_solver_per_cl                    1000
% 11.28/2.04  --min_unsat_core                        false
% 11.28/2.04  --soft_assumptions                      false
% 11.28/2.04  --soft_lemma_size                       3
% 11.28/2.04  --prop_impl_unit_size                   0
% 11.28/2.04  --prop_impl_unit                        []
% 11.28/2.04  --share_sel_clauses                     true
% 11.28/2.04  --reset_solvers                         false
% 11.28/2.04  --bc_imp_inh                            [conj_cone]
% 11.28/2.04  --conj_cone_tolerance                   3.
% 11.28/2.04  --extra_neg_conj                        none
% 11.28/2.04  --large_theory_mode                     true
% 11.28/2.04  --prolific_symb_bound                   200
% 11.28/2.04  --lt_threshold                          2000
% 11.28/2.04  --clause_weak_htbl                      true
% 11.28/2.04  --gc_record_bc_elim                     false
% 11.28/2.04  
% 11.28/2.04  ------ Preprocessing Options
% 11.28/2.04  
% 11.28/2.04  --preprocessing_flag                    true
% 11.28/2.04  --time_out_prep_mult                    0.1
% 11.28/2.04  --splitting_mode                        input
% 11.28/2.04  --splitting_grd                         true
% 11.28/2.04  --splitting_cvd                         false
% 11.28/2.04  --splitting_cvd_svl                     false
% 11.28/2.04  --splitting_nvd                         32
% 11.28/2.04  --sub_typing                            true
% 11.28/2.04  --prep_gs_sim                           true
% 11.28/2.04  --prep_unflatten                        true
% 11.28/2.04  --prep_res_sim                          true
% 11.28/2.04  --prep_upred                            true
% 11.28/2.04  --prep_sem_filter                       exhaustive
% 11.28/2.04  --prep_sem_filter_out                   false
% 11.28/2.04  --pred_elim                             true
% 11.28/2.04  --res_sim_input                         true
% 11.28/2.04  --eq_ax_congr_red                       true
% 11.28/2.04  --pure_diseq_elim                       true
% 11.28/2.04  --brand_transform                       false
% 11.28/2.04  --non_eq_to_eq                          false
% 11.28/2.04  --prep_def_merge                        true
% 11.28/2.04  --prep_def_merge_prop_impl              false
% 11.28/2.04  --prep_def_merge_mbd                    true
% 11.28/2.04  --prep_def_merge_tr_red                 false
% 11.28/2.04  --prep_def_merge_tr_cl                  false
% 11.28/2.04  --smt_preprocessing                     true
% 11.28/2.04  --smt_ac_axioms                         fast
% 11.28/2.04  --preprocessed_out                      false
% 11.28/2.04  --preprocessed_stats                    false
% 11.28/2.04  
% 11.28/2.04  ------ Abstraction refinement Options
% 11.28/2.04  
% 11.28/2.04  --abstr_ref                             []
% 11.28/2.04  --abstr_ref_prep                        false
% 11.28/2.04  --abstr_ref_until_sat                   false
% 11.28/2.04  --abstr_ref_sig_restrict                funpre
% 11.28/2.04  --abstr_ref_af_restrict_to_split_sk     false
% 11.28/2.04  --abstr_ref_under                       []
% 11.28/2.04  
% 11.28/2.04  ------ SAT Options
% 11.28/2.04  
% 11.28/2.04  --sat_mode                              false
% 11.28/2.04  --sat_fm_restart_options                ""
% 11.28/2.04  --sat_gr_def                            false
% 11.28/2.04  --sat_epr_types                         true
% 11.28/2.04  --sat_non_cyclic_types                  false
% 11.28/2.04  --sat_finite_models                     false
% 11.28/2.04  --sat_fm_lemmas                         false
% 11.28/2.04  --sat_fm_prep                           false
% 11.28/2.04  --sat_fm_uc_incr                        true
% 11.28/2.04  --sat_out_model                         small
% 11.28/2.04  --sat_out_clauses                       false
% 11.28/2.04  
% 11.28/2.04  ------ QBF Options
% 11.28/2.04  
% 11.28/2.04  --qbf_mode                              false
% 11.28/2.04  --qbf_elim_univ                         false
% 11.28/2.04  --qbf_dom_inst                          none
% 11.28/2.04  --qbf_dom_pre_inst                      false
% 11.28/2.04  --qbf_sk_in                             false
% 11.28/2.04  --qbf_pred_elim                         true
% 11.28/2.04  --qbf_split                             512
% 11.28/2.04  
% 11.28/2.04  ------ BMC1 Options
% 11.28/2.04  
% 11.28/2.04  --bmc1_incremental                      false
% 11.28/2.04  --bmc1_axioms                           reachable_all
% 11.28/2.04  --bmc1_min_bound                        0
% 11.28/2.04  --bmc1_max_bound                        -1
% 11.28/2.04  --bmc1_max_bound_default                -1
% 11.28/2.04  --bmc1_symbol_reachability              true
% 11.28/2.04  --bmc1_property_lemmas                  false
% 11.28/2.04  --bmc1_k_induction                      false
% 11.28/2.04  --bmc1_non_equiv_states                 false
% 11.28/2.04  --bmc1_deadlock                         false
% 11.28/2.04  --bmc1_ucm                              false
% 11.28/2.04  --bmc1_add_unsat_core                   none
% 11.28/2.04  --bmc1_unsat_core_children              false
% 11.28/2.04  --bmc1_unsat_core_extrapolate_axioms    false
% 11.28/2.04  --bmc1_out_stat                         full
% 11.28/2.04  --bmc1_ground_init                      false
% 11.28/2.04  --bmc1_pre_inst_next_state              false
% 11.28/2.04  --bmc1_pre_inst_state                   false
% 11.28/2.04  --bmc1_pre_inst_reach_state             false
% 11.28/2.04  --bmc1_out_unsat_core                   false
% 11.28/2.04  --bmc1_aig_witness_out                  false
% 11.28/2.04  --bmc1_verbose                          false
% 11.28/2.04  --bmc1_dump_clauses_tptp                false
% 11.28/2.04  --bmc1_dump_unsat_core_tptp             false
% 11.28/2.04  --bmc1_dump_file                        -
% 11.28/2.04  --bmc1_ucm_expand_uc_limit              128
% 11.28/2.04  --bmc1_ucm_n_expand_iterations          6
% 11.28/2.04  --bmc1_ucm_extend_mode                  1
% 11.28/2.04  --bmc1_ucm_init_mode                    2
% 11.28/2.04  --bmc1_ucm_cone_mode                    none
% 11.28/2.04  --bmc1_ucm_reduced_relation_type        0
% 11.28/2.04  --bmc1_ucm_relax_model                  4
% 11.28/2.04  --bmc1_ucm_full_tr_after_sat            true
% 11.28/2.04  --bmc1_ucm_expand_neg_assumptions       false
% 11.28/2.04  --bmc1_ucm_layered_model                none
% 11.28/2.04  --bmc1_ucm_max_lemma_size               10
% 11.28/2.04  
% 11.28/2.04  ------ AIG Options
% 11.28/2.04  
% 11.28/2.04  --aig_mode                              false
% 11.28/2.04  
% 11.28/2.04  ------ Instantiation Options
% 11.28/2.04  
% 11.28/2.04  --instantiation_flag                    true
% 11.28/2.04  --inst_sos_flag                         true
% 11.28/2.04  --inst_sos_phase                        true
% 11.28/2.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.28/2.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.28/2.04  --inst_lit_sel_side                     num_symb
% 11.28/2.04  --inst_solver_per_active                1400
% 11.28/2.04  --inst_solver_calls_frac                1.
% 11.28/2.04  --inst_passive_queue_type               priority_queues
% 11.28/2.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.28/2.04  --inst_passive_queues_freq              [25;2]
% 11.28/2.04  --inst_dismatching                      true
% 11.28/2.04  --inst_eager_unprocessed_to_passive     true
% 11.28/2.04  --inst_prop_sim_given                   true
% 11.28/2.04  --inst_prop_sim_new                     false
% 11.28/2.04  --inst_subs_new                         false
% 11.28/2.04  --inst_eq_res_simp                      false
% 11.28/2.04  --inst_subs_given                       false
% 11.28/2.04  --inst_orphan_elimination               true
% 11.28/2.04  --inst_learning_loop_flag               true
% 11.28/2.04  --inst_learning_start                   3000
% 11.28/2.04  --inst_learning_factor                  2
% 11.28/2.04  --inst_start_prop_sim_after_learn       3
% 11.28/2.04  --inst_sel_renew                        solver
% 11.28/2.04  --inst_lit_activity_flag                true
% 11.28/2.04  --inst_restr_to_given                   false
% 11.28/2.04  --inst_activity_threshold               500
% 11.28/2.04  --inst_out_proof                        true
% 11.28/2.04  
% 11.28/2.04  ------ Resolution Options
% 11.28/2.04  
% 11.28/2.04  --resolution_flag                       true
% 11.28/2.04  --res_lit_sel                           adaptive
% 11.28/2.04  --res_lit_sel_side                      none
% 11.28/2.04  --res_ordering                          kbo
% 11.28/2.04  --res_to_prop_solver                    active
% 11.28/2.04  --res_prop_simpl_new                    false
% 11.28/2.04  --res_prop_simpl_given                  true
% 11.28/2.04  --res_passive_queue_type                priority_queues
% 11.28/2.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.28/2.04  --res_passive_queues_freq               [15;5]
% 11.28/2.04  --res_forward_subs                      full
% 11.28/2.04  --res_backward_subs                     full
% 11.28/2.04  --res_forward_subs_resolution           true
% 11.28/2.04  --res_backward_subs_resolution          true
% 11.28/2.04  --res_orphan_elimination                true
% 11.28/2.04  --res_time_limit                        2.
% 11.28/2.04  --res_out_proof                         true
% 11.28/2.04  
% 11.28/2.04  ------ Superposition Options
% 11.28/2.04  
% 11.28/2.04  --superposition_flag                    true
% 11.28/2.04  --sup_passive_queue_type                priority_queues
% 11.28/2.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.28/2.04  --sup_passive_queues_freq               [8;1;4]
% 11.28/2.04  --demod_completeness_check              fast
% 11.28/2.04  --demod_use_ground                      true
% 11.28/2.04  --sup_to_prop_solver                    passive
% 11.28/2.04  --sup_prop_simpl_new                    true
% 11.28/2.04  --sup_prop_simpl_given                  true
% 11.28/2.04  --sup_fun_splitting                     true
% 11.28/2.04  --sup_smt_interval                      50000
% 11.28/2.04  
% 11.28/2.04  ------ Superposition Simplification Setup
% 11.28/2.04  
% 11.28/2.04  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.28/2.04  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.28/2.04  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.28/2.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.28/2.04  --sup_full_triv                         [TrivRules;PropSubs]
% 11.28/2.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.28/2.04  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.28/2.04  --sup_immed_triv                        [TrivRules]
% 11.28/2.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.28/2.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.28/2.04  --sup_immed_bw_main                     []
% 11.28/2.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.28/2.04  --sup_input_triv                        [Unflattening;TrivRules]
% 11.28/2.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.28/2.04  --sup_input_bw                          []
% 11.28/2.04  
% 11.28/2.04  ------ Combination Options
% 11.28/2.04  
% 11.28/2.04  --comb_res_mult                         3
% 11.28/2.04  --comb_sup_mult                         2
% 11.28/2.04  --comb_inst_mult                        10
% 11.28/2.04  
% 11.28/2.04  ------ Debug Options
% 11.28/2.04  
% 11.28/2.04  --dbg_backtrace                         false
% 11.28/2.04  --dbg_dump_prop_clauses                 false
% 11.28/2.04  --dbg_dump_prop_clauses_file            -
% 11.28/2.04  --dbg_out_stat                          false
% 11.28/2.04  ------ Parsing...
% 11.28/2.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.28/2.04  
% 11.28/2.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 11.28/2.04  
% 11.28/2.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.28/2.04  
% 11.28/2.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.28/2.04  ------ Proving...
% 11.28/2.04  ------ Problem Properties 
% 11.28/2.04  
% 11.28/2.04  
% 11.28/2.04  clauses                                 12
% 11.28/2.04  conjectures                             4
% 11.28/2.04  EPR                                     4
% 11.28/2.04  Horn                                    12
% 11.28/2.04  unary                                   5
% 11.28/2.04  binary                                  3
% 11.28/2.04  lits                                    23
% 11.28/2.04  lits eq                                 4
% 11.28/2.04  fd_pure                                 0
% 11.28/2.04  fd_pseudo                               0
% 11.28/2.04  fd_cond                                 0
% 11.28/2.04  fd_pseudo_cond                          0
% 11.28/2.04  AC symbols                              0
% 11.28/2.04  
% 11.28/2.04  ------ Schedule dynamic 5 is on 
% 11.28/2.04  
% 11.28/2.04  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.28/2.04  
% 11.28/2.04  
% 11.28/2.04  ------ 
% 11.28/2.04  Current options:
% 11.28/2.04  ------ 
% 11.28/2.04  
% 11.28/2.04  ------ Input Options
% 11.28/2.04  
% 11.28/2.04  --out_options                           all
% 11.28/2.04  --tptp_safe_out                         true
% 11.28/2.04  --problem_path                          ""
% 11.28/2.04  --include_path                          ""
% 11.28/2.04  --clausifier                            res/vclausify_rel
% 11.28/2.04  --clausifier_options                    ""
% 11.28/2.04  --stdin                                 false
% 11.28/2.04  --stats_out                             all
% 11.28/2.04  
% 11.28/2.04  ------ General Options
% 11.28/2.04  
% 11.28/2.04  --fof                                   false
% 11.28/2.04  --time_out_real                         305.
% 11.28/2.04  --time_out_virtual                      -1.
% 11.28/2.04  --symbol_type_check                     false
% 11.28/2.04  --clausify_out                          false
% 11.28/2.04  --sig_cnt_out                           false
% 11.28/2.04  --trig_cnt_out                          false
% 11.28/2.04  --trig_cnt_out_tolerance                1.
% 11.28/2.04  --trig_cnt_out_sk_spl                   false
% 11.28/2.04  --abstr_cl_out                          false
% 11.28/2.04  
% 11.28/2.04  ------ Global Options
% 11.28/2.04  
% 11.28/2.04  --schedule                              default
% 11.28/2.04  --add_important_lit                     false
% 11.28/2.04  --prop_solver_per_cl                    1000
% 11.28/2.04  --min_unsat_core                        false
% 11.28/2.04  --soft_assumptions                      false
% 11.28/2.04  --soft_lemma_size                       3
% 11.28/2.04  --prop_impl_unit_size                   0
% 11.28/2.04  --prop_impl_unit                        []
% 11.28/2.04  --share_sel_clauses                     true
% 11.28/2.04  --reset_solvers                         false
% 11.28/2.04  --bc_imp_inh                            [conj_cone]
% 11.28/2.04  --conj_cone_tolerance                   3.
% 11.28/2.04  --extra_neg_conj                        none
% 11.28/2.04  --large_theory_mode                     true
% 11.28/2.04  --prolific_symb_bound                   200
% 11.28/2.04  --lt_threshold                          2000
% 11.28/2.04  --clause_weak_htbl                      true
% 11.28/2.04  --gc_record_bc_elim                     false
% 11.28/2.04  
% 11.28/2.04  ------ Preprocessing Options
% 11.28/2.04  
% 11.28/2.04  --preprocessing_flag                    true
% 11.28/2.04  --time_out_prep_mult                    0.1
% 11.28/2.04  --splitting_mode                        input
% 11.28/2.04  --splitting_grd                         true
% 11.28/2.04  --splitting_cvd                         false
% 11.28/2.04  --splitting_cvd_svl                     false
% 11.28/2.04  --splitting_nvd                         32
% 11.28/2.04  --sub_typing                            true
% 11.28/2.04  --prep_gs_sim                           true
% 11.28/2.04  --prep_unflatten                        true
% 11.28/2.04  --prep_res_sim                          true
% 11.28/2.04  --prep_upred                            true
% 11.28/2.04  --prep_sem_filter                       exhaustive
% 11.28/2.04  --prep_sem_filter_out                   false
% 11.28/2.04  --pred_elim                             true
% 11.28/2.04  --res_sim_input                         true
% 11.28/2.04  --eq_ax_congr_red                       true
% 11.28/2.04  --pure_diseq_elim                       true
% 11.28/2.04  --brand_transform                       false
% 11.28/2.04  --non_eq_to_eq                          false
% 11.28/2.04  --prep_def_merge                        true
% 11.28/2.04  --prep_def_merge_prop_impl              false
% 11.28/2.04  --prep_def_merge_mbd                    true
% 11.28/2.04  --prep_def_merge_tr_red                 false
% 11.28/2.04  --prep_def_merge_tr_cl                  false
% 11.28/2.04  --smt_preprocessing                     true
% 11.28/2.04  --smt_ac_axioms                         fast
% 11.28/2.04  --preprocessed_out                      false
% 11.28/2.04  --preprocessed_stats                    false
% 11.28/2.04  
% 11.28/2.04  ------ Abstraction refinement Options
% 11.28/2.04  
% 11.28/2.04  --abstr_ref                             []
% 11.28/2.04  --abstr_ref_prep                        false
% 11.28/2.04  --abstr_ref_until_sat                   false
% 11.28/2.04  --abstr_ref_sig_restrict                funpre
% 11.28/2.04  --abstr_ref_af_restrict_to_split_sk     false
% 11.28/2.04  --abstr_ref_under                       []
% 11.28/2.04  
% 11.28/2.04  ------ SAT Options
% 11.28/2.04  
% 11.28/2.04  --sat_mode                              false
% 11.28/2.04  --sat_fm_restart_options                ""
% 11.28/2.04  --sat_gr_def                            false
% 11.28/2.04  --sat_epr_types                         true
% 11.28/2.04  --sat_non_cyclic_types                  false
% 11.28/2.04  --sat_finite_models                     false
% 11.28/2.04  --sat_fm_lemmas                         false
% 11.28/2.04  --sat_fm_prep                           false
% 11.28/2.04  --sat_fm_uc_incr                        true
% 11.28/2.04  --sat_out_model                         small
% 11.28/2.04  --sat_out_clauses                       false
% 11.28/2.04  
% 11.28/2.04  ------ QBF Options
% 11.28/2.04  
% 11.28/2.04  --qbf_mode                              false
% 11.28/2.04  --qbf_elim_univ                         false
% 11.28/2.04  --qbf_dom_inst                          none
% 11.28/2.04  --qbf_dom_pre_inst                      false
% 11.28/2.04  --qbf_sk_in                             false
% 11.28/2.04  --qbf_pred_elim                         true
% 11.28/2.04  --qbf_split                             512
% 11.28/2.04  
% 11.28/2.04  ------ BMC1 Options
% 11.28/2.04  
% 11.28/2.04  --bmc1_incremental                      false
% 11.28/2.04  --bmc1_axioms                           reachable_all
% 11.28/2.04  --bmc1_min_bound                        0
% 11.28/2.04  --bmc1_max_bound                        -1
% 11.28/2.04  --bmc1_max_bound_default                -1
% 11.28/2.04  --bmc1_symbol_reachability              true
% 11.28/2.04  --bmc1_property_lemmas                  false
% 11.28/2.04  --bmc1_k_induction                      false
% 11.28/2.04  --bmc1_non_equiv_states                 false
% 11.28/2.04  --bmc1_deadlock                         false
% 11.28/2.04  --bmc1_ucm                              false
% 11.28/2.04  --bmc1_add_unsat_core                   none
% 11.28/2.04  --bmc1_unsat_core_children              false
% 11.28/2.04  --bmc1_unsat_core_extrapolate_axioms    false
% 11.28/2.04  --bmc1_out_stat                         full
% 11.28/2.04  --bmc1_ground_init                      false
% 11.28/2.04  --bmc1_pre_inst_next_state              false
% 11.28/2.04  --bmc1_pre_inst_state                   false
% 11.28/2.04  --bmc1_pre_inst_reach_state             false
% 11.28/2.04  --bmc1_out_unsat_core                   false
% 11.28/2.04  --bmc1_aig_witness_out                  false
% 11.28/2.04  --bmc1_verbose                          false
% 11.28/2.04  --bmc1_dump_clauses_tptp                false
% 11.28/2.04  --bmc1_dump_unsat_core_tptp             false
% 11.28/2.04  --bmc1_dump_file                        -
% 11.28/2.04  --bmc1_ucm_expand_uc_limit              128
% 11.28/2.04  --bmc1_ucm_n_expand_iterations          6
% 11.28/2.04  --bmc1_ucm_extend_mode                  1
% 11.28/2.04  --bmc1_ucm_init_mode                    2
% 11.28/2.04  --bmc1_ucm_cone_mode                    none
% 11.28/2.04  --bmc1_ucm_reduced_relation_type        0
% 11.28/2.04  --bmc1_ucm_relax_model                  4
% 11.28/2.04  --bmc1_ucm_full_tr_after_sat            true
% 11.28/2.04  --bmc1_ucm_expand_neg_assumptions       false
% 11.28/2.04  --bmc1_ucm_layered_model                none
% 11.28/2.04  --bmc1_ucm_max_lemma_size               10
% 11.28/2.04  
% 11.28/2.04  ------ AIG Options
% 11.28/2.04  
% 11.28/2.04  --aig_mode                              false
% 11.28/2.04  
% 11.28/2.04  ------ Instantiation Options
% 11.28/2.04  
% 11.28/2.04  --instantiation_flag                    true
% 11.28/2.04  --inst_sos_flag                         true
% 11.28/2.04  --inst_sos_phase                        true
% 11.28/2.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.28/2.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.28/2.04  --inst_lit_sel_side                     none
% 11.28/2.04  --inst_solver_per_active                1400
% 11.28/2.04  --inst_solver_calls_frac                1.
% 11.28/2.04  --inst_passive_queue_type               priority_queues
% 11.28/2.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.28/2.04  --inst_passive_queues_freq              [25;2]
% 11.28/2.04  --inst_dismatching                      true
% 11.28/2.04  --inst_eager_unprocessed_to_passive     true
% 11.28/2.04  --inst_prop_sim_given                   true
% 11.28/2.04  --inst_prop_sim_new                     false
% 11.28/2.04  --inst_subs_new                         false
% 11.28/2.04  --inst_eq_res_simp                      false
% 11.28/2.04  --inst_subs_given                       false
% 11.28/2.04  --inst_orphan_elimination               true
% 11.28/2.04  --inst_learning_loop_flag               true
% 11.28/2.04  --inst_learning_start                   3000
% 11.28/2.04  --inst_learning_factor                  2
% 11.28/2.04  --inst_start_prop_sim_after_learn       3
% 11.28/2.04  --inst_sel_renew                        solver
% 11.28/2.04  --inst_lit_activity_flag                true
% 11.28/2.04  --inst_restr_to_given                   false
% 11.28/2.04  --inst_activity_threshold               500
% 11.28/2.04  --inst_out_proof                        true
% 11.28/2.04  
% 11.28/2.04  ------ Resolution Options
% 11.28/2.04  
% 11.28/2.04  --resolution_flag                       false
% 11.28/2.04  --res_lit_sel                           adaptive
% 11.28/2.04  --res_lit_sel_side                      none
% 11.28/2.04  --res_ordering                          kbo
% 11.28/2.04  --res_to_prop_solver                    active
% 11.28/2.04  --res_prop_simpl_new                    false
% 11.28/2.04  --res_prop_simpl_given                  true
% 11.28/2.04  --res_passive_queue_type                priority_queues
% 11.28/2.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.28/2.04  --res_passive_queues_freq               [15;5]
% 11.28/2.04  --res_forward_subs                      full
% 11.28/2.04  --res_backward_subs                     full
% 11.28/2.04  --res_forward_subs_resolution           true
% 11.28/2.04  --res_backward_subs_resolution          true
% 11.28/2.04  --res_orphan_elimination                true
% 11.28/2.04  --res_time_limit                        2.
% 11.28/2.04  --res_out_proof                         true
% 11.28/2.04  
% 11.28/2.04  ------ Superposition Options
% 11.28/2.04  
% 11.28/2.04  --superposition_flag                    true
% 11.28/2.04  --sup_passive_queue_type                priority_queues
% 11.28/2.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.28/2.04  --sup_passive_queues_freq               [8;1;4]
% 11.28/2.04  --demod_completeness_check              fast
% 11.28/2.04  --demod_use_ground                      true
% 11.28/2.04  --sup_to_prop_solver                    passive
% 11.28/2.04  --sup_prop_simpl_new                    true
% 11.28/2.04  --sup_prop_simpl_given                  true
% 11.28/2.04  --sup_fun_splitting                     true
% 11.28/2.04  --sup_smt_interval                      50000
% 11.28/2.04  
% 11.28/2.04  ------ Superposition Simplification Setup
% 11.28/2.04  
% 11.28/2.04  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.28/2.04  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.28/2.04  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.28/2.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.28/2.04  --sup_full_triv                         [TrivRules;PropSubs]
% 11.28/2.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.28/2.04  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.28/2.04  --sup_immed_triv                        [TrivRules]
% 11.28/2.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.28/2.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.28/2.04  --sup_immed_bw_main                     []
% 11.28/2.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.28/2.04  --sup_input_triv                        [Unflattening;TrivRules]
% 11.28/2.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.28/2.04  --sup_input_bw                          []
% 11.28/2.04  
% 11.28/2.04  ------ Combination Options
% 11.28/2.04  
% 11.28/2.04  --comb_res_mult                         3
% 11.28/2.04  --comb_sup_mult                         2
% 11.28/2.04  --comb_inst_mult                        10
% 11.28/2.04  
% 11.28/2.04  ------ Debug Options
% 11.28/2.04  
% 11.28/2.04  --dbg_backtrace                         false
% 11.28/2.04  --dbg_dump_prop_clauses                 false
% 11.28/2.04  --dbg_dump_prop_clauses_file            -
% 11.28/2.04  --dbg_out_stat                          false
% 11.28/2.04  
% 11.28/2.04  
% 11.28/2.04  
% 11.28/2.04  
% 11.28/2.04  ------ Proving...
% 11.28/2.04  
% 11.28/2.04  
% 11.28/2.04  % SZS status Theorem for theBenchmark.p
% 11.28/2.04  
% 11.28/2.04  % SZS output start CNFRefutation for theBenchmark.p
% 11.28/2.04  
% 11.28/2.04  fof(f5,axiom,(
% 11.28/2.04    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 11.28/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.28/2.04  
% 11.28/2.04  fof(f15,plain,(
% 11.28/2.04    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 11.28/2.04    inference(ennf_transformation,[],[f5])).
% 11.28/2.04  
% 11.28/2.04  fof(f16,plain,(
% 11.28/2.04    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 11.28/2.04    inference(flattening,[],[f15])).
% 11.28/2.04  
% 11.28/2.04  fof(f29,plain,(
% 11.28/2.04    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 11.28/2.04    inference(cnf_transformation,[],[f16])).
% 11.28/2.04  
% 11.28/2.04  fof(f9,conjecture,(
% 11.28/2.04    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 11.28/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.28/2.04  
% 11.28/2.04  fof(f10,negated_conjecture,(
% 11.28/2.04    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 11.28/2.04    inference(negated_conjecture,[],[f9])).
% 11.28/2.04  
% 11.28/2.04  fof(f20,plain,(
% 11.28/2.04    ? [X0] : (? [X1] : ((~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 11.28/2.04    inference(ennf_transformation,[],[f10])).
% 11.28/2.04  
% 11.28/2.04  fof(f21,plain,(
% 11.28/2.04    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 11.28/2.04    inference(flattening,[],[f20])).
% 11.28/2.04  
% 11.28/2.04  fof(f23,plain,(
% 11.28/2.04    ( ! [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(X0),k3_relat_1(sK1)) & r1_tarski(X0,sK1) & v1_relat_1(sK1))) )),
% 11.28/2.04    introduced(choice_axiom,[])).
% 11.28/2.04  
% 11.28/2.04  fof(f22,plain,(
% 11.28/2.04    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(sK0),k3_relat_1(X1)) & r1_tarski(sK0,X1) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 11.28/2.04    introduced(choice_axiom,[])).
% 11.28/2.04  
% 11.28/2.04  fof(f24,plain,(
% 11.28/2.04    (~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 11.28/2.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f23,f22])).
% 11.28/2.04  
% 11.28/2.04  fof(f34,plain,(
% 11.28/2.04    v1_relat_1(sK1)),
% 11.28/2.04    inference(cnf_transformation,[],[f24])).
% 11.28/2.04  
% 11.28/2.04  fof(f6,axiom,(
% 11.28/2.04    ! [X0] : (v1_relat_1(X0) => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0))),
% 11.28/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.28/2.04  
% 11.28/2.04  fof(f17,plain,(
% 11.28/2.04    ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0))),
% 11.28/2.04    inference(ennf_transformation,[],[f6])).
% 11.28/2.04  
% 11.28/2.04  fof(f30,plain,(
% 11.28/2.04    ( ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 11.28/2.04    inference(cnf_transformation,[],[f17])).
% 11.28/2.04  
% 11.28/2.04  fof(f4,axiom,(
% 11.28/2.04    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 11.28/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.28/2.04  
% 11.28/2.04  fof(f28,plain,(
% 11.28/2.04    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 11.28/2.04    inference(cnf_transformation,[],[f4])).
% 11.28/2.04  
% 11.28/2.04  fof(f33,plain,(
% 11.28/2.04    v1_relat_1(sK0)),
% 11.28/2.04    inference(cnf_transformation,[],[f24])).
% 11.28/2.04  
% 11.28/2.04  fof(f7,axiom,(
% 11.28/2.04    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1))))),
% 11.28/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.28/2.04  
% 11.28/2.04  fof(f18,plain,(
% 11.28/2.04    ! [X0] : (! [X1] : (k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 11.28/2.04    inference(ennf_transformation,[],[f7])).
% 11.28/2.04  
% 11.28/2.04  fof(f31,plain,(
% 11.28/2.04    ( ! [X0,X1] : (k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 11.28/2.04    inference(cnf_transformation,[],[f18])).
% 11.28/2.04  
% 11.28/2.04  fof(f35,plain,(
% 11.28/2.04    r1_tarski(sK0,sK1)),
% 11.28/2.04    inference(cnf_transformation,[],[f24])).
% 11.28/2.04  
% 11.28/2.04  fof(f2,axiom,(
% 11.28/2.04    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 11.28/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.28/2.04  
% 11.28/2.04  fof(f12,plain,(
% 11.28/2.04    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 11.28/2.04    inference(ennf_transformation,[],[f2])).
% 11.28/2.04  
% 11.28/2.04  fof(f26,plain,(
% 11.28/2.04    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 11.28/2.04    inference(cnf_transformation,[],[f12])).
% 11.28/2.04  
% 11.28/2.04  fof(f3,axiom,(
% 11.28/2.04    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 11.28/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.28/2.04  
% 11.28/2.04  fof(f13,plain,(
% 11.28/2.04    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 11.28/2.04    inference(ennf_transformation,[],[f3])).
% 11.28/2.04  
% 11.28/2.04  fof(f14,plain,(
% 11.28/2.04    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 11.28/2.04    inference(flattening,[],[f13])).
% 11.28/2.04  
% 11.28/2.04  fof(f27,plain,(
% 11.28/2.04    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 11.28/2.04    inference(cnf_transformation,[],[f14])).
% 11.28/2.04  
% 11.28/2.04  fof(f8,axiom,(
% 11.28/2.04    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1))))),
% 11.28/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.28/2.04  
% 11.28/2.04  fof(f19,plain,(
% 11.28/2.04    ! [X0] : (! [X1] : (k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 11.28/2.04    inference(ennf_transformation,[],[f8])).
% 11.28/2.04  
% 11.28/2.04  fof(f32,plain,(
% 11.28/2.04    ( ! [X0,X1] : (k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 11.28/2.04    inference(cnf_transformation,[],[f19])).
% 11.28/2.04  
% 11.28/2.04  fof(f1,axiom,(
% 11.28/2.04    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 11.28/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.28/2.04  
% 11.28/2.04  fof(f11,plain,(
% 11.28/2.04    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 11.28/2.04    inference(ennf_transformation,[],[f1])).
% 11.28/2.04  
% 11.28/2.04  fof(f25,plain,(
% 11.28/2.04    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 11.28/2.04    inference(cnf_transformation,[],[f11])).
% 11.28/2.04  
% 11.28/2.04  fof(f36,plain,(
% 11.28/2.04    ~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))),
% 11.28/2.04    inference(cnf_transformation,[],[f24])).
% 11.28/2.04  
% 11.28/2.04  cnf(c_4,plain,
% 11.28/2.04      ( ~ r1_tarski(X0,X1)
% 11.28/2.04      | ~ r1_tarski(X2,X1)
% 11.28/2.04      | r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 11.28/2.04      inference(cnf_transformation,[],[f29]) ).
% 11.28/2.04  
% 11.28/2.04  cnf(c_1124,plain,
% 11.28/2.04      ( r1_tarski(k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)),X0)
% 11.28/2.04      | ~ r1_tarski(k2_relat_1(sK0),X0)
% 11.28/2.04      | ~ r1_tarski(k1_relat_1(sK0),X0) ),
% 11.28/2.04      inference(instantiation,[status(thm)],[c_4]) ).
% 11.28/2.04  
% 11.28/2.04  cnf(c_41479,plain,
% 11.28/2.04      ( r1_tarski(k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)),k3_relat_1(sK1))
% 11.28/2.04      | ~ r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1))
% 11.28/2.04      | ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
% 11.28/2.04      inference(instantiation,[status(thm)],[c_1124]) ).
% 11.28/2.04  
% 11.28/2.04  cnf(c_10,negated_conjecture,
% 11.28/2.04      ( v1_relat_1(sK1) ),
% 11.28/2.04      inference(cnf_transformation,[],[f34]) ).
% 11.28/2.04  
% 11.28/2.04  cnf(c_340,plain,
% 11.28/2.04      ( v1_relat_1(sK1) = iProver_top ),
% 11.28/2.04      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.28/2.04  
% 11.28/2.04  cnf(c_5,plain,
% 11.28/2.04      ( ~ v1_relat_1(X0)
% 11.28/2.04      | k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ),
% 11.28/2.04      inference(cnf_transformation,[],[f30]) ).
% 11.28/2.04  
% 11.28/2.04  cnf(c_345,plain,
% 11.28/2.04      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
% 11.28/2.04      | v1_relat_1(X0) != iProver_top ),
% 11.28/2.04      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.28/2.04  
% 11.28/2.04  cnf(c_716,plain,
% 11.28/2.04      ( k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1)) = k3_relat_1(sK1) ),
% 11.28/2.04      inference(superposition,[status(thm)],[c_340,c_345]) ).
% 11.28/2.04  
% 11.28/2.04  cnf(c_3,plain,
% 11.28/2.04      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 11.28/2.04      inference(cnf_transformation,[],[f28]) ).
% 11.28/2.04  
% 11.28/2.04  cnf(c_347,plain,
% 11.28/2.04      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 11.28/2.04      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.28/2.04  
% 11.28/2.04  cnf(c_882,plain,
% 11.28/2.04      ( r1_tarski(k1_relat_1(sK1),k3_relat_1(sK1)) = iProver_top ),
% 11.28/2.04      inference(superposition,[status(thm)],[c_716,c_347]) ).
% 11.28/2.04  
% 11.28/2.04  cnf(c_11,negated_conjecture,
% 11.28/2.04      ( v1_relat_1(sK0) ),
% 11.28/2.04      inference(cnf_transformation,[],[f33]) ).
% 11.28/2.04  
% 11.28/2.04  cnf(c_339,plain,
% 11.28/2.04      ( v1_relat_1(sK0) = iProver_top ),
% 11.28/2.04      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.28/2.04  
% 11.28/2.04  cnf(c_6,plain,
% 11.28/2.04      ( ~ v1_relat_1(X0)
% 11.28/2.04      | ~ v1_relat_1(X1)
% 11.28/2.04      | k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) ),
% 11.28/2.04      inference(cnf_transformation,[],[f31]) ).
% 11.28/2.04  
% 11.28/2.04  cnf(c_344,plain,
% 11.28/2.04      ( k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1))
% 11.28/2.04      | v1_relat_1(X0) != iProver_top
% 11.28/2.04      | v1_relat_1(X1) != iProver_top ),
% 11.28/2.04      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.28/2.04  
% 11.28/2.04  cnf(c_1268,plain,
% 11.28/2.04      ( k2_xboole_0(k1_relat_1(sK0),k1_relat_1(X0)) = k1_relat_1(k2_xboole_0(sK0,X0))
% 11.28/2.04      | v1_relat_1(X0) != iProver_top ),
% 11.28/2.04      inference(superposition,[status(thm)],[c_339,c_344]) ).
% 11.28/2.04  
% 11.28/2.04  cnf(c_1689,plain,
% 11.28/2.04      ( k2_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) = k1_relat_1(k2_xboole_0(sK0,sK1)) ),
% 11.28/2.04      inference(superposition,[status(thm)],[c_340,c_1268]) ).
% 11.28/2.04  
% 11.28/2.04  cnf(c_9,negated_conjecture,
% 11.28/2.04      ( r1_tarski(sK0,sK1) ),
% 11.28/2.04      inference(cnf_transformation,[],[f35]) ).
% 11.28/2.04  
% 11.28/2.04  cnf(c_341,plain,
% 11.28/2.04      ( r1_tarski(sK0,sK1) = iProver_top ),
% 11.28/2.04      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.28/2.04  
% 11.28/2.04  cnf(c_1,plain,
% 11.28/2.04      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 11.28/2.04      inference(cnf_transformation,[],[f26]) ).
% 11.28/2.04  
% 11.28/2.04  cnf(c_349,plain,
% 11.28/2.04      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 11.28/2.04      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 11.28/2.04  
% 11.28/2.04  cnf(c_542,plain,
% 11.28/2.04      ( k2_xboole_0(sK0,sK1) = sK1 ),
% 11.28/2.04      inference(superposition,[status(thm)],[c_341,c_349]) ).
% 11.28/2.04  
% 11.28/2.04  cnf(c_1691,plain,
% 11.28/2.04      ( k2_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) = k1_relat_1(sK1) ),
% 11.28/2.04      inference(light_normalisation,[status(thm)],[c_1689,c_542]) ).
% 11.28/2.04  
% 11.28/2.04  cnf(c_2147,plain,
% 11.28/2.04      ( r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1)) = iProver_top ),
% 11.28/2.04      inference(superposition,[status(thm)],[c_1691,c_347]) ).
% 11.28/2.04  
% 11.28/2.04  cnf(c_2,plain,
% 11.28/2.04      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 11.28/2.04      inference(cnf_transformation,[],[f27]) ).
% 11.28/2.04  
% 11.28/2.04  cnf(c_348,plain,
% 11.28/2.04      ( r1_tarski(X0,X1) != iProver_top
% 11.28/2.04      | r1_tarski(X1,X2) != iProver_top
% 11.28/2.04      | r1_tarski(X0,X2) = iProver_top ),
% 11.28/2.04      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 11.28/2.04  
% 11.28/2.04  cnf(c_2616,plain,
% 11.28/2.04      ( r1_tarski(k1_relat_1(sK1),X0) != iProver_top
% 11.28/2.04      | r1_tarski(k1_relat_1(sK0),X0) = iProver_top ),
% 11.28/2.04      inference(superposition,[status(thm)],[c_2147,c_348]) ).
% 11.28/2.04  
% 11.28/2.04  cnf(c_6240,plain,
% 11.28/2.04      ( r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) = iProver_top ),
% 11.28/2.04      inference(superposition,[status(thm)],[c_882,c_2616]) ).
% 11.28/2.04  
% 11.28/2.04  cnf(c_6252,plain,
% 11.28/2.04      ( r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
% 11.28/2.04      inference(predicate_to_equality_rev,[status(thm)],[c_6240]) ).
% 11.28/2.04  
% 11.28/2.04  cnf(c_7,plain,
% 11.28/2.04      ( ~ v1_relat_1(X0)
% 11.28/2.04      | ~ v1_relat_1(X1)
% 11.28/2.04      | k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1)) ),
% 11.28/2.04      inference(cnf_transformation,[],[f32]) ).
% 11.28/2.04  
% 11.28/2.04  cnf(c_343,plain,
% 11.28/2.04      ( k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1))
% 11.28/2.04      | v1_relat_1(X0) != iProver_top
% 11.28/2.04      | v1_relat_1(X1) != iProver_top ),
% 11.28/2.04      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.28/2.04  
% 11.28/2.04  cnf(c_710,plain,
% 11.28/2.04      ( k2_xboole_0(k2_relat_1(sK0),k2_relat_1(X0)) = k2_relat_1(k2_xboole_0(sK0,X0))
% 11.28/2.04      | v1_relat_1(X0) != iProver_top ),
% 11.28/2.04      inference(superposition,[status(thm)],[c_339,c_343]) ).
% 11.28/2.04  
% 11.28/2.04  cnf(c_1161,plain,
% 11.28/2.04      ( k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)) = k2_relat_1(k2_xboole_0(sK0,sK1)) ),
% 11.28/2.04      inference(superposition,[status(thm)],[c_340,c_710]) ).
% 11.28/2.04  
% 11.28/2.04  cnf(c_1163,plain,
% 11.28/2.04      ( k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)) = k2_relat_1(sK1) ),
% 11.28/2.04      inference(light_normalisation,[status(thm)],[c_1161,c_542]) ).
% 11.28/2.04  
% 11.28/2.04  cnf(c_1842,plain,
% 11.28/2.04      ( r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) = iProver_top ),
% 11.28/2.04      inference(superposition,[status(thm)],[c_1163,c_347]) ).
% 11.28/2.04  
% 11.28/2.04  cnf(c_0,plain,
% 11.28/2.04      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
% 11.28/2.04      inference(cnf_transformation,[],[f25]) ).
% 11.28/2.04  
% 11.28/2.04  cnf(c_350,plain,
% 11.28/2.04      ( r1_tarski(X0,X1) != iProver_top
% 11.28/2.04      | r1_tarski(X0,k2_xboole_0(X2,X1)) = iProver_top ),
% 11.28/2.04      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 11.28/2.04  
% 11.28/2.04  cnf(c_879,plain,
% 11.28/2.04      ( r1_tarski(X0,k3_relat_1(sK1)) = iProver_top
% 11.28/2.04      | r1_tarski(X0,k2_relat_1(sK1)) != iProver_top ),
% 11.28/2.04      inference(superposition,[status(thm)],[c_716,c_350]) ).
% 11.28/2.04  
% 11.28/2.04  cnf(c_4041,plain,
% 11.28/2.04      ( r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1)) = iProver_top ),
% 11.28/2.04      inference(superposition,[status(thm)],[c_1842,c_879]) ).
% 11.28/2.04  
% 11.28/2.04  cnf(c_4045,plain,
% 11.28/2.04      ( r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1)) ),
% 11.28/2.04      inference(predicate_to_equality_rev,[status(thm)],[c_4041]) ).
% 11.28/2.04  
% 11.28/2.04  cnf(c_136,plain,
% 11.28/2.04      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.28/2.04      theory(equality) ).
% 11.28/2.04  
% 11.28/2.04  cnf(c_372,plain,
% 11.28/2.04      ( ~ r1_tarski(X0,X1)
% 11.28/2.04      | r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
% 11.28/2.04      | k3_relat_1(sK1) != X1
% 11.28/2.04      | k3_relat_1(sK0) != X0 ),
% 11.28/2.04      inference(instantiation,[status(thm)],[c_136]) ).
% 11.28/2.04  
% 11.28/2.04  cnf(c_396,plain,
% 11.28/2.04      ( ~ r1_tarski(X0,k3_relat_1(X1))
% 11.28/2.04      | r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
% 11.28/2.04      | k3_relat_1(sK1) != k3_relat_1(X1)
% 11.28/2.04      | k3_relat_1(sK0) != X0 ),
% 11.28/2.04      inference(instantiation,[status(thm)],[c_372]) ).
% 11.28/2.04  
% 11.28/2.04  cnf(c_660,plain,
% 11.28/2.04      ( ~ r1_tarski(k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)),k3_relat_1(X0))
% 11.28/2.04      | r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
% 11.28/2.04      | k3_relat_1(sK1) != k3_relat_1(X0)
% 11.28/2.04      | k3_relat_1(sK0) != k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)) ),
% 11.28/2.04      inference(instantiation,[status(thm)],[c_396]) ).
% 11.28/2.04  
% 11.28/2.04  cnf(c_852,plain,
% 11.28/2.04      ( ~ r1_tarski(k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)),k3_relat_1(sK1))
% 11.28/2.04      | r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
% 11.28/2.04      | k3_relat_1(sK1) != k3_relat_1(sK1)
% 11.28/2.04      | k3_relat_1(sK0) != k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)) ),
% 11.28/2.04      inference(instantiation,[status(thm)],[c_660]) ).
% 11.28/2.04  
% 11.28/2.04  cnf(c_134,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.28/2.04  
% 11.28/2.04  cnf(c_435,plain,
% 11.28/2.04      ( X0 != X1 | k3_relat_1(sK0) != X1 | k3_relat_1(sK0) = X0 ),
% 11.28/2.04      inference(instantiation,[status(thm)],[c_134]) ).
% 11.28/2.04  
% 11.28/2.04  cnf(c_492,plain,
% 11.28/2.04      ( X0 != k3_relat_1(sK0)
% 11.28/2.04      | k3_relat_1(sK0) = X0
% 11.28/2.04      | k3_relat_1(sK0) != k3_relat_1(sK0) ),
% 11.28/2.04      inference(instantiation,[status(thm)],[c_435]) ).
% 11.28/2.04  
% 11.28/2.04  cnf(c_548,plain,
% 11.28/2.04      ( k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)) != k3_relat_1(sK0)
% 11.28/2.04      | k3_relat_1(sK0) = k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0))
% 11.28/2.04      | k3_relat_1(sK0) != k3_relat_1(sK0) ),
% 11.28/2.04      inference(instantiation,[status(thm)],[c_492]) ).
% 11.28/2.04  
% 11.28/2.04  cnf(c_133,plain,( X0 = X0 ),theory(equality) ).
% 11.28/2.04  
% 11.28/2.04  cnf(c_406,plain,
% 11.28/2.04      ( k3_relat_1(sK1) = k3_relat_1(sK1) ),
% 11.28/2.04      inference(instantiation,[status(thm)],[c_133]) ).
% 11.28/2.04  
% 11.28/2.04  cnf(c_148,plain,
% 11.28/2.04      ( sK0 = sK0 ),
% 11.28/2.04      inference(instantiation,[status(thm)],[c_133]) ).
% 11.28/2.04  
% 11.28/2.04  cnf(c_139,plain,
% 11.28/2.04      ( X0 != X1 | k3_relat_1(X0) = k3_relat_1(X1) ),
% 11.28/2.04      theory(equality) ).
% 11.28/2.04  
% 11.28/2.04  cnf(c_145,plain,
% 11.28/2.04      ( k3_relat_1(sK0) = k3_relat_1(sK0) | sK0 != sK0 ),
% 11.28/2.04      inference(instantiation,[status(thm)],[c_139]) ).
% 11.28/2.04  
% 11.28/2.04  cnf(c_23,plain,
% 11.28/2.04      ( ~ v1_relat_1(sK0)
% 11.28/2.04      | k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)) = k3_relat_1(sK0) ),
% 11.28/2.04      inference(instantiation,[status(thm)],[c_5]) ).
% 11.28/2.04  
% 11.28/2.04  cnf(c_8,negated_conjecture,
% 11.28/2.04      ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) ),
% 11.28/2.04      inference(cnf_transformation,[],[f36]) ).
% 11.28/2.04  
% 11.28/2.04  cnf(contradiction,plain,
% 11.28/2.04      ( $false ),
% 11.28/2.04      inference(minisat,
% 11.28/2.04                [status(thm)],
% 11.28/2.04                [c_41479,c_6252,c_4045,c_852,c_548,c_406,c_148,c_145,
% 11.28/2.04                 c_23,c_8,c_11]) ).
% 11.28/2.04  
% 11.28/2.04  
% 11.28/2.04  % SZS output end CNFRefutation for theBenchmark.p
% 11.28/2.04  
% 11.28/2.04  ------                               Statistics
% 11.28/2.04  
% 11.28/2.04  ------ General
% 11.28/2.04  
% 11.28/2.04  abstr_ref_over_cycles:                  0
% 11.28/2.04  abstr_ref_under_cycles:                 0
% 11.28/2.04  gc_basic_clause_elim:                   0
% 11.28/2.04  forced_gc_time:                         0
% 11.28/2.04  parsing_time:                           0.054
% 11.28/2.04  unif_index_cands_time:                  0.
% 11.28/2.04  unif_index_add_time:                    0.
% 11.28/2.04  orderings_time:                         0.
% 11.28/2.04  out_proof_time:                         0.01
% 11.28/2.04  total_time:                             1.205
% 11.28/2.04  num_of_symbols:                         39
% 11.28/2.04  num_of_terms:                           32975
% 11.28/2.04  
% 11.28/2.04  ------ Preprocessing
% 11.28/2.04  
% 11.28/2.04  num_of_splits:                          0
% 11.28/2.04  num_of_split_atoms:                     0
% 11.28/2.04  num_of_reused_defs:                     0
% 11.28/2.04  num_eq_ax_congr_red:                    0
% 11.28/2.04  num_of_sem_filtered_clauses:            1
% 11.28/2.04  num_of_subtypes:                        0
% 11.28/2.04  monotx_restored_types:                  0
% 11.28/2.04  sat_num_of_epr_types:                   0
% 11.28/2.04  sat_num_of_non_cyclic_types:            0
% 11.28/2.04  sat_guarded_non_collapsed_types:        0
% 11.28/2.04  num_pure_diseq_elim:                    0
% 11.28/2.04  simp_replaced_by:                       0
% 11.28/2.04  res_preprocessed:                       53
% 11.28/2.04  prep_upred:                             0
% 11.28/2.04  prep_unflattend:                        0
% 11.28/2.04  smt_new_axioms:                         0
% 11.28/2.04  pred_elim_cands:                        2
% 11.28/2.04  pred_elim:                              0
% 11.28/2.04  pred_elim_cl:                           0
% 11.28/2.04  pred_elim_cycles:                       1
% 11.28/2.04  merged_defs:                            0
% 11.28/2.04  merged_defs_ncl:                        0
% 11.28/2.04  bin_hyper_res:                          0
% 11.28/2.04  prep_cycles:                            3
% 11.28/2.04  pred_elim_time:                         0.
% 11.28/2.04  splitting_time:                         0.
% 11.28/2.04  sem_filter_time:                        0.
% 11.28/2.04  monotx_time:                            0.
% 11.28/2.04  subtype_inf_time:                       0.
% 11.28/2.04  
% 11.28/2.04  ------ Problem properties
% 11.28/2.04  
% 11.28/2.04  clauses:                                12
% 11.28/2.04  conjectures:                            4
% 11.28/2.04  epr:                                    4
% 11.28/2.04  horn:                                   12
% 11.28/2.04  ground:                                 4
% 11.28/2.04  unary:                                  5
% 11.28/2.04  binary:                                 3
% 11.28/2.04  lits:                                   23
% 11.28/2.04  lits_eq:                                4
% 11.28/2.04  fd_pure:                                0
% 11.28/2.04  fd_pseudo:                              0
% 11.28/2.04  fd_cond:                                0
% 11.28/2.04  fd_pseudo_cond:                         0
% 11.28/2.04  ac_symbols:                             0
% 11.28/2.04  
% 11.28/2.04  ------ Propositional Solver
% 11.28/2.04  
% 11.28/2.04  prop_solver_calls:                      33
% 11.28/2.04  prop_fast_solver_calls:                 725
% 11.28/2.04  smt_solver_calls:                       0
% 11.28/2.04  smt_fast_solver_calls:                  0
% 11.28/2.04  prop_num_of_clauses:                    18923
% 11.28/2.04  prop_preprocess_simplified:             27703
% 11.28/2.04  prop_fo_subsumed:                       3
% 11.28/2.04  prop_solver_time:                       0.
% 11.28/2.04  smt_solver_time:                        0.
% 11.28/2.04  smt_fast_solver_time:                   0.
% 11.28/2.04  prop_fast_solver_time:                  0.
% 11.28/2.04  prop_unsat_core_time:                   0.002
% 11.28/2.04  
% 11.28/2.04  ------ QBF
% 11.28/2.04  
% 11.28/2.04  qbf_q_res:                              0
% 11.28/2.04  qbf_num_tautologies:                    0
% 11.28/2.04  qbf_prep_cycles:                        0
% 11.28/2.04  
% 11.28/2.04  ------ BMC1
% 11.28/2.04  
% 11.28/2.04  bmc1_current_bound:                     -1
% 11.28/2.04  bmc1_last_solved_bound:                 -1
% 11.28/2.04  bmc1_unsat_core_size:                   -1
% 11.28/2.04  bmc1_unsat_core_parents_size:           -1
% 11.28/2.04  bmc1_merge_next_fun:                    0
% 11.28/2.04  bmc1_unsat_core_clauses_time:           0.
% 11.28/2.04  
% 11.28/2.04  ------ Instantiation
% 11.28/2.04  
% 11.28/2.04  inst_num_of_clauses:                    4165
% 11.28/2.04  inst_num_in_passive:                    2694
% 11.28/2.04  inst_num_in_active:                     1374
% 11.28/2.04  inst_num_in_unprocessed:                97
% 11.28/2.04  inst_num_of_loops:                      1435
% 11.28/2.04  inst_num_of_learning_restarts:          0
% 11.28/2.04  inst_num_moves_active_passive:          53
% 11.28/2.04  inst_lit_activity:                      0
% 11.28/2.04  inst_lit_activity_moves:                1
% 11.28/2.04  inst_num_tautologies:                   0
% 11.28/2.04  inst_num_prop_implied:                  0
% 11.28/2.04  inst_num_existing_simplified:           0
% 11.28/2.04  inst_num_eq_res_simplified:             0
% 11.28/2.04  inst_num_child_elim:                    0
% 11.28/2.04  inst_num_of_dismatching_blockings:      4647
% 11.28/2.04  inst_num_of_non_proper_insts:           6052
% 11.28/2.04  inst_num_of_duplicates:                 0
% 11.28/2.04  inst_inst_num_from_inst_to_res:         0
% 11.28/2.04  inst_dismatching_checking_time:         0.
% 11.28/2.04  
% 11.28/2.04  ------ Resolution
% 11.28/2.04  
% 11.28/2.04  res_num_of_clauses:                     0
% 11.28/2.04  res_num_in_passive:                     0
% 11.28/2.04  res_num_in_active:                      0
% 11.28/2.04  res_num_of_loops:                       56
% 11.28/2.04  res_forward_subset_subsumed:            370
% 11.28/2.04  res_backward_subset_subsumed:           6
% 11.28/2.04  res_forward_subsumed:                   0
% 11.28/2.04  res_backward_subsumed:                  0
% 11.28/2.04  res_forward_subsumption_resolution:     0
% 11.28/2.04  res_backward_subsumption_resolution:    0
% 11.28/2.04  res_clause_to_clause_subsumption:       18618
% 11.28/2.04  res_orphan_elimination:                 0
% 11.28/2.04  res_tautology_del:                      386
% 11.28/2.04  res_num_eq_res_simplified:              0
% 11.28/2.04  res_num_sel_changes:                    0
% 11.28/2.04  res_moves_from_active_to_pass:          0
% 11.28/2.04  
% 11.28/2.04  ------ Superposition
% 11.28/2.04  
% 11.28/2.04  sup_time_total:                         0.
% 11.28/2.04  sup_time_generating:                    0.
% 11.28/2.04  sup_time_sim_full:                      0.
% 11.28/2.04  sup_time_sim_immed:                     0.
% 11.28/2.04  
% 11.28/2.04  sup_num_of_clauses:                     2367
% 11.28/2.04  sup_num_in_active:                      286
% 11.28/2.04  sup_num_in_passive:                     2081
% 11.28/2.04  sup_num_of_loops:                       286
% 11.28/2.04  sup_fw_superposition:                   2475
% 11.28/2.04  sup_bw_superposition:                   2178
% 11.28/2.04  sup_immediate_simplified:               1207
% 11.28/2.04  sup_given_eliminated:                   0
% 11.28/2.04  comparisons_done:                       0
% 11.28/2.04  comparisons_avoided:                    0
% 11.28/2.04  
% 11.28/2.04  ------ Simplifications
% 11.28/2.04  
% 11.28/2.04  
% 11.28/2.04  sim_fw_subset_subsumed:                 226
% 11.28/2.04  sim_bw_subset_subsumed:                 35
% 11.28/2.04  sim_fw_subsumed:                        491
% 11.28/2.04  sim_bw_subsumed:                        15
% 11.28/2.04  sim_fw_subsumption_res:                 0
% 11.28/2.04  sim_bw_subsumption_res:                 0
% 11.28/2.04  sim_tautology_del:                      128
% 11.28/2.04  sim_eq_tautology_del:                   162
% 11.28/2.04  sim_eq_res_simp:                        0
% 11.28/2.04  sim_fw_demodulated:                     332
% 11.28/2.04  sim_bw_demodulated:                     0
% 11.28/2.04  sim_light_normalised:                   156
% 11.28/2.04  sim_joinable_taut:                      0
% 11.28/2.04  sim_joinable_simp:                      0
% 11.28/2.04  sim_ac_normalised:                      0
% 11.28/2.04  sim_smt_subsumption:                    0
% 11.28/2.04  
%------------------------------------------------------------------------------
