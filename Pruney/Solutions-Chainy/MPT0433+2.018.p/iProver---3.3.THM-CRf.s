%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:42:53 EST 2020

% Result     : Theorem 35.95s
% Output     : CNFRefutation 35.95s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 194 expanded)
%              Number of clauses        :   75 (  96 expanded)
%              Number of leaves         :   15 (  38 expanded)
%              Depth                    :   11
%              Number of atoms          :  241 ( 477 expanded)
%              Number of equality atoms :  114 ( 176 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f18])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f37,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f23])).

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

fof(f6,axiom,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

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

fof(f9,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
          & v1_relat_1(X1) )
     => ( ~ r1_tarski(k1_relat_1(k3_xboole_0(X0,sK1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(sK1)))
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f21,f20])).

fof(f34,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f33,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f35,plain,(
    ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f25,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_387,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_385,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_751,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_387,c_385])).

cnf(c_7,plain,
    ( r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_382,plain,
    ( r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_386,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1138,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_382,c_386])).

cnf(c_2396,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(superposition,[status(thm)],[c_1138,c_385])).

cnf(c_4448,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X1) ),
    inference(superposition,[status(thm)],[c_751,c_2396])).

cnf(c_4490,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),X1) = X1 ),
    inference(demodulation,[status(thm)],[c_4448,c_751])).

cnf(c_11,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_378,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_12,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_377,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_381,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k3_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_380,plain,
    ( k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_845,plain,
    ( k2_xboole_0(k1_relat_1(k3_xboole_0(X0,X1)),k1_relat_1(X2)) = k1_relat_1(k2_xboole_0(k3_xboole_0(X0,X1),X2))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_381,c_380])).

cnf(c_3703,plain,
    ( k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,X0)),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(k3_xboole_0(sK0,X0),X1))
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_377,c_845])).

cnf(c_4848,plain,
    ( k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,X0)),k1_relat_1(sK1)) = k1_relat_1(k2_xboole_0(k3_xboole_0(sK0,X0),sK1)) ),
    inference(superposition,[status(thm)],[c_378,c_3703])).

cnf(c_1137,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_387,c_386])).

cnf(c_5061,plain,
    ( r1_tarski(k1_relat_1(k3_xboole_0(sK0,X0)),k1_relat_1(k2_xboole_0(k3_xboole_0(sK0,X0),sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4848,c_1137])).

cnf(c_131257,plain,
    ( r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4490,c_5061])).

cnf(c_178,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_735,plain,
    ( X0 != X1
    | k1_relat_1(sK0) != X1
    | k1_relat_1(sK0) = X0 ),
    inference(instantiation,[status(thm)],[c_178])).

cnf(c_1091,plain,
    ( X0 != k1_relat_1(sK0)
    | k1_relat_1(sK0) = X0
    | k1_relat_1(sK0) != k1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_735])).

cnf(c_2046,plain,
    ( k1_relat_1(X0) != k1_relat_1(sK0)
    | k1_relat_1(sK0) = k1_relat_1(X0)
    | k1_relat_1(sK0) != k1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_1091])).

cnf(c_30151,plain,
    ( k1_relat_1(k2_xboole_0(k3_xboole_0(sK0,sK1),X0)) != k1_relat_1(sK0)
    | k1_relat_1(sK0) = k1_relat_1(k2_xboole_0(k3_xboole_0(sK0,sK1),X0))
    | k1_relat_1(sK0) != k1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_2046])).

cnf(c_30153,plain,
    ( k1_relat_1(k2_xboole_0(k3_xboole_0(sK0,sK1),sK0)) != k1_relat_1(sK0)
    | k1_relat_1(sK0) = k1_relat_1(k2_xboole_0(k3_xboole_0(sK0,sK1),sK0))
    | k1_relat_1(sK0) != k1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_30151])).

cnf(c_470,plain,
    ( r1_tarski(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2528,plain,
    ( r1_tarski(k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),X0),k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),X0)) ),
    inference(instantiation,[status(thm)],[c_470])).

cnf(c_24137,plain,
    ( r1_tarski(k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(X0)),k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(X0))) ),
    inference(instantiation,[status(thm)],[c_2528])).

cnf(c_24142,plain,
    ( r1_tarski(k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(X0)),k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24137])).

cnf(c_24144,plain,
    ( r1_tarski(k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0)),k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_24142])).

cnf(c_179,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_550,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0))
    | k1_relat_1(k3_xboole_0(sK0,sK1)) != X0
    | k1_relat_1(sK0) != X1 ),
    inference(instantiation,[status(thm)],[c_179])).

cnf(c_8546,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(k1_relat_1(X1),k1_relat_1(X2)))
    | r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0))
    | k1_relat_1(k3_xboole_0(sK0,sK1)) != X0
    | k1_relat_1(sK0) != k2_xboole_0(k1_relat_1(X1),k1_relat_1(X2)) ),
    inference(instantiation,[status(thm)],[c_550])).

cnf(c_9244,plain,
    ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
    | r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0))
    | k1_relat_1(k3_xboole_0(sK0,sK1)) != k1_relat_1(k3_xboole_0(sK0,sK1))
    | k1_relat_1(sK0) != k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) ),
    inference(instantiation,[status(thm)],[c_8546])).

cnf(c_21992,plain,
    ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(X0)))
    | r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0))
    | k1_relat_1(k3_xboole_0(sK0,sK1)) != k1_relat_1(k3_xboole_0(sK0,sK1))
    | k1_relat_1(sK0) != k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(X0)) ),
    inference(instantiation,[status(thm)],[c_9244])).

cnf(c_21997,plain,
    ( k1_relat_1(k3_xboole_0(sK0,sK1)) != k1_relat_1(k3_xboole_0(sK0,sK1))
    | k1_relat_1(sK0) != k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(X0))
    | r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(X0))) != iProver_top
    | r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21992])).

cnf(c_21999,plain,
    ( k1_relat_1(k3_xboole_0(sK0,sK1)) != k1_relat_1(k3_xboole_0(sK0,sK1))
    | k1_relat_1(sK0) != k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0))
    | r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0))) != iProver_top
    | r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_21997])).

cnf(c_469,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1))
    | ~ r1_tarski(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1308,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),X0),k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),X0))
    | r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),X0)) ),
    inference(instantiation,[status(thm)],[c_469])).

cnf(c_18133,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(X0)),k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(X0)))
    | r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(X0))) ),
    inference(instantiation,[status(thm)],[c_1308])).

cnf(c_18138,plain,
    ( r1_tarski(k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(X0)),k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(X0))) != iProver_top
    | r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18133])).

cnf(c_18140,plain,
    ( r1_tarski(k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0)),k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0))) != iProver_top
    | r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_18138])).

cnf(c_1093,plain,
    ( X0 != k1_relat_1(X1)
    | k1_relat_1(sK0) = X0
    | k1_relat_1(sK0) != k1_relat_1(X1) ),
    inference(instantiation,[status(thm)],[c_735])).

cnf(c_2548,plain,
    ( k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) != k1_relat_1(k2_xboole_0(X0,X1))
    | k1_relat_1(sK0) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
    | k1_relat_1(sK0) != k1_relat_1(k2_xboole_0(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_1093])).

cnf(c_10388,plain,
    ( k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(X0)) != k1_relat_1(k2_xboole_0(k3_xboole_0(sK0,sK1),X0))
    | k1_relat_1(sK0) = k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(X0))
    | k1_relat_1(sK0) != k1_relat_1(k2_xboole_0(k3_xboole_0(sK0,sK1),X0)) ),
    inference(instantiation,[status(thm)],[c_2548])).

cnf(c_10390,plain,
    ( k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0)) != k1_relat_1(k2_xboole_0(k3_xboole_0(sK0,sK1),sK0))
    | k1_relat_1(sK0) = k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0))
    | k1_relat_1(sK0) != k1_relat_1(k2_xboole_0(k3_xboole_0(sK0,sK1),sK0)) ),
    inference(instantiation,[status(thm)],[c_10388])).

cnf(c_8354,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK1),X0)
    | k2_xboole_0(k3_xboole_0(sK0,sK1),X0) = X0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_8356,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK1),sK0)
    | k2_xboole_0(k3_xboole_0(sK0,sK1),sK0) = sK0 ),
    inference(instantiation,[status(thm)],[c_8354])).

cnf(c_183,plain,
    ( X0 != X1
    | k1_relat_1(X0) = k1_relat_1(X1) ),
    theory(equality)).

cnf(c_7643,plain,
    ( k2_xboole_0(k3_xboole_0(sK0,sK1),X0) != X1
    | k1_relat_1(k2_xboole_0(k3_xboole_0(sK0,sK1),X0)) = k1_relat_1(X1) ),
    inference(instantiation,[status(thm)],[c_183])).

cnf(c_7648,plain,
    ( k2_xboole_0(k3_xboole_0(sK0,sK1),sK0) != sK0
    | k1_relat_1(k2_xboole_0(k3_xboole_0(sK0,sK1),sK0)) = k1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_7643])).

cnf(c_2510,plain,
    ( v1_relat_1(k3_xboole_0(sK0,sK1))
    | ~ v1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1252,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(X0)) = k1_relat_1(k2_xboole_0(k3_xboole_0(sK0,sK1),X0)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1258,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | ~ v1_relat_1(sK0)
    | k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0)) = k1_relat_1(k2_xboole_0(k3_xboole_0(sK0,sK1),sK0)) ),
    inference(instantiation,[status(thm)],[c_1252])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_10,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1179,plain,
    ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0)) ),
    inference(resolution,[status(thm)],[c_6,c_10])).

cnf(c_1180,plain,
    ( r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK1)) != iProver_top
    | r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1179])).

cnf(c_5,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_1008,plain,
    ( r1_tarski(k3_xboole_0(sK0,sK1),sK0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_177,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_561,plain,
    ( k1_relat_1(k3_xboole_0(sK0,sK1)) = k1_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_177])).

cnf(c_188,plain,
    ( k1_relat_1(sK0) = k1_relat_1(sK0)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_183])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_42,plain,
    ( ~ r1_tarski(sK0,sK0)
    | sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_38,plain,
    ( r1_tarski(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_131257,c_30153,c_24144,c_21999,c_18140,c_10390,c_8356,c_7648,c_2510,c_1258,c_1180,c_1008,c_561,c_188,c_42,c_38,c_12])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:32:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 35.95/5.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 35.95/5.00  
% 35.95/5.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 35.95/5.00  
% 35.95/5.00  ------  iProver source info
% 35.95/5.00  
% 35.95/5.00  git: date: 2020-06-30 10:37:57 +0100
% 35.95/5.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 35.95/5.00  git: non_committed_changes: false
% 35.95/5.00  git: last_make_outside_of_git: false
% 35.95/5.00  
% 35.95/5.00  ------ 
% 35.95/5.00  ------ Parsing...
% 35.95/5.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 35.95/5.00  
% 35.95/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 35.95/5.00  
% 35.95/5.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 35.95/5.00  
% 35.95/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.95/5.00  ------ Proving...
% 35.95/5.00  ------ Problem Properties 
% 35.95/5.00  
% 35.95/5.00  
% 35.95/5.00  clauses                                 12
% 35.95/5.00  conjectures                             3
% 35.95/5.00  EPR                                     4
% 35.95/5.00  Horn                                    12
% 35.95/5.00  unary                                   6
% 35.95/5.00  binary                                  3
% 35.95/5.00  lits                                    21
% 35.95/5.00  lits eq                                 3
% 35.95/5.00  fd_pure                                 0
% 35.95/5.00  fd_pseudo                               0
% 35.95/5.00  fd_cond                                 0
% 35.95/5.00  fd_pseudo_cond                          1
% 35.95/5.00  AC symbols                              0
% 35.95/5.00  
% 35.95/5.00  ------ Input Options Time Limit: Unbounded
% 35.95/5.00  
% 35.95/5.00  
% 35.95/5.00  ------ 
% 35.95/5.00  Current options:
% 35.95/5.00  ------ 
% 35.95/5.00  
% 35.95/5.00  
% 35.95/5.00  
% 35.95/5.00  
% 35.95/5.00  ------ Proving...
% 35.95/5.00  
% 35.95/5.00  
% 35.95/5.00  % SZS status Theorem for theBenchmark.p
% 35.95/5.00  
% 35.95/5.00  % SZS output start CNFRefutation for theBenchmark.p
% 35.95/5.00  
% 35.95/5.00  fof(f1,axiom,(
% 35.95/5.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 35.95/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.95/5.00  
% 35.95/5.00  fof(f18,plain,(
% 35.95/5.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 35.95/5.00    inference(nnf_transformation,[],[f1])).
% 35.95/5.00  
% 35.95/5.00  fof(f19,plain,(
% 35.95/5.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 35.95/5.00    inference(flattening,[],[f18])).
% 35.95/5.00  
% 35.95/5.00  fof(f23,plain,(
% 35.95/5.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 35.95/5.00    inference(cnf_transformation,[],[f19])).
% 35.95/5.00  
% 35.95/5.00  fof(f37,plain,(
% 35.95/5.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 35.95/5.00    inference(equality_resolution,[],[f23])).
% 35.95/5.00  
% 35.95/5.00  fof(f3,axiom,(
% 35.95/5.00    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 35.95/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.95/5.00  
% 35.95/5.00  fof(f12,plain,(
% 35.95/5.00    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 35.95/5.00    inference(ennf_transformation,[],[f3])).
% 35.95/5.00  
% 35.95/5.00  fof(f27,plain,(
% 35.95/5.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 35.95/5.00    inference(cnf_transformation,[],[f12])).
% 35.95/5.00  
% 35.95/5.00  fof(f6,axiom,(
% 35.95/5.00    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 35.95/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.95/5.00  
% 35.95/5.00  fof(f30,plain,(
% 35.95/5.00    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) )),
% 35.95/5.00    inference(cnf_transformation,[],[f6])).
% 35.95/5.00  
% 35.95/5.00  fof(f2,axiom,(
% 35.95/5.00    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 35.95/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.95/5.00  
% 35.95/5.00  fof(f11,plain,(
% 35.95/5.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 35.95/5.00    inference(ennf_transformation,[],[f2])).
% 35.95/5.00  
% 35.95/5.00  fof(f26,plain,(
% 35.95/5.00    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 35.95/5.00    inference(cnf_transformation,[],[f11])).
% 35.95/5.00  
% 35.95/5.00  fof(f9,conjecture,(
% 35.95/5.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))))),
% 35.95/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.95/5.00  
% 35.95/5.00  fof(f10,negated_conjecture,(
% 35.95/5.00    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))))),
% 35.95/5.00    inference(negated_conjecture,[],[f9])).
% 35.95/5.00  
% 35.95/5.00  fof(f17,plain,(
% 35.95/5.00    ? [X0] : (? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 35.95/5.00    inference(ennf_transformation,[],[f10])).
% 35.95/5.00  
% 35.95/5.00  fof(f21,plain,(
% 35.95/5.00    ( ! [X0] : (? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) & v1_relat_1(X1)) => (~r1_tarski(k1_relat_1(k3_xboole_0(X0,sK1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(sK1))) & v1_relat_1(sK1))) )),
% 35.95/5.00    introduced(choice_axiom,[])).
% 35.95/5.00  
% 35.95/5.00  fof(f20,plain,(
% 35.95/5.00    ? [X0] : (? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 35.95/5.00    introduced(choice_axiom,[])).
% 35.95/5.00  
% 35.95/5.00  fof(f22,plain,(
% 35.95/5.00    (~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 35.95/5.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f21,f20])).
% 35.95/5.00  
% 35.95/5.00  fof(f34,plain,(
% 35.95/5.00    v1_relat_1(sK1)),
% 35.95/5.00    inference(cnf_transformation,[],[f22])).
% 35.95/5.00  
% 35.95/5.00  fof(f33,plain,(
% 35.95/5.00    v1_relat_1(sK0)),
% 35.95/5.00    inference(cnf_transformation,[],[f22])).
% 35.95/5.00  
% 35.95/5.00  fof(f7,axiom,(
% 35.95/5.00    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 35.95/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.95/5.00  
% 35.95/5.00  fof(f15,plain,(
% 35.95/5.00    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 35.95/5.00    inference(ennf_transformation,[],[f7])).
% 35.95/5.00  
% 35.95/5.00  fof(f31,plain,(
% 35.95/5.00    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 35.95/5.00    inference(cnf_transformation,[],[f15])).
% 35.95/5.00  
% 35.95/5.00  fof(f8,axiom,(
% 35.95/5.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1))))),
% 35.95/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.95/5.00  
% 35.95/5.00  fof(f16,plain,(
% 35.95/5.00    ! [X0] : (! [X1] : (k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 35.95/5.00    inference(ennf_transformation,[],[f8])).
% 35.95/5.00  
% 35.95/5.00  fof(f32,plain,(
% 35.95/5.00    ( ! [X0,X1] : (k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 35.95/5.00    inference(cnf_transformation,[],[f16])).
% 35.95/5.00  
% 35.95/5.00  fof(f5,axiom,(
% 35.95/5.00    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 35.95/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.95/5.00  
% 35.95/5.00  fof(f13,plain,(
% 35.95/5.00    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 35.95/5.00    inference(ennf_transformation,[],[f5])).
% 35.95/5.00  
% 35.95/5.00  fof(f14,plain,(
% 35.95/5.00    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 35.95/5.00    inference(flattening,[],[f13])).
% 35.95/5.00  
% 35.95/5.00  fof(f29,plain,(
% 35.95/5.00    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 35.95/5.00    inference(cnf_transformation,[],[f14])).
% 35.95/5.00  
% 35.95/5.00  fof(f35,plain,(
% 35.95/5.00    ~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))),
% 35.95/5.00    inference(cnf_transformation,[],[f22])).
% 35.95/5.00  
% 35.95/5.00  fof(f4,axiom,(
% 35.95/5.00    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 35.95/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.95/5.00  
% 35.95/5.00  fof(f28,plain,(
% 35.95/5.00    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 35.95/5.00    inference(cnf_transformation,[],[f4])).
% 35.95/5.00  
% 35.95/5.00  fof(f25,plain,(
% 35.95/5.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 35.95/5.00    inference(cnf_transformation,[],[f19])).
% 35.95/5.00  
% 35.95/5.00  cnf(c_2,plain,
% 35.95/5.00      ( r1_tarski(X0,X0) ),
% 35.95/5.00      inference(cnf_transformation,[],[f37]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_387,plain,
% 35.95/5.00      ( r1_tarski(X0,X0) = iProver_top ),
% 35.95/5.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_4,plain,
% 35.95/5.00      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 35.95/5.00      inference(cnf_transformation,[],[f27]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_385,plain,
% 35.95/5.00      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 35.95/5.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_751,plain,
% 35.95/5.00      ( k2_xboole_0(X0,X0) = X0 ),
% 35.95/5.00      inference(superposition,[status(thm)],[c_387,c_385]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_7,plain,
% 35.95/5.00      ( r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
% 35.95/5.00      inference(cnf_transformation,[],[f30]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_382,plain,
% 35.95/5.00      ( r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) = iProver_top ),
% 35.95/5.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_3,plain,
% 35.95/5.00      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 35.95/5.00      inference(cnf_transformation,[],[f26]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_386,plain,
% 35.95/5.00      ( r1_tarski(X0,X1) = iProver_top
% 35.95/5.00      | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
% 35.95/5.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_1138,plain,
% 35.95/5.00      ( r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = iProver_top ),
% 35.95/5.00      inference(superposition,[status(thm)],[c_382,c_386]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_2396,plain,
% 35.95/5.00      ( k2_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
% 35.95/5.00      inference(superposition,[status(thm)],[c_1138,c_385]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_4448,plain,
% 35.95/5.00      ( k2_xboole_0(k3_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X1) ),
% 35.95/5.00      inference(superposition,[status(thm)],[c_751,c_2396]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_4490,plain,
% 35.95/5.00      ( k2_xboole_0(k3_xboole_0(X0,X1),X1) = X1 ),
% 35.95/5.00      inference(demodulation,[status(thm)],[c_4448,c_751]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_11,negated_conjecture,
% 35.95/5.00      ( v1_relat_1(sK1) ),
% 35.95/5.00      inference(cnf_transformation,[],[f34]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_378,plain,
% 35.95/5.00      ( v1_relat_1(sK1) = iProver_top ),
% 35.95/5.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_12,negated_conjecture,
% 35.95/5.00      ( v1_relat_1(sK0) ),
% 35.95/5.00      inference(cnf_transformation,[],[f33]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_377,plain,
% 35.95/5.00      ( v1_relat_1(sK0) = iProver_top ),
% 35.95/5.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_8,plain,
% 35.95/5.00      ( ~ v1_relat_1(X0) | v1_relat_1(k3_xboole_0(X0,X1)) ),
% 35.95/5.00      inference(cnf_transformation,[],[f31]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_381,plain,
% 35.95/5.00      ( v1_relat_1(X0) != iProver_top
% 35.95/5.00      | v1_relat_1(k3_xboole_0(X0,X1)) = iProver_top ),
% 35.95/5.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_9,plain,
% 35.95/5.00      ( ~ v1_relat_1(X0)
% 35.95/5.00      | ~ v1_relat_1(X1)
% 35.95/5.00      | k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) ),
% 35.95/5.00      inference(cnf_transformation,[],[f32]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_380,plain,
% 35.95/5.00      ( k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1))
% 35.95/5.00      | v1_relat_1(X0) != iProver_top
% 35.95/5.00      | v1_relat_1(X1) != iProver_top ),
% 35.95/5.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_845,plain,
% 35.95/5.00      ( k2_xboole_0(k1_relat_1(k3_xboole_0(X0,X1)),k1_relat_1(X2)) = k1_relat_1(k2_xboole_0(k3_xboole_0(X0,X1),X2))
% 35.95/5.00      | v1_relat_1(X0) != iProver_top
% 35.95/5.00      | v1_relat_1(X2) != iProver_top ),
% 35.95/5.00      inference(superposition,[status(thm)],[c_381,c_380]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_3703,plain,
% 35.95/5.00      ( k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,X0)),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(k3_xboole_0(sK0,X0),X1))
% 35.95/5.00      | v1_relat_1(X1) != iProver_top ),
% 35.95/5.00      inference(superposition,[status(thm)],[c_377,c_845]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_4848,plain,
% 35.95/5.00      ( k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,X0)),k1_relat_1(sK1)) = k1_relat_1(k2_xboole_0(k3_xboole_0(sK0,X0),sK1)) ),
% 35.95/5.00      inference(superposition,[status(thm)],[c_378,c_3703]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_1137,plain,
% 35.95/5.00      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 35.95/5.00      inference(superposition,[status(thm)],[c_387,c_386]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_5061,plain,
% 35.95/5.00      ( r1_tarski(k1_relat_1(k3_xboole_0(sK0,X0)),k1_relat_1(k2_xboole_0(k3_xboole_0(sK0,X0),sK1))) = iProver_top ),
% 35.95/5.00      inference(superposition,[status(thm)],[c_4848,c_1137]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_131257,plain,
% 35.95/5.00      ( r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK1)) = iProver_top ),
% 35.95/5.00      inference(superposition,[status(thm)],[c_4490,c_5061]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_178,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_735,plain,
% 35.95/5.00      ( X0 != X1 | k1_relat_1(sK0) != X1 | k1_relat_1(sK0) = X0 ),
% 35.95/5.00      inference(instantiation,[status(thm)],[c_178]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_1091,plain,
% 35.95/5.00      ( X0 != k1_relat_1(sK0)
% 35.95/5.00      | k1_relat_1(sK0) = X0
% 35.95/5.00      | k1_relat_1(sK0) != k1_relat_1(sK0) ),
% 35.95/5.00      inference(instantiation,[status(thm)],[c_735]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_2046,plain,
% 35.95/5.00      ( k1_relat_1(X0) != k1_relat_1(sK0)
% 35.95/5.00      | k1_relat_1(sK0) = k1_relat_1(X0)
% 35.95/5.00      | k1_relat_1(sK0) != k1_relat_1(sK0) ),
% 35.95/5.00      inference(instantiation,[status(thm)],[c_1091]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_30151,plain,
% 35.95/5.00      ( k1_relat_1(k2_xboole_0(k3_xboole_0(sK0,sK1),X0)) != k1_relat_1(sK0)
% 35.95/5.00      | k1_relat_1(sK0) = k1_relat_1(k2_xboole_0(k3_xboole_0(sK0,sK1),X0))
% 35.95/5.00      | k1_relat_1(sK0) != k1_relat_1(sK0) ),
% 35.95/5.00      inference(instantiation,[status(thm)],[c_2046]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_30153,plain,
% 35.95/5.00      ( k1_relat_1(k2_xboole_0(k3_xboole_0(sK0,sK1),sK0)) != k1_relat_1(sK0)
% 35.95/5.00      | k1_relat_1(sK0) = k1_relat_1(k2_xboole_0(k3_xboole_0(sK0,sK1),sK0))
% 35.95/5.00      | k1_relat_1(sK0) != k1_relat_1(sK0) ),
% 35.95/5.00      inference(instantiation,[status(thm)],[c_30151]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_470,plain,
% 35.95/5.00      ( r1_tarski(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
% 35.95/5.00      inference(instantiation,[status(thm)],[c_2]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_2528,plain,
% 35.95/5.00      ( r1_tarski(k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),X0),k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),X0)) ),
% 35.95/5.00      inference(instantiation,[status(thm)],[c_470]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_24137,plain,
% 35.95/5.00      ( r1_tarski(k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(X0)),k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(X0))) ),
% 35.95/5.00      inference(instantiation,[status(thm)],[c_2528]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_24142,plain,
% 35.95/5.00      ( r1_tarski(k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(X0)),k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(X0))) = iProver_top ),
% 35.95/5.00      inference(predicate_to_equality,[status(thm)],[c_24137]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_24144,plain,
% 35.95/5.00      ( r1_tarski(k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0)),k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0))) = iProver_top ),
% 35.95/5.00      inference(instantiation,[status(thm)],[c_24142]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_179,plain,
% 35.95/5.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 35.95/5.00      theory(equality) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_550,plain,
% 35.95/5.00      ( ~ r1_tarski(X0,X1)
% 35.95/5.00      | r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0))
% 35.95/5.00      | k1_relat_1(k3_xboole_0(sK0,sK1)) != X0
% 35.95/5.00      | k1_relat_1(sK0) != X1 ),
% 35.95/5.00      inference(instantiation,[status(thm)],[c_179]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_8546,plain,
% 35.95/5.00      ( ~ r1_tarski(X0,k2_xboole_0(k1_relat_1(X1),k1_relat_1(X2)))
% 35.95/5.00      | r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0))
% 35.95/5.00      | k1_relat_1(k3_xboole_0(sK0,sK1)) != X0
% 35.95/5.00      | k1_relat_1(sK0) != k2_xboole_0(k1_relat_1(X1),k1_relat_1(X2)) ),
% 35.95/5.00      inference(instantiation,[status(thm)],[c_550]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_9244,plain,
% 35.95/5.00      ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
% 35.95/5.00      | r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0))
% 35.95/5.00      | k1_relat_1(k3_xboole_0(sK0,sK1)) != k1_relat_1(k3_xboole_0(sK0,sK1))
% 35.95/5.00      | k1_relat_1(sK0) != k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) ),
% 35.95/5.00      inference(instantiation,[status(thm)],[c_8546]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_21992,plain,
% 35.95/5.00      ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(X0)))
% 35.95/5.00      | r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0))
% 35.95/5.00      | k1_relat_1(k3_xboole_0(sK0,sK1)) != k1_relat_1(k3_xboole_0(sK0,sK1))
% 35.95/5.00      | k1_relat_1(sK0) != k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(X0)) ),
% 35.95/5.00      inference(instantiation,[status(thm)],[c_9244]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_21997,plain,
% 35.95/5.00      ( k1_relat_1(k3_xboole_0(sK0,sK1)) != k1_relat_1(k3_xboole_0(sK0,sK1))
% 35.95/5.00      | k1_relat_1(sK0) != k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(X0))
% 35.95/5.00      | r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(X0))) != iProver_top
% 35.95/5.00      | r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0)) = iProver_top ),
% 35.95/5.00      inference(predicate_to_equality,[status(thm)],[c_21992]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_21999,plain,
% 35.95/5.00      ( k1_relat_1(k3_xboole_0(sK0,sK1)) != k1_relat_1(k3_xboole_0(sK0,sK1))
% 35.95/5.00      | k1_relat_1(sK0) != k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0))
% 35.95/5.00      | r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0))) != iProver_top
% 35.95/5.00      | r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0)) = iProver_top ),
% 35.95/5.00      inference(instantiation,[status(thm)],[c_21997]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_469,plain,
% 35.95/5.00      ( r1_tarski(X0,k2_xboole_0(X0,X1))
% 35.95/5.00      | ~ r1_tarski(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
% 35.95/5.00      inference(instantiation,[status(thm)],[c_3]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_1308,plain,
% 35.95/5.00      ( ~ r1_tarski(k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),X0),k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),X0))
% 35.95/5.00      | r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),X0)) ),
% 35.95/5.00      inference(instantiation,[status(thm)],[c_469]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_18133,plain,
% 35.95/5.00      ( ~ r1_tarski(k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(X0)),k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(X0)))
% 35.95/5.00      | r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(X0))) ),
% 35.95/5.00      inference(instantiation,[status(thm)],[c_1308]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_18138,plain,
% 35.95/5.00      ( r1_tarski(k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(X0)),k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(X0))) != iProver_top
% 35.95/5.00      | r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(X0))) = iProver_top ),
% 35.95/5.00      inference(predicate_to_equality,[status(thm)],[c_18133]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_18140,plain,
% 35.95/5.00      ( r1_tarski(k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0)),k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0))) != iProver_top
% 35.95/5.00      | r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0))) = iProver_top ),
% 35.95/5.00      inference(instantiation,[status(thm)],[c_18138]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_1093,plain,
% 35.95/5.00      ( X0 != k1_relat_1(X1)
% 35.95/5.00      | k1_relat_1(sK0) = X0
% 35.95/5.00      | k1_relat_1(sK0) != k1_relat_1(X1) ),
% 35.95/5.00      inference(instantiation,[status(thm)],[c_735]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_2548,plain,
% 35.95/5.00      ( k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) != k1_relat_1(k2_xboole_0(X0,X1))
% 35.95/5.00      | k1_relat_1(sK0) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
% 35.95/5.00      | k1_relat_1(sK0) != k1_relat_1(k2_xboole_0(X0,X1)) ),
% 35.95/5.00      inference(instantiation,[status(thm)],[c_1093]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_10388,plain,
% 35.95/5.00      ( k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(X0)) != k1_relat_1(k2_xboole_0(k3_xboole_0(sK0,sK1),X0))
% 35.95/5.00      | k1_relat_1(sK0) = k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(X0))
% 35.95/5.00      | k1_relat_1(sK0) != k1_relat_1(k2_xboole_0(k3_xboole_0(sK0,sK1),X0)) ),
% 35.95/5.00      inference(instantiation,[status(thm)],[c_2548]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_10390,plain,
% 35.95/5.00      ( k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0)) != k1_relat_1(k2_xboole_0(k3_xboole_0(sK0,sK1),sK0))
% 35.95/5.00      | k1_relat_1(sK0) = k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0))
% 35.95/5.00      | k1_relat_1(sK0) != k1_relat_1(k2_xboole_0(k3_xboole_0(sK0,sK1),sK0)) ),
% 35.95/5.00      inference(instantiation,[status(thm)],[c_10388]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_8354,plain,
% 35.95/5.00      ( ~ r1_tarski(k3_xboole_0(sK0,sK1),X0)
% 35.95/5.00      | k2_xboole_0(k3_xboole_0(sK0,sK1),X0) = X0 ),
% 35.95/5.00      inference(instantiation,[status(thm)],[c_4]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_8356,plain,
% 35.95/5.00      ( ~ r1_tarski(k3_xboole_0(sK0,sK1),sK0)
% 35.95/5.00      | k2_xboole_0(k3_xboole_0(sK0,sK1),sK0) = sK0 ),
% 35.95/5.00      inference(instantiation,[status(thm)],[c_8354]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_183,plain,
% 35.95/5.00      ( X0 != X1 | k1_relat_1(X0) = k1_relat_1(X1) ),
% 35.95/5.00      theory(equality) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_7643,plain,
% 35.95/5.00      ( k2_xboole_0(k3_xboole_0(sK0,sK1),X0) != X1
% 35.95/5.00      | k1_relat_1(k2_xboole_0(k3_xboole_0(sK0,sK1),X0)) = k1_relat_1(X1) ),
% 35.95/5.00      inference(instantiation,[status(thm)],[c_183]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_7648,plain,
% 35.95/5.00      ( k2_xboole_0(k3_xboole_0(sK0,sK1),sK0) != sK0
% 35.95/5.00      | k1_relat_1(k2_xboole_0(k3_xboole_0(sK0,sK1),sK0)) = k1_relat_1(sK0) ),
% 35.95/5.00      inference(instantiation,[status(thm)],[c_7643]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_2510,plain,
% 35.95/5.00      ( v1_relat_1(k3_xboole_0(sK0,sK1)) | ~ v1_relat_1(sK0) ),
% 35.95/5.00      inference(instantiation,[status(thm)],[c_8]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_1252,plain,
% 35.95/5.00      ( ~ v1_relat_1(X0)
% 35.95/5.00      | ~ v1_relat_1(k3_xboole_0(sK0,sK1))
% 35.95/5.00      | k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(X0)) = k1_relat_1(k2_xboole_0(k3_xboole_0(sK0,sK1),X0)) ),
% 35.95/5.00      inference(instantiation,[status(thm)],[c_9]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_1258,plain,
% 35.95/5.00      ( ~ v1_relat_1(k3_xboole_0(sK0,sK1))
% 35.95/5.00      | ~ v1_relat_1(sK0)
% 35.95/5.00      | k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0)) = k1_relat_1(k2_xboole_0(k3_xboole_0(sK0,sK1),sK0)) ),
% 35.95/5.00      inference(instantiation,[status(thm)],[c_1252]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_6,plain,
% 35.95/5.00      ( ~ r1_tarski(X0,X1)
% 35.95/5.00      | ~ r1_tarski(X0,X2)
% 35.95/5.00      | r1_tarski(X0,k3_xboole_0(X1,X2)) ),
% 35.95/5.00      inference(cnf_transformation,[],[f29]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_10,negated_conjecture,
% 35.95/5.00      ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) ),
% 35.95/5.00      inference(cnf_transformation,[],[f35]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_1179,plain,
% 35.95/5.00      ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK1))
% 35.95/5.00      | ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0)) ),
% 35.95/5.00      inference(resolution,[status(thm)],[c_6,c_10]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_1180,plain,
% 35.95/5.00      ( r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK1)) != iProver_top
% 35.95/5.00      | r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0)) != iProver_top ),
% 35.95/5.00      inference(predicate_to_equality,[status(thm)],[c_1179]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_5,plain,
% 35.95/5.00      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 35.95/5.00      inference(cnf_transformation,[],[f28]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_1008,plain,
% 35.95/5.00      ( r1_tarski(k3_xboole_0(sK0,sK1),sK0) ),
% 35.95/5.00      inference(instantiation,[status(thm)],[c_5]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_177,plain,( X0 = X0 ),theory(equality) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_561,plain,
% 35.95/5.00      ( k1_relat_1(k3_xboole_0(sK0,sK1)) = k1_relat_1(k3_xboole_0(sK0,sK1)) ),
% 35.95/5.00      inference(instantiation,[status(thm)],[c_177]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_188,plain,
% 35.95/5.00      ( k1_relat_1(sK0) = k1_relat_1(sK0) | sK0 != sK0 ),
% 35.95/5.00      inference(instantiation,[status(thm)],[c_183]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_0,plain,
% 35.95/5.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 35.95/5.00      inference(cnf_transformation,[],[f25]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_42,plain,
% 35.95/5.00      ( ~ r1_tarski(sK0,sK0) | sK0 = sK0 ),
% 35.95/5.00      inference(instantiation,[status(thm)],[c_0]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(c_38,plain,
% 35.95/5.00      ( r1_tarski(sK0,sK0) ),
% 35.95/5.00      inference(instantiation,[status(thm)],[c_2]) ).
% 35.95/5.00  
% 35.95/5.00  cnf(contradiction,plain,
% 35.95/5.00      ( $false ),
% 35.95/5.00      inference(minisat,
% 35.95/5.00                [status(thm)],
% 35.95/5.00                [c_131257,c_30153,c_24144,c_21999,c_18140,c_10390,c_8356,
% 35.95/5.00                 c_7648,c_2510,c_1258,c_1180,c_1008,c_561,c_188,c_42,
% 35.95/5.00                 c_38,c_12]) ).
% 35.95/5.00  
% 35.95/5.00  
% 35.95/5.00  % SZS output end CNFRefutation for theBenchmark.p
% 35.95/5.00  
% 35.95/5.00  ------                               Statistics
% 35.95/5.00  
% 35.95/5.00  ------ Selected
% 35.95/5.00  
% 35.95/5.00  total_time:                             4.492
% 35.95/5.00  
%------------------------------------------------------------------------------
