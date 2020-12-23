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
% DateTime   : Thu Dec  3 11:48:51 EST 2020

% Result     : Theorem 35.38s
% Output     : CNFRefutation 35.38s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 429 expanded)
%              Number of clauses        :   74 ( 161 expanded)
%              Number of leaves         :   16 (  97 expanded)
%              Depth                    :   17
%              Number of atoms          :  294 (1292 expanded)
%              Number of equality atoms :  134 ( 296 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
           => r1_xboole_0(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
             => r1_xboole_0(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(X0,X1)
          & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(X0,X1)
          & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f46])).

fof(f55,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(X0,X1)
          & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          & v1_relat_1(X1) )
     => ( ~ r1_xboole_0(X0,sK3)
        & r1_xboole_0(k1_relat_1(X0),k1_relat_1(sK3))
        & v1_relat_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_xboole_0(X0,X1)
            & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_xboole_0(sK2,X1)
          & r1_xboole_0(k1_relat_1(sK2),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ~ r1_xboole_0(sK2,sK3)
    & r1_xboole_0(k1_relat_1(sK2),k1_relat_1(sK3))
    & v1_relat_1(sK3)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f47,f55,f54])).

fof(f88,plain,(
    r1_xboole_0(k1_relat_1(sK2),k1_relat_1(sK3)) ),
    inference(cnf_transformation,[],[f56])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f86,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f87,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f7,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f67,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f90,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f67])).

fof(f6,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f82,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f68,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( ( k1_xboole_0 = k1_relat_1(X1)
              & k1_xboole_0 = k1_relat_1(X0) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | k1_xboole_0 != k1_relat_1(X1)
          | k1_xboole_0 != k1_relat_1(X0)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | k1_xboole_0 != k1_relat_1(X1)
          | k1_xboole_0 != k1_relat_1(X0)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f44])).

fof(f85,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_xboole_0 != k1_relat_1(X1)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f89,plain,(
    ~ r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_30,negated_conjecture,
    ( r1_xboole_0(k1_relat_1(sK2),k1_relat_1(sK3)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1145,plain,
    ( r1_xboole_0(k1_relat_1(sK2),k1_relat_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1173,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2273,plain,
    ( r1_xboole_0(k1_relat_1(sK3),k1_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1145,c_1173])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1174,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3097,plain,
    ( k3_xboole_0(k1_relat_1(sK3),k1_relat_1(sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2273,c_1174])).

cnf(c_27,plain,
    ( r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1148,plain,
    ( r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3757,plain,
    ( r1_tarski(k1_relat_1(k3_xboole_0(sK3,sK2)),k1_xboole_0) = iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3097,c_1148])).

cnf(c_32,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_33,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_34,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_4406,plain,
    ( r1_tarski(k1_relat_1(k3_xboole_0(sK3,sK2)),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3757,c_33,c_34])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | ~ r1_xboole_0(X1,X2)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1163,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_7042,plain,
    ( k1_relat_1(k3_xboole_0(sK3,sK2)) = k1_xboole_0
    | r1_tarski(k1_relat_1(k3_xboole_0(sK3,sK2)),X0) != iProver_top
    | r1_xboole_0(k1_xboole_0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4406,c_1163])).

cnf(c_21,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_59,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_20,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_61,plain,
    ( k4_xboole_0(X0,X1) != X0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_63,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_61])).

cnf(c_11,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_7098,plain,
    ( k1_relat_1(k3_xboole_0(sK3,sK2)) = k1_xboole_0
    | r1_tarski(k1_relat_1(k3_xboole_0(sK3,sK2)),k1_xboole_0) != iProver_top
    | r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7042])).

cnf(c_158300,plain,
    ( k1_relat_1(k3_xboole_0(sK3,sK2)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7042,c_33,c_34,c_59,c_63,c_11,c_3757,c_7098])).

cnf(c_9,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1166,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3092,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1166,c_1174])).

cnf(c_7361,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),k3_xboole_0(k1_relat_1(X0),k1_relat_1(k1_xboole_0))) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3092,c_1148])).

cnf(c_25,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1150,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k3_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_7362,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3092,c_1150])).

cnf(c_7384,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),k3_xboole_0(k1_relat_1(X0),k1_relat_1(k1_xboole_0))) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7361,c_7362])).

cnf(c_162014,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),k3_xboole_0(k1_xboole_0,k1_relat_1(k1_xboole_0))) = iProver_top
    | v1_relat_1(k3_xboole_0(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_158300,c_7384])).

cnf(c_2271,plain,
    ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1166,c_1173])).

cnf(c_3095,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2271,c_1174])).

cnf(c_162098,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) = iProver_top
    | v1_relat_1(k3_xboole_0(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_162014,c_3095])).

cnf(c_52965,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ r1_tarski(k1_relat_1(X0),X2)
    | ~ r1_xboole_0(X1,X2)
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_52971,plain,
    ( k1_xboole_0 = k1_relat_1(X0)
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),X2) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_52965])).

cnf(c_52973,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) != iProver_top
    | r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_52971])).

cnf(c_425,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_13787,plain,
    ( k1_relat_1(k1_xboole_0) != X0
    | k1_relat_1(k1_xboole_0) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_425])).

cnf(c_25521,plain,
    ( k1_relat_1(k1_xboole_0) != k1_relat_1(k1_xboole_0)
    | k1_relat_1(k1_xboole_0) = k1_xboole_0
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_13787])).

cnf(c_1381,plain,
    ( v1_relat_1(k3_xboole_0(sK3,X0))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_13794,plain,
    ( v1_relat_1(k3_xboole_0(sK3,sK2))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1381])).

cnf(c_13795,plain,
    ( v1_relat_1(k3_xboole_0(sK3,sK2)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13794])).

cnf(c_17,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_8963,plain,
    ( ~ r1_xboole_0(X0,X0)
    | r1_xboole_0(k3_xboole_0(sK3,X0),k3_xboole_0(sK3,X0)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_8965,plain,
    ( r1_xboole_0(k3_xboole_0(sK3,k1_xboole_0),k3_xboole_0(sK3,k1_xboole_0))
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_8963])).

cnf(c_3094,plain,
    ( k3_xboole_0(k1_relat_1(sK2),k1_relat_1(sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1145,c_1174])).

cnf(c_3534,plain,
    ( r1_tarski(k1_relat_1(k3_xboole_0(sK2,sK3)),k1_xboole_0) = iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3094,c_1148])).

cnf(c_4269,plain,
    ( r1_tarski(k1_relat_1(k3_xboole_0(sK2,sK3)),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3534,c_33,c_34])).

cnf(c_7040,plain,
    ( k1_relat_1(k3_xboole_0(sK2,sK3)) = k1_xboole_0
    | r1_tarski(k1_relat_1(k3_xboole_0(sK2,sK3)),X0) != iProver_top
    | r1_xboole_0(k1_xboole_0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4269,c_1163])).

cnf(c_7092,plain,
    ( k1_relat_1(k3_xboole_0(sK2,sK3)) = k1_xboole_0
    | r1_tarski(k1_relat_1(k3_xboole_0(sK2,sK3)),k1_xboole_0) != iProver_top
    | r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7040])).

cnf(c_1386,plain,
    ( v1_relat_1(k3_xboole_0(sK2,X0))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_5540,plain,
    ( v1_relat_1(k3_xboole_0(sK2,sK3))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1386])).

cnf(c_10,plain,
    ( ~ r1_xboole_0(X0,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_3561,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK3,X0),k3_xboole_0(sK3,X0))
    | k1_xboole_0 = k3_xboole_0(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_3565,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK3,k1_xboole_0),k3_xboole_0(sK3,k1_xboole_0))
    | k1_xboole_0 = k3_xboole_0(sK3,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3561])).

cnf(c_431,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1560,plain,
    ( v1_relat_1(X0)
    | ~ v1_relat_1(k3_xboole_0(sK3,X1))
    | X0 != k3_xboole_0(sK3,X1) ),
    inference(instantiation,[status(thm)],[c_431])).

cnf(c_1572,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK3,k1_xboole_0))
    | v1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k3_xboole_0(sK3,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1560])).

cnf(c_28,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | X1 = X0
    | k1_relat_1(X0) != k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1482,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK2,sK3))
    | ~ v1_relat_1(k1_xboole_0)
    | k3_xboole_0(sK2,sK3) = k1_xboole_0
    | k1_relat_1(k3_xboole_0(sK2,sK3)) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_0,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1401,plain,
    ( r1_xboole_0(sK2,sK3)
    | k3_xboole_0(sK2,sK3) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1383,plain,
    ( v1_relat_1(k3_xboole_0(sK3,k1_xboole_0))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1381])).

cnf(c_432,plain,
    ( X0 != X1
    | k1_relat_1(X0) = k1_relat_1(X1) ),
    theory(equality)).

cnf(c_439,plain,
    ( k1_relat_1(k1_xboole_0) = k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_432])).

cnf(c_86,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_29,negated_conjecture,
    ( ~ r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f89])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_162098,c_52973,c_25521,c_13795,c_8965,c_7092,c_5540,c_3565,c_3534,c_1572,c_1482,c_1401,c_1383,c_439,c_86,c_11,c_63,c_59,c_29,c_34,c_31,c_33,c_32])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:59:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 35.38/5.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 35.38/5.00  
% 35.38/5.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 35.38/5.00  
% 35.38/5.00  ------  iProver source info
% 35.38/5.00  
% 35.38/5.00  git: date: 2020-06-30 10:37:57 +0100
% 35.38/5.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 35.38/5.00  git: non_committed_changes: false
% 35.38/5.00  git: last_make_outside_of_git: false
% 35.38/5.00  
% 35.38/5.00  ------ 
% 35.38/5.00  
% 35.38/5.00  ------ Input Options
% 35.38/5.00  
% 35.38/5.00  --out_options                           all
% 35.38/5.00  --tptp_safe_out                         true
% 35.38/5.00  --problem_path                          ""
% 35.38/5.00  --include_path                          ""
% 35.38/5.00  --clausifier                            res/vclausify_rel
% 35.38/5.00  --clausifier_options                    --mode clausify
% 35.38/5.00  --stdin                                 false
% 35.38/5.00  --stats_out                             all
% 35.38/5.00  
% 35.38/5.00  ------ General Options
% 35.38/5.00  
% 35.38/5.00  --fof                                   false
% 35.38/5.00  --time_out_real                         305.
% 35.38/5.00  --time_out_virtual                      -1.
% 35.38/5.00  --symbol_type_check                     false
% 35.38/5.00  --clausify_out                          false
% 35.38/5.00  --sig_cnt_out                           false
% 35.38/5.00  --trig_cnt_out                          false
% 35.38/5.00  --trig_cnt_out_tolerance                1.
% 35.38/5.00  --trig_cnt_out_sk_spl                   false
% 35.38/5.00  --abstr_cl_out                          false
% 35.38/5.00  
% 35.38/5.00  ------ Global Options
% 35.38/5.00  
% 35.38/5.00  --schedule                              default
% 35.38/5.00  --add_important_lit                     false
% 35.38/5.00  --prop_solver_per_cl                    1000
% 35.38/5.00  --min_unsat_core                        false
% 35.38/5.00  --soft_assumptions                      false
% 35.38/5.00  --soft_lemma_size                       3
% 35.38/5.00  --prop_impl_unit_size                   0
% 35.38/5.00  --prop_impl_unit                        []
% 35.38/5.00  --share_sel_clauses                     true
% 35.38/5.00  --reset_solvers                         false
% 35.38/5.00  --bc_imp_inh                            [conj_cone]
% 35.38/5.00  --conj_cone_tolerance                   3.
% 35.38/5.00  --extra_neg_conj                        none
% 35.38/5.00  --large_theory_mode                     true
% 35.38/5.00  --prolific_symb_bound                   200
% 35.38/5.00  --lt_threshold                          2000
% 35.38/5.00  --clause_weak_htbl                      true
% 35.38/5.00  --gc_record_bc_elim                     false
% 35.38/5.00  
% 35.38/5.00  ------ Preprocessing Options
% 35.38/5.00  
% 35.38/5.00  --preprocessing_flag                    true
% 35.38/5.00  --time_out_prep_mult                    0.1
% 35.38/5.00  --splitting_mode                        input
% 35.38/5.00  --splitting_grd                         true
% 35.38/5.00  --splitting_cvd                         false
% 35.38/5.00  --splitting_cvd_svl                     false
% 35.38/5.00  --splitting_nvd                         32
% 35.38/5.00  --sub_typing                            true
% 35.38/5.00  --prep_gs_sim                           true
% 35.38/5.00  --prep_unflatten                        true
% 35.38/5.00  --prep_res_sim                          true
% 35.38/5.00  --prep_upred                            true
% 35.38/5.00  --prep_sem_filter                       exhaustive
% 35.38/5.00  --prep_sem_filter_out                   false
% 35.38/5.00  --pred_elim                             true
% 35.38/5.00  --res_sim_input                         true
% 35.38/5.00  --eq_ax_congr_red                       true
% 35.38/5.00  --pure_diseq_elim                       true
% 35.38/5.00  --brand_transform                       false
% 35.38/5.00  --non_eq_to_eq                          false
% 35.38/5.00  --prep_def_merge                        true
% 35.38/5.00  --prep_def_merge_prop_impl              false
% 35.38/5.00  --prep_def_merge_mbd                    true
% 35.38/5.00  --prep_def_merge_tr_red                 false
% 35.38/5.00  --prep_def_merge_tr_cl                  false
% 35.38/5.00  --smt_preprocessing                     true
% 35.38/5.00  --smt_ac_axioms                         fast
% 35.38/5.00  --preprocessed_out                      false
% 35.38/5.00  --preprocessed_stats                    false
% 35.38/5.00  
% 35.38/5.00  ------ Abstraction refinement Options
% 35.38/5.00  
% 35.38/5.00  --abstr_ref                             []
% 35.38/5.00  --abstr_ref_prep                        false
% 35.38/5.00  --abstr_ref_until_sat                   false
% 35.38/5.00  --abstr_ref_sig_restrict                funpre
% 35.38/5.00  --abstr_ref_af_restrict_to_split_sk     false
% 35.38/5.00  --abstr_ref_under                       []
% 35.38/5.00  
% 35.38/5.00  ------ SAT Options
% 35.38/5.00  
% 35.38/5.00  --sat_mode                              false
% 35.38/5.00  --sat_fm_restart_options                ""
% 35.38/5.00  --sat_gr_def                            false
% 35.38/5.00  --sat_epr_types                         true
% 35.38/5.00  --sat_non_cyclic_types                  false
% 35.38/5.00  --sat_finite_models                     false
% 35.38/5.00  --sat_fm_lemmas                         false
% 35.38/5.00  --sat_fm_prep                           false
% 35.38/5.00  --sat_fm_uc_incr                        true
% 35.38/5.00  --sat_out_model                         small
% 35.38/5.00  --sat_out_clauses                       false
% 35.38/5.00  
% 35.38/5.00  ------ QBF Options
% 35.38/5.00  
% 35.38/5.00  --qbf_mode                              false
% 35.38/5.00  --qbf_elim_univ                         false
% 35.38/5.00  --qbf_dom_inst                          none
% 35.38/5.00  --qbf_dom_pre_inst                      false
% 35.38/5.00  --qbf_sk_in                             false
% 35.38/5.00  --qbf_pred_elim                         true
% 35.38/5.00  --qbf_split                             512
% 35.38/5.00  
% 35.38/5.00  ------ BMC1 Options
% 35.38/5.00  
% 35.38/5.00  --bmc1_incremental                      false
% 35.38/5.00  --bmc1_axioms                           reachable_all
% 35.38/5.00  --bmc1_min_bound                        0
% 35.38/5.00  --bmc1_max_bound                        -1
% 35.38/5.00  --bmc1_max_bound_default                -1
% 35.38/5.00  --bmc1_symbol_reachability              true
% 35.38/5.00  --bmc1_property_lemmas                  false
% 35.38/5.00  --bmc1_k_induction                      false
% 35.38/5.00  --bmc1_non_equiv_states                 false
% 35.38/5.00  --bmc1_deadlock                         false
% 35.38/5.00  --bmc1_ucm                              false
% 35.38/5.00  --bmc1_add_unsat_core                   none
% 35.38/5.00  --bmc1_unsat_core_children              false
% 35.38/5.00  --bmc1_unsat_core_extrapolate_axioms    false
% 35.38/5.00  --bmc1_out_stat                         full
% 35.38/5.00  --bmc1_ground_init                      false
% 35.38/5.00  --bmc1_pre_inst_next_state              false
% 35.38/5.00  --bmc1_pre_inst_state                   false
% 35.38/5.00  --bmc1_pre_inst_reach_state             false
% 35.38/5.00  --bmc1_out_unsat_core                   false
% 35.38/5.00  --bmc1_aig_witness_out                  false
% 35.38/5.00  --bmc1_verbose                          false
% 35.38/5.00  --bmc1_dump_clauses_tptp                false
% 35.38/5.00  --bmc1_dump_unsat_core_tptp             false
% 35.38/5.00  --bmc1_dump_file                        -
% 35.38/5.00  --bmc1_ucm_expand_uc_limit              128
% 35.38/5.00  --bmc1_ucm_n_expand_iterations          6
% 35.38/5.00  --bmc1_ucm_extend_mode                  1
% 35.38/5.00  --bmc1_ucm_init_mode                    2
% 35.38/5.00  --bmc1_ucm_cone_mode                    none
% 35.38/5.00  --bmc1_ucm_reduced_relation_type        0
% 35.38/5.00  --bmc1_ucm_relax_model                  4
% 35.38/5.00  --bmc1_ucm_full_tr_after_sat            true
% 35.38/5.00  --bmc1_ucm_expand_neg_assumptions       false
% 35.38/5.00  --bmc1_ucm_layered_model                none
% 35.38/5.00  --bmc1_ucm_max_lemma_size               10
% 35.38/5.00  
% 35.38/5.00  ------ AIG Options
% 35.38/5.00  
% 35.38/5.00  --aig_mode                              false
% 35.38/5.00  
% 35.38/5.00  ------ Instantiation Options
% 35.38/5.00  
% 35.38/5.00  --instantiation_flag                    true
% 35.38/5.00  --inst_sos_flag                         false
% 35.38/5.00  --inst_sos_phase                        true
% 35.38/5.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.38/5.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.38/5.00  --inst_lit_sel_side                     num_symb
% 35.38/5.00  --inst_solver_per_active                1400
% 35.38/5.00  --inst_solver_calls_frac                1.
% 35.38/5.00  --inst_passive_queue_type               priority_queues
% 35.38/5.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.38/5.00  --inst_passive_queues_freq              [25;2]
% 35.38/5.00  --inst_dismatching                      true
% 35.38/5.00  --inst_eager_unprocessed_to_passive     true
% 35.38/5.00  --inst_prop_sim_given                   true
% 35.38/5.00  --inst_prop_sim_new                     false
% 35.38/5.00  --inst_subs_new                         false
% 35.38/5.00  --inst_eq_res_simp                      false
% 35.38/5.00  --inst_subs_given                       false
% 35.38/5.00  --inst_orphan_elimination               true
% 35.38/5.00  --inst_learning_loop_flag               true
% 35.38/5.00  --inst_learning_start                   3000
% 35.38/5.00  --inst_learning_factor                  2
% 35.38/5.00  --inst_start_prop_sim_after_learn       3
% 35.38/5.00  --inst_sel_renew                        solver
% 35.38/5.00  --inst_lit_activity_flag                true
% 35.38/5.00  --inst_restr_to_given                   false
% 35.38/5.00  --inst_activity_threshold               500
% 35.38/5.00  --inst_out_proof                        true
% 35.38/5.00  
% 35.38/5.00  ------ Resolution Options
% 35.38/5.00  
% 35.38/5.00  --resolution_flag                       true
% 35.38/5.00  --res_lit_sel                           adaptive
% 35.38/5.00  --res_lit_sel_side                      none
% 35.38/5.00  --res_ordering                          kbo
% 35.38/5.00  --res_to_prop_solver                    active
% 35.38/5.00  --res_prop_simpl_new                    false
% 35.38/5.00  --res_prop_simpl_given                  true
% 35.38/5.00  --res_passive_queue_type                priority_queues
% 35.38/5.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.38/5.00  --res_passive_queues_freq               [15;5]
% 35.38/5.00  --res_forward_subs                      full
% 35.38/5.00  --res_backward_subs                     full
% 35.38/5.00  --res_forward_subs_resolution           true
% 35.38/5.00  --res_backward_subs_resolution          true
% 35.38/5.00  --res_orphan_elimination                true
% 35.38/5.00  --res_time_limit                        2.
% 35.38/5.00  --res_out_proof                         true
% 35.38/5.00  
% 35.38/5.00  ------ Superposition Options
% 35.38/5.00  
% 35.38/5.00  --superposition_flag                    true
% 35.38/5.00  --sup_passive_queue_type                priority_queues
% 35.38/5.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.38/5.00  --sup_passive_queues_freq               [8;1;4]
% 35.38/5.00  --demod_completeness_check              fast
% 35.38/5.00  --demod_use_ground                      true
% 35.38/5.00  --sup_to_prop_solver                    passive
% 35.38/5.00  --sup_prop_simpl_new                    true
% 35.38/5.00  --sup_prop_simpl_given                  true
% 35.38/5.00  --sup_fun_splitting                     false
% 35.38/5.00  --sup_smt_interval                      50000
% 35.38/5.00  
% 35.38/5.00  ------ Superposition Simplification Setup
% 35.38/5.00  
% 35.38/5.00  --sup_indices_passive                   []
% 35.38/5.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 35.38/5.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 35.38/5.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 35.38/5.00  --sup_full_triv                         [TrivRules;PropSubs]
% 35.38/5.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 35.38/5.00  --sup_full_bw                           [BwDemod]
% 35.38/5.00  --sup_immed_triv                        [TrivRules]
% 35.38/5.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.38/5.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 35.38/5.00  --sup_immed_bw_main                     []
% 35.38/5.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 35.38/5.00  --sup_input_triv                        [Unflattening;TrivRules]
% 35.38/5.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 35.38/5.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 35.38/5.00  
% 35.38/5.00  ------ Combination Options
% 35.38/5.00  
% 35.38/5.00  --comb_res_mult                         3
% 35.38/5.00  --comb_sup_mult                         2
% 35.38/5.00  --comb_inst_mult                        10
% 35.38/5.00  
% 35.38/5.00  ------ Debug Options
% 35.38/5.00  
% 35.38/5.00  --dbg_backtrace                         false
% 35.38/5.00  --dbg_dump_prop_clauses                 false
% 35.38/5.00  --dbg_dump_prop_clauses_file            -
% 35.38/5.00  --dbg_out_stat                          false
% 35.38/5.00  ------ Parsing...
% 35.38/5.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 35.38/5.00  
% 35.38/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 35.38/5.00  
% 35.38/5.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 35.38/5.00  
% 35.38/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.38/5.00  ------ Proving...
% 35.38/5.00  ------ Problem Properties 
% 35.38/5.00  
% 35.38/5.00  
% 35.38/5.00  clauses                                 33
% 35.38/5.00  conjectures                             4
% 35.38/5.00  EPR                                     10
% 35.38/5.00  Horn                                    30
% 35.38/5.00  unary                                   7
% 35.38/5.00  binary                                  20
% 35.38/5.00  lits                                    68
% 35.38/5.00  lits eq                                 10
% 35.38/5.00  fd_pure                                 0
% 35.38/5.00  fd_pseudo                               0
% 35.38/5.00  fd_cond                                 2
% 35.38/5.00  fd_pseudo_cond                          1
% 35.38/5.00  AC symbols                              0
% 35.38/5.00  
% 35.38/5.00  ------ Schedule dynamic 5 is on 
% 35.38/5.00  
% 35.38/5.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 35.38/5.00  
% 35.38/5.00  
% 35.38/5.00  ------ 
% 35.38/5.00  Current options:
% 35.38/5.00  ------ 
% 35.38/5.00  
% 35.38/5.00  ------ Input Options
% 35.38/5.00  
% 35.38/5.00  --out_options                           all
% 35.38/5.00  --tptp_safe_out                         true
% 35.38/5.00  --problem_path                          ""
% 35.38/5.00  --include_path                          ""
% 35.38/5.00  --clausifier                            res/vclausify_rel
% 35.38/5.00  --clausifier_options                    --mode clausify
% 35.38/5.00  --stdin                                 false
% 35.38/5.00  --stats_out                             all
% 35.38/5.00  
% 35.38/5.00  ------ General Options
% 35.38/5.00  
% 35.38/5.00  --fof                                   false
% 35.38/5.00  --time_out_real                         305.
% 35.38/5.00  --time_out_virtual                      -1.
% 35.38/5.00  --symbol_type_check                     false
% 35.38/5.00  --clausify_out                          false
% 35.38/5.00  --sig_cnt_out                           false
% 35.38/5.00  --trig_cnt_out                          false
% 35.38/5.00  --trig_cnt_out_tolerance                1.
% 35.38/5.00  --trig_cnt_out_sk_spl                   false
% 35.38/5.00  --abstr_cl_out                          false
% 35.38/5.00  
% 35.38/5.00  ------ Global Options
% 35.38/5.00  
% 35.38/5.00  --schedule                              default
% 35.38/5.00  --add_important_lit                     false
% 35.38/5.00  --prop_solver_per_cl                    1000
% 35.38/5.00  --min_unsat_core                        false
% 35.38/5.00  --soft_assumptions                      false
% 35.38/5.00  --soft_lemma_size                       3
% 35.38/5.00  --prop_impl_unit_size                   0
% 35.38/5.00  --prop_impl_unit                        []
% 35.38/5.00  --share_sel_clauses                     true
% 35.38/5.00  --reset_solvers                         false
% 35.38/5.00  --bc_imp_inh                            [conj_cone]
% 35.38/5.00  --conj_cone_tolerance                   3.
% 35.38/5.00  --extra_neg_conj                        none
% 35.38/5.00  --large_theory_mode                     true
% 35.38/5.00  --prolific_symb_bound                   200
% 35.38/5.00  --lt_threshold                          2000
% 35.38/5.00  --clause_weak_htbl                      true
% 35.38/5.00  --gc_record_bc_elim                     false
% 35.38/5.00  
% 35.38/5.00  ------ Preprocessing Options
% 35.38/5.00  
% 35.38/5.00  --preprocessing_flag                    true
% 35.38/5.00  --time_out_prep_mult                    0.1
% 35.38/5.00  --splitting_mode                        input
% 35.38/5.00  --splitting_grd                         true
% 35.38/5.00  --splitting_cvd                         false
% 35.38/5.00  --splitting_cvd_svl                     false
% 35.38/5.00  --splitting_nvd                         32
% 35.38/5.00  --sub_typing                            true
% 35.38/5.00  --prep_gs_sim                           true
% 35.38/5.00  --prep_unflatten                        true
% 35.38/5.00  --prep_res_sim                          true
% 35.38/5.00  --prep_upred                            true
% 35.38/5.00  --prep_sem_filter                       exhaustive
% 35.38/5.00  --prep_sem_filter_out                   false
% 35.38/5.00  --pred_elim                             true
% 35.38/5.00  --res_sim_input                         true
% 35.38/5.00  --eq_ax_congr_red                       true
% 35.38/5.00  --pure_diseq_elim                       true
% 35.38/5.00  --brand_transform                       false
% 35.38/5.00  --non_eq_to_eq                          false
% 35.38/5.00  --prep_def_merge                        true
% 35.38/5.00  --prep_def_merge_prop_impl              false
% 35.38/5.00  --prep_def_merge_mbd                    true
% 35.38/5.00  --prep_def_merge_tr_red                 false
% 35.38/5.00  --prep_def_merge_tr_cl                  false
% 35.38/5.00  --smt_preprocessing                     true
% 35.38/5.00  --smt_ac_axioms                         fast
% 35.38/5.00  --preprocessed_out                      false
% 35.38/5.00  --preprocessed_stats                    false
% 35.38/5.00  
% 35.38/5.00  ------ Abstraction refinement Options
% 35.38/5.00  
% 35.38/5.00  --abstr_ref                             []
% 35.38/5.00  --abstr_ref_prep                        false
% 35.38/5.00  --abstr_ref_until_sat                   false
% 35.38/5.00  --abstr_ref_sig_restrict                funpre
% 35.38/5.00  --abstr_ref_af_restrict_to_split_sk     false
% 35.38/5.00  --abstr_ref_under                       []
% 35.38/5.00  
% 35.38/5.00  ------ SAT Options
% 35.38/5.00  
% 35.38/5.00  --sat_mode                              false
% 35.38/5.00  --sat_fm_restart_options                ""
% 35.38/5.00  --sat_gr_def                            false
% 35.38/5.00  --sat_epr_types                         true
% 35.38/5.00  --sat_non_cyclic_types                  false
% 35.38/5.00  --sat_finite_models                     false
% 35.38/5.00  --sat_fm_lemmas                         false
% 35.38/5.00  --sat_fm_prep                           false
% 35.38/5.00  --sat_fm_uc_incr                        true
% 35.38/5.00  --sat_out_model                         small
% 35.38/5.00  --sat_out_clauses                       false
% 35.38/5.00  
% 35.38/5.00  ------ QBF Options
% 35.38/5.00  
% 35.38/5.00  --qbf_mode                              false
% 35.38/5.00  --qbf_elim_univ                         false
% 35.38/5.00  --qbf_dom_inst                          none
% 35.38/5.00  --qbf_dom_pre_inst                      false
% 35.38/5.00  --qbf_sk_in                             false
% 35.38/5.00  --qbf_pred_elim                         true
% 35.38/5.00  --qbf_split                             512
% 35.38/5.00  
% 35.38/5.00  ------ BMC1 Options
% 35.38/5.00  
% 35.38/5.00  --bmc1_incremental                      false
% 35.38/5.00  --bmc1_axioms                           reachable_all
% 35.38/5.00  --bmc1_min_bound                        0
% 35.38/5.00  --bmc1_max_bound                        -1
% 35.38/5.00  --bmc1_max_bound_default                -1
% 35.38/5.00  --bmc1_symbol_reachability              true
% 35.38/5.00  --bmc1_property_lemmas                  false
% 35.38/5.00  --bmc1_k_induction                      false
% 35.38/5.00  --bmc1_non_equiv_states                 false
% 35.38/5.00  --bmc1_deadlock                         false
% 35.38/5.00  --bmc1_ucm                              false
% 35.38/5.00  --bmc1_add_unsat_core                   none
% 35.38/5.00  --bmc1_unsat_core_children              false
% 35.38/5.00  --bmc1_unsat_core_extrapolate_axioms    false
% 35.38/5.00  --bmc1_out_stat                         full
% 35.38/5.00  --bmc1_ground_init                      false
% 35.38/5.00  --bmc1_pre_inst_next_state              false
% 35.38/5.00  --bmc1_pre_inst_state                   false
% 35.38/5.00  --bmc1_pre_inst_reach_state             false
% 35.38/5.00  --bmc1_out_unsat_core                   false
% 35.38/5.00  --bmc1_aig_witness_out                  false
% 35.38/5.00  --bmc1_verbose                          false
% 35.38/5.00  --bmc1_dump_clauses_tptp                false
% 35.38/5.00  --bmc1_dump_unsat_core_tptp             false
% 35.38/5.00  --bmc1_dump_file                        -
% 35.38/5.00  --bmc1_ucm_expand_uc_limit              128
% 35.38/5.00  --bmc1_ucm_n_expand_iterations          6
% 35.38/5.00  --bmc1_ucm_extend_mode                  1
% 35.38/5.00  --bmc1_ucm_init_mode                    2
% 35.38/5.00  --bmc1_ucm_cone_mode                    none
% 35.38/5.00  --bmc1_ucm_reduced_relation_type        0
% 35.38/5.00  --bmc1_ucm_relax_model                  4
% 35.38/5.00  --bmc1_ucm_full_tr_after_sat            true
% 35.38/5.00  --bmc1_ucm_expand_neg_assumptions       false
% 35.38/5.00  --bmc1_ucm_layered_model                none
% 35.38/5.00  --bmc1_ucm_max_lemma_size               10
% 35.38/5.00  
% 35.38/5.00  ------ AIG Options
% 35.38/5.00  
% 35.38/5.00  --aig_mode                              false
% 35.38/5.00  
% 35.38/5.00  ------ Instantiation Options
% 35.38/5.00  
% 35.38/5.00  --instantiation_flag                    true
% 35.38/5.00  --inst_sos_flag                         false
% 35.38/5.00  --inst_sos_phase                        true
% 35.38/5.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.38/5.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.38/5.00  --inst_lit_sel_side                     none
% 35.38/5.00  --inst_solver_per_active                1400
% 35.38/5.00  --inst_solver_calls_frac                1.
% 35.38/5.00  --inst_passive_queue_type               priority_queues
% 35.38/5.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.38/5.00  --inst_passive_queues_freq              [25;2]
% 35.38/5.00  --inst_dismatching                      true
% 35.38/5.00  --inst_eager_unprocessed_to_passive     true
% 35.38/5.00  --inst_prop_sim_given                   true
% 35.38/5.00  --inst_prop_sim_new                     false
% 35.38/5.00  --inst_subs_new                         false
% 35.38/5.00  --inst_eq_res_simp                      false
% 35.38/5.00  --inst_subs_given                       false
% 35.38/5.00  --inst_orphan_elimination               true
% 35.38/5.00  --inst_learning_loop_flag               true
% 35.38/5.00  --inst_learning_start                   3000
% 35.38/5.00  --inst_learning_factor                  2
% 35.38/5.00  --inst_start_prop_sim_after_learn       3
% 35.38/5.00  --inst_sel_renew                        solver
% 35.38/5.00  --inst_lit_activity_flag                true
% 35.38/5.00  --inst_restr_to_given                   false
% 35.38/5.00  --inst_activity_threshold               500
% 35.38/5.00  --inst_out_proof                        true
% 35.38/5.00  
% 35.38/5.00  ------ Resolution Options
% 35.38/5.00  
% 35.38/5.00  --resolution_flag                       false
% 35.38/5.00  --res_lit_sel                           adaptive
% 35.38/5.00  --res_lit_sel_side                      none
% 35.38/5.00  --res_ordering                          kbo
% 35.38/5.00  --res_to_prop_solver                    active
% 35.38/5.00  --res_prop_simpl_new                    false
% 35.38/5.00  --res_prop_simpl_given                  true
% 35.38/5.00  --res_passive_queue_type                priority_queues
% 35.38/5.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.38/5.00  --res_passive_queues_freq               [15;5]
% 35.38/5.00  --res_forward_subs                      full
% 35.38/5.00  --res_backward_subs                     full
% 35.38/5.00  --res_forward_subs_resolution           true
% 35.38/5.00  --res_backward_subs_resolution          true
% 35.38/5.00  --res_orphan_elimination                true
% 35.38/5.00  --res_time_limit                        2.
% 35.38/5.00  --res_out_proof                         true
% 35.38/5.00  
% 35.38/5.00  ------ Superposition Options
% 35.38/5.00  
% 35.38/5.00  --superposition_flag                    true
% 35.38/5.00  --sup_passive_queue_type                priority_queues
% 35.38/5.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.38/5.00  --sup_passive_queues_freq               [8;1;4]
% 35.38/5.00  --demod_completeness_check              fast
% 35.38/5.00  --demod_use_ground                      true
% 35.38/5.00  --sup_to_prop_solver                    passive
% 35.38/5.00  --sup_prop_simpl_new                    true
% 35.38/5.00  --sup_prop_simpl_given                  true
% 35.38/5.00  --sup_fun_splitting                     false
% 35.38/5.00  --sup_smt_interval                      50000
% 35.38/5.00  
% 35.38/5.00  ------ Superposition Simplification Setup
% 35.38/5.00  
% 35.38/5.00  --sup_indices_passive                   []
% 35.38/5.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 35.38/5.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 35.38/5.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 35.38/5.00  --sup_full_triv                         [TrivRules;PropSubs]
% 35.38/5.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 35.38/5.00  --sup_full_bw                           [BwDemod]
% 35.38/5.00  --sup_immed_triv                        [TrivRules]
% 35.38/5.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.38/5.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 35.38/5.01  --sup_immed_bw_main                     []
% 35.38/5.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 35.38/5.01  --sup_input_triv                        [Unflattening;TrivRules]
% 35.38/5.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 35.38/5.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 35.38/5.01  
% 35.38/5.01  ------ Combination Options
% 35.38/5.01  
% 35.38/5.01  --comb_res_mult                         3
% 35.38/5.01  --comb_sup_mult                         2
% 35.38/5.01  --comb_inst_mult                        10
% 35.38/5.01  
% 35.38/5.01  ------ Debug Options
% 35.38/5.01  
% 35.38/5.01  --dbg_backtrace                         false
% 35.38/5.01  --dbg_dump_prop_clauses                 false
% 35.38/5.01  --dbg_dump_prop_clauses_file            -
% 35.38/5.01  --dbg_out_stat                          false
% 35.38/5.01  
% 35.38/5.01  
% 35.38/5.01  
% 35.38/5.01  
% 35.38/5.01  ------ Proving...
% 35.38/5.01  
% 35.38/5.01  
% 35.38/5.01  % SZS status Theorem for theBenchmark.p
% 35.38/5.01  
% 35.38/5.01  % SZS output start CNFRefutation for theBenchmark.p
% 35.38/5.01  
% 35.38/5.01  fof(f22,conjecture,(
% 35.38/5.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) => r1_xboole_0(X0,X1))))),
% 35.38/5.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.38/5.01  
% 35.38/5.01  fof(f23,negated_conjecture,(
% 35.38/5.01    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) => r1_xboole_0(X0,X1))))),
% 35.38/5.01    inference(negated_conjecture,[],[f22])).
% 35.38/5.01  
% 35.38/5.01  fof(f46,plain,(
% 35.38/5.01    ? [X0] : (? [X1] : ((~r1_xboole_0(X0,X1) & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 35.38/5.01    inference(ennf_transformation,[],[f23])).
% 35.38/5.01  
% 35.38/5.01  fof(f47,plain,(
% 35.38/5.01    ? [X0] : (? [X1] : (~r1_xboole_0(X0,X1) & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 35.38/5.01    inference(flattening,[],[f46])).
% 35.38/5.01  
% 35.38/5.01  fof(f55,plain,(
% 35.38/5.01    ( ! [X0] : (? [X1] : (~r1_xboole_0(X0,X1) & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_xboole_0(X0,sK3) & r1_xboole_0(k1_relat_1(X0),k1_relat_1(sK3)) & v1_relat_1(sK3))) )),
% 35.38/5.01    introduced(choice_axiom,[])).
% 35.38/5.01  
% 35.38/5.01  fof(f54,plain,(
% 35.38/5.01    ? [X0] : (? [X1] : (~r1_xboole_0(X0,X1) & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_xboole_0(sK2,X1) & r1_xboole_0(k1_relat_1(sK2),k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(sK2))),
% 35.38/5.01    introduced(choice_axiom,[])).
% 35.38/5.01  
% 35.38/5.01  fof(f56,plain,(
% 35.38/5.01    (~r1_xboole_0(sK2,sK3) & r1_xboole_0(k1_relat_1(sK2),k1_relat_1(sK3)) & v1_relat_1(sK3)) & v1_relat_1(sK2)),
% 35.38/5.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f47,f55,f54])).
% 35.38/5.01  
% 35.38/5.01  fof(f88,plain,(
% 35.38/5.01    r1_xboole_0(k1_relat_1(sK2),k1_relat_1(sK3))),
% 35.38/5.01    inference(cnf_transformation,[],[f56])).
% 35.38/5.01  
% 35.38/5.01  fof(f2,axiom,(
% 35.38/5.01    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 35.38/5.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.38/5.01  
% 35.38/5.01  fof(f26,plain,(
% 35.38/5.01    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 35.38/5.01    inference(ennf_transformation,[],[f2])).
% 35.38/5.01  
% 35.38/5.01  fof(f59,plain,(
% 35.38/5.01    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 35.38/5.01    inference(cnf_transformation,[],[f26])).
% 35.38/5.01  
% 35.38/5.01  fof(f1,axiom,(
% 35.38/5.01    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 35.38/5.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.38/5.01  
% 35.38/5.01  fof(f48,plain,(
% 35.38/5.01    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 35.38/5.01    inference(nnf_transformation,[],[f1])).
% 35.38/5.01  
% 35.38/5.01  fof(f57,plain,(
% 35.38/5.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 35.38/5.01    inference(cnf_transformation,[],[f48])).
% 35.38/5.01  
% 35.38/5.01  fof(f20,axiom,(
% 35.38/5.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))))),
% 35.38/5.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.38/5.01  
% 35.38/5.01  fof(f43,plain,(
% 35.38/5.01    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 35.38/5.01    inference(ennf_transformation,[],[f20])).
% 35.38/5.01  
% 35.38/5.01  fof(f84,plain,(
% 35.38/5.01    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 35.38/5.01    inference(cnf_transformation,[],[f43])).
% 35.38/5.01  
% 35.38/5.01  fof(f86,plain,(
% 35.38/5.01    v1_relat_1(sK2)),
% 35.38/5.01    inference(cnf_transformation,[],[f56])).
% 35.38/5.01  
% 35.38/5.01  fof(f87,plain,(
% 35.38/5.01    v1_relat_1(sK3)),
% 35.38/5.01    inference(cnf_transformation,[],[f56])).
% 35.38/5.01  
% 35.38/5.01  fof(f8,axiom,(
% 35.38/5.01    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k1_xboole_0 = X0)),
% 35.38/5.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.38/5.01  
% 35.38/5.01  fof(f32,plain,(
% 35.38/5.01    ! [X0,X1,X2] : (k1_xboole_0 = X0 | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 35.38/5.01    inference(ennf_transformation,[],[f8])).
% 35.38/5.01  
% 35.38/5.01  fof(f33,plain,(
% 35.38/5.01    ! [X0,X1,X2] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 35.38/5.01    inference(flattening,[],[f32])).
% 35.38/5.01  
% 35.38/5.01  fof(f69,plain,(
% 35.38/5.01    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 35.38/5.01    inference(cnf_transformation,[],[f33])).
% 35.38/5.01  
% 35.38/5.01  fof(f14,axiom,(
% 35.38/5.01    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 35.38/5.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.38/5.01  
% 35.38/5.01  fof(f53,plain,(
% 35.38/5.01    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 35.38/5.01    inference(nnf_transformation,[],[f14])).
% 35.38/5.01  
% 35.38/5.01  fof(f77,plain,(
% 35.38/5.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 35.38/5.01    inference(cnf_transformation,[],[f53])).
% 35.38/5.01  
% 35.38/5.01  fof(f78,plain,(
% 35.38/5.01    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 35.38/5.01    inference(cnf_transformation,[],[f53])).
% 35.38/5.01  
% 35.38/5.01  fof(f7,axiom,(
% 35.38/5.01    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 35.38/5.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.38/5.01  
% 35.38/5.01  fof(f31,plain,(
% 35.38/5.01    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 35.38/5.01    inference(ennf_transformation,[],[f7])).
% 35.38/5.01  
% 35.38/5.01  fof(f67,plain,(
% 35.38/5.01    ( ! [X0] : (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)) )),
% 35.38/5.01    inference(cnf_transformation,[],[f31])).
% 35.38/5.01  
% 35.38/5.01  fof(f90,plain,(
% 35.38/5.01    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 35.38/5.01    inference(equality_resolution,[],[f67])).
% 35.38/5.01  
% 35.38/5.01  fof(f6,axiom,(
% 35.38/5.01    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 35.38/5.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.38/5.01  
% 35.38/5.01  fof(f66,plain,(
% 35.38/5.01    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 35.38/5.01    inference(cnf_transformation,[],[f6])).
% 35.38/5.01  
% 35.38/5.01  fof(f18,axiom,(
% 35.38/5.01    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 35.38/5.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.38/5.01  
% 35.38/5.01  fof(f41,plain,(
% 35.38/5.01    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 35.38/5.01    inference(ennf_transformation,[],[f18])).
% 35.38/5.01  
% 35.38/5.01  fof(f82,plain,(
% 35.38/5.01    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 35.38/5.01    inference(cnf_transformation,[],[f41])).
% 35.38/5.01  
% 35.38/5.01  fof(f11,axiom,(
% 35.38/5.01    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)))),
% 35.38/5.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.38/5.01  
% 35.38/5.01  fof(f36,plain,(
% 35.38/5.01    ! [X0,X1,X2] : (r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) | ~r1_xboole_0(X0,X1))),
% 35.38/5.01    inference(ennf_transformation,[],[f11])).
% 35.38/5.01  
% 35.38/5.01  fof(f74,plain,(
% 35.38/5.01    ( ! [X2,X0,X1] : (r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) | ~r1_xboole_0(X0,X1)) )),
% 35.38/5.01    inference(cnf_transformation,[],[f36])).
% 35.38/5.01  
% 35.38/5.01  fof(f68,plain,(
% 35.38/5.01    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 35.38/5.01    inference(cnf_transformation,[],[f31])).
% 35.38/5.01  
% 35.38/5.01  fof(f21,axiom,(
% 35.38/5.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ((k1_xboole_0 = k1_relat_1(X1) & k1_xboole_0 = k1_relat_1(X0)) => X0 = X1)))),
% 35.38/5.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.38/5.01  
% 35.38/5.01  fof(f44,plain,(
% 35.38/5.01    ! [X0] : (! [X1] : ((X0 = X1 | (k1_xboole_0 != k1_relat_1(X1) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 35.38/5.01    inference(ennf_transformation,[],[f21])).
% 35.38/5.01  
% 35.38/5.01  fof(f45,plain,(
% 35.38/5.01    ! [X0] : (! [X1] : (X0 = X1 | k1_xboole_0 != k1_relat_1(X1) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 35.38/5.01    inference(flattening,[],[f44])).
% 35.38/5.01  
% 35.38/5.01  fof(f85,plain,(
% 35.38/5.01    ( ! [X0,X1] : (X0 = X1 | k1_xboole_0 != k1_relat_1(X1) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 35.38/5.01    inference(cnf_transformation,[],[f45])).
% 35.38/5.01  
% 35.38/5.01  fof(f58,plain,(
% 35.38/5.01    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 35.38/5.01    inference(cnf_transformation,[],[f48])).
% 35.38/5.01  
% 35.38/5.01  fof(f89,plain,(
% 35.38/5.01    ~r1_xboole_0(sK2,sK3)),
% 35.38/5.01    inference(cnf_transformation,[],[f56])).
% 35.38/5.01  
% 35.38/5.01  cnf(c_30,negated_conjecture,
% 35.38/5.01      ( r1_xboole_0(k1_relat_1(sK2),k1_relat_1(sK3)) ),
% 35.38/5.01      inference(cnf_transformation,[],[f88]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_1145,plain,
% 35.38/5.01      ( r1_xboole_0(k1_relat_1(sK2),k1_relat_1(sK3)) = iProver_top ),
% 35.38/5.01      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_2,plain,
% 35.38/5.01      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 35.38/5.01      inference(cnf_transformation,[],[f59]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_1173,plain,
% 35.38/5.01      ( r1_xboole_0(X0,X1) != iProver_top
% 35.38/5.01      | r1_xboole_0(X1,X0) = iProver_top ),
% 35.38/5.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_2273,plain,
% 35.38/5.01      ( r1_xboole_0(k1_relat_1(sK3),k1_relat_1(sK2)) = iProver_top ),
% 35.38/5.01      inference(superposition,[status(thm)],[c_1145,c_1173]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_1,plain,
% 35.38/5.01      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 35.38/5.01      inference(cnf_transformation,[],[f57]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_1174,plain,
% 35.38/5.01      ( k3_xboole_0(X0,X1) = k1_xboole_0
% 35.38/5.01      | r1_xboole_0(X0,X1) != iProver_top ),
% 35.38/5.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_3097,plain,
% 35.38/5.01      ( k3_xboole_0(k1_relat_1(sK3),k1_relat_1(sK2)) = k1_xboole_0 ),
% 35.38/5.01      inference(superposition,[status(thm)],[c_2273,c_1174]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_27,plain,
% 35.38/5.01      ( r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
% 35.38/5.01      | ~ v1_relat_1(X0)
% 35.38/5.01      | ~ v1_relat_1(X1) ),
% 35.38/5.01      inference(cnf_transformation,[],[f84]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_1148,plain,
% 35.38/5.01      ( r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) = iProver_top
% 35.38/5.01      | v1_relat_1(X0) != iProver_top
% 35.38/5.01      | v1_relat_1(X1) != iProver_top ),
% 35.38/5.01      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_3757,plain,
% 35.38/5.01      ( r1_tarski(k1_relat_1(k3_xboole_0(sK3,sK2)),k1_xboole_0) = iProver_top
% 35.38/5.01      | v1_relat_1(sK3) != iProver_top
% 35.38/5.01      | v1_relat_1(sK2) != iProver_top ),
% 35.38/5.01      inference(superposition,[status(thm)],[c_3097,c_1148]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_32,negated_conjecture,
% 35.38/5.01      ( v1_relat_1(sK2) ),
% 35.38/5.01      inference(cnf_transformation,[],[f86]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_33,plain,
% 35.38/5.01      ( v1_relat_1(sK2) = iProver_top ),
% 35.38/5.01      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_31,negated_conjecture,
% 35.38/5.01      ( v1_relat_1(sK3) ),
% 35.38/5.01      inference(cnf_transformation,[],[f87]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_34,plain,
% 35.38/5.01      ( v1_relat_1(sK3) = iProver_top ),
% 35.38/5.01      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_4406,plain,
% 35.38/5.01      ( r1_tarski(k1_relat_1(k3_xboole_0(sK3,sK2)),k1_xboole_0) = iProver_top ),
% 35.38/5.01      inference(global_propositional_subsumption,
% 35.38/5.01                [status(thm)],
% 35.38/5.01                [c_3757,c_33,c_34]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_12,plain,
% 35.38/5.01      ( ~ r1_tarski(X0,X1)
% 35.38/5.01      | ~ r1_tarski(X0,X2)
% 35.38/5.01      | ~ r1_xboole_0(X1,X2)
% 35.38/5.01      | k1_xboole_0 = X0 ),
% 35.38/5.01      inference(cnf_transformation,[],[f69]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_1163,plain,
% 35.38/5.01      ( k1_xboole_0 = X0
% 35.38/5.01      | r1_tarski(X0,X1) != iProver_top
% 35.38/5.01      | r1_tarski(X0,X2) != iProver_top
% 35.38/5.01      | r1_xboole_0(X1,X2) != iProver_top ),
% 35.38/5.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_7042,plain,
% 35.38/5.01      ( k1_relat_1(k3_xboole_0(sK3,sK2)) = k1_xboole_0
% 35.38/5.01      | r1_tarski(k1_relat_1(k3_xboole_0(sK3,sK2)),X0) != iProver_top
% 35.38/5.01      | r1_xboole_0(k1_xboole_0,X0) != iProver_top ),
% 35.38/5.01      inference(superposition,[status(thm)],[c_4406,c_1163]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_21,plain,
% 35.38/5.01      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 35.38/5.01      inference(cnf_transformation,[],[f77]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_59,plain,
% 35.38/5.01      ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 35.38/5.01      | k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 35.38/5.01      inference(instantiation,[status(thm)],[c_21]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_20,plain,
% 35.38/5.01      ( r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0 ),
% 35.38/5.01      inference(cnf_transformation,[],[f78]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_61,plain,
% 35.38/5.01      ( k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1) = iProver_top ),
% 35.38/5.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_63,plain,
% 35.38/5.01      ( k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 35.38/5.01      | r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 35.38/5.01      inference(instantiation,[status(thm)],[c_61]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_11,plain,
% 35.38/5.01      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 35.38/5.01      inference(cnf_transformation,[],[f90]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_7098,plain,
% 35.38/5.01      ( k1_relat_1(k3_xboole_0(sK3,sK2)) = k1_xboole_0
% 35.38/5.01      | r1_tarski(k1_relat_1(k3_xboole_0(sK3,sK2)),k1_xboole_0) != iProver_top
% 35.38/5.01      | r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 35.38/5.01      inference(instantiation,[status(thm)],[c_7042]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_158300,plain,
% 35.38/5.01      ( k1_relat_1(k3_xboole_0(sK3,sK2)) = k1_xboole_0 ),
% 35.38/5.01      inference(global_propositional_subsumption,
% 35.38/5.01                [status(thm)],
% 35.38/5.01                [c_7042,c_33,c_34,c_59,c_63,c_11,c_3757,c_7098]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_9,plain,
% 35.38/5.01      ( r1_xboole_0(X0,k1_xboole_0) ),
% 35.38/5.01      inference(cnf_transformation,[],[f66]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_1166,plain,
% 35.38/5.01      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 35.38/5.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_3092,plain,
% 35.38/5.01      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 35.38/5.01      inference(superposition,[status(thm)],[c_1166,c_1174]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_7361,plain,
% 35.38/5.01      ( r1_tarski(k1_relat_1(k1_xboole_0),k3_xboole_0(k1_relat_1(X0),k1_relat_1(k1_xboole_0))) = iProver_top
% 35.38/5.01      | v1_relat_1(X0) != iProver_top
% 35.38/5.01      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 35.38/5.01      inference(superposition,[status(thm)],[c_3092,c_1148]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_25,plain,
% 35.38/5.01      ( ~ v1_relat_1(X0) | v1_relat_1(k3_xboole_0(X0,X1)) ),
% 35.38/5.01      inference(cnf_transformation,[],[f82]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_1150,plain,
% 35.38/5.01      ( v1_relat_1(X0) != iProver_top
% 35.38/5.01      | v1_relat_1(k3_xboole_0(X0,X1)) = iProver_top ),
% 35.38/5.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_7362,plain,
% 35.38/5.01      ( v1_relat_1(X0) != iProver_top
% 35.38/5.01      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 35.38/5.01      inference(superposition,[status(thm)],[c_3092,c_1150]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_7384,plain,
% 35.38/5.01      ( r1_tarski(k1_relat_1(k1_xboole_0),k3_xboole_0(k1_relat_1(X0),k1_relat_1(k1_xboole_0))) = iProver_top
% 35.38/5.01      | v1_relat_1(X0) != iProver_top ),
% 35.38/5.01      inference(forward_subsumption_resolution,
% 35.38/5.01                [status(thm)],
% 35.38/5.01                [c_7361,c_7362]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_162014,plain,
% 35.38/5.01      ( r1_tarski(k1_relat_1(k1_xboole_0),k3_xboole_0(k1_xboole_0,k1_relat_1(k1_xboole_0))) = iProver_top
% 35.38/5.01      | v1_relat_1(k3_xboole_0(sK3,sK2)) != iProver_top ),
% 35.38/5.01      inference(superposition,[status(thm)],[c_158300,c_7384]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_2271,plain,
% 35.38/5.01      ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
% 35.38/5.01      inference(superposition,[status(thm)],[c_1166,c_1173]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_3095,plain,
% 35.38/5.01      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 35.38/5.01      inference(superposition,[status(thm)],[c_2271,c_1174]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_162098,plain,
% 35.38/5.01      ( r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) = iProver_top
% 35.38/5.01      | v1_relat_1(k3_xboole_0(sK3,sK2)) != iProver_top ),
% 35.38/5.01      inference(demodulation,[status(thm)],[c_162014,c_3095]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_52965,plain,
% 35.38/5.01      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 35.38/5.01      | ~ r1_tarski(k1_relat_1(X0),X2)
% 35.38/5.01      | ~ r1_xboole_0(X1,X2)
% 35.38/5.01      | k1_xboole_0 = k1_relat_1(X0) ),
% 35.38/5.01      inference(instantiation,[status(thm)],[c_12]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_52971,plain,
% 35.38/5.01      ( k1_xboole_0 = k1_relat_1(X0)
% 35.38/5.01      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 35.38/5.01      | r1_tarski(k1_relat_1(X0),X2) != iProver_top
% 35.38/5.01      | r1_xboole_0(X1,X2) != iProver_top ),
% 35.38/5.01      inference(predicate_to_equality,[status(thm)],[c_52965]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_52973,plain,
% 35.38/5.01      ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
% 35.38/5.01      | r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) != iProver_top
% 35.38/5.01      | r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 35.38/5.01      inference(instantiation,[status(thm)],[c_52971]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_425,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_13787,plain,
% 35.38/5.01      ( k1_relat_1(k1_xboole_0) != X0
% 35.38/5.01      | k1_relat_1(k1_xboole_0) = k1_xboole_0
% 35.38/5.01      | k1_xboole_0 != X0 ),
% 35.38/5.01      inference(instantiation,[status(thm)],[c_425]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_25521,plain,
% 35.38/5.01      ( k1_relat_1(k1_xboole_0) != k1_relat_1(k1_xboole_0)
% 35.38/5.01      | k1_relat_1(k1_xboole_0) = k1_xboole_0
% 35.38/5.01      | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
% 35.38/5.01      inference(instantiation,[status(thm)],[c_13787]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_1381,plain,
% 35.38/5.01      ( v1_relat_1(k3_xboole_0(sK3,X0)) | ~ v1_relat_1(sK3) ),
% 35.38/5.01      inference(instantiation,[status(thm)],[c_25]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_13794,plain,
% 35.38/5.01      ( v1_relat_1(k3_xboole_0(sK3,sK2)) | ~ v1_relat_1(sK3) ),
% 35.38/5.01      inference(instantiation,[status(thm)],[c_1381]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_13795,plain,
% 35.38/5.01      ( v1_relat_1(k3_xboole_0(sK3,sK2)) = iProver_top
% 35.38/5.01      | v1_relat_1(sK3) != iProver_top ),
% 35.38/5.01      inference(predicate_to_equality,[status(thm)],[c_13794]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_17,plain,
% 35.38/5.01      ( ~ r1_xboole_0(X0,X1)
% 35.38/5.01      | r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) ),
% 35.38/5.01      inference(cnf_transformation,[],[f74]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_8963,plain,
% 35.38/5.01      ( ~ r1_xboole_0(X0,X0)
% 35.38/5.01      | r1_xboole_0(k3_xboole_0(sK3,X0),k3_xboole_0(sK3,X0)) ),
% 35.38/5.01      inference(instantiation,[status(thm)],[c_17]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_8965,plain,
% 35.38/5.01      ( r1_xboole_0(k3_xboole_0(sK3,k1_xboole_0),k3_xboole_0(sK3,k1_xboole_0))
% 35.38/5.01      | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 35.38/5.01      inference(instantiation,[status(thm)],[c_8963]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_3094,plain,
% 35.38/5.01      ( k3_xboole_0(k1_relat_1(sK2),k1_relat_1(sK3)) = k1_xboole_0 ),
% 35.38/5.01      inference(superposition,[status(thm)],[c_1145,c_1174]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_3534,plain,
% 35.38/5.01      ( r1_tarski(k1_relat_1(k3_xboole_0(sK2,sK3)),k1_xboole_0) = iProver_top
% 35.38/5.01      | v1_relat_1(sK3) != iProver_top
% 35.38/5.01      | v1_relat_1(sK2) != iProver_top ),
% 35.38/5.01      inference(superposition,[status(thm)],[c_3094,c_1148]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_4269,plain,
% 35.38/5.01      ( r1_tarski(k1_relat_1(k3_xboole_0(sK2,sK3)),k1_xboole_0) = iProver_top ),
% 35.38/5.01      inference(global_propositional_subsumption,
% 35.38/5.01                [status(thm)],
% 35.38/5.01                [c_3534,c_33,c_34]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_7040,plain,
% 35.38/5.01      ( k1_relat_1(k3_xboole_0(sK2,sK3)) = k1_xboole_0
% 35.38/5.01      | r1_tarski(k1_relat_1(k3_xboole_0(sK2,sK3)),X0) != iProver_top
% 35.38/5.01      | r1_xboole_0(k1_xboole_0,X0) != iProver_top ),
% 35.38/5.01      inference(superposition,[status(thm)],[c_4269,c_1163]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_7092,plain,
% 35.38/5.01      ( k1_relat_1(k3_xboole_0(sK2,sK3)) = k1_xboole_0
% 35.38/5.01      | r1_tarski(k1_relat_1(k3_xboole_0(sK2,sK3)),k1_xboole_0) != iProver_top
% 35.38/5.01      | r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 35.38/5.01      inference(instantiation,[status(thm)],[c_7040]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_1386,plain,
% 35.38/5.01      ( v1_relat_1(k3_xboole_0(sK2,X0)) | ~ v1_relat_1(sK2) ),
% 35.38/5.01      inference(instantiation,[status(thm)],[c_25]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_5540,plain,
% 35.38/5.01      ( v1_relat_1(k3_xboole_0(sK2,sK3)) | ~ v1_relat_1(sK2) ),
% 35.38/5.01      inference(instantiation,[status(thm)],[c_1386]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_10,plain,
% 35.38/5.01      ( ~ r1_xboole_0(X0,X0) | k1_xboole_0 = X0 ),
% 35.38/5.01      inference(cnf_transformation,[],[f68]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_3561,plain,
% 35.38/5.01      ( ~ r1_xboole_0(k3_xboole_0(sK3,X0),k3_xboole_0(sK3,X0))
% 35.38/5.01      | k1_xboole_0 = k3_xboole_0(sK3,X0) ),
% 35.38/5.01      inference(instantiation,[status(thm)],[c_10]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_3565,plain,
% 35.38/5.01      ( ~ r1_xboole_0(k3_xboole_0(sK3,k1_xboole_0),k3_xboole_0(sK3,k1_xboole_0))
% 35.38/5.01      | k1_xboole_0 = k3_xboole_0(sK3,k1_xboole_0) ),
% 35.38/5.01      inference(instantiation,[status(thm)],[c_3561]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_431,plain,
% 35.38/5.01      ( ~ v1_relat_1(X0) | v1_relat_1(X1) | X1 != X0 ),
% 35.38/5.01      theory(equality) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_1560,plain,
% 35.38/5.01      ( v1_relat_1(X0)
% 35.38/5.01      | ~ v1_relat_1(k3_xboole_0(sK3,X1))
% 35.38/5.01      | X0 != k3_xboole_0(sK3,X1) ),
% 35.38/5.01      inference(instantiation,[status(thm)],[c_431]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_1572,plain,
% 35.38/5.01      ( ~ v1_relat_1(k3_xboole_0(sK3,k1_xboole_0))
% 35.38/5.01      | v1_relat_1(k1_xboole_0)
% 35.38/5.01      | k1_xboole_0 != k3_xboole_0(sK3,k1_xboole_0) ),
% 35.38/5.01      inference(instantiation,[status(thm)],[c_1560]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_28,plain,
% 35.38/5.01      ( ~ v1_relat_1(X0)
% 35.38/5.01      | ~ v1_relat_1(X1)
% 35.38/5.01      | X1 = X0
% 35.38/5.01      | k1_relat_1(X0) != k1_xboole_0
% 35.38/5.01      | k1_relat_1(X1) != k1_xboole_0 ),
% 35.38/5.01      inference(cnf_transformation,[],[f85]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_1482,plain,
% 35.38/5.01      ( ~ v1_relat_1(k3_xboole_0(sK2,sK3))
% 35.38/5.01      | ~ v1_relat_1(k1_xboole_0)
% 35.38/5.01      | k3_xboole_0(sK2,sK3) = k1_xboole_0
% 35.38/5.01      | k1_relat_1(k3_xboole_0(sK2,sK3)) != k1_xboole_0
% 35.38/5.01      | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
% 35.38/5.01      inference(instantiation,[status(thm)],[c_28]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_0,plain,
% 35.38/5.01      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 35.38/5.01      inference(cnf_transformation,[],[f58]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_1401,plain,
% 35.38/5.01      ( r1_xboole_0(sK2,sK3) | k3_xboole_0(sK2,sK3) != k1_xboole_0 ),
% 35.38/5.01      inference(instantiation,[status(thm)],[c_0]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_1383,plain,
% 35.38/5.01      ( v1_relat_1(k3_xboole_0(sK3,k1_xboole_0)) | ~ v1_relat_1(sK3) ),
% 35.38/5.01      inference(instantiation,[status(thm)],[c_1381]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_432,plain,
% 35.38/5.01      ( X0 != X1 | k1_relat_1(X0) = k1_relat_1(X1) ),
% 35.38/5.01      theory(equality) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_439,plain,
% 35.38/5.01      ( k1_relat_1(k1_xboole_0) = k1_relat_1(k1_xboole_0)
% 35.38/5.01      | k1_xboole_0 != k1_xboole_0 ),
% 35.38/5.01      inference(instantiation,[status(thm)],[c_432]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_86,plain,
% 35.38/5.01      ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 35.38/5.01      | k1_xboole_0 = k1_xboole_0 ),
% 35.38/5.01      inference(instantiation,[status(thm)],[c_10]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(c_29,negated_conjecture,
% 35.38/5.01      ( ~ r1_xboole_0(sK2,sK3) ),
% 35.38/5.01      inference(cnf_transformation,[],[f89]) ).
% 35.38/5.01  
% 35.38/5.01  cnf(contradiction,plain,
% 35.38/5.01      ( $false ),
% 35.38/5.01      inference(minisat,
% 35.38/5.01                [status(thm)],
% 35.38/5.01                [c_162098,c_52973,c_25521,c_13795,c_8965,c_7092,c_5540,
% 35.38/5.01                 c_3565,c_3534,c_1572,c_1482,c_1401,c_1383,c_439,c_86,
% 35.38/5.01                 c_11,c_63,c_59,c_29,c_34,c_31,c_33,c_32]) ).
% 35.38/5.01  
% 35.38/5.01  
% 35.38/5.01  % SZS output end CNFRefutation for theBenchmark.p
% 35.38/5.01  
% 35.38/5.01  ------                               Statistics
% 35.38/5.01  
% 35.38/5.01  ------ General
% 35.38/5.01  
% 35.38/5.01  abstr_ref_over_cycles:                  0
% 35.38/5.01  abstr_ref_under_cycles:                 0
% 35.38/5.01  gc_basic_clause_elim:                   0
% 35.38/5.01  forced_gc_time:                         0
% 35.38/5.01  parsing_time:                           0.012
% 35.38/5.01  unif_index_cands_time:                  0.
% 35.38/5.01  unif_index_add_time:                    0.
% 35.38/5.01  orderings_time:                         0.
% 35.38/5.01  out_proof_time:                         0.024
% 35.38/5.01  total_time:                             4.383
% 35.38/5.01  num_of_symbols:                         44
% 35.38/5.01  num_of_terms:                           179441
% 35.38/5.01  
% 35.38/5.01  ------ Preprocessing
% 35.38/5.01  
% 35.38/5.01  num_of_splits:                          0
% 35.38/5.01  num_of_split_atoms:                     0
% 35.38/5.01  num_of_reused_defs:                     0
% 35.38/5.01  num_eq_ax_congr_red:                    12
% 35.38/5.01  num_of_sem_filtered_clauses:            1
% 35.38/5.01  num_of_subtypes:                        0
% 35.38/5.01  monotx_restored_types:                  0
% 35.38/5.01  sat_num_of_epr_types:                   0
% 35.38/5.01  sat_num_of_non_cyclic_types:            0
% 35.38/5.01  sat_guarded_non_collapsed_types:        0
% 35.38/5.01  num_pure_diseq_elim:                    0
% 35.38/5.01  simp_replaced_by:                       0
% 35.38/5.01  res_preprocessed:                       118
% 35.38/5.01  prep_upred:                             0
% 35.38/5.01  prep_unflattend:                        0
% 35.38/5.01  smt_new_axioms:                         0
% 35.38/5.01  pred_elim_cands:                        4
% 35.38/5.01  pred_elim:                              0
% 35.38/5.01  pred_elim_cl:                           0
% 35.38/5.01  pred_elim_cycles:                       1
% 35.38/5.01  merged_defs:                            12
% 35.38/5.01  merged_defs_ncl:                        0
% 35.38/5.01  bin_hyper_res:                          12
% 35.38/5.01  prep_cycles:                            3
% 35.38/5.01  pred_elim_time:                         0.
% 35.38/5.01  splitting_time:                         0.
% 35.38/5.01  sem_filter_time:                        0.
% 35.38/5.01  monotx_time:                            0.
% 35.38/5.01  subtype_inf_time:                       0.
% 35.38/5.01  
% 35.38/5.01  ------ Problem properties
% 35.38/5.01  
% 35.38/5.01  clauses:                                33
% 35.38/5.01  conjectures:                            4
% 35.38/5.01  epr:                                    10
% 35.38/5.01  horn:                                   30
% 35.38/5.01  ground:                                 5
% 35.38/5.01  unary:                                  7
% 35.38/5.01  binary:                                 20
% 35.38/5.01  lits:                                   68
% 35.38/5.01  lits_eq:                                10
% 35.38/5.01  fd_pure:                                0
% 35.38/5.01  fd_pseudo:                              0
% 35.38/5.01  fd_cond:                                2
% 35.38/5.01  fd_pseudo_cond:                         1
% 35.38/5.01  ac_symbols:                             0
% 35.38/5.01  
% 35.38/5.01  ------ Propositional Solver
% 35.38/5.01  
% 35.38/5.01  prop_solver_calls:                      59
% 35.38/5.01  prop_fast_solver_calls:                 1525
% 35.38/5.01  smt_solver_calls:                       0
% 35.38/5.01  smt_fast_solver_calls:                  0
% 35.38/5.01  prop_num_of_clauses:                    58265
% 35.38/5.01  prop_preprocess_simplified:             58851
% 35.38/5.01  prop_fo_subsumed:                       15
% 35.38/5.01  prop_solver_time:                       0.
% 35.38/5.01  smt_solver_time:                        0.
% 35.38/5.01  smt_fast_solver_time:                   0.
% 35.38/5.01  prop_fast_solver_time:                  0.
% 35.38/5.01  prop_unsat_core_time:                   0.006
% 35.38/5.01  
% 35.38/5.01  ------ QBF
% 35.38/5.01  
% 35.38/5.01  qbf_q_res:                              0
% 35.38/5.01  qbf_num_tautologies:                    0
% 35.38/5.01  qbf_prep_cycles:                        0
% 35.38/5.01  
% 35.38/5.01  ------ BMC1
% 35.38/5.01  
% 35.38/5.01  bmc1_current_bound:                     -1
% 35.38/5.01  bmc1_last_solved_bound:                 -1
% 35.38/5.01  bmc1_unsat_core_size:                   -1
% 35.38/5.01  bmc1_unsat_core_parents_size:           -1
% 35.38/5.01  bmc1_merge_next_fun:                    0
% 35.38/5.01  bmc1_unsat_core_clauses_time:           0.
% 35.38/5.01  
% 35.38/5.01  ------ Instantiation
% 35.38/5.01  
% 35.38/5.01  inst_num_of_clauses:                    623
% 35.38/5.01  inst_num_in_passive:                    167
% 35.38/5.01  inst_num_in_active:                     2913
% 35.38/5.01  inst_num_in_unprocessed:                248
% 35.38/5.01  inst_num_of_loops:                      3209
% 35.38/5.01  inst_num_of_learning_restarts:          1
% 35.38/5.01  inst_num_moves_active_passive:          294
% 35.38/5.01  inst_lit_activity:                      0
% 35.38/5.01  inst_lit_activity_moves:                0
% 35.38/5.01  inst_num_tautologies:                   0
% 35.38/5.01  inst_num_prop_implied:                  0
% 35.38/5.01  inst_num_existing_simplified:           0
% 35.38/5.01  inst_num_eq_res_simplified:             0
% 35.38/5.01  inst_num_child_elim:                    0
% 35.38/5.01  inst_num_of_dismatching_blockings:      7803
% 35.38/5.01  inst_num_of_non_proper_insts:           7990
% 35.38/5.01  inst_num_of_duplicates:                 0
% 35.38/5.01  inst_inst_num_from_inst_to_res:         0
% 35.38/5.01  inst_dismatching_checking_time:         0.
% 35.38/5.01  
% 35.38/5.01  ------ Resolution
% 35.38/5.01  
% 35.38/5.01  res_num_of_clauses:                     42
% 35.38/5.01  res_num_in_passive:                     42
% 35.38/5.01  res_num_in_active:                      0
% 35.38/5.01  res_num_of_loops:                       121
% 35.38/5.01  res_forward_subset_subsumed:            254
% 35.38/5.01  res_backward_subset_subsumed:           0
% 35.38/5.01  res_forward_subsumed:                   0
% 35.38/5.01  res_backward_subsumed:                  0
% 35.38/5.01  res_forward_subsumption_resolution:     0
% 35.38/5.01  res_backward_subsumption_resolution:    0
% 35.38/5.01  res_clause_to_clause_subsumption:       115566
% 35.38/5.01  res_orphan_elimination:                 0
% 35.38/5.01  res_tautology_del:                      310
% 35.38/5.01  res_num_eq_res_simplified:              0
% 35.38/5.01  res_num_sel_changes:                    0
% 35.38/5.01  res_moves_from_active_to_pass:          0
% 35.38/5.01  
% 35.38/5.01  ------ Superposition
% 35.38/5.01  
% 35.38/5.01  sup_time_total:                         0.
% 35.38/5.01  sup_time_generating:                    0.
% 35.38/5.01  sup_time_sim_full:                      0.
% 35.38/5.01  sup_time_sim_immed:                     0.
% 35.38/5.01  
% 35.38/5.01  sup_num_of_clauses:                     13599
% 35.38/5.01  sup_num_in_active:                      629
% 35.38/5.01  sup_num_in_passive:                     12970
% 35.38/5.01  sup_num_of_loops:                       640
% 35.38/5.01  sup_fw_superposition:                   13664
% 35.38/5.01  sup_bw_superposition:                   15054
% 35.38/5.01  sup_immediate_simplified:               11614
% 35.38/5.01  sup_given_eliminated:                   8
% 35.38/5.01  comparisons_done:                       0
% 35.38/5.01  comparisons_avoided:                    0
% 35.38/5.01  
% 35.38/5.01  ------ Simplifications
% 35.38/5.01  
% 35.38/5.01  
% 35.38/5.01  sim_fw_subset_subsumed:                 730
% 35.38/5.01  sim_bw_subset_subsumed:                 6
% 35.38/5.01  sim_fw_subsumed:                        2398
% 35.38/5.01  sim_bw_subsumed:                        323
% 35.38/5.01  sim_fw_subsumption_res:                 110
% 35.38/5.01  sim_bw_subsumption_res:                 0
% 35.38/5.01  sim_tautology_del:                      282
% 35.38/5.01  sim_eq_tautology_del:                   510
% 35.38/5.01  sim_eq_res_simp:                        12
% 35.38/5.01  sim_fw_demodulated:                     7218
% 35.38/5.01  sim_bw_demodulated:                     35
% 35.38/5.01  sim_light_normalised:                   1496
% 35.38/5.01  sim_joinable_taut:                      0
% 35.38/5.01  sim_joinable_simp:                      0
% 35.38/5.01  sim_ac_normalised:                      0
% 35.38/5.01  sim_smt_subsumption:                    0
% 35.38/5.01  
%------------------------------------------------------------------------------
