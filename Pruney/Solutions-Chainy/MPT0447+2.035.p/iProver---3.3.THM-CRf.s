%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:43:15 EST 2020

% Result     : Theorem 15.31s
% Output     : CNFRefutation 15.31s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 273 expanded)
%              Number of clauses        :   67 ( 111 expanded)
%              Number of leaves         :   15 (  61 expanded)
%              Depth                    :   14
%              Number of atoms          :  234 ( 758 expanded)
%              Number of equality atoms :  111 ( 198 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
             => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
     => ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(sK1))
        & r1_tarski(X0,sK1)
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
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

fof(f26,plain,
    ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f25,f24])).

fof(f40,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f22])).

fof(f30,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f43,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f28])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f38,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f39,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f35,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f41,plain,(
    ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_12,negated_conjecture,
    ( r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_400,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_405,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_6,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_406,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_410,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1160,plain,
    ( k2_xboole_0(X0,X1) = X0
    | r1_tarski(k2_xboole_0(X0,X1),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_406,c_410])).

cnf(c_4094,plain,
    ( k2_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X0) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_405,c_1160])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_36,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_51983,plain,
    ( k2_xboole_0(X0,X1) = X0
    | r1_tarski(X1,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4094,c_36])).

cnf(c_51993,plain,
    ( k2_xboole_0(sK1,sK0) = sK1 ),
    inference(superposition,[status(thm)],[c_400,c_51983])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_53255,plain,
    ( k2_xboole_0(sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_51993,c_0])).

cnf(c_14,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_398,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_13,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_399,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_402,plain,
    ( k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_999,plain,
    ( k2_xboole_0(k2_relat_1(sK1),k2_relat_1(X0)) = k2_relat_1(k2_xboole_0(sK1,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_399,c_402])).

cnf(c_2225,plain,
    ( k2_xboole_0(k2_relat_1(sK1),k2_relat_1(sK0)) = k2_relat_1(k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_398,c_999])).

cnf(c_736,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_406])).

cnf(c_2973,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_relat_1(k2_xboole_0(sK1,sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2225,c_736])).

cnf(c_3752,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_relat_1(k2_xboole_0(sK0,sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_2973])).

cnf(c_54059,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_53255,c_3752])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_404,plain,
    ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_861,plain,
    ( k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1)) = k3_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_399,c_404])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_408,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k2_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1625,plain,
    ( r1_tarski(X0,k3_relat_1(sK1)) = iProver_top
    | r1_tarski(X0,k2_relat_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_861,c_408])).

cnf(c_55681,plain,
    ( r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_54059,c_1625])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_403,plain,
    ( k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1418,plain,
    ( k2_xboole_0(k1_relat_1(sK1),k1_relat_1(X0)) = k1_relat_1(k2_xboole_0(sK1,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_399,c_403])).

cnf(c_12697,plain,
    ( k2_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0)) = k1_relat_1(k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_398,c_1418])).

cnf(c_13074,plain,
    ( r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK1,sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_12697,c_736])).

cnf(c_13548,plain,
    ( r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK0,sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_13074])).

cnf(c_54054,plain,
    ( r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_53255,c_13548])).

cnf(c_870,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k2_xboole_0(X1,X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_408])).

cnf(c_1627,plain,
    ( r1_tarski(X0,k3_relat_1(sK1)) = iProver_top
    | r1_tarski(X0,k1_relat_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_861,c_870])).

cnf(c_54251,plain,
    ( r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_54054,c_1627])).

cnf(c_1749,plain,
    ( r1_tarski(k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)),X0)
    | ~ r1_tarski(k2_relat_1(sK0),X0)
    | ~ r1_tarski(k1_relat_1(sK0),X0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_10378,plain,
    ( r1_tarski(k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)),k3_relat_1(sK1))
    | ~ r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_1749])).

cnf(c_10383,plain,
    ( r1_tarski(k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)),k3_relat_1(sK1)) = iProver_top
    | r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1)) != iProver_top
    | r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10378])).

cnf(c_189,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_522,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
    | k3_relat_1(sK1) != X1
    | k3_relat_1(sK0) != X0 ),
    inference(instantiation,[status(thm)],[c_189])).

cnf(c_984,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)),X0)
    | r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
    | k3_relat_1(sK1) != X0
    | k3_relat_1(sK0) != k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_522])).

cnf(c_1088,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)),k3_relat_1(sK1))
    | r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
    | k3_relat_1(sK1) != k3_relat_1(sK1)
    | k3_relat_1(sK0) != k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_984])).

cnf(c_1089,plain,
    ( k3_relat_1(sK1) != k3_relat_1(sK1)
    | k3_relat_1(sK0) != k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0))
    | r1_tarski(k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)),k3_relat_1(sK1)) != iProver_top
    | r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1088])).

cnf(c_187,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_579,plain,
    ( X0 != X1
    | k3_relat_1(sK0) != X1
    | k3_relat_1(sK0) = X0 ),
    inference(instantiation,[status(thm)],[c_187])).

cnf(c_682,plain,
    ( X0 != k3_relat_1(sK0)
    | k3_relat_1(sK0) = X0
    | k3_relat_1(sK0) != k3_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_579])).

cnf(c_768,plain,
    ( k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)) != k3_relat_1(sK0)
    | k3_relat_1(sK0) = k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0))
    | k3_relat_1(sK0) != k3_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_682])).

cnf(c_186,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_695,plain,
    ( k3_relat_1(sK1) = k3_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_186])).

cnf(c_192,plain,
    ( X0 != X1
    | k3_relat_1(X0) = k3_relat_1(X1) ),
    theory(equality)).

cnf(c_197,plain,
    ( k3_relat_1(sK0) = k3_relat_1(sK0)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_192])).

cnf(c_41,plain,
    ( ~ r1_tarski(sK0,sK0)
    | sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_37,plain,
    ( r1_tarski(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_26,plain,
    ( ~ v1_relat_1(sK0)
    | k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)) = k3_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_11,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_18,plain,
    ( r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_55681,c_54251,c_10383,c_1089,c_768,c_695,c_197,c_41,c_37,c_26,c_18,c_14])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n021.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 15:27:19 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running in FOF mode
% 15.31/2.47  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.31/2.47  
% 15.31/2.47  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.31/2.47  
% 15.31/2.47  ------  iProver source info
% 15.31/2.47  
% 15.31/2.47  git: date: 2020-06-30 10:37:57 +0100
% 15.31/2.47  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.31/2.47  git: non_committed_changes: false
% 15.31/2.47  git: last_make_outside_of_git: false
% 15.31/2.47  
% 15.31/2.47  ------ 
% 15.31/2.47  
% 15.31/2.47  ------ Input Options
% 15.31/2.47  
% 15.31/2.47  --out_options                           all
% 15.31/2.47  --tptp_safe_out                         true
% 15.31/2.47  --problem_path                          ""
% 15.31/2.47  --include_path                          ""
% 15.31/2.47  --clausifier                            res/vclausify_rel
% 15.31/2.47  --clausifier_options                    --mode clausify
% 15.31/2.47  --stdin                                 false
% 15.31/2.47  --stats_out                             sel
% 15.31/2.47  
% 15.31/2.47  ------ General Options
% 15.31/2.47  
% 15.31/2.47  --fof                                   false
% 15.31/2.47  --time_out_real                         604.99
% 15.31/2.47  --time_out_virtual                      -1.
% 15.31/2.47  --symbol_type_check                     false
% 15.31/2.47  --clausify_out                          false
% 15.31/2.47  --sig_cnt_out                           false
% 15.31/2.47  --trig_cnt_out                          false
% 15.31/2.47  --trig_cnt_out_tolerance                1.
% 15.31/2.47  --trig_cnt_out_sk_spl                   false
% 15.31/2.47  --abstr_cl_out                          false
% 15.31/2.47  
% 15.31/2.47  ------ Global Options
% 15.31/2.47  
% 15.31/2.47  --schedule                              none
% 15.31/2.47  --add_important_lit                     false
% 15.31/2.47  --prop_solver_per_cl                    1000
% 15.31/2.47  --min_unsat_core                        false
% 15.31/2.47  --soft_assumptions                      false
% 15.31/2.47  --soft_lemma_size                       3
% 15.31/2.47  --prop_impl_unit_size                   0
% 15.31/2.47  --prop_impl_unit                        []
% 15.31/2.47  --share_sel_clauses                     true
% 15.31/2.47  --reset_solvers                         false
% 15.31/2.47  --bc_imp_inh                            [conj_cone]
% 15.31/2.47  --conj_cone_tolerance                   3.
% 15.31/2.47  --extra_neg_conj                        none
% 15.31/2.47  --large_theory_mode                     true
% 15.31/2.47  --prolific_symb_bound                   200
% 15.31/2.47  --lt_threshold                          2000
% 15.31/2.47  --clause_weak_htbl                      true
% 15.31/2.47  --gc_record_bc_elim                     false
% 15.31/2.47  
% 15.31/2.47  ------ Preprocessing Options
% 15.31/2.47  
% 15.31/2.47  --preprocessing_flag                    true
% 15.31/2.47  --time_out_prep_mult                    0.1
% 15.31/2.47  --splitting_mode                        input
% 15.31/2.47  --splitting_grd                         true
% 15.31/2.47  --splitting_cvd                         false
% 15.31/2.47  --splitting_cvd_svl                     false
% 15.31/2.47  --splitting_nvd                         32
% 15.31/2.47  --sub_typing                            true
% 15.31/2.47  --prep_gs_sim                           false
% 15.31/2.47  --prep_unflatten                        true
% 15.31/2.47  --prep_res_sim                          true
% 15.31/2.47  --prep_upred                            true
% 15.31/2.47  --prep_sem_filter                       exhaustive
% 15.31/2.47  --prep_sem_filter_out                   false
% 15.31/2.47  --pred_elim                             false
% 15.31/2.47  --res_sim_input                         true
% 15.31/2.47  --eq_ax_congr_red                       true
% 15.31/2.47  --pure_diseq_elim                       true
% 15.31/2.47  --brand_transform                       false
% 15.31/2.47  --non_eq_to_eq                          false
% 15.31/2.47  --prep_def_merge                        true
% 15.31/2.47  --prep_def_merge_prop_impl              false
% 15.31/2.47  --prep_def_merge_mbd                    true
% 15.31/2.47  --prep_def_merge_tr_red                 false
% 15.31/2.47  --prep_def_merge_tr_cl                  false
% 15.31/2.47  --smt_preprocessing                     true
% 15.31/2.47  --smt_ac_axioms                         fast
% 15.31/2.47  --preprocessed_out                      false
% 15.31/2.47  --preprocessed_stats                    false
% 15.31/2.47  
% 15.31/2.47  ------ Abstraction refinement Options
% 15.31/2.47  
% 15.31/2.47  --abstr_ref                             []
% 15.31/2.47  --abstr_ref_prep                        false
% 15.31/2.47  --abstr_ref_until_sat                   false
% 15.31/2.47  --abstr_ref_sig_restrict                funpre
% 15.31/2.47  --abstr_ref_af_restrict_to_split_sk     false
% 15.31/2.47  --abstr_ref_under                       []
% 15.31/2.47  
% 15.31/2.47  ------ SAT Options
% 15.31/2.47  
% 15.31/2.47  --sat_mode                              false
% 15.31/2.47  --sat_fm_restart_options                ""
% 15.31/2.47  --sat_gr_def                            false
% 15.31/2.47  --sat_epr_types                         true
% 15.31/2.47  --sat_non_cyclic_types                  false
% 15.31/2.47  --sat_finite_models                     false
% 15.31/2.47  --sat_fm_lemmas                         false
% 15.31/2.47  --sat_fm_prep                           false
% 15.31/2.47  --sat_fm_uc_incr                        true
% 15.31/2.47  --sat_out_model                         small
% 15.31/2.47  --sat_out_clauses                       false
% 15.31/2.47  
% 15.31/2.47  ------ QBF Options
% 15.31/2.47  
% 15.31/2.47  --qbf_mode                              false
% 15.31/2.47  --qbf_elim_univ                         false
% 15.31/2.47  --qbf_dom_inst                          none
% 15.31/2.47  --qbf_dom_pre_inst                      false
% 15.31/2.47  --qbf_sk_in                             false
% 15.31/2.47  --qbf_pred_elim                         true
% 15.31/2.47  --qbf_split                             512
% 15.31/2.47  
% 15.31/2.47  ------ BMC1 Options
% 15.31/2.47  
% 15.31/2.47  --bmc1_incremental                      false
% 15.31/2.47  --bmc1_axioms                           reachable_all
% 15.31/2.47  --bmc1_min_bound                        0
% 15.31/2.47  --bmc1_max_bound                        -1
% 15.31/2.47  --bmc1_max_bound_default                -1
% 15.31/2.47  --bmc1_symbol_reachability              true
% 15.31/2.47  --bmc1_property_lemmas                  false
% 15.31/2.47  --bmc1_k_induction                      false
% 15.31/2.47  --bmc1_non_equiv_states                 false
% 15.31/2.47  --bmc1_deadlock                         false
% 15.31/2.47  --bmc1_ucm                              false
% 15.31/2.47  --bmc1_add_unsat_core                   none
% 15.31/2.47  --bmc1_unsat_core_children              false
% 15.31/2.47  --bmc1_unsat_core_extrapolate_axioms    false
% 15.31/2.47  --bmc1_out_stat                         full
% 15.31/2.47  --bmc1_ground_init                      false
% 15.31/2.47  --bmc1_pre_inst_next_state              false
% 15.31/2.47  --bmc1_pre_inst_state                   false
% 15.31/2.47  --bmc1_pre_inst_reach_state             false
% 15.31/2.47  --bmc1_out_unsat_core                   false
% 15.31/2.47  --bmc1_aig_witness_out                  false
% 15.31/2.47  --bmc1_verbose                          false
% 15.31/2.47  --bmc1_dump_clauses_tptp                false
% 15.31/2.47  --bmc1_dump_unsat_core_tptp             false
% 15.31/2.47  --bmc1_dump_file                        -
% 15.31/2.47  --bmc1_ucm_expand_uc_limit              128
% 15.31/2.47  --bmc1_ucm_n_expand_iterations          6
% 15.31/2.47  --bmc1_ucm_extend_mode                  1
% 15.31/2.47  --bmc1_ucm_init_mode                    2
% 15.31/2.47  --bmc1_ucm_cone_mode                    none
% 15.31/2.47  --bmc1_ucm_reduced_relation_type        0
% 15.31/2.47  --bmc1_ucm_relax_model                  4
% 15.31/2.47  --bmc1_ucm_full_tr_after_sat            true
% 15.31/2.47  --bmc1_ucm_expand_neg_assumptions       false
% 15.31/2.47  --bmc1_ucm_layered_model                none
% 15.31/2.47  --bmc1_ucm_max_lemma_size               10
% 15.31/2.47  
% 15.31/2.47  ------ AIG Options
% 15.31/2.47  
% 15.31/2.47  --aig_mode                              false
% 15.31/2.47  
% 15.31/2.47  ------ Instantiation Options
% 15.31/2.47  
% 15.31/2.47  --instantiation_flag                    true
% 15.31/2.47  --inst_sos_flag                         false
% 15.31/2.47  --inst_sos_phase                        true
% 15.31/2.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.31/2.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.31/2.47  --inst_lit_sel_side                     num_symb
% 15.31/2.47  --inst_solver_per_active                1400
% 15.31/2.47  --inst_solver_calls_frac                1.
% 15.31/2.47  --inst_passive_queue_type               priority_queues
% 15.31/2.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.31/2.47  --inst_passive_queues_freq              [25;2]
% 15.31/2.47  --inst_dismatching                      true
% 15.31/2.47  --inst_eager_unprocessed_to_passive     true
% 15.31/2.47  --inst_prop_sim_given                   true
% 15.31/2.47  --inst_prop_sim_new                     false
% 15.31/2.47  --inst_subs_new                         false
% 15.31/2.47  --inst_eq_res_simp                      false
% 15.31/2.47  --inst_subs_given                       false
% 15.31/2.47  --inst_orphan_elimination               true
% 15.31/2.47  --inst_learning_loop_flag               true
% 15.31/2.47  --inst_learning_start                   3000
% 15.31/2.47  --inst_learning_factor                  2
% 15.31/2.47  --inst_start_prop_sim_after_learn       3
% 15.31/2.47  --inst_sel_renew                        solver
% 15.31/2.47  --inst_lit_activity_flag                true
% 15.31/2.47  --inst_restr_to_given                   false
% 15.31/2.47  --inst_activity_threshold               500
% 15.31/2.47  --inst_out_proof                        true
% 15.31/2.47  
% 15.31/2.47  ------ Resolution Options
% 15.31/2.47  
% 15.31/2.47  --resolution_flag                       true
% 15.31/2.47  --res_lit_sel                           adaptive
% 15.31/2.47  --res_lit_sel_side                      none
% 15.31/2.47  --res_ordering                          kbo
% 15.31/2.47  --res_to_prop_solver                    active
% 15.31/2.47  --res_prop_simpl_new                    false
% 15.31/2.47  --res_prop_simpl_given                  true
% 15.31/2.47  --res_passive_queue_type                priority_queues
% 15.31/2.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.31/2.47  --res_passive_queues_freq               [15;5]
% 15.31/2.47  --res_forward_subs                      full
% 15.31/2.47  --res_backward_subs                     full
% 15.31/2.47  --res_forward_subs_resolution           true
% 15.31/2.47  --res_backward_subs_resolution          true
% 15.31/2.47  --res_orphan_elimination                true
% 15.31/2.47  --res_time_limit                        2.
% 15.31/2.47  --res_out_proof                         true
% 15.31/2.47  
% 15.31/2.47  ------ Superposition Options
% 15.31/2.47  
% 15.31/2.47  --superposition_flag                    true
% 15.31/2.47  --sup_passive_queue_type                priority_queues
% 15.31/2.47  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.31/2.47  --sup_passive_queues_freq               [1;4]
% 15.31/2.47  --demod_completeness_check              fast
% 15.31/2.47  --demod_use_ground                      true
% 15.31/2.47  --sup_to_prop_solver                    passive
% 15.31/2.47  --sup_prop_simpl_new                    true
% 15.31/2.47  --sup_prop_simpl_given                  true
% 15.31/2.47  --sup_fun_splitting                     false
% 15.31/2.47  --sup_smt_interval                      50000
% 15.31/2.47  
% 15.31/2.47  ------ Superposition Simplification Setup
% 15.31/2.47  
% 15.31/2.47  --sup_indices_passive                   []
% 15.31/2.47  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.31/2.47  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.31/2.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.31/2.47  --sup_full_triv                         [TrivRules;PropSubs]
% 15.31/2.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.31/2.47  --sup_full_bw                           [BwDemod]
% 15.31/2.47  --sup_immed_triv                        [TrivRules]
% 15.31/2.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.31/2.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.31/2.47  --sup_immed_bw_main                     []
% 15.31/2.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.31/2.47  --sup_input_triv                        [Unflattening;TrivRules]
% 15.31/2.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.31/2.47  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.31/2.47  
% 15.31/2.47  ------ Combination Options
% 15.31/2.47  
% 15.31/2.47  --comb_res_mult                         3
% 15.31/2.47  --comb_sup_mult                         2
% 15.31/2.47  --comb_inst_mult                        10
% 15.31/2.47  
% 15.31/2.47  ------ Debug Options
% 15.31/2.47  
% 15.31/2.47  --dbg_backtrace                         false
% 15.31/2.47  --dbg_dump_prop_clauses                 false
% 15.31/2.47  --dbg_dump_prop_clauses_file            -
% 15.31/2.47  --dbg_out_stat                          false
% 15.31/2.47  ------ Parsing...
% 15.31/2.47  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.31/2.47  
% 15.31/2.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 15.31/2.47  
% 15.31/2.47  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.31/2.47  
% 15.31/2.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.31/2.47  ------ Proving...
% 15.31/2.47  ------ Problem Properties 
% 15.31/2.47  
% 15.31/2.47  
% 15.31/2.47  clauses                                 14
% 15.31/2.47  conjectures                             4
% 15.31/2.47  EPR                                     6
% 15.31/2.47  Horn                                    14
% 15.31/2.47  unary                                   7
% 15.31/2.47  binary                                  2
% 15.31/2.47  lits                                    26
% 15.31/2.47  lits eq                                 5
% 15.31/2.47  fd_pure                                 0
% 15.31/2.47  fd_pseudo                               0
% 15.31/2.47  fd_cond                                 0
% 15.31/2.47  fd_pseudo_cond                          1
% 15.31/2.47  AC symbols                              0
% 15.31/2.47  
% 15.31/2.47  ------ Input Options Time Limit: Unbounded
% 15.31/2.47  
% 15.31/2.47  
% 15.31/2.47  ------ 
% 15.31/2.47  Current options:
% 15.31/2.47  ------ 
% 15.31/2.47  
% 15.31/2.47  ------ Input Options
% 15.31/2.47  
% 15.31/2.47  --out_options                           all
% 15.31/2.47  --tptp_safe_out                         true
% 15.31/2.47  --problem_path                          ""
% 15.31/2.47  --include_path                          ""
% 15.31/2.47  --clausifier                            res/vclausify_rel
% 15.31/2.47  --clausifier_options                    --mode clausify
% 15.31/2.47  --stdin                                 false
% 15.31/2.47  --stats_out                             sel
% 15.31/2.47  
% 15.31/2.47  ------ General Options
% 15.31/2.47  
% 15.31/2.47  --fof                                   false
% 15.31/2.47  --time_out_real                         604.99
% 15.31/2.47  --time_out_virtual                      -1.
% 15.31/2.47  --symbol_type_check                     false
% 15.31/2.47  --clausify_out                          false
% 15.31/2.47  --sig_cnt_out                           false
% 15.31/2.47  --trig_cnt_out                          false
% 15.31/2.47  --trig_cnt_out_tolerance                1.
% 15.31/2.47  --trig_cnt_out_sk_spl                   false
% 15.31/2.47  --abstr_cl_out                          false
% 15.31/2.47  
% 15.31/2.47  ------ Global Options
% 15.31/2.47  
% 15.31/2.47  --schedule                              none
% 15.31/2.47  --add_important_lit                     false
% 15.31/2.47  --prop_solver_per_cl                    1000
% 15.31/2.47  --min_unsat_core                        false
% 15.31/2.47  --soft_assumptions                      false
% 15.31/2.47  --soft_lemma_size                       3
% 15.31/2.47  --prop_impl_unit_size                   0
% 15.31/2.47  --prop_impl_unit                        []
% 15.31/2.47  --share_sel_clauses                     true
% 15.31/2.47  --reset_solvers                         false
% 15.31/2.47  --bc_imp_inh                            [conj_cone]
% 15.31/2.47  --conj_cone_tolerance                   3.
% 15.31/2.47  --extra_neg_conj                        none
% 15.31/2.47  --large_theory_mode                     true
% 15.31/2.47  --prolific_symb_bound                   200
% 15.31/2.47  --lt_threshold                          2000
% 15.31/2.47  --clause_weak_htbl                      true
% 15.31/2.47  --gc_record_bc_elim                     false
% 15.31/2.47  
% 15.31/2.47  ------ Preprocessing Options
% 15.31/2.47  
% 15.31/2.47  --preprocessing_flag                    true
% 15.31/2.47  --time_out_prep_mult                    0.1
% 15.31/2.47  --splitting_mode                        input
% 15.31/2.47  --splitting_grd                         true
% 15.31/2.47  --splitting_cvd                         false
% 15.31/2.47  --splitting_cvd_svl                     false
% 15.31/2.47  --splitting_nvd                         32
% 15.31/2.47  --sub_typing                            true
% 15.31/2.47  --prep_gs_sim                           false
% 15.31/2.47  --prep_unflatten                        true
% 15.31/2.47  --prep_res_sim                          true
% 15.31/2.47  --prep_upred                            true
% 15.31/2.47  --prep_sem_filter                       exhaustive
% 15.31/2.47  --prep_sem_filter_out                   false
% 15.31/2.47  --pred_elim                             false
% 15.31/2.47  --res_sim_input                         true
% 15.31/2.47  --eq_ax_congr_red                       true
% 15.31/2.47  --pure_diseq_elim                       true
% 15.31/2.47  --brand_transform                       false
% 15.31/2.47  --non_eq_to_eq                          false
% 15.31/2.47  --prep_def_merge                        true
% 15.31/2.47  --prep_def_merge_prop_impl              false
% 15.31/2.47  --prep_def_merge_mbd                    true
% 15.31/2.47  --prep_def_merge_tr_red                 false
% 15.31/2.47  --prep_def_merge_tr_cl                  false
% 15.31/2.47  --smt_preprocessing                     true
% 15.31/2.47  --smt_ac_axioms                         fast
% 15.31/2.47  --preprocessed_out                      false
% 15.31/2.47  --preprocessed_stats                    false
% 15.31/2.47  
% 15.31/2.47  ------ Abstraction refinement Options
% 15.31/2.47  
% 15.31/2.47  --abstr_ref                             []
% 15.31/2.47  --abstr_ref_prep                        false
% 15.31/2.47  --abstr_ref_until_sat                   false
% 15.31/2.47  --abstr_ref_sig_restrict                funpre
% 15.31/2.47  --abstr_ref_af_restrict_to_split_sk     false
% 15.31/2.47  --abstr_ref_under                       []
% 15.31/2.47  
% 15.31/2.47  ------ SAT Options
% 15.31/2.47  
% 15.31/2.47  --sat_mode                              false
% 15.31/2.47  --sat_fm_restart_options                ""
% 15.31/2.47  --sat_gr_def                            false
% 15.31/2.47  --sat_epr_types                         true
% 15.31/2.47  --sat_non_cyclic_types                  false
% 15.31/2.47  --sat_finite_models                     false
% 15.31/2.47  --sat_fm_lemmas                         false
% 15.31/2.47  --sat_fm_prep                           false
% 15.31/2.47  --sat_fm_uc_incr                        true
% 15.31/2.47  --sat_out_model                         small
% 15.31/2.47  --sat_out_clauses                       false
% 15.31/2.47  
% 15.31/2.47  ------ QBF Options
% 15.31/2.47  
% 15.31/2.47  --qbf_mode                              false
% 15.31/2.47  --qbf_elim_univ                         false
% 15.31/2.47  --qbf_dom_inst                          none
% 15.31/2.47  --qbf_dom_pre_inst                      false
% 15.31/2.47  --qbf_sk_in                             false
% 15.31/2.47  --qbf_pred_elim                         true
% 15.31/2.47  --qbf_split                             512
% 15.31/2.47  
% 15.31/2.47  ------ BMC1 Options
% 15.31/2.47  
% 15.31/2.47  --bmc1_incremental                      false
% 15.31/2.47  --bmc1_axioms                           reachable_all
% 15.31/2.47  --bmc1_min_bound                        0
% 15.31/2.47  --bmc1_max_bound                        -1
% 15.31/2.47  --bmc1_max_bound_default                -1
% 15.31/2.47  --bmc1_symbol_reachability              true
% 15.31/2.47  --bmc1_property_lemmas                  false
% 15.31/2.47  --bmc1_k_induction                      false
% 15.31/2.47  --bmc1_non_equiv_states                 false
% 15.31/2.47  --bmc1_deadlock                         false
% 15.31/2.47  --bmc1_ucm                              false
% 15.31/2.47  --bmc1_add_unsat_core                   none
% 15.31/2.47  --bmc1_unsat_core_children              false
% 15.31/2.47  --bmc1_unsat_core_extrapolate_axioms    false
% 15.31/2.47  --bmc1_out_stat                         full
% 15.31/2.47  --bmc1_ground_init                      false
% 15.31/2.47  --bmc1_pre_inst_next_state              false
% 15.31/2.47  --bmc1_pre_inst_state                   false
% 15.31/2.47  --bmc1_pre_inst_reach_state             false
% 15.31/2.47  --bmc1_out_unsat_core                   false
% 15.31/2.47  --bmc1_aig_witness_out                  false
% 15.31/2.47  --bmc1_verbose                          false
% 15.31/2.47  --bmc1_dump_clauses_tptp                false
% 15.31/2.47  --bmc1_dump_unsat_core_tptp             false
% 15.31/2.47  --bmc1_dump_file                        -
% 15.31/2.47  --bmc1_ucm_expand_uc_limit              128
% 15.31/2.47  --bmc1_ucm_n_expand_iterations          6
% 15.31/2.47  --bmc1_ucm_extend_mode                  1
% 15.31/2.47  --bmc1_ucm_init_mode                    2
% 15.31/2.47  --bmc1_ucm_cone_mode                    none
% 15.31/2.47  --bmc1_ucm_reduced_relation_type        0
% 15.31/2.47  --bmc1_ucm_relax_model                  4
% 15.31/2.47  --bmc1_ucm_full_tr_after_sat            true
% 15.31/2.47  --bmc1_ucm_expand_neg_assumptions       false
% 15.31/2.47  --bmc1_ucm_layered_model                none
% 15.31/2.47  --bmc1_ucm_max_lemma_size               10
% 15.31/2.47  
% 15.31/2.47  ------ AIG Options
% 15.31/2.47  
% 15.31/2.47  --aig_mode                              false
% 15.31/2.47  
% 15.31/2.47  ------ Instantiation Options
% 15.31/2.47  
% 15.31/2.47  --instantiation_flag                    true
% 15.31/2.47  --inst_sos_flag                         false
% 15.31/2.47  --inst_sos_phase                        true
% 15.31/2.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.31/2.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.31/2.47  --inst_lit_sel_side                     num_symb
% 15.31/2.47  --inst_solver_per_active                1400
% 15.31/2.47  --inst_solver_calls_frac                1.
% 15.31/2.47  --inst_passive_queue_type               priority_queues
% 15.31/2.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.31/2.47  --inst_passive_queues_freq              [25;2]
% 15.31/2.47  --inst_dismatching                      true
% 15.31/2.47  --inst_eager_unprocessed_to_passive     true
% 15.31/2.47  --inst_prop_sim_given                   true
% 15.31/2.47  --inst_prop_sim_new                     false
% 15.31/2.47  --inst_subs_new                         false
% 15.31/2.47  --inst_eq_res_simp                      false
% 15.31/2.47  --inst_subs_given                       false
% 15.31/2.47  --inst_orphan_elimination               true
% 15.31/2.47  --inst_learning_loop_flag               true
% 15.31/2.47  --inst_learning_start                   3000
% 15.31/2.47  --inst_learning_factor                  2
% 15.31/2.47  --inst_start_prop_sim_after_learn       3
% 15.31/2.47  --inst_sel_renew                        solver
% 15.31/2.47  --inst_lit_activity_flag                true
% 15.31/2.47  --inst_restr_to_given                   false
% 15.31/2.47  --inst_activity_threshold               500
% 15.31/2.47  --inst_out_proof                        true
% 15.31/2.47  
% 15.31/2.47  ------ Resolution Options
% 15.31/2.47  
% 15.31/2.47  --resolution_flag                       true
% 15.31/2.47  --res_lit_sel                           adaptive
% 15.31/2.47  --res_lit_sel_side                      none
% 15.31/2.47  --res_ordering                          kbo
% 15.31/2.47  --res_to_prop_solver                    active
% 15.31/2.47  --res_prop_simpl_new                    false
% 15.31/2.47  --res_prop_simpl_given                  true
% 15.31/2.47  --res_passive_queue_type                priority_queues
% 15.31/2.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.31/2.47  --res_passive_queues_freq               [15;5]
% 15.31/2.47  --res_forward_subs                      full
% 15.31/2.47  --res_backward_subs                     full
% 15.31/2.47  --res_forward_subs_resolution           true
% 15.31/2.47  --res_backward_subs_resolution          true
% 15.31/2.47  --res_orphan_elimination                true
% 15.31/2.47  --res_time_limit                        2.
% 15.31/2.47  --res_out_proof                         true
% 15.31/2.47  
% 15.31/2.47  ------ Superposition Options
% 15.31/2.47  
% 15.31/2.47  --superposition_flag                    true
% 15.31/2.47  --sup_passive_queue_type                priority_queues
% 15.31/2.47  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.31/2.47  --sup_passive_queues_freq               [1;4]
% 15.31/2.47  --demod_completeness_check              fast
% 15.31/2.47  --demod_use_ground                      true
% 15.31/2.47  --sup_to_prop_solver                    passive
% 15.31/2.47  --sup_prop_simpl_new                    true
% 15.31/2.47  --sup_prop_simpl_given                  true
% 15.31/2.47  --sup_fun_splitting                     false
% 15.31/2.47  --sup_smt_interval                      50000
% 15.31/2.47  
% 15.31/2.47  ------ Superposition Simplification Setup
% 15.31/2.47  
% 15.31/2.47  --sup_indices_passive                   []
% 15.31/2.47  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.31/2.47  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.31/2.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.31/2.47  --sup_full_triv                         [TrivRules;PropSubs]
% 15.31/2.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.31/2.47  --sup_full_bw                           [BwDemod]
% 15.31/2.47  --sup_immed_triv                        [TrivRules]
% 15.31/2.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.31/2.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.31/2.47  --sup_immed_bw_main                     []
% 15.31/2.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.31/2.47  --sup_input_triv                        [Unflattening;TrivRules]
% 15.31/2.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.31/2.47  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.31/2.47  
% 15.31/2.47  ------ Combination Options
% 15.31/2.47  
% 15.31/2.47  --comb_res_mult                         3
% 15.31/2.47  --comb_sup_mult                         2
% 15.31/2.47  --comb_inst_mult                        10
% 15.31/2.47  
% 15.31/2.47  ------ Debug Options
% 15.31/2.47  
% 15.31/2.47  --dbg_backtrace                         false
% 15.31/2.47  --dbg_dump_prop_clauses                 false
% 15.31/2.47  --dbg_dump_prop_clauses_file            -
% 15.31/2.47  --dbg_out_stat                          false
% 15.31/2.47  
% 15.31/2.47  
% 15.31/2.47  
% 15.31/2.47  
% 15.31/2.47  ------ Proving...
% 15.31/2.47  
% 15.31/2.47  
% 15.31/2.47  % SZS status Theorem for theBenchmark.p
% 15.31/2.47  
% 15.31/2.47  % SZS output start CNFRefutation for theBenchmark.p
% 15.31/2.47  
% 15.31/2.47  fof(f10,conjecture,(
% 15.31/2.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 15.31/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.31/2.47  
% 15.31/2.47  fof(f11,negated_conjecture,(
% 15.31/2.47    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 15.31/2.47    inference(negated_conjecture,[],[f10])).
% 15.31/2.47  
% 15.31/2.47  fof(f20,plain,(
% 15.31/2.47    ? [X0] : (? [X1] : ((~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 15.31/2.47    inference(ennf_transformation,[],[f11])).
% 15.31/2.47  
% 15.31/2.47  fof(f21,plain,(
% 15.31/2.47    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 15.31/2.47    inference(flattening,[],[f20])).
% 15.31/2.47  
% 15.31/2.47  fof(f25,plain,(
% 15.31/2.47    ( ! [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(X0),k3_relat_1(sK1)) & r1_tarski(X0,sK1) & v1_relat_1(sK1))) )),
% 15.31/2.47    introduced(choice_axiom,[])).
% 15.31/2.47  
% 15.31/2.47  fof(f24,plain,(
% 15.31/2.47    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(sK0),k3_relat_1(X1)) & r1_tarski(sK0,X1) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 15.31/2.47    introduced(choice_axiom,[])).
% 15.31/2.47  
% 15.31/2.47  fof(f26,plain,(
% 15.31/2.47    (~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 15.31/2.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f25,f24])).
% 15.31/2.47  
% 15.31/2.47  fof(f40,plain,(
% 15.31/2.47    r1_tarski(sK0,sK1)),
% 15.31/2.47    inference(cnf_transformation,[],[f26])).
% 15.31/2.47  
% 15.31/2.47  fof(f6,axiom,(
% 15.31/2.47    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 15.31/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.31/2.47  
% 15.31/2.47  fof(f15,plain,(
% 15.31/2.47    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 15.31/2.47    inference(ennf_transformation,[],[f6])).
% 15.31/2.47  
% 15.31/2.47  fof(f16,plain,(
% 15.31/2.47    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 15.31/2.47    inference(flattening,[],[f15])).
% 15.31/2.47  
% 15.31/2.47  fof(f34,plain,(
% 15.31/2.47    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 15.31/2.47    inference(cnf_transformation,[],[f16])).
% 15.31/2.47  
% 15.31/2.47  fof(f5,axiom,(
% 15.31/2.47    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 15.31/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.31/2.47  
% 15.31/2.47  fof(f33,plain,(
% 15.31/2.47    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 15.31/2.47    inference(cnf_transformation,[],[f5])).
% 15.31/2.47  
% 15.31/2.47  fof(f2,axiom,(
% 15.31/2.47    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 15.31/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.31/2.47  
% 15.31/2.47  fof(f22,plain,(
% 15.31/2.47    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.31/2.47    inference(nnf_transformation,[],[f2])).
% 15.31/2.47  
% 15.31/2.47  fof(f23,plain,(
% 15.31/2.47    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.31/2.47    inference(flattening,[],[f22])).
% 15.31/2.47  
% 15.31/2.47  fof(f30,plain,(
% 15.31/2.47    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 15.31/2.47    inference(cnf_transformation,[],[f23])).
% 15.31/2.47  
% 15.31/2.47  fof(f28,plain,(
% 15.31/2.47    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 15.31/2.47    inference(cnf_transformation,[],[f23])).
% 15.31/2.47  
% 15.31/2.47  fof(f43,plain,(
% 15.31/2.47    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 15.31/2.47    inference(equality_resolution,[],[f28])).
% 15.31/2.47  
% 15.31/2.47  fof(f1,axiom,(
% 15.31/2.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 15.31/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.31/2.47  
% 15.31/2.47  fof(f27,plain,(
% 15.31/2.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 15.31/2.47    inference(cnf_transformation,[],[f1])).
% 15.31/2.47  
% 15.31/2.47  fof(f38,plain,(
% 15.31/2.47    v1_relat_1(sK0)),
% 15.31/2.47    inference(cnf_transformation,[],[f26])).
% 15.31/2.47  
% 15.31/2.47  fof(f39,plain,(
% 15.31/2.47    v1_relat_1(sK1)),
% 15.31/2.47    inference(cnf_transformation,[],[f26])).
% 15.31/2.47  
% 15.31/2.47  fof(f9,axiom,(
% 15.31/2.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1))))),
% 15.31/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.31/2.47  
% 15.31/2.47  fof(f19,plain,(
% 15.31/2.47    ! [X0] : (! [X1] : (k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 15.31/2.47    inference(ennf_transformation,[],[f9])).
% 15.31/2.47  
% 15.31/2.47  fof(f37,plain,(
% 15.31/2.47    ( ! [X0,X1] : (k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 15.31/2.47    inference(cnf_transformation,[],[f19])).
% 15.31/2.47  
% 15.31/2.47  fof(f7,axiom,(
% 15.31/2.47    ! [X0] : (v1_relat_1(X0) => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0))),
% 15.31/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.31/2.47  
% 15.31/2.47  fof(f17,plain,(
% 15.31/2.47    ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0))),
% 15.31/2.47    inference(ennf_transformation,[],[f7])).
% 15.31/2.47  
% 15.31/2.47  fof(f35,plain,(
% 15.31/2.47    ( ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 15.31/2.47    inference(cnf_transformation,[],[f17])).
% 15.31/2.47  
% 15.31/2.47  fof(f3,axiom,(
% 15.31/2.47    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 15.31/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.31/2.47  
% 15.31/2.47  fof(f12,plain,(
% 15.31/2.47    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 15.31/2.47    inference(ennf_transformation,[],[f3])).
% 15.31/2.47  
% 15.31/2.47  fof(f31,plain,(
% 15.31/2.47    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 15.31/2.47    inference(cnf_transformation,[],[f12])).
% 15.31/2.47  
% 15.31/2.47  fof(f8,axiom,(
% 15.31/2.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1))))),
% 15.31/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.31/2.47  
% 15.31/2.47  fof(f18,plain,(
% 15.31/2.47    ! [X0] : (! [X1] : (k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 15.31/2.47    inference(ennf_transformation,[],[f8])).
% 15.31/2.47  
% 15.31/2.47  fof(f36,plain,(
% 15.31/2.47    ( ! [X0,X1] : (k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 15.31/2.47    inference(cnf_transformation,[],[f18])).
% 15.31/2.47  
% 15.31/2.47  fof(f41,plain,(
% 15.31/2.47    ~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))),
% 15.31/2.47    inference(cnf_transformation,[],[f26])).
% 15.31/2.47  
% 15.31/2.47  cnf(c_12,negated_conjecture,
% 15.31/2.47      ( r1_tarski(sK0,sK1) ),
% 15.31/2.47      inference(cnf_transformation,[],[f40]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_400,plain,
% 15.31/2.47      ( r1_tarski(sK0,sK1) = iProver_top ),
% 15.31/2.47      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_7,plain,
% 15.31/2.47      ( ~ r1_tarski(X0,X1)
% 15.31/2.47      | ~ r1_tarski(X2,X1)
% 15.31/2.47      | r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 15.31/2.47      inference(cnf_transformation,[],[f34]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_405,plain,
% 15.31/2.47      ( r1_tarski(X0,X1) != iProver_top
% 15.31/2.47      | r1_tarski(X2,X1) != iProver_top
% 15.31/2.47      | r1_tarski(k2_xboole_0(X0,X2),X1) = iProver_top ),
% 15.31/2.47      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_6,plain,
% 15.31/2.47      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 15.31/2.47      inference(cnf_transformation,[],[f33]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_406,plain,
% 15.31/2.47      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 15.31/2.47      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_1,plain,
% 15.31/2.47      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 15.31/2.47      inference(cnf_transformation,[],[f30]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_410,plain,
% 15.31/2.47      ( X0 = X1
% 15.31/2.47      | r1_tarski(X0,X1) != iProver_top
% 15.31/2.47      | r1_tarski(X1,X0) != iProver_top ),
% 15.31/2.47      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_1160,plain,
% 15.31/2.47      ( k2_xboole_0(X0,X1) = X0
% 15.31/2.47      | r1_tarski(k2_xboole_0(X0,X1),X0) != iProver_top ),
% 15.31/2.47      inference(superposition,[status(thm)],[c_406,c_410]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_4094,plain,
% 15.31/2.47      ( k2_xboole_0(X0,X1) = X0
% 15.31/2.47      | r1_tarski(X0,X0) != iProver_top
% 15.31/2.47      | r1_tarski(X1,X0) != iProver_top ),
% 15.31/2.47      inference(superposition,[status(thm)],[c_405,c_1160]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_3,plain,
% 15.31/2.47      ( r1_tarski(X0,X0) ),
% 15.31/2.47      inference(cnf_transformation,[],[f43]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_36,plain,
% 15.31/2.47      ( r1_tarski(X0,X0) = iProver_top ),
% 15.31/2.47      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_51983,plain,
% 15.31/2.47      ( k2_xboole_0(X0,X1) = X0 | r1_tarski(X1,X0) != iProver_top ),
% 15.31/2.47      inference(global_propositional_subsumption,
% 15.31/2.47                [status(thm)],
% 15.31/2.47                [c_4094,c_36]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_51993,plain,
% 15.31/2.47      ( k2_xboole_0(sK1,sK0) = sK1 ),
% 15.31/2.47      inference(superposition,[status(thm)],[c_400,c_51983]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_0,plain,
% 15.31/2.47      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 15.31/2.47      inference(cnf_transformation,[],[f27]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_53255,plain,
% 15.31/2.47      ( k2_xboole_0(sK0,sK1) = sK1 ),
% 15.31/2.47      inference(superposition,[status(thm)],[c_51993,c_0]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_14,negated_conjecture,
% 15.31/2.47      ( v1_relat_1(sK0) ),
% 15.31/2.47      inference(cnf_transformation,[],[f38]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_398,plain,
% 15.31/2.47      ( v1_relat_1(sK0) = iProver_top ),
% 15.31/2.47      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_13,negated_conjecture,
% 15.31/2.47      ( v1_relat_1(sK1) ),
% 15.31/2.47      inference(cnf_transformation,[],[f39]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_399,plain,
% 15.31/2.47      ( v1_relat_1(sK1) = iProver_top ),
% 15.31/2.47      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_10,plain,
% 15.31/2.47      ( ~ v1_relat_1(X0)
% 15.31/2.47      | ~ v1_relat_1(X1)
% 15.31/2.47      | k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1)) ),
% 15.31/2.47      inference(cnf_transformation,[],[f37]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_402,plain,
% 15.31/2.47      ( k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1))
% 15.31/2.47      | v1_relat_1(X0) != iProver_top
% 15.31/2.47      | v1_relat_1(X1) != iProver_top ),
% 15.31/2.47      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_999,plain,
% 15.31/2.47      ( k2_xboole_0(k2_relat_1(sK1),k2_relat_1(X0)) = k2_relat_1(k2_xboole_0(sK1,X0))
% 15.31/2.47      | v1_relat_1(X0) != iProver_top ),
% 15.31/2.47      inference(superposition,[status(thm)],[c_399,c_402]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_2225,plain,
% 15.31/2.47      ( k2_xboole_0(k2_relat_1(sK1),k2_relat_1(sK0)) = k2_relat_1(k2_xboole_0(sK1,sK0)) ),
% 15.31/2.47      inference(superposition,[status(thm)],[c_398,c_999]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_736,plain,
% 15.31/2.47      ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
% 15.31/2.47      inference(superposition,[status(thm)],[c_0,c_406]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_2973,plain,
% 15.31/2.47      ( r1_tarski(k2_relat_1(sK0),k2_relat_1(k2_xboole_0(sK1,sK0))) = iProver_top ),
% 15.31/2.47      inference(superposition,[status(thm)],[c_2225,c_736]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_3752,plain,
% 15.31/2.47      ( r1_tarski(k2_relat_1(sK0),k2_relat_1(k2_xboole_0(sK0,sK1))) = iProver_top ),
% 15.31/2.47      inference(superposition,[status(thm)],[c_0,c_2973]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_54059,plain,
% 15.31/2.47      ( r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) = iProver_top ),
% 15.31/2.47      inference(demodulation,[status(thm)],[c_53255,c_3752]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_8,plain,
% 15.31/2.47      ( ~ v1_relat_1(X0)
% 15.31/2.47      | k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ),
% 15.31/2.47      inference(cnf_transformation,[],[f35]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_404,plain,
% 15.31/2.47      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
% 15.31/2.47      | v1_relat_1(X0) != iProver_top ),
% 15.31/2.47      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_861,plain,
% 15.31/2.47      ( k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1)) = k3_relat_1(sK1) ),
% 15.31/2.47      inference(superposition,[status(thm)],[c_399,c_404]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_4,plain,
% 15.31/2.47      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
% 15.31/2.47      inference(cnf_transformation,[],[f31]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_408,plain,
% 15.31/2.47      ( r1_tarski(X0,X1) != iProver_top
% 15.31/2.47      | r1_tarski(X0,k2_xboole_0(X2,X1)) = iProver_top ),
% 15.31/2.47      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_1625,plain,
% 15.31/2.47      ( r1_tarski(X0,k3_relat_1(sK1)) = iProver_top
% 15.31/2.47      | r1_tarski(X0,k2_relat_1(sK1)) != iProver_top ),
% 15.31/2.47      inference(superposition,[status(thm)],[c_861,c_408]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_55681,plain,
% 15.31/2.47      ( r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1)) = iProver_top ),
% 15.31/2.47      inference(superposition,[status(thm)],[c_54059,c_1625]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_9,plain,
% 15.31/2.47      ( ~ v1_relat_1(X0)
% 15.31/2.47      | ~ v1_relat_1(X1)
% 15.31/2.47      | k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) ),
% 15.31/2.47      inference(cnf_transformation,[],[f36]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_403,plain,
% 15.31/2.47      ( k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1))
% 15.31/2.47      | v1_relat_1(X0) != iProver_top
% 15.31/2.47      | v1_relat_1(X1) != iProver_top ),
% 15.31/2.47      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_1418,plain,
% 15.31/2.47      ( k2_xboole_0(k1_relat_1(sK1),k1_relat_1(X0)) = k1_relat_1(k2_xboole_0(sK1,X0))
% 15.31/2.47      | v1_relat_1(X0) != iProver_top ),
% 15.31/2.47      inference(superposition,[status(thm)],[c_399,c_403]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_12697,plain,
% 15.31/2.47      ( k2_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0)) = k1_relat_1(k2_xboole_0(sK1,sK0)) ),
% 15.31/2.47      inference(superposition,[status(thm)],[c_398,c_1418]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_13074,plain,
% 15.31/2.47      ( r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK1,sK0))) = iProver_top ),
% 15.31/2.47      inference(superposition,[status(thm)],[c_12697,c_736]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_13548,plain,
% 15.31/2.47      ( r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK0,sK1))) = iProver_top ),
% 15.31/2.47      inference(superposition,[status(thm)],[c_0,c_13074]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_54054,plain,
% 15.31/2.47      ( r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1)) = iProver_top ),
% 15.31/2.47      inference(demodulation,[status(thm)],[c_53255,c_13548]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_870,plain,
% 15.31/2.47      ( r1_tarski(X0,X1) != iProver_top
% 15.31/2.47      | r1_tarski(X0,k2_xboole_0(X1,X2)) = iProver_top ),
% 15.31/2.47      inference(superposition,[status(thm)],[c_0,c_408]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_1627,plain,
% 15.31/2.47      ( r1_tarski(X0,k3_relat_1(sK1)) = iProver_top
% 15.31/2.47      | r1_tarski(X0,k1_relat_1(sK1)) != iProver_top ),
% 15.31/2.47      inference(superposition,[status(thm)],[c_861,c_870]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_54251,plain,
% 15.31/2.47      ( r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) = iProver_top ),
% 15.31/2.47      inference(superposition,[status(thm)],[c_54054,c_1627]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_1749,plain,
% 15.31/2.47      ( r1_tarski(k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)),X0)
% 15.31/2.47      | ~ r1_tarski(k2_relat_1(sK0),X0)
% 15.31/2.47      | ~ r1_tarski(k1_relat_1(sK0),X0) ),
% 15.31/2.47      inference(instantiation,[status(thm)],[c_7]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_10378,plain,
% 15.31/2.47      ( r1_tarski(k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)),k3_relat_1(sK1))
% 15.31/2.47      | ~ r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1))
% 15.31/2.47      | ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
% 15.31/2.47      inference(instantiation,[status(thm)],[c_1749]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_10383,plain,
% 15.31/2.47      ( r1_tarski(k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)),k3_relat_1(sK1)) = iProver_top
% 15.31/2.47      | r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1)) != iProver_top
% 15.31/2.47      | r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) != iProver_top ),
% 15.31/2.47      inference(predicate_to_equality,[status(thm)],[c_10378]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_189,plain,
% 15.31/2.47      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 15.31/2.47      theory(equality) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_522,plain,
% 15.31/2.47      ( ~ r1_tarski(X0,X1)
% 15.31/2.47      | r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
% 15.31/2.47      | k3_relat_1(sK1) != X1
% 15.31/2.47      | k3_relat_1(sK0) != X0 ),
% 15.31/2.47      inference(instantiation,[status(thm)],[c_189]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_984,plain,
% 15.31/2.47      ( ~ r1_tarski(k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)),X0)
% 15.31/2.47      | r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
% 15.31/2.47      | k3_relat_1(sK1) != X0
% 15.31/2.47      | k3_relat_1(sK0) != k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)) ),
% 15.31/2.47      inference(instantiation,[status(thm)],[c_522]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_1088,plain,
% 15.31/2.47      ( ~ r1_tarski(k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)),k3_relat_1(sK1))
% 15.31/2.47      | r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
% 15.31/2.47      | k3_relat_1(sK1) != k3_relat_1(sK1)
% 15.31/2.47      | k3_relat_1(sK0) != k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)) ),
% 15.31/2.47      inference(instantiation,[status(thm)],[c_984]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_1089,plain,
% 15.31/2.47      ( k3_relat_1(sK1) != k3_relat_1(sK1)
% 15.31/2.47      | k3_relat_1(sK0) != k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0))
% 15.31/2.47      | r1_tarski(k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)),k3_relat_1(sK1)) != iProver_top
% 15.31/2.47      | r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) = iProver_top ),
% 15.31/2.47      inference(predicate_to_equality,[status(thm)],[c_1088]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_187,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_579,plain,
% 15.31/2.47      ( X0 != X1 | k3_relat_1(sK0) != X1 | k3_relat_1(sK0) = X0 ),
% 15.31/2.47      inference(instantiation,[status(thm)],[c_187]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_682,plain,
% 15.31/2.47      ( X0 != k3_relat_1(sK0)
% 15.31/2.47      | k3_relat_1(sK0) = X0
% 15.31/2.47      | k3_relat_1(sK0) != k3_relat_1(sK0) ),
% 15.31/2.47      inference(instantiation,[status(thm)],[c_579]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_768,plain,
% 15.31/2.47      ( k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)) != k3_relat_1(sK0)
% 15.31/2.47      | k3_relat_1(sK0) = k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0))
% 15.31/2.47      | k3_relat_1(sK0) != k3_relat_1(sK0) ),
% 15.31/2.47      inference(instantiation,[status(thm)],[c_682]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_186,plain,( X0 = X0 ),theory(equality) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_695,plain,
% 15.31/2.47      ( k3_relat_1(sK1) = k3_relat_1(sK1) ),
% 15.31/2.47      inference(instantiation,[status(thm)],[c_186]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_192,plain,
% 15.31/2.47      ( X0 != X1 | k3_relat_1(X0) = k3_relat_1(X1) ),
% 15.31/2.47      theory(equality) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_197,plain,
% 15.31/2.47      ( k3_relat_1(sK0) = k3_relat_1(sK0) | sK0 != sK0 ),
% 15.31/2.47      inference(instantiation,[status(thm)],[c_192]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_41,plain,
% 15.31/2.47      ( ~ r1_tarski(sK0,sK0) | sK0 = sK0 ),
% 15.31/2.47      inference(instantiation,[status(thm)],[c_1]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_37,plain,
% 15.31/2.47      ( r1_tarski(sK0,sK0) ),
% 15.31/2.47      inference(instantiation,[status(thm)],[c_3]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_26,plain,
% 15.31/2.47      ( ~ v1_relat_1(sK0)
% 15.31/2.47      | k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)) = k3_relat_1(sK0) ),
% 15.31/2.47      inference(instantiation,[status(thm)],[c_8]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_11,negated_conjecture,
% 15.31/2.47      ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) ),
% 15.31/2.47      inference(cnf_transformation,[],[f41]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_18,plain,
% 15.31/2.47      ( r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) != iProver_top ),
% 15.31/2.47      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(contradiction,plain,
% 15.31/2.47      ( $false ),
% 15.31/2.47      inference(minisat,
% 15.31/2.47                [status(thm)],
% 15.31/2.47                [c_55681,c_54251,c_10383,c_1089,c_768,c_695,c_197,c_41,
% 15.31/2.47                 c_37,c_26,c_18,c_14]) ).
% 15.31/2.47  
% 15.31/2.47  
% 15.31/2.47  % SZS output end CNFRefutation for theBenchmark.p
% 15.31/2.47  
% 15.31/2.47  ------                               Statistics
% 15.31/2.47  
% 15.31/2.47  ------ Selected
% 15.31/2.47  
% 15.31/2.47  total_time:                             1.517
% 15.31/2.47  
%------------------------------------------------------------------------------
