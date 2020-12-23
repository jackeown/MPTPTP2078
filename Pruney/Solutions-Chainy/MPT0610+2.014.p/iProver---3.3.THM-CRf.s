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
% DateTime   : Thu Dec  3 11:48:52 EST 2020

% Result     : Theorem 2.57s
% Output     : CNFRefutation 2.57s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 148 expanded)
%              Number of clauses        :   49 (  61 expanded)
%              Number of leaves         :   10 (  31 expanded)
%              Depth                    :   18
%              Number of atoms          :  187 ( 430 expanded)
%              Number of equality atoms :   85 (  94 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f9,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
           => r1_xboole_0(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
             => r1_xboole_0(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(X0,X1)
          & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(X0,X1)
          & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(X0,X1)
          & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          & v1_relat_1(X1) )
     => ( ~ r1_xboole_0(X0,sK2)
        & r1_xboole_0(k1_relat_1(X0),k1_relat_1(sK2))
        & v1_relat_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_xboole_0(X0,X1)
            & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_xboole_0(sK1,X1)
          & r1_xboole_0(k1_relat_1(sK1),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    & r1_xboole_0(k1_relat_1(sK1),k1_relat_1(sK2))
    & v1_relat_1(sK2)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f20,f26,f25])).

fof(f42,plain,(
    r1_xboole_0(k1_relat_1(sK1),k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f33,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f40,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f41,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f38,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k8_relat_1(k2_relat_1(X0),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( k8_relat_1(k2_relat_1(X0),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f35,plain,(
    ! [X0] :
      ( k8_relat_1(k2_relat_1(X0),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k8_relat_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = k8_relat_1(k1_xboole_0,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f36,plain,(
    ! [X0] :
      ( k1_xboole_0 = k8_relat_1(k1_xboole_0,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f43,plain,(
    ~ r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_631,plain,
    ( ~ v1_relat_1(X0_40)
    | v1_relat_1(k3_xboole_0(X0_40,X1_40)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1031,plain,
    ( v1_relat_1(X0_40) != iProver_top
    | v1_relat_1(k3_xboole_0(X0_40,X1_40)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_631])).

cnf(c_13,negated_conjecture,
    ( r1_xboole_0(k1_relat_1(sK1),k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_625,negated_conjecture,
    ( r1_xboole_0(k1_relat_1(sK1),k1_relat_1(sK2)) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1037,plain,
    ( r1_xboole_0(k1_relat_1(sK1),k1_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_625])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_635,plain,
    ( ~ r1_xboole_0(X0_40,X1_40)
    | k3_xboole_0(X0_40,X1_40) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1027,plain,
    ( k3_xboole_0(X0_40,X1_40) = k1_xboole_0
    | r1_xboole_0(X0_40,X1_40) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_635])).

cnf(c_1478,plain,
    ( k3_xboole_0(k1_relat_1(sK1),k1_relat_1(sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1037,c_1027])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_9,plain,
    ( r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_215,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) != k1_xboole_0
    | k1_relat_1(k3_xboole_0(X0,X1)) != X2
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_9])).

cnf(c_216,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(k3_xboole_0(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_215])).

cnf(c_622,plain,
    ( ~ v1_relat_1(X0_40)
    | ~ v1_relat_1(X1_40)
    | k3_xboole_0(k1_relat_1(X0_40),k1_relat_1(X1_40)) != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(k3_xboole_0(X0_40,X1_40)) ),
    inference(subtyping,[status(esa)],[c_216])).

cnf(c_1040,plain,
    ( k3_xboole_0(k1_relat_1(X0_40),k1_relat_1(X1_40)) != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(k3_xboole_0(X0_40,X1_40))
    | v1_relat_1(X0_40) != iProver_top
    | v1_relat_1(X1_40) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_622])).

cnf(c_2801,plain,
    ( k1_relat_1(k3_xboole_0(sK1,sK2)) = k1_xboole_0
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1478,c_1040])).

cnf(c_15,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_16,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_14,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_17,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3017,plain,
    ( k1_relat_1(k3_xboole_0(sK1,sK2)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2801,c_16,c_17])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k2_relat_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_627,plain,
    ( ~ v1_relat_1(X0_40)
    | k1_relat_1(X0_40) != k1_xboole_0
    | k2_relat_1(X0_40) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1035,plain,
    ( k1_relat_1(X0_40) != k1_xboole_0
    | k2_relat_1(X0_40) = k1_xboole_0
    | v1_relat_1(X0_40) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_627])).

cnf(c_3021,plain,
    ( k2_relat_1(k3_xboole_0(sK1,sK2)) = k1_xboole_0
    | v1_relat_1(k3_xboole_0(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3017,c_1035])).

cnf(c_3165,plain,
    ( k2_relat_1(k3_xboole_0(sK1,sK2)) = k1_xboole_0
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1031,c_3021])).

cnf(c_3578,plain,
    ( k2_relat_1(k3_xboole_0(sK1,sK2)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3165,c_16])).

cnf(c_623,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1039,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_623])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k8_relat_1(k2_relat_1(X0),X0) = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_630,plain,
    ( ~ v1_relat_1(X0_40)
    | k8_relat_1(k2_relat_1(X0_40),X0_40) = X0_40 ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1032,plain,
    ( k8_relat_1(k2_relat_1(X0_40),X0_40) = X0_40
    | v1_relat_1(X0_40) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_630])).

cnf(c_1549,plain,
    ( k8_relat_1(k2_relat_1(k3_xboole_0(X0_40,X1_40)),k3_xboole_0(X0_40,X1_40)) = k3_xboole_0(X0_40,X1_40)
    | v1_relat_1(X0_40) != iProver_top ),
    inference(superposition,[status(thm)],[c_1031,c_1032])).

cnf(c_2422,plain,
    ( k8_relat_1(k2_relat_1(k3_xboole_0(sK1,X0_40)),k3_xboole_0(sK1,X0_40)) = k3_xboole_0(sK1,X0_40) ),
    inference(superposition,[status(thm)],[c_1039,c_1549])).

cnf(c_3582,plain,
    ( k8_relat_1(k1_xboole_0,k3_xboole_0(sK1,sK2)) = k3_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_3578,c_2422])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k8_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_629,plain,
    ( ~ v1_relat_1(X0_40)
    | k8_relat_1(k1_xboole_0,X0_40) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1033,plain,
    ( k8_relat_1(k1_xboole_0,X0_40) = k1_xboole_0
    | v1_relat_1(X0_40) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_629])).

cnf(c_1482,plain,
    ( k8_relat_1(k1_xboole_0,k3_xboole_0(X0_40,X1_40)) = k1_xboole_0
    | v1_relat_1(X0_40) != iProver_top ),
    inference(superposition,[status(thm)],[c_1031,c_1033])).

cnf(c_1830,plain,
    ( k8_relat_1(k1_xboole_0,k3_xboole_0(sK1,X0_40)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1039,c_1482])).

cnf(c_3584,plain,
    ( k3_xboole_0(sK1,sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3582,c_1830])).

cnf(c_0,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_636,plain,
    ( r1_xboole_0(X0_40,X1_40)
    | k3_xboole_0(X0_40,X1_40) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1026,plain,
    ( k3_xboole_0(X0_40,X1_40) != k1_xboole_0
    | r1_xboole_0(X0_40,X1_40) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_636])).

cnf(c_3634,plain,
    ( r1_xboole_0(sK1,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3584,c_1026])).

cnf(c_12,negated_conjecture,
    ( ~ r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_19,plain,
    ( r1_xboole_0(sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3634,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:58:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.57/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.01  
% 2.57/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.57/1.01  
% 2.57/1.01  ------  iProver source info
% 2.57/1.01  
% 2.57/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.57/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.57/1.01  git: non_committed_changes: false
% 2.57/1.01  git: last_make_outside_of_git: false
% 2.57/1.01  
% 2.57/1.01  ------ 
% 2.57/1.01  
% 2.57/1.01  ------ Input Options
% 2.57/1.01  
% 2.57/1.01  --out_options                           all
% 2.57/1.01  --tptp_safe_out                         true
% 2.57/1.01  --problem_path                          ""
% 2.57/1.01  --include_path                          ""
% 2.57/1.01  --clausifier                            res/vclausify_rel
% 2.57/1.01  --clausifier_options                    --mode clausify
% 2.57/1.01  --stdin                                 false
% 2.57/1.01  --stats_out                             all
% 2.57/1.01  
% 2.57/1.01  ------ General Options
% 2.57/1.01  
% 2.57/1.01  --fof                                   false
% 2.57/1.01  --time_out_real                         305.
% 2.57/1.01  --time_out_virtual                      -1.
% 2.57/1.01  --symbol_type_check                     false
% 2.57/1.01  --clausify_out                          false
% 2.57/1.01  --sig_cnt_out                           false
% 2.57/1.01  --trig_cnt_out                          false
% 2.57/1.01  --trig_cnt_out_tolerance                1.
% 2.57/1.01  --trig_cnt_out_sk_spl                   false
% 2.57/1.01  --abstr_cl_out                          false
% 2.57/1.01  
% 2.57/1.01  ------ Global Options
% 2.57/1.01  
% 2.57/1.01  --schedule                              default
% 2.57/1.01  --add_important_lit                     false
% 2.57/1.01  --prop_solver_per_cl                    1000
% 2.57/1.01  --min_unsat_core                        false
% 2.57/1.01  --soft_assumptions                      false
% 2.57/1.01  --soft_lemma_size                       3
% 2.57/1.01  --prop_impl_unit_size                   0
% 2.57/1.01  --prop_impl_unit                        []
% 2.57/1.01  --share_sel_clauses                     true
% 2.57/1.01  --reset_solvers                         false
% 2.57/1.01  --bc_imp_inh                            [conj_cone]
% 2.57/1.01  --conj_cone_tolerance                   3.
% 2.57/1.01  --extra_neg_conj                        none
% 2.57/1.01  --large_theory_mode                     true
% 2.57/1.01  --prolific_symb_bound                   200
% 2.57/1.01  --lt_threshold                          2000
% 2.57/1.01  --clause_weak_htbl                      true
% 2.57/1.01  --gc_record_bc_elim                     false
% 2.57/1.01  
% 2.57/1.01  ------ Preprocessing Options
% 2.57/1.01  
% 2.57/1.01  --preprocessing_flag                    true
% 2.57/1.01  --time_out_prep_mult                    0.1
% 2.57/1.01  --splitting_mode                        input
% 2.57/1.01  --splitting_grd                         true
% 2.57/1.01  --splitting_cvd                         false
% 2.57/1.01  --splitting_cvd_svl                     false
% 2.57/1.01  --splitting_nvd                         32
% 2.57/1.01  --sub_typing                            true
% 2.57/1.01  --prep_gs_sim                           true
% 2.57/1.01  --prep_unflatten                        true
% 2.57/1.01  --prep_res_sim                          true
% 2.57/1.01  --prep_upred                            true
% 2.57/1.01  --prep_sem_filter                       exhaustive
% 2.57/1.01  --prep_sem_filter_out                   false
% 2.57/1.01  --pred_elim                             true
% 2.57/1.01  --res_sim_input                         true
% 2.57/1.01  --eq_ax_congr_red                       true
% 2.57/1.01  --pure_diseq_elim                       true
% 2.57/1.01  --brand_transform                       false
% 2.57/1.01  --non_eq_to_eq                          false
% 2.57/1.01  --prep_def_merge                        true
% 2.57/1.01  --prep_def_merge_prop_impl              false
% 2.57/1.01  --prep_def_merge_mbd                    true
% 2.57/1.01  --prep_def_merge_tr_red                 false
% 2.57/1.01  --prep_def_merge_tr_cl                  false
% 2.57/1.01  --smt_preprocessing                     true
% 2.57/1.01  --smt_ac_axioms                         fast
% 2.57/1.01  --preprocessed_out                      false
% 2.57/1.01  --preprocessed_stats                    false
% 2.57/1.01  
% 2.57/1.01  ------ Abstraction refinement Options
% 2.57/1.01  
% 2.57/1.01  --abstr_ref                             []
% 2.57/1.01  --abstr_ref_prep                        false
% 2.57/1.01  --abstr_ref_until_sat                   false
% 2.57/1.01  --abstr_ref_sig_restrict                funpre
% 2.57/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.57/1.01  --abstr_ref_under                       []
% 2.57/1.01  
% 2.57/1.01  ------ SAT Options
% 2.57/1.01  
% 2.57/1.01  --sat_mode                              false
% 2.57/1.01  --sat_fm_restart_options                ""
% 2.57/1.01  --sat_gr_def                            false
% 2.57/1.01  --sat_epr_types                         true
% 2.57/1.01  --sat_non_cyclic_types                  false
% 2.57/1.01  --sat_finite_models                     false
% 2.57/1.01  --sat_fm_lemmas                         false
% 2.57/1.01  --sat_fm_prep                           false
% 2.57/1.01  --sat_fm_uc_incr                        true
% 2.57/1.01  --sat_out_model                         small
% 2.57/1.01  --sat_out_clauses                       false
% 2.57/1.01  
% 2.57/1.01  ------ QBF Options
% 2.57/1.01  
% 2.57/1.01  --qbf_mode                              false
% 2.57/1.01  --qbf_elim_univ                         false
% 2.57/1.01  --qbf_dom_inst                          none
% 2.57/1.01  --qbf_dom_pre_inst                      false
% 2.57/1.01  --qbf_sk_in                             false
% 2.57/1.01  --qbf_pred_elim                         true
% 2.57/1.01  --qbf_split                             512
% 2.57/1.01  
% 2.57/1.01  ------ BMC1 Options
% 2.57/1.01  
% 2.57/1.01  --bmc1_incremental                      false
% 2.57/1.01  --bmc1_axioms                           reachable_all
% 2.57/1.01  --bmc1_min_bound                        0
% 2.57/1.01  --bmc1_max_bound                        -1
% 2.57/1.01  --bmc1_max_bound_default                -1
% 2.57/1.01  --bmc1_symbol_reachability              true
% 2.57/1.01  --bmc1_property_lemmas                  false
% 2.57/1.01  --bmc1_k_induction                      false
% 2.57/1.01  --bmc1_non_equiv_states                 false
% 2.57/1.01  --bmc1_deadlock                         false
% 2.57/1.01  --bmc1_ucm                              false
% 2.57/1.01  --bmc1_add_unsat_core                   none
% 2.57/1.01  --bmc1_unsat_core_children              false
% 2.57/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.57/1.01  --bmc1_out_stat                         full
% 2.57/1.01  --bmc1_ground_init                      false
% 2.57/1.01  --bmc1_pre_inst_next_state              false
% 2.57/1.01  --bmc1_pre_inst_state                   false
% 2.57/1.01  --bmc1_pre_inst_reach_state             false
% 2.57/1.01  --bmc1_out_unsat_core                   false
% 2.57/1.01  --bmc1_aig_witness_out                  false
% 2.57/1.01  --bmc1_verbose                          false
% 2.57/1.01  --bmc1_dump_clauses_tptp                false
% 2.57/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.57/1.01  --bmc1_dump_file                        -
% 2.57/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.57/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.57/1.01  --bmc1_ucm_extend_mode                  1
% 2.57/1.01  --bmc1_ucm_init_mode                    2
% 2.57/1.01  --bmc1_ucm_cone_mode                    none
% 2.57/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.57/1.01  --bmc1_ucm_relax_model                  4
% 2.57/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.57/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.57/1.01  --bmc1_ucm_layered_model                none
% 2.57/1.01  --bmc1_ucm_max_lemma_size               10
% 2.57/1.01  
% 2.57/1.01  ------ AIG Options
% 2.57/1.01  
% 2.57/1.01  --aig_mode                              false
% 2.57/1.01  
% 2.57/1.01  ------ Instantiation Options
% 2.57/1.01  
% 2.57/1.01  --instantiation_flag                    true
% 2.57/1.01  --inst_sos_flag                         false
% 2.57/1.01  --inst_sos_phase                        true
% 2.57/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.57/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.57/1.01  --inst_lit_sel_side                     num_symb
% 2.57/1.01  --inst_solver_per_active                1400
% 2.57/1.01  --inst_solver_calls_frac                1.
% 2.57/1.01  --inst_passive_queue_type               priority_queues
% 2.57/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.57/1.01  --inst_passive_queues_freq              [25;2]
% 2.57/1.01  --inst_dismatching                      true
% 2.57/1.01  --inst_eager_unprocessed_to_passive     true
% 2.57/1.01  --inst_prop_sim_given                   true
% 2.57/1.01  --inst_prop_sim_new                     false
% 2.57/1.01  --inst_subs_new                         false
% 2.57/1.01  --inst_eq_res_simp                      false
% 2.57/1.01  --inst_subs_given                       false
% 2.57/1.01  --inst_orphan_elimination               true
% 2.57/1.01  --inst_learning_loop_flag               true
% 2.57/1.01  --inst_learning_start                   3000
% 2.57/1.01  --inst_learning_factor                  2
% 2.57/1.01  --inst_start_prop_sim_after_learn       3
% 2.57/1.01  --inst_sel_renew                        solver
% 2.57/1.01  --inst_lit_activity_flag                true
% 2.57/1.01  --inst_restr_to_given                   false
% 2.57/1.01  --inst_activity_threshold               500
% 2.57/1.01  --inst_out_proof                        true
% 2.57/1.01  
% 2.57/1.01  ------ Resolution Options
% 2.57/1.01  
% 2.57/1.01  --resolution_flag                       true
% 2.57/1.01  --res_lit_sel                           adaptive
% 2.57/1.01  --res_lit_sel_side                      none
% 2.57/1.01  --res_ordering                          kbo
% 2.57/1.01  --res_to_prop_solver                    active
% 2.57/1.01  --res_prop_simpl_new                    false
% 2.57/1.01  --res_prop_simpl_given                  true
% 2.57/1.01  --res_passive_queue_type                priority_queues
% 2.57/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.57/1.01  --res_passive_queues_freq               [15;5]
% 2.57/1.01  --res_forward_subs                      full
% 2.57/1.01  --res_backward_subs                     full
% 2.57/1.01  --res_forward_subs_resolution           true
% 2.57/1.01  --res_backward_subs_resolution          true
% 2.57/1.01  --res_orphan_elimination                true
% 2.57/1.01  --res_time_limit                        2.
% 2.57/1.01  --res_out_proof                         true
% 2.57/1.01  
% 2.57/1.01  ------ Superposition Options
% 2.57/1.01  
% 2.57/1.01  --superposition_flag                    true
% 2.57/1.01  --sup_passive_queue_type                priority_queues
% 2.57/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.57/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.57/1.01  --demod_completeness_check              fast
% 2.57/1.01  --demod_use_ground                      true
% 2.57/1.01  --sup_to_prop_solver                    passive
% 2.57/1.01  --sup_prop_simpl_new                    true
% 2.57/1.01  --sup_prop_simpl_given                  true
% 2.57/1.01  --sup_fun_splitting                     false
% 2.57/1.01  --sup_smt_interval                      50000
% 2.57/1.01  
% 2.57/1.01  ------ Superposition Simplification Setup
% 2.57/1.01  
% 2.57/1.01  --sup_indices_passive                   []
% 2.57/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.57/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.57/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.57/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.57/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.57/1.01  --sup_full_bw                           [BwDemod]
% 2.57/1.01  --sup_immed_triv                        [TrivRules]
% 2.57/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.57/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.57/1.01  --sup_immed_bw_main                     []
% 2.57/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.57/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.57/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.57/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.57/1.01  
% 2.57/1.01  ------ Combination Options
% 2.57/1.01  
% 2.57/1.01  --comb_res_mult                         3
% 2.57/1.01  --comb_sup_mult                         2
% 2.57/1.01  --comb_inst_mult                        10
% 2.57/1.01  
% 2.57/1.01  ------ Debug Options
% 2.57/1.01  
% 2.57/1.01  --dbg_backtrace                         false
% 2.57/1.01  --dbg_dump_prop_clauses                 false
% 2.57/1.01  --dbg_dump_prop_clauses_file            -
% 2.57/1.01  --dbg_out_stat                          false
% 2.57/1.01  ------ Parsing...
% 2.57/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.57/1.01  
% 2.57/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.57/1.01  
% 2.57/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.57/1.01  
% 2.57/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.57/1.01  ------ Proving...
% 2.57/1.01  ------ Problem Properties 
% 2.57/1.01  
% 2.57/1.01  
% 2.57/1.01  clauses                                 15
% 2.57/1.01  conjectures                             4
% 2.57/1.01  EPR                                     4
% 2.57/1.01  Horn                                    13
% 2.57/1.01  unary                                   4
% 2.57/1.01  binary                                  7
% 2.57/1.01  lits                                    31
% 2.57/1.01  lits eq                                 10
% 2.57/1.01  fd_pure                                 0
% 2.57/1.01  fd_pseudo                               0
% 2.57/1.01  fd_cond                                 0
% 2.57/1.01  fd_pseudo_cond                          0
% 2.57/1.01  AC symbols                              0
% 2.57/1.01  
% 2.57/1.01  ------ Schedule dynamic 5 is on 
% 2.57/1.01  
% 2.57/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.57/1.01  
% 2.57/1.01  
% 2.57/1.01  ------ 
% 2.57/1.01  Current options:
% 2.57/1.01  ------ 
% 2.57/1.01  
% 2.57/1.01  ------ Input Options
% 2.57/1.01  
% 2.57/1.01  --out_options                           all
% 2.57/1.01  --tptp_safe_out                         true
% 2.57/1.01  --problem_path                          ""
% 2.57/1.01  --include_path                          ""
% 2.57/1.01  --clausifier                            res/vclausify_rel
% 2.57/1.01  --clausifier_options                    --mode clausify
% 2.57/1.01  --stdin                                 false
% 2.57/1.01  --stats_out                             all
% 2.57/1.01  
% 2.57/1.01  ------ General Options
% 2.57/1.01  
% 2.57/1.01  --fof                                   false
% 2.57/1.01  --time_out_real                         305.
% 2.57/1.01  --time_out_virtual                      -1.
% 2.57/1.01  --symbol_type_check                     false
% 2.57/1.01  --clausify_out                          false
% 2.57/1.01  --sig_cnt_out                           false
% 2.57/1.01  --trig_cnt_out                          false
% 2.57/1.01  --trig_cnt_out_tolerance                1.
% 2.57/1.01  --trig_cnt_out_sk_spl                   false
% 2.57/1.01  --abstr_cl_out                          false
% 2.57/1.01  
% 2.57/1.01  ------ Global Options
% 2.57/1.01  
% 2.57/1.01  --schedule                              default
% 2.57/1.01  --add_important_lit                     false
% 2.57/1.01  --prop_solver_per_cl                    1000
% 2.57/1.01  --min_unsat_core                        false
% 2.57/1.01  --soft_assumptions                      false
% 2.57/1.01  --soft_lemma_size                       3
% 2.57/1.01  --prop_impl_unit_size                   0
% 2.57/1.01  --prop_impl_unit                        []
% 2.57/1.01  --share_sel_clauses                     true
% 2.57/1.01  --reset_solvers                         false
% 2.57/1.01  --bc_imp_inh                            [conj_cone]
% 2.57/1.01  --conj_cone_tolerance                   3.
% 2.57/1.01  --extra_neg_conj                        none
% 2.57/1.01  --large_theory_mode                     true
% 2.57/1.01  --prolific_symb_bound                   200
% 2.57/1.01  --lt_threshold                          2000
% 2.57/1.01  --clause_weak_htbl                      true
% 2.57/1.01  --gc_record_bc_elim                     false
% 2.57/1.01  
% 2.57/1.01  ------ Preprocessing Options
% 2.57/1.01  
% 2.57/1.01  --preprocessing_flag                    true
% 2.57/1.01  --time_out_prep_mult                    0.1
% 2.57/1.01  --splitting_mode                        input
% 2.57/1.01  --splitting_grd                         true
% 2.57/1.01  --splitting_cvd                         false
% 2.57/1.01  --splitting_cvd_svl                     false
% 2.57/1.01  --splitting_nvd                         32
% 2.57/1.01  --sub_typing                            true
% 2.57/1.01  --prep_gs_sim                           true
% 2.57/1.01  --prep_unflatten                        true
% 2.57/1.01  --prep_res_sim                          true
% 2.57/1.01  --prep_upred                            true
% 2.57/1.01  --prep_sem_filter                       exhaustive
% 2.57/1.01  --prep_sem_filter_out                   false
% 2.57/1.01  --pred_elim                             true
% 2.57/1.01  --res_sim_input                         true
% 2.57/1.01  --eq_ax_congr_red                       true
% 2.57/1.01  --pure_diseq_elim                       true
% 2.57/1.01  --brand_transform                       false
% 2.57/1.01  --non_eq_to_eq                          false
% 2.57/1.01  --prep_def_merge                        true
% 2.57/1.01  --prep_def_merge_prop_impl              false
% 2.57/1.01  --prep_def_merge_mbd                    true
% 2.57/1.01  --prep_def_merge_tr_red                 false
% 2.57/1.01  --prep_def_merge_tr_cl                  false
% 2.57/1.01  --smt_preprocessing                     true
% 2.57/1.01  --smt_ac_axioms                         fast
% 2.57/1.01  --preprocessed_out                      false
% 2.57/1.01  --preprocessed_stats                    false
% 2.57/1.01  
% 2.57/1.01  ------ Abstraction refinement Options
% 2.57/1.01  
% 2.57/1.01  --abstr_ref                             []
% 2.57/1.01  --abstr_ref_prep                        false
% 2.57/1.01  --abstr_ref_until_sat                   false
% 2.57/1.01  --abstr_ref_sig_restrict                funpre
% 2.57/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.57/1.01  --abstr_ref_under                       []
% 2.57/1.01  
% 2.57/1.01  ------ SAT Options
% 2.57/1.01  
% 2.57/1.01  --sat_mode                              false
% 2.57/1.01  --sat_fm_restart_options                ""
% 2.57/1.01  --sat_gr_def                            false
% 2.57/1.01  --sat_epr_types                         true
% 2.57/1.01  --sat_non_cyclic_types                  false
% 2.57/1.01  --sat_finite_models                     false
% 2.57/1.01  --sat_fm_lemmas                         false
% 2.57/1.01  --sat_fm_prep                           false
% 2.57/1.01  --sat_fm_uc_incr                        true
% 2.57/1.01  --sat_out_model                         small
% 2.57/1.01  --sat_out_clauses                       false
% 2.57/1.01  
% 2.57/1.01  ------ QBF Options
% 2.57/1.01  
% 2.57/1.01  --qbf_mode                              false
% 2.57/1.01  --qbf_elim_univ                         false
% 2.57/1.01  --qbf_dom_inst                          none
% 2.57/1.01  --qbf_dom_pre_inst                      false
% 2.57/1.01  --qbf_sk_in                             false
% 2.57/1.01  --qbf_pred_elim                         true
% 2.57/1.01  --qbf_split                             512
% 2.57/1.01  
% 2.57/1.01  ------ BMC1 Options
% 2.57/1.01  
% 2.57/1.01  --bmc1_incremental                      false
% 2.57/1.01  --bmc1_axioms                           reachable_all
% 2.57/1.01  --bmc1_min_bound                        0
% 2.57/1.01  --bmc1_max_bound                        -1
% 2.57/1.01  --bmc1_max_bound_default                -1
% 2.57/1.01  --bmc1_symbol_reachability              true
% 2.57/1.01  --bmc1_property_lemmas                  false
% 2.57/1.01  --bmc1_k_induction                      false
% 2.57/1.01  --bmc1_non_equiv_states                 false
% 2.57/1.01  --bmc1_deadlock                         false
% 2.57/1.01  --bmc1_ucm                              false
% 2.57/1.01  --bmc1_add_unsat_core                   none
% 2.57/1.01  --bmc1_unsat_core_children              false
% 2.57/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.57/1.01  --bmc1_out_stat                         full
% 2.57/1.01  --bmc1_ground_init                      false
% 2.57/1.01  --bmc1_pre_inst_next_state              false
% 2.57/1.01  --bmc1_pre_inst_state                   false
% 2.57/1.01  --bmc1_pre_inst_reach_state             false
% 2.57/1.01  --bmc1_out_unsat_core                   false
% 2.57/1.01  --bmc1_aig_witness_out                  false
% 2.57/1.01  --bmc1_verbose                          false
% 2.57/1.01  --bmc1_dump_clauses_tptp                false
% 2.57/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.57/1.01  --bmc1_dump_file                        -
% 2.57/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.57/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.57/1.01  --bmc1_ucm_extend_mode                  1
% 2.57/1.01  --bmc1_ucm_init_mode                    2
% 2.57/1.01  --bmc1_ucm_cone_mode                    none
% 2.57/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.57/1.01  --bmc1_ucm_relax_model                  4
% 2.57/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.57/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.57/1.01  --bmc1_ucm_layered_model                none
% 2.57/1.01  --bmc1_ucm_max_lemma_size               10
% 2.57/1.01  
% 2.57/1.01  ------ AIG Options
% 2.57/1.01  
% 2.57/1.01  --aig_mode                              false
% 2.57/1.01  
% 2.57/1.01  ------ Instantiation Options
% 2.57/1.01  
% 2.57/1.01  --instantiation_flag                    true
% 2.57/1.01  --inst_sos_flag                         false
% 2.57/1.01  --inst_sos_phase                        true
% 2.57/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.57/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.57/1.01  --inst_lit_sel_side                     none
% 2.57/1.01  --inst_solver_per_active                1400
% 2.57/1.01  --inst_solver_calls_frac                1.
% 2.57/1.01  --inst_passive_queue_type               priority_queues
% 2.57/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.57/1.01  --inst_passive_queues_freq              [25;2]
% 2.57/1.01  --inst_dismatching                      true
% 2.57/1.01  --inst_eager_unprocessed_to_passive     true
% 2.57/1.01  --inst_prop_sim_given                   true
% 2.57/1.01  --inst_prop_sim_new                     false
% 2.57/1.01  --inst_subs_new                         false
% 2.57/1.01  --inst_eq_res_simp                      false
% 2.57/1.01  --inst_subs_given                       false
% 2.57/1.01  --inst_orphan_elimination               true
% 2.57/1.01  --inst_learning_loop_flag               true
% 2.57/1.01  --inst_learning_start                   3000
% 2.57/1.01  --inst_learning_factor                  2
% 2.57/1.01  --inst_start_prop_sim_after_learn       3
% 2.57/1.01  --inst_sel_renew                        solver
% 2.57/1.01  --inst_lit_activity_flag                true
% 2.57/1.01  --inst_restr_to_given                   false
% 2.57/1.01  --inst_activity_threshold               500
% 2.57/1.01  --inst_out_proof                        true
% 2.57/1.01  
% 2.57/1.01  ------ Resolution Options
% 2.57/1.01  
% 2.57/1.01  --resolution_flag                       false
% 2.57/1.01  --res_lit_sel                           adaptive
% 2.57/1.01  --res_lit_sel_side                      none
% 2.57/1.01  --res_ordering                          kbo
% 2.57/1.01  --res_to_prop_solver                    active
% 2.57/1.01  --res_prop_simpl_new                    false
% 2.57/1.01  --res_prop_simpl_given                  true
% 2.57/1.01  --res_passive_queue_type                priority_queues
% 2.57/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.57/1.01  --res_passive_queues_freq               [15;5]
% 2.57/1.01  --res_forward_subs                      full
% 2.57/1.01  --res_backward_subs                     full
% 2.57/1.01  --res_forward_subs_resolution           true
% 2.57/1.01  --res_backward_subs_resolution          true
% 2.57/1.01  --res_orphan_elimination                true
% 2.57/1.01  --res_time_limit                        2.
% 2.57/1.01  --res_out_proof                         true
% 2.57/1.01  
% 2.57/1.01  ------ Superposition Options
% 2.57/1.01  
% 2.57/1.01  --superposition_flag                    true
% 2.57/1.01  --sup_passive_queue_type                priority_queues
% 2.57/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.57/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.57/1.01  --demod_completeness_check              fast
% 2.57/1.01  --demod_use_ground                      true
% 2.57/1.01  --sup_to_prop_solver                    passive
% 2.57/1.01  --sup_prop_simpl_new                    true
% 2.57/1.01  --sup_prop_simpl_given                  true
% 2.57/1.01  --sup_fun_splitting                     false
% 2.57/1.01  --sup_smt_interval                      50000
% 2.57/1.01  
% 2.57/1.01  ------ Superposition Simplification Setup
% 2.57/1.01  
% 2.57/1.01  --sup_indices_passive                   []
% 2.57/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.57/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.57/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.57/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.57/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.57/1.01  --sup_full_bw                           [BwDemod]
% 2.57/1.01  --sup_immed_triv                        [TrivRules]
% 2.57/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.57/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.57/1.01  --sup_immed_bw_main                     []
% 2.57/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.57/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.57/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.57/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.57/1.01  
% 2.57/1.01  ------ Combination Options
% 2.57/1.01  
% 2.57/1.01  --comb_res_mult                         3
% 2.57/1.01  --comb_sup_mult                         2
% 2.57/1.01  --comb_inst_mult                        10
% 2.57/1.01  
% 2.57/1.01  ------ Debug Options
% 2.57/1.01  
% 2.57/1.01  --dbg_backtrace                         false
% 2.57/1.01  --dbg_dump_prop_clauses                 false
% 2.57/1.01  --dbg_dump_prop_clauses_file            -
% 2.57/1.01  --dbg_out_stat                          false
% 2.57/1.01  
% 2.57/1.01  
% 2.57/1.01  
% 2.57/1.01  
% 2.57/1.01  ------ Proving...
% 2.57/1.01  
% 2.57/1.01  
% 2.57/1.01  % SZS status Theorem for theBenchmark.p
% 2.57/1.01  
% 2.57/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.57/1.01  
% 2.57/1.01  fof(f4,axiom,(
% 2.57/1.01    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 2.57/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.57/1.01  
% 2.57/1.01  fof(f14,plain,(
% 2.57/1.01    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 2.57/1.01    inference(ennf_transformation,[],[f4])).
% 2.57/1.01  
% 2.57/1.01  fof(f34,plain,(
% 2.57/1.01    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 2.57/1.01    inference(cnf_transformation,[],[f14])).
% 2.57/1.01  
% 2.57/1.01  fof(f9,conjecture,(
% 2.57/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) => r1_xboole_0(X0,X1))))),
% 2.57/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.57/1.01  
% 2.57/1.01  fof(f10,negated_conjecture,(
% 2.57/1.01    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) => r1_xboole_0(X0,X1))))),
% 2.57/1.01    inference(negated_conjecture,[],[f9])).
% 2.57/1.01  
% 2.57/1.01  fof(f19,plain,(
% 2.57/1.01    ? [X0] : (? [X1] : ((~r1_xboole_0(X0,X1) & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 2.57/1.01    inference(ennf_transformation,[],[f10])).
% 2.57/1.01  
% 2.57/1.01  fof(f20,plain,(
% 2.57/1.01    ? [X0] : (? [X1] : (~r1_xboole_0(X0,X1) & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 2.57/1.01    inference(flattening,[],[f19])).
% 2.57/1.01  
% 2.57/1.01  fof(f26,plain,(
% 2.57/1.01    ( ! [X0] : (? [X1] : (~r1_xboole_0(X0,X1) & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_xboole_0(X0,sK2) & r1_xboole_0(k1_relat_1(X0),k1_relat_1(sK2)) & v1_relat_1(sK2))) )),
% 2.57/1.01    introduced(choice_axiom,[])).
% 2.57/1.01  
% 2.57/1.01  fof(f25,plain,(
% 2.57/1.01    ? [X0] : (? [X1] : (~r1_xboole_0(X0,X1) & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_xboole_0(sK1,X1) & r1_xboole_0(k1_relat_1(sK1),k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(sK1))),
% 2.57/1.01    introduced(choice_axiom,[])).
% 2.57/1.01  
% 2.57/1.01  fof(f27,plain,(
% 2.57/1.01    (~r1_xboole_0(sK1,sK2) & r1_xboole_0(k1_relat_1(sK1),k1_relat_1(sK2)) & v1_relat_1(sK2)) & v1_relat_1(sK1)),
% 2.57/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f20,f26,f25])).
% 2.57/1.01  
% 2.57/1.01  fof(f42,plain,(
% 2.57/1.01    r1_xboole_0(k1_relat_1(sK1),k1_relat_1(sK2))),
% 2.57/1.01    inference(cnf_transformation,[],[f27])).
% 2.57/1.01  
% 2.57/1.01  fof(f1,axiom,(
% 2.57/1.01    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.57/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.57/1.01  
% 2.57/1.01  fof(f21,plain,(
% 2.57/1.01    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 2.57/1.01    inference(nnf_transformation,[],[f1])).
% 2.57/1.01  
% 2.57/1.01  fof(f28,plain,(
% 2.57/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 2.57/1.01    inference(cnf_transformation,[],[f21])).
% 2.57/1.01  
% 2.57/1.01  fof(f3,axiom,(
% 2.57/1.01    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 2.57/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.57/1.01  
% 2.57/1.01  fof(f13,plain,(
% 2.57/1.01    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 2.57/1.01    inference(ennf_transformation,[],[f3])).
% 2.57/1.01  
% 2.57/1.01  fof(f33,plain,(
% 2.57/1.01    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 2.57/1.01    inference(cnf_transformation,[],[f13])).
% 2.57/1.01  
% 2.57/1.01  fof(f7,axiom,(
% 2.57/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))))),
% 2.57/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.57/1.01  
% 2.57/1.01  fof(f17,plain,(
% 2.57/1.01    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.57/1.01    inference(ennf_transformation,[],[f7])).
% 2.57/1.01  
% 2.57/1.01  fof(f37,plain,(
% 2.57/1.01    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.57/1.01    inference(cnf_transformation,[],[f17])).
% 2.57/1.01  
% 2.57/1.01  fof(f40,plain,(
% 2.57/1.01    v1_relat_1(sK1)),
% 2.57/1.01    inference(cnf_transformation,[],[f27])).
% 2.57/1.01  
% 2.57/1.01  fof(f41,plain,(
% 2.57/1.01    v1_relat_1(sK2)),
% 2.57/1.01    inference(cnf_transformation,[],[f27])).
% 2.57/1.01  
% 2.57/1.01  fof(f8,axiom,(
% 2.57/1.01    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 2.57/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.57/1.01  
% 2.57/1.01  fof(f18,plain,(
% 2.57/1.01    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.57/1.01    inference(ennf_transformation,[],[f8])).
% 2.57/1.01  
% 2.57/1.01  fof(f24,plain,(
% 2.57/1.01    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.57/1.01    inference(nnf_transformation,[],[f18])).
% 2.57/1.01  
% 2.57/1.01  fof(f38,plain,(
% 2.57/1.01    ( ! [X0] : (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.57/1.01    inference(cnf_transformation,[],[f24])).
% 2.57/1.01  
% 2.57/1.01  fof(f5,axiom,(
% 2.57/1.01    ! [X0] : (v1_relat_1(X0) => k8_relat_1(k2_relat_1(X0),X0) = X0)),
% 2.57/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.57/1.01  
% 2.57/1.01  fof(f15,plain,(
% 2.57/1.01    ! [X0] : (k8_relat_1(k2_relat_1(X0),X0) = X0 | ~v1_relat_1(X0))),
% 2.57/1.01    inference(ennf_transformation,[],[f5])).
% 2.57/1.01  
% 2.57/1.01  fof(f35,plain,(
% 2.57/1.01    ( ! [X0] : (k8_relat_1(k2_relat_1(X0),X0) = X0 | ~v1_relat_1(X0)) )),
% 2.57/1.01    inference(cnf_transformation,[],[f15])).
% 2.57/1.01  
% 2.57/1.01  fof(f6,axiom,(
% 2.57/1.01    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k8_relat_1(k1_xboole_0,X0))),
% 2.57/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.57/1.01  
% 2.57/1.01  fof(f16,plain,(
% 2.57/1.01    ! [X0] : (k1_xboole_0 = k8_relat_1(k1_xboole_0,X0) | ~v1_relat_1(X0))),
% 2.57/1.01    inference(ennf_transformation,[],[f6])).
% 2.57/1.01  
% 2.57/1.01  fof(f36,plain,(
% 2.57/1.01    ( ! [X0] : (k1_xboole_0 = k8_relat_1(k1_xboole_0,X0) | ~v1_relat_1(X0)) )),
% 2.57/1.01    inference(cnf_transformation,[],[f16])).
% 2.57/1.01  
% 2.57/1.01  fof(f29,plain,(
% 2.57/1.01    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 2.57/1.01    inference(cnf_transformation,[],[f21])).
% 2.57/1.01  
% 2.57/1.01  fof(f43,plain,(
% 2.57/1.01    ~r1_xboole_0(sK1,sK2)),
% 2.57/1.01    inference(cnf_transformation,[],[f27])).
% 2.57/1.01  
% 2.57/1.01  cnf(c_6,plain,
% 2.57/1.01      ( ~ v1_relat_1(X0) | v1_relat_1(k3_xboole_0(X0,X1)) ),
% 2.57/1.01      inference(cnf_transformation,[],[f34]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_631,plain,
% 2.57/1.01      ( ~ v1_relat_1(X0_40) | v1_relat_1(k3_xboole_0(X0_40,X1_40)) ),
% 2.57/1.01      inference(subtyping,[status(esa)],[c_6]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_1031,plain,
% 2.57/1.01      ( v1_relat_1(X0_40) != iProver_top
% 2.57/1.01      | v1_relat_1(k3_xboole_0(X0_40,X1_40)) = iProver_top ),
% 2.57/1.01      inference(predicate_to_equality,[status(thm)],[c_631]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_13,negated_conjecture,
% 2.57/1.01      ( r1_xboole_0(k1_relat_1(sK1),k1_relat_1(sK2)) ),
% 2.57/1.01      inference(cnf_transformation,[],[f42]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_625,negated_conjecture,
% 2.57/1.01      ( r1_xboole_0(k1_relat_1(sK1),k1_relat_1(sK2)) ),
% 2.57/1.01      inference(subtyping,[status(esa)],[c_13]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_1037,plain,
% 2.57/1.01      ( r1_xboole_0(k1_relat_1(sK1),k1_relat_1(sK2)) = iProver_top ),
% 2.57/1.01      inference(predicate_to_equality,[status(thm)],[c_625]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_1,plain,
% 2.57/1.01      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 2.57/1.01      inference(cnf_transformation,[],[f28]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_635,plain,
% 2.57/1.01      ( ~ r1_xboole_0(X0_40,X1_40)
% 2.57/1.01      | k3_xboole_0(X0_40,X1_40) = k1_xboole_0 ),
% 2.57/1.01      inference(subtyping,[status(esa)],[c_1]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_1027,plain,
% 2.57/1.01      ( k3_xboole_0(X0_40,X1_40) = k1_xboole_0
% 2.57/1.01      | r1_xboole_0(X0_40,X1_40) != iProver_top ),
% 2.57/1.01      inference(predicate_to_equality,[status(thm)],[c_635]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_1478,plain,
% 2.57/1.01      ( k3_xboole_0(k1_relat_1(sK1),k1_relat_1(sK2)) = k1_xboole_0 ),
% 2.57/1.01      inference(superposition,[status(thm)],[c_1037,c_1027]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_5,plain,
% 2.57/1.01      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 2.57/1.01      inference(cnf_transformation,[],[f33]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_9,plain,
% 2.57/1.01      ( r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
% 2.57/1.01      | ~ v1_relat_1(X0)
% 2.57/1.01      | ~ v1_relat_1(X1) ),
% 2.57/1.01      inference(cnf_transformation,[],[f37]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_215,plain,
% 2.57/1.01      ( ~ v1_relat_1(X0)
% 2.57/1.01      | ~ v1_relat_1(X1)
% 2.57/1.01      | k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) != k1_xboole_0
% 2.57/1.01      | k1_relat_1(k3_xboole_0(X0,X1)) != X2
% 2.57/1.01      | k1_xboole_0 = X2 ),
% 2.57/1.01      inference(resolution_lifted,[status(thm)],[c_5,c_9]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_216,plain,
% 2.57/1.01      ( ~ v1_relat_1(X0)
% 2.57/1.01      | ~ v1_relat_1(X1)
% 2.57/1.01      | k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) != k1_xboole_0
% 2.57/1.01      | k1_xboole_0 = k1_relat_1(k3_xboole_0(X0,X1)) ),
% 2.57/1.01      inference(unflattening,[status(thm)],[c_215]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_622,plain,
% 2.57/1.01      ( ~ v1_relat_1(X0_40)
% 2.57/1.01      | ~ v1_relat_1(X1_40)
% 2.57/1.01      | k3_xboole_0(k1_relat_1(X0_40),k1_relat_1(X1_40)) != k1_xboole_0
% 2.57/1.01      | k1_xboole_0 = k1_relat_1(k3_xboole_0(X0_40,X1_40)) ),
% 2.57/1.01      inference(subtyping,[status(esa)],[c_216]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_1040,plain,
% 2.57/1.01      ( k3_xboole_0(k1_relat_1(X0_40),k1_relat_1(X1_40)) != k1_xboole_0
% 2.57/1.01      | k1_xboole_0 = k1_relat_1(k3_xboole_0(X0_40,X1_40))
% 2.57/1.01      | v1_relat_1(X0_40) != iProver_top
% 2.57/1.01      | v1_relat_1(X1_40) != iProver_top ),
% 2.57/1.01      inference(predicate_to_equality,[status(thm)],[c_622]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_2801,plain,
% 2.57/1.01      ( k1_relat_1(k3_xboole_0(sK1,sK2)) = k1_xboole_0
% 2.57/1.01      | v1_relat_1(sK2) != iProver_top
% 2.57/1.01      | v1_relat_1(sK1) != iProver_top ),
% 2.57/1.01      inference(superposition,[status(thm)],[c_1478,c_1040]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_15,negated_conjecture,
% 2.57/1.01      ( v1_relat_1(sK1) ),
% 2.57/1.01      inference(cnf_transformation,[],[f40]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_16,plain,
% 2.57/1.01      ( v1_relat_1(sK1) = iProver_top ),
% 2.57/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_14,negated_conjecture,
% 2.57/1.01      ( v1_relat_1(sK2) ),
% 2.57/1.01      inference(cnf_transformation,[],[f41]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_17,plain,
% 2.57/1.01      ( v1_relat_1(sK2) = iProver_top ),
% 2.57/1.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_3017,plain,
% 2.57/1.01      ( k1_relat_1(k3_xboole_0(sK1,sK2)) = k1_xboole_0 ),
% 2.57/1.01      inference(global_propositional_subsumption,
% 2.57/1.01                [status(thm)],
% 2.57/1.01                [c_2801,c_16,c_17]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_11,plain,
% 2.57/1.01      ( ~ v1_relat_1(X0)
% 2.57/1.01      | k1_relat_1(X0) != k1_xboole_0
% 2.57/1.01      | k2_relat_1(X0) = k1_xboole_0 ),
% 2.57/1.01      inference(cnf_transformation,[],[f38]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_627,plain,
% 2.57/1.01      ( ~ v1_relat_1(X0_40)
% 2.57/1.01      | k1_relat_1(X0_40) != k1_xboole_0
% 2.57/1.01      | k2_relat_1(X0_40) = k1_xboole_0 ),
% 2.57/1.01      inference(subtyping,[status(esa)],[c_11]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_1035,plain,
% 2.57/1.01      ( k1_relat_1(X0_40) != k1_xboole_0
% 2.57/1.01      | k2_relat_1(X0_40) = k1_xboole_0
% 2.57/1.01      | v1_relat_1(X0_40) != iProver_top ),
% 2.57/1.01      inference(predicate_to_equality,[status(thm)],[c_627]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_3021,plain,
% 2.57/1.01      ( k2_relat_1(k3_xboole_0(sK1,sK2)) = k1_xboole_0
% 2.57/1.01      | v1_relat_1(k3_xboole_0(sK1,sK2)) != iProver_top ),
% 2.57/1.01      inference(superposition,[status(thm)],[c_3017,c_1035]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_3165,plain,
% 2.57/1.01      ( k2_relat_1(k3_xboole_0(sK1,sK2)) = k1_xboole_0
% 2.57/1.01      | v1_relat_1(sK1) != iProver_top ),
% 2.57/1.01      inference(superposition,[status(thm)],[c_1031,c_3021]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_3578,plain,
% 2.57/1.01      ( k2_relat_1(k3_xboole_0(sK1,sK2)) = k1_xboole_0 ),
% 2.57/1.01      inference(global_propositional_subsumption,
% 2.57/1.01                [status(thm)],
% 2.57/1.01                [c_3165,c_16]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_623,negated_conjecture,
% 2.57/1.01      ( v1_relat_1(sK1) ),
% 2.57/1.01      inference(subtyping,[status(esa)],[c_15]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_1039,plain,
% 2.57/1.01      ( v1_relat_1(sK1) = iProver_top ),
% 2.57/1.01      inference(predicate_to_equality,[status(thm)],[c_623]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_7,plain,
% 2.57/1.01      ( ~ v1_relat_1(X0) | k8_relat_1(k2_relat_1(X0),X0) = X0 ),
% 2.57/1.01      inference(cnf_transformation,[],[f35]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_630,plain,
% 2.57/1.01      ( ~ v1_relat_1(X0_40)
% 2.57/1.01      | k8_relat_1(k2_relat_1(X0_40),X0_40) = X0_40 ),
% 2.57/1.01      inference(subtyping,[status(esa)],[c_7]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_1032,plain,
% 2.57/1.01      ( k8_relat_1(k2_relat_1(X0_40),X0_40) = X0_40
% 2.57/1.01      | v1_relat_1(X0_40) != iProver_top ),
% 2.57/1.01      inference(predicate_to_equality,[status(thm)],[c_630]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_1549,plain,
% 2.57/1.01      ( k8_relat_1(k2_relat_1(k3_xboole_0(X0_40,X1_40)),k3_xboole_0(X0_40,X1_40)) = k3_xboole_0(X0_40,X1_40)
% 2.57/1.01      | v1_relat_1(X0_40) != iProver_top ),
% 2.57/1.01      inference(superposition,[status(thm)],[c_1031,c_1032]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_2422,plain,
% 2.57/1.01      ( k8_relat_1(k2_relat_1(k3_xboole_0(sK1,X0_40)),k3_xboole_0(sK1,X0_40)) = k3_xboole_0(sK1,X0_40) ),
% 2.57/1.01      inference(superposition,[status(thm)],[c_1039,c_1549]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_3582,plain,
% 2.57/1.01      ( k8_relat_1(k1_xboole_0,k3_xboole_0(sK1,sK2)) = k3_xboole_0(sK1,sK2) ),
% 2.57/1.01      inference(superposition,[status(thm)],[c_3578,c_2422]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_8,plain,
% 2.57/1.01      ( ~ v1_relat_1(X0) | k8_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.57/1.01      inference(cnf_transformation,[],[f36]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_629,plain,
% 2.57/1.01      ( ~ v1_relat_1(X0_40)
% 2.57/1.01      | k8_relat_1(k1_xboole_0,X0_40) = k1_xboole_0 ),
% 2.57/1.01      inference(subtyping,[status(esa)],[c_8]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_1033,plain,
% 2.57/1.01      ( k8_relat_1(k1_xboole_0,X0_40) = k1_xboole_0
% 2.57/1.01      | v1_relat_1(X0_40) != iProver_top ),
% 2.57/1.01      inference(predicate_to_equality,[status(thm)],[c_629]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_1482,plain,
% 2.57/1.01      ( k8_relat_1(k1_xboole_0,k3_xboole_0(X0_40,X1_40)) = k1_xboole_0
% 2.57/1.01      | v1_relat_1(X0_40) != iProver_top ),
% 2.57/1.01      inference(superposition,[status(thm)],[c_1031,c_1033]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_1830,plain,
% 2.57/1.01      ( k8_relat_1(k1_xboole_0,k3_xboole_0(sK1,X0_40)) = k1_xboole_0 ),
% 2.57/1.01      inference(superposition,[status(thm)],[c_1039,c_1482]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_3584,plain,
% 2.57/1.01      ( k3_xboole_0(sK1,sK2) = k1_xboole_0 ),
% 2.57/1.01      inference(demodulation,[status(thm)],[c_3582,c_1830]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_0,plain,
% 2.57/1.01      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 2.57/1.01      inference(cnf_transformation,[],[f29]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_636,plain,
% 2.57/1.01      ( r1_xboole_0(X0_40,X1_40)
% 2.57/1.01      | k3_xboole_0(X0_40,X1_40) != k1_xboole_0 ),
% 2.57/1.01      inference(subtyping,[status(esa)],[c_0]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_1026,plain,
% 2.57/1.01      ( k3_xboole_0(X0_40,X1_40) != k1_xboole_0
% 2.57/1.01      | r1_xboole_0(X0_40,X1_40) = iProver_top ),
% 2.57/1.01      inference(predicate_to_equality,[status(thm)],[c_636]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_3634,plain,
% 2.57/1.01      ( r1_xboole_0(sK1,sK2) = iProver_top ),
% 2.57/1.01      inference(superposition,[status(thm)],[c_3584,c_1026]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_12,negated_conjecture,
% 2.57/1.01      ( ~ r1_xboole_0(sK1,sK2) ),
% 2.57/1.01      inference(cnf_transformation,[],[f43]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_19,plain,
% 2.57/1.01      ( r1_xboole_0(sK1,sK2) != iProver_top ),
% 2.57/1.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(contradiction,plain,
% 2.57/1.01      ( $false ),
% 2.57/1.01      inference(minisat,[status(thm)],[c_3634,c_19]) ).
% 2.57/1.01  
% 2.57/1.01  
% 2.57/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.57/1.01  
% 2.57/1.01  ------                               Statistics
% 2.57/1.01  
% 2.57/1.01  ------ General
% 2.57/1.01  
% 2.57/1.01  abstr_ref_over_cycles:                  0
% 2.57/1.01  abstr_ref_under_cycles:                 0
% 2.57/1.01  gc_basic_clause_elim:                   0
% 2.57/1.01  forced_gc_time:                         0
% 2.57/1.01  parsing_time:                           0.013
% 2.57/1.01  unif_index_cands_time:                  0.
% 2.57/1.01  unif_index_add_time:                    0.
% 2.57/1.01  orderings_time:                         0.
% 2.57/1.01  out_proof_time:                         0.01
% 2.57/1.01  total_time:                             0.182
% 2.57/1.01  num_of_symbols:                         45
% 2.57/1.01  num_of_terms:                           5531
% 2.57/1.01  
% 2.57/1.01  ------ Preprocessing
% 2.57/1.01  
% 2.57/1.01  num_of_splits:                          0
% 2.57/1.01  num_of_split_atoms:                     0
% 2.57/1.01  num_of_reused_defs:                     0
% 2.57/1.01  num_eq_ax_congr_red:                    15
% 2.57/1.01  num_of_sem_filtered_clauses:            1
% 2.57/1.01  num_of_subtypes:                        2
% 2.57/1.01  monotx_restored_types:                  0
% 2.57/1.01  sat_num_of_epr_types:                   0
% 2.57/1.01  sat_num_of_non_cyclic_types:            0
% 2.57/1.01  sat_guarded_non_collapsed_types:        1
% 2.57/1.01  num_pure_diseq_elim:                    0
% 2.57/1.01  simp_replaced_by:                       0
% 2.57/1.01  res_preprocessed:                       80
% 2.57/1.01  prep_upred:                             0
% 2.57/1.01  prep_unflattend:                        33
% 2.57/1.01  smt_new_axioms:                         0
% 2.57/1.01  pred_elim_cands:                        3
% 2.57/1.01  pred_elim:                              1
% 2.57/1.01  pred_elim_cl:                           1
% 2.57/1.01  pred_elim_cycles:                       3
% 2.57/1.01  merged_defs:                            8
% 2.57/1.01  merged_defs_ncl:                        0
% 2.57/1.01  bin_hyper_res:                          8
% 2.57/1.01  prep_cycles:                            4
% 2.57/1.01  pred_elim_time:                         0.004
% 2.57/1.01  splitting_time:                         0.
% 2.57/1.01  sem_filter_time:                        0.
% 2.57/1.01  monotx_time:                            0.
% 2.57/1.01  subtype_inf_time:                       0.
% 2.57/1.01  
% 2.57/1.01  ------ Problem properties
% 2.57/1.01  
% 2.57/1.01  clauses:                                15
% 2.57/1.01  conjectures:                            4
% 2.57/1.01  epr:                                    4
% 2.57/1.01  horn:                                   13
% 2.57/1.01  ground:                                 4
% 2.57/1.01  unary:                                  4
% 2.57/1.01  binary:                                 7
% 2.57/1.01  lits:                                   31
% 2.57/1.01  lits_eq:                                10
% 2.57/1.01  fd_pure:                                0
% 2.57/1.01  fd_pseudo:                              0
% 2.57/1.01  fd_cond:                                0
% 2.57/1.01  fd_pseudo_cond:                         0
% 2.57/1.01  ac_symbols:                             0
% 2.57/1.01  
% 2.57/1.01  ------ Propositional Solver
% 2.57/1.01  
% 2.57/1.01  prop_solver_calls:                      26
% 2.57/1.01  prop_fast_solver_calls:                 473
% 2.57/1.01  smt_solver_calls:                       0
% 2.57/1.01  smt_fast_solver_calls:                  0
% 2.57/1.01  prop_num_of_clauses:                    1574
% 2.57/1.01  prop_preprocess_simplified:             5004
% 2.57/1.01  prop_fo_subsumed:                       3
% 2.57/1.01  prop_solver_time:                       0.
% 2.57/1.01  smt_solver_time:                        0.
% 2.57/1.01  smt_fast_solver_time:                   0.
% 2.57/1.01  prop_fast_solver_time:                  0.
% 2.57/1.01  prop_unsat_core_time:                   0.
% 2.57/1.01  
% 2.57/1.01  ------ QBF
% 2.57/1.01  
% 2.57/1.01  qbf_q_res:                              0
% 2.57/1.01  qbf_num_tautologies:                    0
% 2.57/1.01  qbf_prep_cycles:                        0
% 2.57/1.01  
% 2.57/1.01  ------ BMC1
% 2.57/1.01  
% 2.57/1.01  bmc1_current_bound:                     -1
% 2.57/1.01  bmc1_last_solved_bound:                 -1
% 2.57/1.01  bmc1_unsat_core_size:                   -1
% 2.57/1.01  bmc1_unsat_core_parents_size:           -1
% 2.57/1.01  bmc1_merge_next_fun:                    0
% 2.57/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.57/1.01  
% 2.57/1.01  ------ Instantiation
% 2.57/1.01  
% 2.57/1.01  inst_num_of_clauses:                    461
% 2.57/1.01  inst_num_in_passive:                    232
% 2.57/1.01  inst_num_in_active:                     229
% 2.57/1.01  inst_num_in_unprocessed:                0
% 2.57/1.01  inst_num_of_loops:                      230
% 2.57/1.01  inst_num_of_learning_restarts:          0
% 2.57/1.01  inst_num_moves_active_passive:          0
% 2.57/1.01  inst_lit_activity:                      0
% 2.57/1.01  inst_lit_activity_moves:                0
% 2.57/1.01  inst_num_tautologies:                   0
% 2.57/1.01  inst_num_prop_implied:                  0
% 2.57/1.01  inst_num_existing_simplified:           0
% 2.57/1.01  inst_num_eq_res_simplified:             0
% 2.57/1.01  inst_num_child_elim:                    0
% 2.57/1.01  inst_num_of_dismatching_blockings:      83
% 2.57/1.01  inst_num_of_non_proper_insts:           343
% 2.57/1.01  inst_num_of_duplicates:                 0
% 2.57/1.01  inst_inst_num_from_inst_to_res:         0
% 2.57/1.01  inst_dismatching_checking_time:         0.
% 2.57/1.01  
% 2.57/1.01  ------ Resolution
% 2.57/1.01  
% 2.57/1.01  res_num_of_clauses:                     0
% 2.57/1.01  res_num_in_passive:                     0
% 2.57/1.01  res_num_in_active:                      0
% 2.57/1.01  res_num_of_loops:                       84
% 2.57/1.01  res_forward_subset_subsumed:            17
% 2.57/1.01  res_backward_subset_subsumed:           0
% 2.57/1.01  res_forward_subsumed:                   0
% 2.57/1.01  res_backward_subsumed:                  0
% 2.57/1.01  res_forward_subsumption_resolution:     0
% 2.57/1.01  res_backward_subsumption_resolution:    0
% 2.57/1.01  res_clause_to_clause_subsumption:       147
% 2.57/1.01  res_orphan_elimination:                 0
% 2.57/1.01  res_tautology_del:                      53
% 2.57/1.01  res_num_eq_res_simplified:              0
% 2.57/1.01  res_num_sel_changes:                    0
% 2.57/1.01  res_moves_from_active_to_pass:          0
% 2.57/1.01  
% 2.57/1.01  ------ Superposition
% 2.57/1.01  
% 2.57/1.01  sup_time_total:                         0.
% 2.57/1.01  sup_time_generating:                    0.
% 2.57/1.01  sup_time_sim_full:                      0.
% 2.57/1.01  sup_time_sim_immed:                     0.
% 2.57/1.01  
% 2.57/1.01  sup_num_of_clauses:                     52
% 2.57/1.01  sup_num_in_active:                      40
% 2.57/1.01  sup_num_in_passive:                     12
% 2.57/1.01  sup_num_of_loops:                       45
% 2.57/1.01  sup_fw_superposition:                   31
% 2.57/1.01  sup_bw_superposition:                   16
% 2.57/1.01  sup_immediate_simplified:               3
% 2.57/1.01  sup_given_eliminated:                   1
% 2.57/1.01  comparisons_done:                       0
% 2.57/1.01  comparisons_avoided:                    0
% 2.57/1.01  
% 2.57/1.01  ------ Simplifications
% 2.57/1.01  
% 2.57/1.01  
% 2.57/1.01  sim_fw_subset_subsumed:                 1
% 2.57/1.01  sim_bw_subset_subsumed:                 1
% 2.57/1.01  sim_fw_subsumed:                        0
% 2.57/1.01  sim_bw_subsumed:                        0
% 2.57/1.01  sim_fw_subsumption_res:                 0
% 2.57/1.01  sim_bw_subsumption_res:                 0
% 2.57/1.01  sim_tautology_del:                      1
% 2.57/1.01  sim_eq_tautology_del:                   0
% 2.57/1.01  sim_eq_res_simp:                        0
% 2.57/1.01  sim_fw_demodulated:                     1
% 2.57/1.01  sim_bw_demodulated:                     5
% 2.57/1.01  sim_light_normalised:                   3
% 2.57/1.01  sim_joinable_taut:                      0
% 2.57/1.01  sim_joinable_simp:                      0
% 2.57/1.01  sim_ac_normalised:                      0
% 2.57/1.01  sim_smt_subsumption:                    0
% 2.57/1.01  
%------------------------------------------------------------------------------
