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
% DateTime   : Thu Dec  3 11:50:29 EST 2020

% Result     : Theorem 2.79s
% Output     : CNFRefutation 2.79s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 217 expanded)
%              Number of clauses        :   52 (  76 expanded)
%              Number of leaves         :   12 (  43 expanded)
%              Depth                    :   13
%              Number of atoms          :  227 ( 735 expanded)
%              Number of equality atoms :  117 ( 315 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
            & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f25,plain,(
    ? [X0] :
      ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f26,plain,(
    ? [X0] :
      ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f27,plain,
    ( ? [X0] :
        ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
        & v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
        | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) )
      & v2_funct_1(sK0)
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
      | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) )
    & v2_funct_1(sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f42,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f32,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f34,plain,(
    ! [X0] :
      ( k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f35,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k9_relat_1(X1,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_relat_1(X1,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f40,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f45,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f41,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f44,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f43,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_16,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_545,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k4_relat_1(X0)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_555,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_552,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1509,plain,
    ( k9_relat_1(k4_relat_1(X0),k1_relat_1(k4_relat_1(X0))) = k2_relat_1(k4_relat_1(X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_555,c_552])).

cnf(c_7279,plain,
    ( k9_relat_1(k4_relat_1(sK0),k1_relat_1(k4_relat_1(sK0))) = k2_relat_1(k4_relat_1(sK0)) ),
    inference(superposition,[status(thm)],[c_545,c_1509])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_549,plain,
    ( k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1101,plain,
    ( k1_relat_1(k4_relat_1(sK0)) = k2_relat_1(sK0) ),
    inference(superposition,[status(thm)],[c_545,c_549])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_550,plain,
    ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1338,plain,
    ( k2_relat_1(k4_relat_1(sK0)) = k1_relat_1(sK0) ),
    inference(superposition,[status(thm)],[c_545,c_550])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_551,plain,
    ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2163,plain,
    ( k2_relat_1(k5_relat_1(sK0,X0)) = k9_relat_1(X0,k2_relat_1(sK0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_545,c_551])).

cnf(c_2398,plain,
    ( k2_relat_1(k5_relat_1(sK0,k4_relat_1(X0))) = k9_relat_1(k4_relat_1(X0),k2_relat_1(sK0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_555,c_2163])).

cnf(c_2537,plain,
    ( k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) = k9_relat_1(k4_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(superposition,[status(thm)],[c_545,c_2398])).

cnf(c_7281,plain,
    ( k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) = k1_relat_1(sK0) ),
    inference(light_normalisation,[status(thm)],[c_7279,c_1101,c_1338,c_2537])).

cnf(c_1,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_554,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_546,plain,
    ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_912,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k6_relat_1(X0)))) = k6_relat_1(X0) ),
    inference(superposition,[status(thm)],[c_554,c_546])).

cnf(c_9,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_917,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)) = k6_relat_1(X0) ),
    inference(light_normalisation,[status(thm)],[c_912,c_9])).

cnf(c_7,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_548,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1972,plain,
    ( r1_tarski(k2_relat_1(k6_relat_1(X0)),k2_relat_1(k6_relat_1(X0))) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_917,c_548])).

cnf(c_1996,plain,
    ( r1_tarski(X0,X0) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1972,c_9])).

cnf(c_49,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2150,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1996,c_49])).

cnf(c_8,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_547,plain,
    ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
    | r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1733,plain,
    ( k1_relat_1(k5_relat_1(X0,k4_relat_1(sK0))) = k1_relat_1(X0)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(sK0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_relat_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1101,c_547])).

cnf(c_17,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_52,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_54,plain,
    ( v1_relat_1(k4_relat_1(sK0)) = iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_52])).

cnf(c_3118,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_tarski(k2_relat_1(X0),k2_relat_1(sK0)) != iProver_top
    | k1_relat_1(k5_relat_1(X0,k4_relat_1(sK0))) = k1_relat_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1733,c_17,c_54])).

cnf(c_3119,plain,
    ( k1_relat_1(k5_relat_1(X0,k4_relat_1(sK0))) = k1_relat_1(X0)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(sK0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3118])).

cnf(c_3128,plain,
    ( k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) = k1_relat_1(sK0)
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2150,c_3119])).

cnf(c_13,negated_conjecture,
    ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_12,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_14,negated_conjecture,
    ( v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_173,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_14])).

cnf(c_174,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(unflattening,[status(thm)],[c_173])).

cnf(c_15,negated_conjecture,
    ( v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_21,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v2_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_176,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_174,c_16,c_15,c_14,c_21])).

cnf(c_590,plain,
    ( k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) != k1_relat_1(sK0)
    | k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) != k1_relat_1(sK0) ),
    inference(light_normalisation,[status(thm)],[c_13,c_176])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7281,c_3128,c_590,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.06  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.06  % Command    : iproveropt_run.sh %d %s
% 0.06/0.25  % Computer   : n003.cluster.edu
% 0.06/0.25  % Model      : x86_64 x86_64
% 0.06/0.25  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.06/0.25  % Memory     : 8042.1875MB
% 0.06/0.25  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.06/0.25  % CPULimit   : 60
% 0.06/0.25  % WCLimit    : 600
% 0.06/0.25  % DateTime   : Tue Dec  1 12:26:12 EST 2020
% 0.06/0.25  % CPUTime    : 
% 0.06/0.25  % Running in FOF mode
% 2.79/0.83  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/0.83  
% 2.79/0.83  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.79/0.83  
% 2.79/0.83  ------  iProver source info
% 2.79/0.83  
% 2.79/0.83  git: date: 2020-06-30 10:37:57 +0100
% 2.79/0.83  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.79/0.83  git: non_committed_changes: false
% 2.79/0.83  git: last_make_outside_of_git: false
% 2.79/0.83  
% 2.79/0.83  ------ 
% 2.79/0.83  
% 2.79/0.83  ------ Input Options
% 2.79/0.83  
% 2.79/0.83  --out_options                           all
% 2.79/0.83  --tptp_safe_out                         true
% 2.79/0.83  --problem_path                          ""
% 2.79/0.83  --include_path                          ""
% 2.79/0.83  --clausifier                            res/vclausify_rel
% 2.79/0.83  --clausifier_options                    --mode clausify
% 2.79/0.83  --stdin                                 false
% 2.79/0.83  --stats_out                             all
% 2.79/0.83  
% 2.79/0.83  ------ General Options
% 2.79/0.83  
% 2.79/0.83  --fof                                   false
% 2.79/0.83  --time_out_real                         305.
% 2.79/0.83  --time_out_virtual                      -1.
% 2.79/0.83  --symbol_type_check                     false
% 2.79/0.83  --clausify_out                          false
% 2.79/0.83  --sig_cnt_out                           false
% 2.79/0.83  --trig_cnt_out                          false
% 2.79/0.83  --trig_cnt_out_tolerance                1.
% 2.79/0.83  --trig_cnt_out_sk_spl                   false
% 2.79/0.83  --abstr_cl_out                          false
% 2.79/0.83  
% 2.79/0.83  ------ Global Options
% 2.79/0.83  
% 2.79/0.83  --schedule                              default
% 2.79/0.83  --add_important_lit                     false
% 2.79/0.83  --prop_solver_per_cl                    1000
% 2.79/0.83  --min_unsat_core                        false
% 2.79/0.83  --soft_assumptions                      false
% 2.79/0.83  --soft_lemma_size                       3
% 2.79/0.83  --prop_impl_unit_size                   0
% 2.79/0.83  --prop_impl_unit                        []
% 2.79/0.83  --share_sel_clauses                     true
% 2.79/0.83  --reset_solvers                         false
% 2.79/0.83  --bc_imp_inh                            [conj_cone]
% 2.79/0.83  --conj_cone_tolerance                   3.
% 2.79/0.83  --extra_neg_conj                        none
% 2.79/0.83  --large_theory_mode                     true
% 2.79/0.83  --prolific_symb_bound                   200
% 2.79/0.83  --lt_threshold                          2000
% 2.79/0.83  --clause_weak_htbl                      true
% 2.79/0.83  --gc_record_bc_elim                     false
% 2.79/0.83  
% 2.79/0.83  ------ Preprocessing Options
% 2.79/0.83  
% 2.79/0.83  --preprocessing_flag                    true
% 2.79/0.83  --time_out_prep_mult                    0.1
% 2.79/0.83  --splitting_mode                        input
% 2.79/0.83  --splitting_grd                         true
% 2.79/0.83  --splitting_cvd                         false
% 2.79/0.83  --splitting_cvd_svl                     false
% 2.79/0.83  --splitting_nvd                         32
% 2.79/0.83  --sub_typing                            true
% 2.79/0.83  --prep_gs_sim                           true
% 2.79/0.83  --prep_unflatten                        true
% 2.79/0.83  --prep_res_sim                          true
% 2.79/0.83  --prep_upred                            true
% 2.79/0.83  --prep_sem_filter                       exhaustive
% 2.79/0.83  --prep_sem_filter_out                   false
% 2.79/0.83  --pred_elim                             true
% 2.79/0.83  --res_sim_input                         true
% 2.79/0.83  --eq_ax_congr_red                       true
% 2.79/0.83  --pure_diseq_elim                       true
% 2.79/0.83  --brand_transform                       false
% 2.79/0.83  --non_eq_to_eq                          false
% 2.79/0.83  --prep_def_merge                        true
% 2.79/0.83  --prep_def_merge_prop_impl              false
% 2.79/0.83  --prep_def_merge_mbd                    true
% 2.79/0.83  --prep_def_merge_tr_red                 false
% 2.79/0.83  --prep_def_merge_tr_cl                  false
% 2.79/0.83  --smt_preprocessing                     true
% 2.79/0.83  --smt_ac_axioms                         fast
% 2.79/0.83  --preprocessed_out                      false
% 2.79/0.83  --preprocessed_stats                    false
% 2.79/0.83  
% 2.79/0.83  ------ Abstraction refinement Options
% 2.79/0.83  
% 2.79/0.83  --abstr_ref                             []
% 2.79/0.83  --abstr_ref_prep                        false
% 2.79/0.83  --abstr_ref_until_sat                   false
% 2.79/0.83  --abstr_ref_sig_restrict                funpre
% 2.79/0.83  --abstr_ref_af_restrict_to_split_sk     false
% 2.79/0.83  --abstr_ref_under                       []
% 2.79/0.83  
% 2.79/0.83  ------ SAT Options
% 2.79/0.83  
% 2.79/0.83  --sat_mode                              false
% 2.79/0.83  --sat_fm_restart_options                ""
% 2.79/0.83  --sat_gr_def                            false
% 2.79/0.83  --sat_epr_types                         true
% 2.79/0.83  --sat_non_cyclic_types                  false
% 2.79/0.83  --sat_finite_models                     false
% 2.79/0.83  --sat_fm_lemmas                         false
% 2.79/0.83  --sat_fm_prep                           false
% 2.79/0.83  --sat_fm_uc_incr                        true
% 2.79/0.83  --sat_out_model                         small
% 2.79/0.83  --sat_out_clauses                       false
% 2.79/0.83  
% 2.79/0.83  ------ QBF Options
% 2.79/0.83  
% 2.79/0.83  --qbf_mode                              false
% 2.79/0.83  --qbf_elim_univ                         false
% 2.79/0.83  --qbf_dom_inst                          none
% 2.79/0.83  --qbf_dom_pre_inst                      false
% 2.79/0.83  --qbf_sk_in                             false
% 2.79/0.83  --qbf_pred_elim                         true
% 2.79/0.83  --qbf_split                             512
% 2.79/0.83  
% 2.79/0.83  ------ BMC1 Options
% 2.79/0.83  
% 2.79/0.83  --bmc1_incremental                      false
% 2.79/0.83  --bmc1_axioms                           reachable_all
% 2.79/0.83  --bmc1_min_bound                        0
% 2.79/0.83  --bmc1_max_bound                        -1
% 2.79/0.83  --bmc1_max_bound_default                -1
% 2.79/0.83  --bmc1_symbol_reachability              true
% 2.79/0.83  --bmc1_property_lemmas                  false
% 2.79/0.83  --bmc1_k_induction                      false
% 2.79/0.83  --bmc1_non_equiv_states                 false
% 2.79/0.83  --bmc1_deadlock                         false
% 2.79/0.83  --bmc1_ucm                              false
% 2.79/0.83  --bmc1_add_unsat_core                   none
% 2.79/0.83  --bmc1_unsat_core_children              false
% 2.79/0.83  --bmc1_unsat_core_extrapolate_axioms    false
% 2.79/0.83  --bmc1_out_stat                         full
% 2.79/0.83  --bmc1_ground_init                      false
% 2.79/0.83  --bmc1_pre_inst_next_state              false
% 2.79/0.83  --bmc1_pre_inst_state                   false
% 2.79/0.83  --bmc1_pre_inst_reach_state             false
% 2.79/0.83  --bmc1_out_unsat_core                   false
% 2.79/0.83  --bmc1_aig_witness_out                  false
% 2.79/0.83  --bmc1_verbose                          false
% 2.79/0.83  --bmc1_dump_clauses_tptp                false
% 2.79/0.83  --bmc1_dump_unsat_core_tptp             false
% 2.79/0.83  --bmc1_dump_file                        -
% 2.79/0.83  --bmc1_ucm_expand_uc_limit              128
% 2.79/0.83  --bmc1_ucm_n_expand_iterations          6
% 2.79/0.83  --bmc1_ucm_extend_mode                  1
% 2.79/0.83  --bmc1_ucm_init_mode                    2
% 2.79/0.83  --bmc1_ucm_cone_mode                    none
% 2.79/0.83  --bmc1_ucm_reduced_relation_type        0
% 2.79/0.83  --bmc1_ucm_relax_model                  4
% 2.79/0.83  --bmc1_ucm_full_tr_after_sat            true
% 2.79/0.83  --bmc1_ucm_expand_neg_assumptions       false
% 2.79/0.83  --bmc1_ucm_layered_model                none
% 2.79/0.83  --bmc1_ucm_max_lemma_size               10
% 2.79/0.83  
% 2.79/0.83  ------ AIG Options
% 2.79/0.83  
% 2.79/0.83  --aig_mode                              false
% 2.79/0.83  
% 2.79/0.83  ------ Instantiation Options
% 2.79/0.83  
% 2.79/0.83  --instantiation_flag                    true
% 2.79/0.83  --inst_sos_flag                         false
% 2.79/0.83  --inst_sos_phase                        true
% 2.79/0.83  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.79/0.83  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.79/0.83  --inst_lit_sel_side                     num_symb
% 2.79/0.83  --inst_solver_per_active                1400
% 2.79/0.83  --inst_solver_calls_frac                1.
% 2.79/0.83  --inst_passive_queue_type               priority_queues
% 2.79/0.83  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.79/0.83  --inst_passive_queues_freq              [25;2]
% 2.79/0.83  --inst_dismatching                      true
% 2.79/0.83  --inst_eager_unprocessed_to_passive     true
% 2.79/0.83  --inst_prop_sim_given                   true
% 2.79/0.83  --inst_prop_sim_new                     false
% 2.79/0.83  --inst_subs_new                         false
% 2.79/0.83  --inst_eq_res_simp                      false
% 2.79/0.83  --inst_subs_given                       false
% 2.79/0.83  --inst_orphan_elimination               true
% 2.79/0.83  --inst_learning_loop_flag               true
% 2.79/0.83  --inst_learning_start                   3000
% 2.79/0.83  --inst_learning_factor                  2
% 2.79/0.83  --inst_start_prop_sim_after_learn       3
% 2.79/0.83  --inst_sel_renew                        solver
% 2.79/0.83  --inst_lit_activity_flag                true
% 2.79/0.83  --inst_restr_to_given                   false
% 2.79/0.83  --inst_activity_threshold               500
% 2.79/0.83  --inst_out_proof                        true
% 2.79/0.83  
% 2.79/0.83  ------ Resolution Options
% 2.79/0.83  
% 2.79/0.83  --resolution_flag                       true
% 2.79/0.83  --res_lit_sel                           adaptive
% 2.79/0.83  --res_lit_sel_side                      none
% 2.79/0.83  --res_ordering                          kbo
% 2.79/0.83  --res_to_prop_solver                    active
% 2.79/0.83  --res_prop_simpl_new                    false
% 2.79/0.83  --res_prop_simpl_given                  true
% 2.79/0.83  --res_passive_queue_type                priority_queues
% 2.79/0.83  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.79/0.83  --res_passive_queues_freq               [15;5]
% 2.79/0.83  --res_forward_subs                      full
% 2.79/0.83  --res_backward_subs                     full
% 2.79/0.83  --res_forward_subs_resolution           true
% 2.79/0.83  --res_backward_subs_resolution          true
% 2.79/0.83  --res_orphan_elimination                true
% 2.79/0.83  --res_time_limit                        2.
% 2.79/0.83  --res_out_proof                         true
% 2.79/0.83  
% 2.79/0.83  ------ Superposition Options
% 2.79/0.83  
% 2.79/0.83  --superposition_flag                    true
% 2.79/0.83  --sup_passive_queue_type                priority_queues
% 2.79/0.83  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.79/0.83  --sup_passive_queues_freq               [8;1;4]
% 2.79/0.83  --demod_completeness_check              fast
% 2.79/0.83  --demod_use_ground                      true
% 2.79/0.83  --sup_to_prop_solver                    passive
% 2.79/0.83  --sup_prop_simpl_new                    true
% 2.79/0.83  --sup_prop_simpl_given                  true
% 2.79/0.83  --sup_fun_splitting                     false
% 2.79/0.83  --sup_smt_interval                      50000
% 2.79/0.83  
% 2.79/0.83  ------ Superposition Simplification Setup
% 2.79/0.83  
% 2.79/0.83  --sup_indices_passive                   []
% 2.79/0.83  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.79/0.83  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.79/0.83  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.79/0.83  --sup_full_triv                         [TrivRules;PropSubs]
% 2.79/0.83  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.79/0.83  --sup_full_bw                           [BwDemod]
% 2.79/0.83  --sup_immed_triv                        [TrivRules]
% 2.79/0.83  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.79/0.83  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.79/0.83  --sup_immed_bw_main                     []
% 2.79/0.83  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.79/0.83  --sup_input_triv                        [Unflattening;TrivRules]
% 2.79/0.83  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.79/0.83  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.79/0.83  
% 2.79/0.83  ------ Combination Options
% 2.79/0.83  
% 2.79/0.83  --comb_res_mult                         3
% 2.79/0.83  --comb_sup_mult                         2
% 2.79/0.83  --comb_inst_mult                        10
% 2.79/0.83  
% 2.79/0.83  ------ Debug Options
% 2.79/0.83  
% 2.79/0.83  --dbg_backtrace                         false
% 2.79/0.83  --dbg_dump_prop_clauses                 false
% 2.79/0.83  --dbg_dump_prop_clauses_file            -
% 2.79/0.83  --dbg_out_stat                          false
% 2.79/0.83  ------ Parsing...
% 2.79/0.83  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.79/0.83  
% 2.79/0.83  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.79/0.83  
% 2.79/0.83  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.79/0.83  
% 2.79/0.83  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.79/0.83  ------ Proving...
% 2.79/0.83  ------ Problem Properties 
% 2.79/0.83  
% 2.79/0.83  
% 2.79/0.83  clauses                                 15
% 2.79/0.83  conjectures                             2
% 2.79/0.83  EPR                                     1
% 2.79/0.83  Horn                                    15
% 2.79/0.83  unary                                   5
% 2.79/0.83  binary                                  7
% 2.79/0.83  lits                                    29
% 2.79/0.83  lits eq                                 12
% 2.79/0.83  fd_pure                                 0
% 2.79/0.83  fd_pseudo                               0
% 2.79/0.83  fd_cond                                 0
% 2.79/0.83  fd_pseudo_cond                          0
% 2.79/0.83  AC symbols                              0
% 2.79/0.83  
% 2.79/0.83  ------ Schedule dynamic 5 is on 
% 2.79/0.83  
% 2.79/0.83  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.79/0.83  
% 2.79/0.83  
% 2.79/0.83  ------ 
% 2.79/0.83  Current options:
% 2.79/0.83  ------ 
% 2.79/0.83  
% 2.79/0.83  ------ Input Options
% 2.79/0.83  
% 2.79/0.83  --out_options                           all
% 2.79/0.83  --tptp_safe_out                         true
% 2.79/0.83  --problem_path                          ""
% 2.79/0.83  --include_path                          ""
% 2.79/0.83  --clausifier                            res/vclausify_rel
% 2.79/0.83  --clausifier_options                    --mode clausify
% 2.79/0.83  --stdin                                 false
% 2.79/0.83  --stats_out                             all
% 2.79/0.83  
% 2.79/0.83  ------ General Options
% 2.79/0.83  
% 2.79/0.83  --fof                                   false
% 2.79/0.83  --time_out_real                         305.
% 2.79/0.83  --time_out_virtual                      -1.
% 2.79/0.83  --symbol_type_check                     false
% 2.79/0.83  --clausify_out                          false
% 2.79/0.83  --sig_cnt_out                           false
% 2.79/0.83  --trig_cnt_out                          false
% 2.79/0.83  --trig_cnt_out_tolerance                1.
% 2.79/0.83  --trig_cnt_out_sk_spl                   false
% 2.79/0.83  --abstr_cl_out                          false
% 2.79/0.83  
% 2.79/0.83  ------ Global Options
% 2.79/0.83  
% 2.79/0.83  --schedule                              default
% 2.79/0.83  --add_important_lit                     false
% 2.79/0.83  --prop_solver_per_cl                    1000
% 2.79/0.83  --min_unsat_core                        false
% 2.79/0.83  --soft_assumptions                      false
% 2.79/0.83  --soft_lemma_size                       3
% 2.79/0.83  --prop_impl_unit_size                   0
% 2.79/0.83  --prop_impl_unit                        []
% 2.79/0.83  --share_sel_clauses                     true
% 2.79/0.83  --reset_solvers                         false
% 2.79/0.83  --bc_imp_inh                            [conj_cone]
% 2.79/0.83  --conj_cone_tolerance                   3.
% 2.79/0.83  --extra_neg_conj                        none
% 2.79/0.83  --large_theory_mode                     true
% 2.79/0.83  --prolific_symb_bound                   200
% 2.79/0.83  --lt_threshold                          2000
% 2.79/0.83  --clause_weak_htbl                      true
% 2.79/0.83  --gc_record_bc_elim                     false
% 2.79/0.83  
% 2.79/0.83  ------ Preprocessing Options
% 2.79/0.83  
% 2.79/0.83  --preprocessing_flag                    true
% 2.79/0.83  --time_out_prep_mult                    0.1
% 2.79/0.83  --splitting_mode                        input
% 2.79/0.83  --splitting_grd                         true
% 2.79/0.83  --splitting_cvd                         false
% 2.79/0.83  --splitting_cvd_svl                     false
% 2.79/0.83  --splitting_nvd                         32
% 2.79/0.83  --sub_typing                            true
% 2.79/0.83  --prep_gs_sim                           true
% 2.79/0.83  --prep_unflatten                        true
% 2.79/0.83  --prep_res_sim                          true
% 2.79/0.83  --prep_upred                            true
% 2.79/0.83  --prep_sem_filter                       exhaustive
% 2.79/0.83  --prep_sem_filter_out                   false
% 2.79/0.83  --pred_elim                             true
% 2.79/0.83  --res_sim_input                         true
% 2.79/0.83  --eq_ax_congr_red                       true
% 2.79/0.83  --pure_diseq_elim                       true
% 2.79/0.83  --brand_transform                       false
% 2.79/0.83  --non_eq_to_eq                          false
% 2.79/0.83  --prep_def_merge                        true
% 2.79/0.83  --prep_def_merge_prop_impl              false
% 2.79/0.83  --prep_def_merge_mbd                    true
% 2.79/0.83  --prep_def_merge_tr_red                 false
% 2.79/0.83  --prep_def_merge_tr_cl                  false
% 2.79/0.83  --smt_preprocessing                     true
% 2.79/0.83  --smt_ac_axioms                         fast
% 2.79/0.83  --preprocessed_out                      false
% 2.79/0.83  --preprocessed_stats                    false
% 2.79/0.83  
% 2.79/0.83  ------ Abstraction refinement Options
% 2.79/0.83  
% 2.79/0.83  --abstr_ref                             []
% 2.79/0.83  --abstr_ref_prep                        false
% 2.79/0.83  --abstr_ref_until_sat                   false
% 2.79/0.83  --abstr_ref_sig_restrict                funpre
% 2.79/0.83  --abstr_ref_af_restrict_to_split_sk     false
% 2.79/0.83  --abstr_ref_under                       []
% 2.79/0.83  
% 2.79/0.83  ------ SAT Options
% 2.79/0.83  
% 2.79/0.83  --sat_mode                              false
% 2.79/0.83  --sat_fm_restart_options                ""
% 2.79/0.83  --sat_gr_def                            false
% 2.79/0.83  --sat_epr_types                         true
% 2.79/0.83  --sat_non_cyclic_types                  false
% 2.79/0.83  --sat_finite_models                     false
% 2.79/0.83  --sat_fm_lemmas                         false
% 2.79/0.83  --sat_fm_prep                           false
% 2.79/0.83  --sat_fm_uc_incr                        true
% 2.79/0.83  --sat_out_model                         small
% 2.79/0.83  --sat_out_clauses                       false
% 2.79/0.83  
% 2.79/0.83  ------ QBF Options
% 2.79/0.83  
% 2.79/0.83  --qbf_mode                              false
% 2.79/0.83  --qbf_elim_univ                         false
% 2.79/0.83  --qbf_dom_inst                          none
% 2.79/0.83  --qbf_dom_pre_inst                      false
% 2.79/0.83  --qbf_sk_in                             false
% 2.79/0.83  --qbf_pred_elim                         true
% 2.79/0.83  --qbf_split                             512
% 2.79/0.83  
% 2.79/0.83  ------ BMC1 Options
% 2.79/0.83  
% 2.79/0.83  --bmc1_incremental                      false
% 2.79/0.83  --bmc1_axioms                           reachable_all
% 2.79/0.83  --bmc1_min_bound                        0
% 2.79/0.83  --bmc1_max_bound                        -1
% 2.79/0.83  --bmc1_max_bound_default                -1
% 2.79/0.83  --bmc1_symbol_reachability              true
% 2.79/0.83  --bmc1_property_lemmas                  false
% 2.79/0.83  --bmc1_k_induction                      false
% 2.79/0.83  --bmc1_non_equiv_states                 false
% 2.79/0.83  --bmc1_deadlock                         false
% 2.79/0.83  --bmc1_ucm                              false
% 2.79/0.83  --bmc1_add_unsat_core                   none
% 2.79/0.83  --bmc1_unsat_core_children              false
% 2.79/0.83  --bmc1_unsat_core_extrapolate_axioms    false
% 2.79/0.83  --bmc1_out_stat                         full
% 2.79/0.83  --bmc1_ground_init                      false
% 2.79/0.83  --bmc1_pre_inst_next_state              false
% 2.79/0.83  --bmc1_pre_inst_state                   false
% 2.79/0.83  --bmc1_pre_inst_reach_state             false
% 2.79/0.83  --bmc1_out_unsat_core                   false
% 2.79/0.83  --bmc1_aig_witness_out                  false
% 2.79/0.83  --bmc1_verbose                          false
% 2.79/0.83  --bmc1_dump_clauses_tptp                false
% 2.79/0.83  --bmc1_dump_unsat_core_tptp             false
% 2.79/0.83  --bmc1_dump_file                        -
% 2.79/0.83  --bmc1_ucm_expand_uc_limit              128
% 2.79/0.83  --bmc1_ucm_n_expand_iterations          6
% 2.79/0.83  --bmc1_ucm_extend_mode                  1
% 2.79/0.83  --bmc1_ucm_init_mode                    2
% 2.79/0.83  --bmc1_ucm_cone_mode                    none
% 2.79/0.83  --bmc1_ucm_reduced_relation_type        0
% 2.79/0.83  --bmc1_ucm_relax_model                  4
% 2.79/0.83  --bmc1_ucm_full_tr_after_sat            true
% 2.79/0.83  --bmc1_ucm_expand_neg_assumptions       false
% 2.79/0.83  --bmc1_ucm_layered_model                none
% 2.79/0.83  --bmc1_ucm_max_lemma_size               10
% 2.79/0.83  
% 2.79/0.83  ------ AIG Options
% 2.79/0.83  
% 2.79/0.83  --aig_mode                              false
% 2.79/0.83  
% 2.79/0.83  ------ Instantiation Options
% 2.79/0.83  
% 2.79/0.83  --instantiation_flag                    true
% 2.79/0.83  --inst_sos_flag                         false
% 2.79/0.83  --inst_sos_phase                        true
% 2.79/0.83  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.79/0.83  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.79/0.83  --inst_lit_sel_side                     none
% 2.79/0.83  --inst_solver_per_active                1400
% 2.79/0.83  --inst_solver_calls_frac                1.
% 2.79/0.83  --inst_passive_queue_type               priority_queues
% 2.79/0.83  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.79/0.83  --inst_passive_queues_freq              [25;2]
% 2.79/0.83  --inst_dismatching                      true
% 2.79/0.83  --inst_eager_unprocessed_to_passive     true
% 2.79/0.83  --inst_prop_sim_given                   true
% 2.79/0.83  --inst_prop_sim_new                     false
% 2.79/0.83  --inst_subs_new                         false
% 2.79/0.83  --inst_eq_res_simp                      false
% 2.79/0.83  --inst_subs_given                       false
% 2.79/0.83  --inst_orphan_elimination               true
% 2.79/0.83  --inst_learning_loop_flag               true
% 2.79/0.83  --inst_learning_start                   3000
% 2.79/0.83  --inst_learning_factor                  2
% 2.79/0.83  --inst_start_prop_sim_after_learn       3
% 2.79/0.83  --inst_sel_renew                        solver
% 2.79/0.83  --inst_lit_activity_flag                true
% 2.79/0.83  --inst_restr_to_given                   false
% 2.79/0.83  --inst_activity_threshold               500
% 2.79/0.83  --inst_out_proof                        true
% 2.79/0.83  
% 2.79/0.83  ------ Resolution Options
% 2.79/0.83  
% 2.79/0.83  --resolution_flag                       false
% 2.79/0.83  --res_lit_sel                           adaptive
% 2.79/0.83  --res_lit_sel_side                      none
% 2.79/0.83  --res_ordering                          kbo
% 2.79/0.83  --res_to_prop_solver                    active
% 2.79/0.83  --res_prop_simpl_new                    false
% 2.79/0.83  --res_prop_simpl_given                  true
% 2.79/0.83  --res_passive_queue_type                priority_queues
% 2.79/0.83  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.79/0.83  --res_passive_queues_freq               [15;5]
% 2.79/0.83  --res_forward_subs                      full
% 2.79/0.83  --res_backward_subs                     full
% 2.79/0.83  --res_forward_subs_resolution           true
% 2.79/0.83  --res_backward_subs_resolution          true
% 2.79/0.83  --res_orphan_elimination                true
% 2.79/0.83  --res_time_limit                        2.
% 2.79/0.83  --res_out_proof                         true
% 2.79/0.83  
% 2.79/0.83  ------ Superposition Options
% 2.79/0.83  
% 2.79/0.83  --superposition_flag                    true
% 2.79/0.83  --sup_passive_queue_type                priority_queues
% 2.79/0.83  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.79/0.83  --sup_passive_queues_freq               [8;1;4]
% 2.79/0.83  --demod_completeness_check              fast
% 2.79/0.83  --demod_use_ground                      true
% 2.79/0.83  --sup_to_prop_solver                    passive
% 2.79/0.83  --sup_prop_simpl_new                    true
% 2.79/0.83  --sup_prop_simpl_given                  true
% 2.79/0.83  --sup_fun_splitting                     false
% 2.79/0.83  --sup_smt_interval                      50000
% 2.79/0.83  
% 2.79/0.83  ------ Superposition Simplification Setup
% 2.79/0.83  
% 2.79/0.83  --sup_indices_passive                   []
% 2.79/0.83  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.79/0.83  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.79/0.83  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.79/0.83  --sup_full_triv                         [TrivRules;PropSubs]
% 2.79/0.83  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.79/0.83  --sup_full_bw                           [BwDemod]
% 2.79/0.83  --sup_immed_triv                        [TrivRules]
% 2.79/0.83  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.79/0.83  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.79/0.83  --sup_immed_bw_main                     []
% 2.79/0.83  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.79/0.83  --sup_input_triv                        [Unflattening;TrivRules]
% 2.79/0.83  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.79/0.83  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.79/0.83  
% 2.79/0.83  ------ Combination Options
% 2.79/0.83  
% 2.79/0.83  --comb_res_mult                         3
% 2.79/0.83  --comb_sup_mult                         2
% 2.79/0.83  --comb_inst_mult                        10
% 2.79/0.83  
% 2.79/0.83  ------ Debug Options
% 2.79/0.83  
% 2.79/0.83  --dbg_backtrace                         false
% 2.79/0.83  --dbg_dump_prop_clauses                 false
% 2.79/0.83  --dbg_dump_prop_clauses_file            -
% 2.79/0.83  --dbg_out_stat                          false
% 2.79/0.83  
% 2.79/0.83  
% 2.79/0.83  
% 2.79/0.83  
% 2.79/0.83  ------ Proving...
% 2.79/0.83  
% 2.79/0.83  
% 2.79/0.83  % SZS status Theorem for theBenchmark.p
% 2.79/0.83  
% 2.79/0.83  % SZS output start CNFRefutation for theBenchmark.p
% 2.79/0.83  
% 2.79/0.83  fof(f12,conjecture,(
% 2.79/0.83    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 2.79/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.79/0.83  
% 2.79/0.83  fof(f13,negated_conjecture,(
% 2.79/0.83    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 2.79/0.83    inference(negated_conjecture,[],[f12])).
% 2.79/0.83  
% 2.79/0.83  fof(f25,plain,(
% 2.79/0.83    ? [X0] : (((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 2.79/0.83    inference(ennf_transformation,[],[f13])).
% 2.79/0.83  
% 2.79/0.83  fof(f26,plain,(
% 2.79/0.83    ? [X0] : ((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 2.79/0.83    inference(flattening,[],[f25])).
% 2.79/0.83  
% 2.79/0.83  fof(f27,plain,(
% 2.79/0.83    ? [X0] : ((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => ((k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 2.79/0.83    introduced(choice_axiom,[])).
% 2.79/0.83  
% 2.79/0.83  fof(f28,plain,(
% 2.79/0.83    (k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 2.79/0.83    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 2.79/0.83  
% 2.79/0.83  fof(f42,plain,(
% 2.79/0.83    v1_relat_1(sK0)),
% 2.79/0.83    inference(cnf_transformation,[],[f28])).
% 2.79/0.83  
% 2.79/0.83  fof(f1,axiom,(
% 2.79/0.83    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 2.79/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.79/0.83  
% 2.79/0.83  fof(f14,plain,(
% 2.79/0.83    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.79/0.83    inference(ennf_transformation,[],[f1])).
% 2.79/0.83  
% 2.79/0.83  fof(f29,plain,(
% 2.79/0.83    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.79/0.83    inference(cnf_transformation,[],[f14])).
% 2.79/0.83  
% 2.79/0.83  fof(f4,axiom,(
% 2.79/0.83    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 2.79/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.79/0.83  
% 2.79/0.83  fof(f16,plain,(
% 2.79/0.83    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 2.79/0.83    inference(ennf_transformation,[],[f4])).
% 2.79/0.83  
% 2.79/0.83  fof(f32,plain,(
% 2.79/0.83    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.79/0.83    inference(cnf_transformation,[],[f16])).
% 2.79/0.83  
% 2.79/0.83  fof(f6,axiom,(
% 2.79/0.83    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)))),
% 2.79/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.79/0.83  
% 2.79/0.83  fof(f18,plain,(
% 2.79/0.83    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.79/0.83    inference(ennf_transformation,[],[f6])).
% 2.79/0.83  
% 2.79/0.83  fof(f34,plain,(
% 2.79/0.83    ( ! [X0] : (k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.79/0.83    inference(cnf_transformation,[],[f18])).
% 2.79/0.83  
% 2.79/0.83  fof(f35,plain,(
% 2.79/0.83    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.79/0.83    inference(cnf_transformation,[],[f18])).
% 2.79/0.83  
% 2.79/0.83  fof(f5,axiom,(
% 2.79/0.83    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k9_relat_1(X1,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,X1))))),
% 2.79/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.79/0.83  
% 2.79/0.83  fof(f17,plain,(
% 2.79/0.83    ! [X0] : (! [X1] : (k9_relat_1(X1,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.79/0.83    inference(ennf_transformation,[],[f5])).
% 2.79/0.83  
% 2.79/0.83  fof(f33,plain,(
% 2.79/0.83    ( ! [X0,X1] : (k9_relat_1(X1,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.79/0.83    inference(cnf_transformation,[],[f17])).
% 2.79/0.83  
% 2.79/0.83  fof(f2,axiom,(
% 2.79/0.83    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 2.79/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.79/0.83  
% 2.79/0.83  fof(f30,plain,(
% 2.79/0.83    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.79/0.83    inference(cnf_transformation,[],[f2])).
% 2.79/0.83  
% 2.79/0.83  fof(f10,axiom,(
% 2.79/0.83    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 2.79/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.79/0.83  
% 2.79/0.83  fof(f22,plain,(
% 2.79/0.83    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 2.79/0.83    inference(ennf_transformation,[],[f10])).
% 2.79/0.83  
% 2.79/0.83  fof(f40,plain,(
% 2.79/0.83    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 2.79/0.83    inference(cnf_transformation,[],[f22])).
% 2.79/0.83  
% 2.79/0.83  fof(f9,axiom,(
% 2.79/0.83    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.79/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.79/0.83  
% 2.79/0.83  fof(f39,plain,(
% 2.79/0.83    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 2.79/0.83    inference(cnf_transformation,[],[f9])).
% 2.79/0.83  
% 2.79/0.83  fof(f7,axiom,(
% 2.79/0.83    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 2.79/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.79/0.83  
% 2.79/0.83  fof(f19,plain,(
% 2.79/0.83    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.79/0.83    inference(ennf_transformation,[],[f7])).
% 2.79/0.83  
% 2.79/0.83  fof(f36,plain,(
% 2.79/0.83    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.79/0.83    inference(cnf_transformation,[],[f19])).
% 2.79/0.83  
% 2.79/0.83  fof(f8,axiom,(
% 2.79/0.83    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 2.79/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.79/0.83  
% 2.79/0.83  fof(f20,plain,(
% 2.79/0.83    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.79/0.83    inference(ennf_transformation,[],[f8])).
% 2.79/0.83  
% 2.79/0.83  fof(f21,plain,(
% 2.79/0.83    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.79/0.83    inference(flattening,[],[f20])).
% 2.79/0.83  
% 2.79/0.83  fof(f37,plain,(
% 2.79/0.83    ( ! [X0,X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.79/0.83    inference(cnf_transformation,[],[f21])).
% 2.79/0.83  
% 2.79/0.83  fof(f45,plain,(
% 2.79/0.83    k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 2.79/0.83    inference(cnf_transformation,[],[f28])).
% 2.79/0.83  
% 2.79/0.83  fof(f11,axiom,(
% 2.79/0.83    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 2.79/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.79/0.83  
% 2.79/0.83  fof(f23,plain,(
% 2.79/0.83    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.79/0.83    inference(ennf_transformation,[],[f11])).
% 2.79/0.83  
% 2.79/0.83  fof(f24,plain,(
% 2.79/0.83    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.79/0.83    inference(flattening,[],[f23])).
% 2.79/0.83  
% 2.79/0.83  fof(f41,plain,(
% 2.79/0.83    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.79/0.83    inference(cnf_transformation,[],[f24])).
% 2.79/0.83  
% 2.79/0.83  fof(f44,plain,(
% 2.79/0.83    v2_funct_1(sK0)),
% 2.79/0.83    inference(cnf_transformation,[],[f28])).
% 2.79/0.83  
% 2.79/0.83  fof(f43,plain,(
% 2.79/0.83    v1_funct_1(sK0)),
% 2.79/0.83    inference(cnf_transformation,[],[f28])).
% 2.79/0.83  
% 2.79/0.83  cnf(c_16,negated_conjecture,
% 2.79/0.83      ( v1_relat_1(sK0) ),
% 2.79/0.83      inference(cnf_transformation,[],[f42]) ).
% 2.79/0.83  
% 2.79/0.83  cnf(c_545,plain,
% 2.79/0.83      ( v1_relat_1(sK0) = iProver_top ),
% 2.79/0.83      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.79/0.83  
% 2.79/0.83  cnf(c_0,plain,
% 2.79/0.83      ( ~ v1_relat_1(X0) | v1_relat_1(k4_relat_1(X0)) ),
% 2.79/0.83      inference(cnf_transformation,[],[f29]) ).
% 2.79/0.83  
% 2.79/0.83  cnf(c_555,plain,
% 2.79/0.83      ( v1_relat_1(X0) != iProver_top
% 2.79/0.83      | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
% 2.79/0.83      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.79/0.83  
% 2.79/0.83  cnf(c_3,plain,
% 2.79/0.83      ( ~ v1_relat_1(X0)
% 2.79/0.83      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 2.79/0.83      inference(cnf_transformation,[],[f32]) ).
% 2.79/0.83  
% 2.79/0.83  cnf(c_552,plain,
% 2.79/0.83      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
% 2.79/0.83      | v1_relat_1(X0) != iProver_top ),
% 2.79/0.83      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.79/0.83  
% 2.79/0.83  cnf(c_1509,plain,
% 2.79/0.83      ( k9_relat_1(k4_relat_1(X0),k1_relat_1(k4_relat_1(X0))) = k2_relat_1(k4_relat_1(X0))
% 2.79/0.83      | v1_relat_1(X0) != iProver_top ),
% 2.79/0.83      inference(superposition,[status(thm)],[c_555,c_552]) ).
% 2.79/0.83  
% 2.79/0.83  cnf(c_7279,plain,
% 2.79/0.83      ( k9_relat_1(k4_relat_1(sK0),k1_relat_1(k4_relat_1(sK0))) = k2_relat_1(k4_relat_1(sK0)) ),
% 2.79/0.83      inference(superposition,[status(thm)],[c_545,c_1509]) ).
% 2.79/0.83  
% 2.79/0.83  cnf(c_6,plain,
% 2.79/0.83      ( ~ v1_relat_1(X0) | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
% 2.79/0.83      inference(cnf_transformation,[],[f34]) ).
% 2.79/0.83  
% 2.79/0.83  cnf(c_549,plain,
% 2.79/0.83      ( k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)
% 2.79/0.83      | v1_relat_1(X0) != iProver_top ),
% 2.79/0.83      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.79/0.83  
% 2.79/0.83  cnf(c_1101,plain,
% 2.79/0.83      ( k1_relat_1(k4_relat_1(sK0)) = k2_relat_1(sK0) ),
% 2.79/0.83      inference(superposition,[status(thm)],[c_545,c_549]) ).
% 2.79/0.83  
% 2.79/0.83  cnf(c_5,plain,
% 2.79/0.83      ( ~ v1_relat_1(X0) | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
% 2.79/0.83      inference(cnf_transformation,[],[f35]) ).
% 2.79/0.83  
% 2.79/0.83  cnf(c_550,plain,
% 2.79/0.83      ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
% 2.79/0.83      | v1_relat_1(X0) != iProver_top ),
% 2.79/0.83      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.79/0.83  
% 2.79/0.83  cnf(c_1338,plain,
% 2.79/0.83      ( k2_relat_1(k4_relat_1(sK0)) = k1_relat_1(sK0) ),
% 2.79/0.83      inference(superposition,[status(thm)],[c_545,c_550]) ).
% 2.79/0.83  
% 2.79/0.83  cnf(c_4,plain,
% 2.79/0.83      ( ~ v1_relat_1(X0)
% 2.79/0.83      | ~ v1_relat_1(X1)
% 2.79/0.83      | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ),
% 2.79/0.83      inference(cnf_transformation,[],[f33]) ).
% 2.79/0.83  
% 2.79/0.83  cnf(c_551,plain,
% 2.79/0.83      ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
% 2.79/0.83      | v1_relat_1(X0) != iProver_top
% 2.79/0.83      | v1_relat_1(X1) != iProver_top ),
% 2.79/0.83      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.79/0.83  
% 2.79/0.83  cnf(c_2163,plain,
% 2.79/0.83      ( k2_relat_1(k5_relat_1(sK0,X0)) = k9_relat_1(X0,k2_relat_1(sK0))
% 2.79/0.83      | v1_relat_1(X0) != iProver_top ),
% 2.79/0.83      inference(superposition,[status(thm)],[c_545,c_551]) ).
% 2.79/0.83  
% 2.79/0.83  cnf(c_2398,plain,
% 2.79/0.83      ( k2_relat_1(k5_relat_1(sK0,k4_relat_1(X0))) = k9_relat_1(k4_relat_1(X0),k2_relat_1(sK0))
% 2.79/0.83      | v1_relat_1(X0) != iProver_top ),
% 2.79/0.83      inference(superposition,[status(thm)],[c_555,c_2163]) ).
% 2.79/0.83  
% 2.79/0.83  cnf(c_2537,plain,
% 2.79/0.83      ( k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) = k9_relat_1(k4_relat_1(sK0),k2_relat_1(sK0)) ),
% 2.79/0.83      inference(superposition,[status(thm)],[c_545,c_2398]) ).
% 2.79/0.83  
% 2.79/0.83  cnf(c_7281,plain,
% 2.79/0.83      ( k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) = k1_relat_1(sK0) ),
% 2.79/0.83      inference(light_normalisation,
% 2.79/0.83                [status(thm)],
% 2.79/0.83                [c_7279,c_1101,c_1338,c_2537]) ).
% 2.79/0.83  
% 2.79/0.83  cnf(c_1,plain,
% 2.79/0.83      ( v1_relat_1(k6_relat_1(X0)) ),
% 2.79/0.83      inference(cnf_transformation,[],[f30]) ).
% 2.79/0.83  
% 2.79/0.83  cnf(c_554,plain,
% 2.79/0.83      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 2.79/0.83      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.79/0.83  
% 2.79/0.83  cnf(c_11,plain,
% 2.79/0.83      ( ~ v1_relat_1(X0)
% 2.79/0.83      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ),
% 2.79/0.83      inference(cnf_transformation,[],[f40]) ).
% 2.79/0.83  
% 2.79/0.83  cnf(c_546,plain,
% 2.79/0.83      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
% 2.79/0.83      | v1_relat_1(X0) != iProver_top ),
% 2.79/0.83      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.79/0.83  
% 2.79/0.83  cnf(c_912,plain,
% 2.79/0.83      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k6_relat_1(X0)))) = k6_relat_1(X0) ),
% 2.79/0.83      inference(superposition,[status(thm)],[c_554,c_546]) ).
% 2.79/0.83  
% 2.79/0.83  cnf(c_9,plain,
% 2.79/0.83      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 2.79/0.83      inference(cnf_transformation,[],[f39]) ).
% 2.79/0.83  
% 2.79/0.83  cnf(c_917,plain,
% 2.79/0.83      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)) = k6_relat_1(X0) ),
% 2.79/0.83      inference(light_normalisation,[status(thm)],[c_912,c_9]) ).
% 2.79/0.83  
% 2.79/0.83  cnf(c_7,plain,
% 2.79/0.83      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
% 2.79/0.83      | ~ v1_relat_1(X0)
% 2.79/0.83      | ~ v1_relat_1(X1) ),
% 2.79/0.83      inference(cnf_transformation,[],[f36]) ).
% 2.79/0.83  
% 2.79/0.83  cnf(c_548,plain,
% 2.79/0.83      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
% 2.79/0.83      | v1_relat_1(X0) != iProver_top
% 2.79/0.83      | v1_relat_1(X1) != iProver_top ),
% 2.79/0.83      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.79/0.83  
% 2.79/0.83  cnf(c_1972,plain,
% 2.79/0.83      ( r1_tarski(k2_relat_1(k6_relat_1(X0)),k2_relat_1(k6_relat_1(X0))) = iProver_top
% 2.79/0.83      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 2.79/0.83      inference(superposition,[status(thm)],[c_917,c_548]) ).
% 2.79/0.83  
% 2.79/0.83  cnf(c_1996,plain,
% 2.79/0.83      ( r1_tarski(X0,X0) = iProver_top
% 2.79/0.83      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 2.79/0.83      inference(light_normalisation,[status(thm)],[c_1972,c_9]) ).
% 2.79/0.83  
% 2.79/0.83  cnf(c_49,plain,
% 2.79/0.83      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 2.79/0.83      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.79/0.83  
% 2.79/0.83  cnf(c_2150,plain,
% 2.79/0.83      ( r1_tarski(X0,X0) = iProver_top ),
% 2.79/0.83      inference(global_propositional_subsumption,
% 2.79/0.83                [status(thm)],
% 2.79/0.83                [c_1996,c_49]) ).
% 2.79/0.83  
% 2.79/0.83  cnf(c_8,plain,
% 2.79/0.83      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
% 2.79/0.83      | ~ v1_relat_1(X0)
% 2.79/0.83      | ~ v1_relat_1(X1)
% 2.79/0.83      | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ),
% 2.79/0.83      inference(cnf_transformation,[],[f37]) ).
% 2.79/0.83  
% 2.79/0.83  cnf(c_547,plain,
% 2.79/0.83      ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
% 2.79/0.83      | r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) != iProver_top
% 2.79/0.83      | v1_relat_1(X0) != iProver_top
% 2.79/0.83      | v1_relat_1(X1) != iProver_top ),
% 2.79/0.83      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.79/0.83  
% 2.79/0.83  cnf(c_1733,plain,
% 2.79/0.83      ( k1_relat_1(k5_relat_1(X0,k4_relat_1(sK0))) = k1_relat_1(X0)
% 2.79/0.83      | r1_tarski(k2_relat_1(X0),k2_relat_1(sK0)) != iProver_top
% 2.79/0.83      | v1_relat_1(X0) != iProver_top
% 2.79/0.83      | v1_relat_1(k4_relat_1(sK0)) != iProver_top ),
% 2.79/0.83      inference(superposition,[status(thm)],[c_1101,c_547]) ).
% 2.79/0.83  
% 2.79/0.83  cnf(c_17,plain,
% 2.79/0.83      ( v1_relat_1(sK0) = iProver_top ),
% 2.79/0.83      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.79/0.83  
% 2.79/0.83  cnf(c_52,plain,
% 2.79/0.83      ( v1_relat_1(X0) != iProver_top
% 2.79/0.83      | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
% 2.79/0.83      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.79/0.83  
% 2.79/0.83  cnf(c_54,plain,
% 2.79/0.83      ( v1_relat_1(k4_relat_1(sK0)) = iProver_top
% 2.79/0.83      | v1_relat_1(sK0) != iProver_top ),
% 2.79/0.83      inference(instantiation,[status(thm)],[c_52]) ).
% 2.79/0.83  
% 2.79/0.83  cnf(c_3118,plain,
% 2.79/0.83      ( v1_relat_1(X0) != iProver_top
% 2.79/0.83      | r1_tarski(k2_relat_1(X0),k2_relat_1(sK0)) != iProver_top
% 2.79/0.83      | k1_relat_1(k5_relat_1(X0,k4_relat_1(sK0))) = k1_relat_1(X0) ),
% 2.79/0.83      inference(global_propositional_subsumption,
% 2.79/0.83                [status(thm)],
% 2.79/0.83                [c_1733,c_17,c_54]) ).
% 2.79/0.83  
% 2.79/0.83  cnf(c_3119,plain,
% 2.79/0.83      ( k1_relat_1(k5_relat_1(X0,k4_relat_1(sK0))) = k1_relat_1(X0)
% 2.79/0.83      | r1_tarski(k2_relat_1(X0),k2_relat_1(sK0)) != iProver_top
% 2.79/0.83      | v1_relat_1(X0) != iProver_top ),
% 2.79/0.83      inference(renaming,[status(thm)],[c_3118]) ).
% 2.79/0.83  
% 2.79/0.83  cnf(c_3128,plain,
% 2.79/0.83      ( k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) = k1_relat_1(sK0)
% 2.79/0.83      | v1_relat_1(sK0) != iProver_top ),
% 2.79/0.83      inference(superposition,[status(thm)],[c_2150,c_3119]) ).
% 2.79/0.83  
% 2.79/0.83  cnf(c_13,negated_conjecture,
% 2.79/0.83      ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
% 2.79/0.83      | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
% 2.79/0.83      inference(cnf_transformation,[],[f45]) ).
% 2.79/0.83  
% 2.79/0.83  cnf(c_12,plain,
% 2.79/0.83      ( ~ v1_funct_1(X0)
% 2.79/0.83      | ~ v2_funct_1(X0)
% 2.79/0.83      | ~ v1_relat_1(X0)
% 2.79/0.83      | k2_funct_1(X0) = k4_relat_1(X0) ),
% 2.79/0.83      inference(cnf_transformation,[],[f41]) ).
% 2.79/0.83  
% 2.79/0.83  cnf(c_14,negated_conjecture,
% 2.79/0.83      ( v2_funct_1(sK0) ),
% 2.79/0.83      inference(cnf_transformation,[],[f44]) ).
% 2.79/0.83  
% 2.79/0.83  cnf(c_173,plain,
% 2.79/0.83      ( ~ v1_funct_1(X0)
% 2.79/0.83      | ~ v1_relat_1(X0)
% 2.79/0.83      | k2_funct_1(X0) = k4_relat_1(X0)
% 2.79/0.83      | sK0 != X0 ),
% 2.79/0.83      inference(resolution_lifted,[status(thm)],[c_12,c_14]) ).
% 2.79/0.83  
% 2.79/0.83  cnf(c_174,plain,
% 2.79/0.83      ( ~ v1_funct_1(sK0)
% 2.79/0.83      | ~ v1_relat_1(sK0)
% 2.79/0.83      | k2_funct_1(sK0) = k4_relat_1(sK0) ),
% 2.79/0.83      inference(unflattening,[status(thm)],[c_173]) ).
% 2.79/0.83  
% 2.79/0.83  cnf(c_15,negated_conjecture,
% 2.79/0.83      ( v1_funct_1(sK0) ),
% 2.79/0.83      inference(cnf_transformation,[],[f43]) ).
% 2.79/0.83  
% 2.79/0.83  cnf(c_21,plain,
% 2.79/0.83      ( ~ v1_funct_1(sK0)
% 2.79/0.83      | ~ v2_funct_1(sK0)
% 2.79/0.83      | ~ v1_relat_1(sK0)
% 2.79/0.83      | k2_funct_1(sK0) = k4_relat_1(sK0) ),
% 2.79/0.83      inference(instantiation,[status(thm)],[c_12]) ).
% 2.79/0.83  
% 2.79/0.83  cnf(c_176,plain,
% 2.79/0.83      ( k2_funct_1(sK0) = k4_relat_1(sK0) ),
% 2.79/0.83      inference(global_propositional_subsumption,
% 2.79/0.83                [status(thm)],
% 2.79/0.83                [c_174,c_16,c_15,c_14,c_21]) ).
% 2.79/0.83  
% 2.79/0.83  cnf(c_590,plain,
% 2.79/0.83      ( k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) != k1_relat_1(sK0)
% 2.79/0.83      | k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) != k1_relat_1(sK0) ),
% 2.79/0.83      inference(light_normalisation,[status(thm)],[c_13,c_176]) ).
% 2.79/0.83  
% 2.79/0.83  cnf(contradiction,plain,
% 2.79/0.83      ( $false ),
% 2.79/0.83      inference(minisat,[status(thm)],[c_7281,c_3128,c_590,c_17]) ).
% 2.79/0.83  
% 2.79/0.83  
% 2.79/0.83  % SZS output end CNFRefutation for theBenchmark.p
% 2.79/0.83  
% 2.79/0.83  ------                               Statistics
% 2.79/0.83  
% 2.79/0.83  ------ General
% 2.79/0.83  
% 2.79/0.83  abstr_ref_over_cycles:                  0
% 2.79/0.83  abstr_ref_under_cycles:                 0
% 2.79/0.83  gc_basic_clause_elim:                   0
% 2.79/0.83  forced_gc_time:                         0
% 2.79/0.83  parsing_time:                           0.005
% 2.79/0.83  unif_index_cands_time:                  0.
% 2.79/0.83  unif_index_add_time:                    0.
% 2.79/0.83  orderings_time:                         0.
% 2.79/0.83  out_proof_time:                         0.006
% 2.79/0.83  total_time:                             0.214
% 2.79/0.83  num_of_symbols:                         43
% 2.79/0.83  num_of_terms:                           6910
% 2.79/0.83  
% 2.79/0.83  ------ Preprocessing
% 2.79/0.83  
% 2.79/0.83  num_of_splits:                          0
% 2.79/0.83  num_of_split_atoms:                     0
% 2.79/0.83  num_of_reused_defs:                     0
% 2.79/0.83  num_eq_ax_congr_red:                    3
% 2.79/0.83  num_of_sem_filtered_clauses:            1
% 2.79/0.83  num_of_subtypes:                        0
% 2.79/0.83  monotx_restored_types:                  0
% 2.79/0.83  sat_num_of_epr_types:                   0
% 2.79/0.83  sat_num_of_non_cyclic_types:            0
% 2.79/0.83  sat_guarded_non_collapsed_types:        0
% 2.79/0.83  num_pure_diseq_elim:                    0
% 2.79/0.83  simp_replaced_by:                       0
% 2.79/0.83  res_preprocessed:                       85
% 2.79/0.83  prep_upred:                             0
% 2.79/0.83  prep_unflattend:                        1
% 2.79/0.83  smt_new_axioms:                         0
% 2.79/0.83  pred_elim_cands:                        2
% 2.79/0.83  pred_elim:                              2
% 2.79/0.83  pred_elim_cl:                           2
% 2.79/0.83  pred_elim_cycles:                       4
% 2.79/0.83  merged_defs:                            0
% 2.79/0.83  merged_defs_ncl:                        0
% 2.79/0.83  bin_hyper_res:                          0
% 2.79/0.83  prep_cycles:                            4
% 2.79/0.83  pred_elim_time:                         0.001
% 2.79/0.83  splitting_time:                         0.
% 2.79/0.83  sem_filter_time:                        0.
% 2.79/0.83  monotx_time:                            0.
% 2.79/0.83  subtype_inf_time:                       0.
% 2.79/0.83  
% 2.79/0.83  ------ Problem properties
% 2.79/0.83  
% 2.79/0.83  clauses:                                15
% 2.79/0.83  conjectures:                            2
% 2.79/0.83  epr:                                    1
% 2.79/0.83  horn:                                   15
% 2.79/0.83  ground:                                 3
% 2.79/0.83  unary:                                  5
% 2.79/0.83  binary:                                 7
% 2.79/0.83  lits:                                   29
% 2.79/0.83  lits_eq:                                12
% 2.79/0.83  fd_pure:                                0
% 2.79/0.83  fd_pseudo:                              0
% 2.79/0.83  fd_cond:                                0
% 2.79/0.83  fd_pseudo_cond:                         0
% 2.79/0.83  ac_symbols:                             0
% 2.79/0.83  
% 2.79/0.83  ------ Propositional Solver
% 2.79/0.83  
% 2.79/0.83  prop_solver_calls:                      28
% 2.79/0.83  prop_fast_solver_calls:                 557
% 2.79/0.83  smt_solver_calls:                       0
% 2.79/0.83  smt_fast_solver_calls:                  0
% 2.79/0.83  prop_num_of_clauses:                    2113
% 2.79/0.83  prop_preprocess_simplified:             5583
% 2.79/0.83  prop_fo_subsumed:                       17
% 2.79/0.83  prop_solver_time:                       0.
% 2.79/0.83  smt_solver_time:                        0.
% 2.79/0.83  smt_fast_solver_time:                   0.
% 2.79/0.83  prop_fast_solver_time:                  0.
% 2.79/0.83  prop_unsat_core_time:                   0.
% 2.79/0.83  
% 2.79/0.83  ------ QBF
% 2.79/0.83  
% 2.79/0.83  qbf_q_res:                              0
% 2.79/0.83  qbf_num_tautologies:                    0
% 2.79/0.83  qbf_prep_cycles:                        0
% 2.79/0.83  
% 2.79/0.83  ------ BMC1
% 2.79/0.83  
% 2.79/0.83  bmc1_current_bound:                     -1
% 2.79/0.83  bmc1_last_solved_bound:                 -1
% 2.79/0.83  bmc1_unsat_core_size:                   -1
% 2.79/0.83  bmc1_unsat_core_parents_size:           -1
% 2.79/0.83  bmc1_merge_next_fun:                    0
% 2.79/0.83  bmc1_unsat_core_clauses_time:           0.
% 2.79/0.83  
% 2.79/0.83  ------ Instantiation
% 2.79/0.83  
% 2.79/0.83  inst_num_of_clauses:                    900
% 2.79/0.83  inst_num_in_passive:                    124
% 2.79/0.83  inst_num_in_active:                     359
% 2.79/0.83  inst_num_in_unprocessed:                418
% 2.79/0.83  inst_num_of_loops:                      370
% 2.79/0.83  inst_num_of_learning_restarts:          0
% 2.79/0.83  inst_num_moves_active_passive:          8
% 2.79/0.83  inst_lit_activity:                      0
% 2.79/0.83  inst_lit_activity_moves:                0
% 2.79/0.83  inst_num_tautologies:                   0
% 2.79/0.83  inst_num_prop_implied:                  0
% 2.79/0.83  inst_num_existing_simplified:           0
% 2.79/0.83  inst_num_eq_res_simplified:             0
% 2.79/0.83  inst_num_child_elim:                    0
% 2.79/0.83  inst_num_of_dismatching_blockings:      1408
% 2.79/0.83  inst_num_of_non_proper_insts:           1229
% 2.79/0.83  inst_num_of_duplicates:                 0
% 2.79/0.83  inst_inst_num_from_inst_to_res:         0
% 2.79/0.83  inst_dismatching_checking_time:         0.
% 2.79/0.83  
% 2.79/0.83  ------ Resolution
% 2.79/0.83  
% 2.79/0.83  res_num_of_clauses:                     0
% 2.79/0.83  res_num_in_passive:                     0
% 2.79/0.83  res_num_in_active:                      0
% 2.79/0.83  res_num_of_loops:                       89
% 2.79/0.83  res_forward_subset_subsumed:            139
% 2.79/0.83  res_backward_subset_subsumed:           8
% 2.79/0.83  res_forward_subsumed:                   0
% 2.79/0.83  res_backward_subsumed:                  0
% 2.79/0.83  res_forward_subsumption_resolution:     0
% 2.79/0.83  res_backward_subsumption_resolution:    0
% 2.79/0.83  res_clause_to_clause_subsumption:       418
% 2.79/0.83  res_orphan_elimination:                 0
% 2.79/0.83  res_tautology_del:                      183
% 2.79/0.83  res_num_eq_res_simplified:              0
% 2.79/0.83  res_num_sel_changes:                    0
% 2.79/0.83  res_moves_from_active_to_pass:          0
% 2.79/0.83  
% 2.79/0.83  ------ Superposition
% 2.79/0.83  
% 2.79/0.83  sup_time_total:                         0.
% 2.79/0.83  sup_time_generating:                    0.
% 2.79/0.83  sup_time_sim_full:                      0.
% 2.79/0.83  sup_time_sim_immed:                     0.
% 2.79/0.83  
% 2.79/0.83  sup_num_of_clauses:                     156
% 2.79/0.83  sup_num_in_active:                      73
% 2.79/0.83  sup_num_in_passive:                     83
% 2.79/0.83  sup_num_of_loops:                       73
% 2.79/0.83  sup_fw_superposition:                   125
% 2.79/0.83  sup_bw_superposition:                   56
% 2.79/0.83  sup_immediate_simplified:               54
% 2.79/0.83  sup_given_eliminated:                   0
% 2.79/0.83  comparisons_done:                       0
% 2.79/0.83  comparisons_avoided:                    0
% 2.79/0.83  
% 2.79/0.83  ------ Simplifications
% 2.79/0.83  
% 2.79/0.83  
% 2.79/0.83  sim_fw_subset_subsumed:                 6
% 2.79/0.83  sim_bw_subset_subsumed:                 0
% 2.79/0.83  sim_fw_subsumed:                        11
% 2.79/0.83  sim_bw_subsumed:                        0
% 2.79/0.83  sim_fw_subsumption_res:                 3
% 2.79/0.83  sim_bw_subsumption_res:                 0
% 2.79/0.83  sim_tautology_del:                      0
% 2.79/0.83  sim_eq_tautology_del:                   15
% 2.79/0.83  sim_eq_res_simp:                        1
% 2.79/0.83  sim_fw_demodulated:                     3
% 2.79/0.83  sim_bw_demodulated:                     1
% 2.79/0.83  sim_light_normalised:                   44
% 2.79/0.83  sim_joinable_taut:                      0
% 2.79/0.83  sim_joinable_simp:                      0
% 2.79/0.83  sim_ac_normalised:                      0
% 2.79/0.83  sim_smt_subsumption:                    0
% 2.79/0.83  
%------------------------------------------------------------------------------
