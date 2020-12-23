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
% DateTime   : Thu Dec  3 11:50:50 EST 2020

% Result     : Theorem 2.71s
% Output     : CNFRefutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 478 expanded)
%              Number of clauses        :   61 ( 137 expanded)
%              Number of leaves         :   12 ( 122 expanded)
%              Depth                    :   21
%              Number of atoms          :  414 (3085 expanded)
%              Number of equality atoms :  221 (1310 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f55,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f32])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
              & k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
                & k2_relat_1(X1) = k1_relat_1(X0)
                & v2_funct_1(X0) )
             => k2_funct_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
          & k2_relat_1(X1) = k1_relat_1(X0)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
          & k2_relat_1(X1) = k1_relat_1(X0)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
          & k2_relat_1(X1) = k1_relat_1(X0)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( k2_funct_1(X0) != sK1
        & k5_relat_1(sK1,X0) = k6_relat_1(k2_relat_1(X0))
        & k2_relat_1(sK1) = k1_relat_1(X0)
        & v2_funct_1(X0)
        & v1_funct_1(sK1)
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_funct_1(X0) != X1
            & k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
            & k2_relat_1(X1) = k1_relat_1(X0)
            & v2_funct_1(X0)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k2_funct_1(sK0) != X1
          & k5_relat_1(X1,sK0) = k6_relat_1(k2_relat_1(sK0))
          & k2_relat_1(X1) = k1_relat_1(sK0)
          & v2_funct_1(sK0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( k2_funct_1(sK0) != sK1
    & k5_relat_1(sK1,sK0) = k6_relat_1(k2_relat_1(sK0))
    & k2_relat_1(sK1) = k1_relat_1(sK0)
    & v2_funct_1(sK0)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f29,f28])).

fof(f52,plain,(
    k2_relat_1(sK1) = k1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f49,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f53,plain,(
    k5_relat_1(sK1,sK0) = k6_relat_1(k2_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f47,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
              & k2_relat_1(X0) = k1_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ? [X1] :
            ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
       => v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ! [X1] :
          ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ! [X1] :
          ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f48,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f50,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => ( v2_funct_1(X0)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X1)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f45,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f54,plain,(
    k2_funct_1(sK0) != sK1 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_675,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_18,negated_conjecture,
    ( k2_relat_1(sK1) = k1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_3,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_674,plain,
    ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
    | r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1664,plain,
    ( k1_relat_1(k5_relat_1(sK1,X0)) = k1_relat_1(sK1)
    | r1_tarski(k1_relat_1(sK0),k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_674])).

cnf(c_21,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_26,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1796,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_tarski(k1_relat_1(sK0),k1_relat_1(X0)) != iProver_top
    | k1_relat_1(k5_relat_1(sK1,X0)) = k1_relat_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1664,c_26])).

cnf(c_1797,plain,
    ( k1_relat_1(k5_relat_1(sK1,X0)) = k1_relat_1(sK1)
    | r1_tarski(k1_relat_1(sK0),k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1796])).

cnf(c_1805,plain,
    ( k1_relat_1(k5_relat_1(sK1,sK0)) = k1_relat_1(sK1)
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_675,c_1797])).

cnf(c_17,negated_conjecture,
    ( k5_relat_1(sK1,sK0) = k6_relat_1(k2_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1822,plain,
    ( k1_relat_1(k6_relat_1(k2_relat_1(sK0))) = k1_relat_1(sK1)
    | v1_relat_1(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1805,c_17])).

cnf(c_5,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1823,plain,
    ( k2_relat_1(sK0) = k1_relat_1(sK1)
    | v1_relat_1(sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1822,c_5])).

cnf(c_23,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_24,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1832,plain,
    ( k2_relat_1(sK0) = k1_relat_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1823,c_24])).

cnf(c_15,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X1,X0) != k6_relat_1(k1_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k2_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_10,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | v2_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X1,X0) != k6_relat_1(k1_relat_1(X1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_109,plain,
    ( ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X1,X0) != k6_relat_1(k1_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k2_relat_1(X1) != k1_relat_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15,c_10])).

cnf(c_110,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
    | k2_funct_1(X0) = X1
    | k2_relat_1(X0) != k1_relat_1(X1) ),
    inference(renaming,[status(thm)],[c_109])).

cnf(c_659,plain,
    ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
    | k2_funct_1(X0) = X1
    | k2_relat_1(X0) != k1_relat_1(X1)
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_110])).

cnf(c_1011,plain,
    ( k2_funct_1(sK1) = sK0
    | k6_relat_1(k1_relat_1(sK1)) != k6_relat_1(k2_relat_1(sK0))
    | k2_relat_1(sK1) != k1_relat_1(sK0)
    | v1_funct_1(sK1) != iProver_top
    | v1_funct_1(sK0) != iProver_top
    | v1_relat_1(sK1) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_17,c_659])).

cnf(c_1012,plain,
    ( k2_funct_1(sK1) = sK0
    | k6_relat_1(k1_relat_1(sK1)) != k6_relat_1(k2_relat_1(sK0))
    | k1_relat_1(sK0) != k1_relat_1(sK0)
    | v1_funct_1(sK1) != iProver_top
    | v1_funct_1(sK0) != iProver_top
    | v1_relat_1(sK1) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1011,c_18])).

cnf(c_1013,plain,
    ( k2_funct_1(sK1) = sK0
    | k6_relat_1(k1_relat_1(sK1)) != k6_relat_1(k2_relat_1(sK0))
    | v1_funct_1(sK1) != iProver_top
    | v1_funct_1(sK0) != iProver_top
    | v1_relat_1(sK1) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_1012])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1014,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | k2_funct_1(sK1) = sK0
    | k6_relat_1(k1_relat_1(sK1)) != k6_relat_1(k2_relat_1(sK0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1013])).

cnf(c_1160,plain,
    ( k2_funct_1(sK1) = sK0
    | k6_relat_1(k1_relat_1(sK1)) != k6_relat_1(k2_relat_1(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1013,c_23,c_22,c_21,c_20,c_1014])).

cnf(c_1836,plain,
    ( k2_funct_1(sK1) = sK0
    | k6_relat_1(k1_relat_1(sK1)) != k6_relat_1(k1_relat_1(sK1)) ),
    inference(demodulation,[status(thm)],[c_1832,c_1160])).

cnf(c_1840,plain,
    ( k2_funct_1(sK1) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_1836])).

cnf(c_9,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | v2_funct_1(X0)
    | ~ v2_funct_1(k5_relat_1(X0,X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k2_relat_1(X0) != k1_relat_1(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_670,plain,
    ( k2_relat_1(X0) != k1_relat_1(X1)
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k5_relat_1(X0,X1)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2765,plain,
    ( k1_relat_1(X0) != k1_relat_1(sK0)
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v2_funct_1(k5_relat_1(sK1,X0)) != iProver_top
    | v2_funct_1(sK1) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_670])).

cnf(c_25,plain,
    ( v1_funct_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_27,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_334,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_892,plain,
    ( k5_relat_1(sK1,sK0) != X0
    | k5_relat_1(sK1,sK0) = k6_relat_1(k1_relat_1(sK1))
    | k6_relat_1(k1_relat_1(sK1)) != X0 ),
    inference(instantiation,[status(thm)],[c_334])).

cnf(c_984,plain,
    ( k5_relat_1(sK1,sK0) != k5_relat_1(sK1,sK0)
    | k5_relat_1(sK1,sK0) = k6_relat_1(k1_relat_1(sK1))
    | k6_relat_1(k1_relat_1(sK1)) != k5_relat_1(sK1,sK0) ),
    inference(instantiation,[status(thm)],[c_892])).

cnf(c_333,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_985,plain,
    ( k5_relat_1(sK1,sK0) = k5_relat_1(sK1,sK0) ),
    inference(instantiation,[status(thm)],[c_333])).

cnf(c_1637,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK1)
    | v2_funct_1(sK1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK1)
    | k5_relat_1(sK1,X0) != k6_relat_1(k1_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1643,plain,
    ( k5_relat_1(sK1,X0) != k6_relat_1(k1_relat_1(sK1))
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v2_funct_1(sK1) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1637])).

cnf(c_1645,plain,
    ( k5_relat_1(sK1,sK0) != k6_relat_1(k1_relat_1(sK1))
    | v1_funct_1(sK1) != iProver_top
    | v1_funct_1(sK0) != iProver_top
    | v2_funct_1(sK1) = iProver_top
    | v1_relat_1(sK1) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1643])).

cnf(c_1837,plain,
    ( k6_relat_1(k1_relat_1(sK1)) = k5_relat_1(sK1,sK0) ),
    inference(demodulation,[status(thm)],[c_1832,c_17])).

cnf(c_2987,plain,
    ( v2_funct_1(sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2765,c_24,c_25,c_26,c_27,c_984,c_985,c_1645,c_1837])).

cnf(c_663,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_13,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_666,plain,
    ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1544,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_relat_1(k2_relat_1(sK1))
    | v2_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_663,c_666])).

cnf(c_1555,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_relat_1(k1_relat_1(sK0))
    | v2_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1544,c_18])).

cnf(c_1652,plain,
    ( v2_funct_1(sK1) != iProver_top
    | k5_relat_1(k2_funct_1(sK1),sK1) = k6_relat_1(k1_relat_1(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1555,c_26])).

cnf(c_1653,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_relat_1(k1_relat_1(sK0))
    | v2_funct_1(sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_1652])).

cnf(c_2992,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_relat_1(k1_relat_1(sK0)) ),
    inference(superposition,[status(thm)],[c_2987,c_1653])).

cnf(c_6387,plain,
    ( k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_1840,c_2992])).

cnf(c_6997,plain,
    ( k2_funct_1(sK0) = sK1
    | k2_relat_1(sK0) != k1_relat_1(sK1)
    | v1_funct_1(sK1) != iProver_top
    | v1_funct_1(sK0) != iProver_top
    | v1_relat_1(sK1) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6387,c_659])).

cnf(c_7004,plain,
    ( k2_funct_1(sK0) = sK1
    | k1_relat_1(sK1) != k1_relat_1(sK1)
    | v1_funct_1(sK1) != iProver_top
    | v1_funct_1(sK0) != iProver_top
    | v1_relat_1(sK1) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6997,c_1832])).

cnf(c_7005,plain,
    ( k2_funct_1(sK0) = sK1
    | v1_funct_1(sK1) != iProver_top
    | v1_funct_1(sK0) != iProver_top
    | v1_relat_1(sK1) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_7004])).

cnf(c_16,negated_conjecture,
    ( k2_funct_1(sK0) != sK1 ),
    inference(cnf_transformation,[],[f54])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7005,c_16,c_27,c_26,c_25,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n022.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 20:53:25 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running in FOF mode
% 2.71/0.96  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/0.96  
% 2.71/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.71/0.96  
% 2.71/0.96  ------  iProver source info
% 2.71/0.96  
% 2.71/0.96  git: date: 2020-06-30 10:37:57 +0100
% 2.71/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.71/0.96  git: non_committed_changes: false
% 2.71/0.96  git: last_make_outside_of_git: false
% 2.71/0.96  
% 2.71/0.96  ------ 
% 2.71/0.96  
% 2.71/0.96  ------ Input Options
% 2.71/0.96  
% 2.71/0.96  --out_options                           all
% 2.71/0.96  --tptp_safe_out                         true
% 2.71/0.96  --problem_path                          ""
% 2.71/0.96  --include_path                          ""
% 2.71/0.96  --clausifier                            res/vclausify_rel
% 2.71/0.96  --clausifier_options                    --mode clausify
% 2.71/0.96  --stdin                                 false
% 2.71/0.96  --stats_out                             all
% 2.71/0.96  
% 2.71/0.96  ------ General Options
% 2.71/0.96  
% 2.71/0.96  --fof                                   false
% 2.71/0.96  --time_out_real                         305.
% 2.71/0.96  --time_out_virtual                      -1.
% 2.71/0.96  --symbol_type_check                     false
% 2.71/0.96  --clausify_out                          false
% 2.71/0.96  --sig_cnt_out                           false
% 2.71/0.96  --trig_cnt_out                          false
% 2.71/0.96  --trig_cnt_out_tolerance                1.
% 2.71/0.96  --trig_cnt_out_sk_spl                   false
% 2.71/0.96  --abstr_cl_out                          false
% 2.71/0.96  
% 2.71/0.96  ------ Global Options
% 2.71/0.96  
% 2.71/0.96  --schedule                              default
% 2.71/0.96  --add_important_lit                     false
% 2.71/0.96  --prop_solver_per_cl                    1000
% 2.71/0.96  --min_unsat_core                        false
% 2.71/0.96  --soft_assumptions                      false
% 2.71/0.96  --soft_lemma_size                       3
% 2.71/0.96  --prop_impl_unit_size                   0
% 2.71/0.96  --prop_impl_unit                        []
% 2.71/0.96  --share_sel_clauses                     true
% 2.71/0.96  --reset_solvers                         false
% 2.71/0.96  --bc_imp_inh                            [conj_cone]
% 2.71/0.96  --conj_cone_tolerance                   3.
% 2.71/0.96  --extra_neg_conj                        none
% 2.71/0.96  --large_theory_mode                     true
% 2.71/0.96  --prolific_symb_bound                   200
% 2.71/0.96  --lt_threshold                          2000
% 2.71/0.96  --clause_weak_htbl                      true
% 2.71/0.96  --gc_record_bc_elim                     false
% 2.71/0.96  
% 2.71/0.96  ------ Preprocessing Options
% 2.71/0.96  
% 2.71/0.96  --preprocessing_flag                    true
% 2.71/0.96  --time_out_prep_mult                    0.1
% 2.71/0.96  --splitting_mode                        input
% 2.71/0.96  --splitting_grd                         true
% 2.71/0.96  --splitting_cvd                         false
% 2.71/0.96  --splitting_cvd_svl                     false
% 2.71/0.96  --splitting_nvd                         32
% 2.71/0.96  --sub_typing                            true
% 2.71/0.96  --prep_gs_sim                           true
% 2.71/0.96  --prep_unflatten                        true
% 2.71/0.96  --prep_res_sim                          true
% 2.71/0.96  --prep_upred                            true
% 2.71/0.96  --prep_sem_filter                       exhaustive
% 2.71/0.96  --prep_sem_filter_out                   false
% 2.71/0.96  --pred_elim                             true
% 2.71/0.96  --res_sim_input                         true
% 2.71/0.96  --eq_ax_congr_red                       true
% 2.71/0.96  --pure_diseq_elim                       true
% 2.71/0.96  --brand_transform                       false
% 2.71/0.96  --non_eq_to_eq                          false
% 2.71/0.96  --prep_def_merge                        true
% 2.71/0.96  --prep_def_merge_prop_impl              false
% 2.71/0.96  --prep_def_merge_mbd                    true
% 2.71/0.96  --prep_def_merge_tr_red                 false
% 2.71/0.96  --prep_def_merge_tr_cl                  false
% 2.71/0.96  --smt_preprocessing                     true
% 2.71/0.96  --smt_ac_axioms                         fast
% 2.71/0.96  --preprocessed_out                      false
% 2.71/0.96  --preprocessed_stats                    false
% 2.71/0.96  
% 2.71/0.96  ------ Abstraction refinement Options
% 2.71/0.96  
% 2.71/0.96  --abstr_ref                             []
% 2.71/0.96  --abstr_ref_prep                        false
% 2.71/0.96  --abstr_ref_until_sat                   false
% 2.71/0.96  --abstr_ref_sig_restrict                funpre
% 2.71/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 2.71/0.96  --abstr_ref_under                       []
% 2.71/0.96  
% 2.71/0.96  ------ SAT Options
% 2.71/0.96  
% 2.71/0.96  --sat_mode                              false
% 2.71/0.96  --sat_fm_restart_options                ""
% 2.71/0.96  --sat_gr_def                            false
% 2.71/0.96  --sat_epr_types                         true
% 2.71/0.96  --sat_non_cyclic_types                  false
% 2.71/0.96  --sat_finite_models                     false
% 2.71/0.96  --sat_fm_lemmas                         false
% 2.71/0.96  --sat_fm_prep                           false
% 2.71/0.96  --sat_fm_uc_incr                        true
% 2.71/0.96  --sat_out_model                         small
% 2.71/0.96  --sat_out_clauses                       false
% 2.71/0.96  
% 2.71/0.96  ------ QBF Options
% 2.71/0.96  
% 2.71/0.96  --qbf_mode                              false
% 2.71/0.96  --qbf_elim_univ                         false
% 2.71/0.96  --qbf_dom_inst                          none
% 2.71/0.96  --qbf_dom_pre_inst                      false
% 2.71/0.96  --qbf_sk_in                             false
% 2.71/0.96  --qbf_pred_elim                         true
% 2.71/0.96  --qbf_split                             512
% 2.71/0.96  
% 2.71/0.96  ------ BMC1 Options
% 2.71/0.96  
% 2.71/0.96  --bmc1_incremental                      false
% 2.71/0.96  --bmc1_axioms                           reachable_all
% 2.71/0.96  --bmc1_min_bound                        0
% 2.71/0.96  --bmc1_max_bound                        -1
% 2.71/0.96  --bmc1_max_bound_default                -1
% 2.71/0.96  --bmc1_symbol_reachability              true
% 2.71/0.96  --bmc1_property_lemmas                  false
% 2.71/0.96  --bmc1_k_induction                      false
% 2.71/0.96  --bmc1_non_equiv_states                 false
% 2.71/0.96  --bmc1_deadlock                         false
% 2.71/0.96  --bmc1_ucm                              false
% 2.71/0.96  --bmc1_add_unsat_core                   none
% 2.71/0.96  --bmc1_unsat_core_children              false
% 2.71/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 2.71/0.96  --bmc1_out_stat                         full
% 2.71/0.96  --bmc1_ground_init                      false
% 2.71/0.96  --bmc1_pre_inst_next_state              false
% 2.71/0.96  --bmc1_pre_inst_state                   false
% 2.71/0.96  --bmc1_pre_inst_reach_state             false
% 2.71/0.96  --bmc1_out_unsat_core                   false
% 2.71/0.96  --bmc1_aig_witness_out                  false
% 2.71/0.96  --bmc1_verbose                          false
% 2.71/0.96  --bmc1_dump_clauses_tptp                false
% 2.71/0.96  --bmc1_dump_unsat_core_tptp             false
% 2.71/0.96  --bmc1_dump_file                        -
% 2.71/0.96  --bmc1_ucm_expand_uc_limit              128
% 2.71/0.96  --bmc1_ucm_n_expand_iterations          6
% 2.71/0.96  --bmc1_ucm_extend_mode                  1
% 2.71/0.96  --bmc1_ucm_init_mode                    2
% 2.71/0.96  --bmc1_ucm_cone_mode                    none
% 2.71/0.96  --bmc1_ucm_reduced_relation_type        0
% 2.71/0.96  --bmc1_ucm_relax_model                  4
% 2.71/0.96  --bmc1_ucm_full_tr_after_sat            true
% 2.71/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 2.71/0.96  --bmc1_ucm_layered_model                none
% 2.71/0.96  --bmc1_ucm_max_lemma_size               10
% 2.71/0.96  
% 2.71/0.96  ------ AIG Options
% 2.71/0.96  
% 2.71/0.96  --aig_mode                              false
% 2.71/0.96  
% 2.71/0.96  ------ Instantiation Options
% 2.71/0.96  
% 2.71/0.96  --instantiation_flag                    true
% 2.71/0.96  --inst_sos_flag                         false
% 2.71/0.96  --inst_sos_phase                        true
% 2.71/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.71/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.71/0.96  --inst_lit_sel_side                     num_symb
% 2.71/0.96  --inst_solver_per_active                1400
% 2.71/0.96  --inst_solver_calls_frac                1.
% 2.71/0.96  --inst_passive_queue_type               priority_queues
% 2.71/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.71/0.96  --inst_passive_queues_freq              [25;2]
% 2.71/0.96  --inst_dismatching                      true
% 2.71/0.96  --inst_eager_unprocessed_to_passive     true
% 2.71/0.96  --inst_prop_sim_given                   true
% 2.71/0.96  --inst_prop_sim_new                     false
% 2.71/0.96  --inst_subs_new                         false
% 2.71/0.96  --inst_eq_res_simp                      false
% 2.71/0.96  --inst_subs_given                       false
% 2.71/0.96  --inst_orphan_elimination               true
% 2.71/0.96  --inst_learning_loop_flag               true
% 2.71/0.96  --inst_learning_start                   3000
% 2.71/0.96  --inst_learning_factor                  2
% 2.71/0.96  --inst_start_prop_sim_after_learn       3
% 2.71/0.96  --inst_sel_renew                        solver
% 2.71/0.96  --inst_lit_activity_flag                true
% 2.71/0.96  --inst_restr_to_given                   false
% 2.71/0.96  --inst_activity_threshold               500
% 2.71/0.96  --inst_out_proof                        true
% 2.71/0.96  
% 2.71/0.96  ------ Resolution Options
% 2.71/0.96  
% 2.71/0.96  --resolution_flag                       true
% 2.71/0.96  --res_lit_sel                           adaptive
% 2.71/0.96  --res_lit_sel_side                      none
% 2.71/0.96  --res_ordering                          kbo
% 2.71/0.96  --res_to_prop_solver                    active
% 2.71/0.96  --res_prop_simpl_new                    false
% 2.71/0.96  --res_prop_simpl_given                  true
% 2.71/0.96  --res_passive_queue_type                priority_queues
% 2.71/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.71/0.96  --res_passive_queues_freq               [15;5]
% 2.71/0.96  --res_forward_subs                      full
% 2.71/0.96  --res_backward_subs                     full
% 2.71/0.96  --res_forward_subs_resolution           true
% 2.71/0.96  --res_backward_subs_resolution          true
% 2.71/0.96  --res_orphan_elimination                true
% 2.71/0.96  --res_time_limit                        2.
% 2.71/0.96  --res_out_proof                         true
% 2.71/0.96  
% 2.71/0.96  ------ Superposition Options
% 2.71/0.96  
% 2.71/0.96  --superposition_flag                    true
% 2.71/0.96  --sup_passive_queue_type                priority_queues
% 2.71/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.71/0.96  --sup_passive_queues_freq               [8;1;4]
% 2.71/0.96  --demod_completeness_check              fast
% 2.71/0.96  --demod_use_ground                      true
% 2.71/0.96  --sup_to_prop_solver                    passive
% 2.71/0.96  --sup_prop_simpl_new                    true
% 2.71/0.96  --sup_prop_simpl_given                  true
% 2.71/0.96  --sup_fun_splitting                     false
% 2.71/0.96  --sup_smt_interval                      50000
% 2.71/0.96  
% 2.71/0.96  ------ Superposition Simplification Setup
% 2.71/0.96  
% 2.71/0.96  --sup_indices_passive                   []
% 2.71/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.71/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.71/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.71/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 2.71/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.71/0.96  --sup_full_bw                           [BwDemod]
% 2.71/0.96  --sup_immed_triv                        [TrivRules]
% 2.71/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.71/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.71/0.96  --sup_immed_bw_main                     []
% 2.71/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.71/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 2.71/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.71/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.71/0.96  
% 2.71/0.96  ------ Combination Options
% 2.71/0.96  
% 2.71/0.96  --comb_res_mult                         3
% 2.71/0.96  --comb_sup_mult                         2
% 2.71/0.96  --comb_inst_mult                        10
% 2.71/0.96  
% 2.71/0.96  ------ Debug Options
% 2.71/0.96  
% 2.71/0.96  --dbg_backtrace                         false
% 2.71/0.96  --dbg_dump_prop_clauses                 false
% 2.71/0.96  --dbg_dump_prop_clauses_file            -
% 2.71/0.96  --dbg_out_stat                          false
% 2.71/0.96  ------ Parsing...
% 2.71/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.71/0.96  
% 2.71/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.71/0.96  
% 2.71/0.96  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.71/0.96  
% 2.71/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.71/0.96  ------ Proving...
% 2.71/0.96  ------ Problem Properties 
% 2.71/0.96  
% 2.71/0.96  
% 2.71/0.96  clauses                                 23
% 2.71/0.96  conjectures                             8
% 2.71/0.96  EPR                                     7
% 2.71/0.96  Horn                                    23
% 2.71/0.96  unary                                   13
% 2.71/0.96  binary                                  0
% 2.71/0.96  lits                                    63
% 2.71/0.96  lits eq                                 17
% 2.71/0.96  fd_pure                                 0
% 2.71/0.96  fd_pseudo                               0
% 2.71/0.96  fd_cond                                 0
% 2.71/0.96  fd_pseudo_cond                          2
% 2.71/0.96  AC symbols                              0
% 2.71/0.96  
% 2.71/0.96  ------ Schedule dynamic 5 is on 
% 2.71/0.96  
% 2.71/0.96  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.71/0.96  
% 2.71/0.96  
% 2.71/0.96  ------ 
% 2.71/0.96  Current options:
% 2.71/0.96  ------ 
% 2.71/0.96  
% 2.71/0.96  ------ Input Options
% 2.71/0.96  
% 2.71/0.96  --out_options                           all
% 2.71/0.96  --tptp_safe_out                         true
% 2.71/0.96  --problem_path                          ""
% 2.71/0.96  --include_path                          ""
% 2.71/0.96  --clausifier                            res/vclausify_rel
% 2.71/0.96  --clausifier_options                    --mode clausify
% 2.71/0.96  --stdin                                 false
% 2.71/0.96  --stats_out                             all
% 2.71/0.96  
% 2.71/0.96  ------ General Options
% 2.71/0.96  
% 2.71/0.96  --fof                                   false
% 2.71/0.96  --time_out_real                         305.
% 2.71/0.96  --time_out_virtual                      -1.
% 2.71/0.96  --symbol_type_check                     false
% 2.71/0.96  --clausify_out                          false
% 2.71/0.96  --sig_cnt_out                           false
% 2.71/0.96  --trig_cnt_out                          false
% 2.71/0.96  --trig_cnt_out_tolerance                1.
% 2.71/0.96  --trig_cnt_out_sk_spl                   false
% 2.71/0.96  --abstr_cl_out                          false
% 2.71/0.96  
% 2.71/0.96  ------ Global Options
% 2.71/0.96  
% 2.71/0.96  --schedule                              default
% 2.71/0.96  --add_important_lit                     false
% 2.71/0.96  --prop_solver_per_cl                    1000
% 2.71/0.96  --min_unsat_core                        false
% 2.71/0.96  --soft_assumptions                      false
% 2.71/0.96  --soft_lemma_size                       3
% 2.71/0.96  --prop_impl_unit_size                   0
% 2.71/0.96  --prop_impl_unit                        []
% 2.71/0.96  --share_sel_clauses                     true
% 2.71/0.96  --reset_solvers                         false
% 2.71/0.96  --bc_imp_inh                            [conj_cone]
% 2.71/0.96  --conj_cone_tolerance                   3.
% 2.71/0.96  --extra_neg_conj                        none
% 2.71/0.96  --large_theory_mode                     true
% 2.71/0.96  --prolific_symb_bound                   200
% 2.71/0.96  --lt_threshold                          2000
% 2.71/0.96  --clause_weak_htbl                      true
% 2.71/0.96  --gc_record_bc_elim                     false
% 2.71/0.96  
% 2.71/0.96  ------ Preprocessing Options
% 2.71/0.96  
% 2.71/0.96  --preprocessing_flag                    true
% 2.71/0.96  --time_out_prep_mult                    0.1
% 2.71/0.96  --splitting_mode                        input
% 2.71/0.96  --splitting_grd                         true
% 2.71/0.96  --splitting_cvd                         false
% 2.71/0.96  --splitting_cvd_svl                     false
% 2.71/0.96  --splitting_nvd                         32
% 2.71/0.96  --sub_typing                            true
% 2.71/0.96  --prep_gs_sim                           true
% 2.71/0.96  --prep_unflatten                        true
% 2.71/0.96  --prep_res_sim                          true
% 2.71/0.96  --prep_upred                            true
% 2.71/0.96  --prep_sem_filter                       exhaustive
% 2.71/0.96  --prep_sem_filter_out                   false
% 2.71/0.96  --pred_elim                             true
% 2.71/0.96  --res_sim_input                         true
% 2.71/0.96  --eq_ax_congr_red                       true
% 2.71/0.96  --pure_diseq_elim                       true
% 2.71/0.96  --brand_transform                       false
% 2.71/0.96  --non_eq_to_eq                          false
% 2.71/0.96  --prep_def_merge                        true
% 2.71/0.96  --prep_def_merge_prop_impl              false
% 2.71/0.96  --prep_def_merge_mbd                    true
% 2.71/0.96  --prep_def_merge_tr_red                 false
% 2.71/0.96  --prep_def_merge_tr_cl                  false
% 2.71/0.96  --smt_preprocessing                     true
% 2.71/0.96  --smt_ac_axioms                         fast
% 2.71/0.96  --preprocessed_out                      false
% 2.71/0.96  --preprocessed_stats                    false
% 2.71/0.96  
% 2.71/0.96  ------ Abstraction refinement Options
% 2.71/0.96  
% 2.71/0.96  --abstr_ref                             []
% 2.71/0.96  --abstr_ref_prep                        false
% 2.71/0.96  --abstr_ref_until_sat                   false
% 2.71/0.96  --abstr_ref_sig_restrict                funpre
% 2.71/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 2.71/0.96  --abstr_ref_under                       []
% 2.71/0.96  
% 2.71/0.96  ------ SAT Options
% 2.71/0.96  
% 2.71/0.96  --sat_mode                              false
% 2.71/0.96  --sat_fm_restart_options                ""
% 2.71/0.96  --sat_gr_def                            false
% 2.71/0.96  --sat_epr_types                         true
% 2.71/0.96  --sat_non_cyclic_types                  false
% 2.71/0.96  --sat_finite_models                     false
% 2.71/0.96  --sat_fm_lemmas                         false
% 2.71/0.96  --sat_fm_prep                           false
% 2.71/0.96  --sat_fm_uc_incr                        true
% 2.71/0.96  --sat_out_model                         small
% 2.71/0.96  --sat_out_clauses                       false
% 2.71/0.96  
% 2.71/0.96  ------ QBF Options
% 2.71/0.96  
% 2.71/0.96  --qbf_mode                              false
% 2.71/0.96  --qbf_elim_univ                         false
% 2.71/0.96  --qbf_dom_inst                          none
% 2.71/0.96  --qbf_dom_pre_inst                      false
% 2.71/0.96  --qbf_sk_in                             false
% 2.71/0.96  --qbf_pred_elim                         true
% 2.71/0.96  --qbf_split                             512
% 2.71/0.96  
% 2.71/0.96  ------ BMC1 Options
% 2.71/0.96  
% 2.71/0.96  --bmc1_incremental                      false
% 2.71/0.96  --bmc1_axioms                           reachable_all
% 2.71/0.96  --bmc1_min_bound                        0
% 2.71/0.96  --bmc1_max_bound                        -1
% 2.71/0.96  --bmc1_max_bound_default                -1
% 2.71/0.96  --bmc1_symbol_reachability              true
% 2.71/0.96  --bmc1_property_lemmas                  false
% 2.71/0.96  --bmc1_k_induction                      false
% 2.71/0.96  --bmc1_non_equiv_states                 false
% 2.71/0.96  --bmc1_deadlock                         false
% 2.71/0.96  --bmc1_ucm                              false
% 2.71/0.96  --bmc1_add_unsat_core                   none
% 2.71/0.96  --bmc1_unsat_core_children              false
% 2.71/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 2.71/0.96  --bmc1_out_stat                         full
% 2.71/0.96  --bmc1_ground_init                      false
% 2.71/0.96  --bmc1_pre_inst_next_state              false
% 2.71/0.96  --bmc1_pre_inst_state                   false
% 2.71/0.96  --bmc1_pre_inst_reach_state             false
% 2.71/0.96  --bmc1_out_unsat_core                   false
% 2.71/0.96  --bmc1_aig_witness_out                  false
% 2.71/0.96  --bmc1_verbose                          false
% 2.71/0.96  --bmc1_dump_clauses_tptp                false
% 2.71/0.96  --bmc1_dump_unsat_core_tptp             false
% 2.71/0.96  --bmc1_dump_file                        -
% 2.71/0.96  --bmc1_ucm_expand_uc_limit              128
% 2.71/0.96  --bmc1_ucm_n_expand_iterations          6
% 2.71/0.96  --bmc1_ucm_extend_mode                  1
% 2.71/0.96  --bmc1_ucm_init_mode                    2
% 2.71/0.96  --bmc1_ucm_cone_mode                    none
% 2.71/0.96  --bmc1_ucm_reduced_relation_type        0
% 2.71/0.96  --bmc1_ucm_relax_model                  4
% 2.71/0.96  --bmc1_ucm_full_tr_after_sat            true
% 2.71/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 2.71/0.96  --bmc1_ucm_layered_model                none
% 2.71/0.96  --bmc1_ucm_max_lemma_size               10
% 2.71/0.96  
% 2.71/0.96  ------ AIG Options
% 2.71/0.96  
% 2.71/0.96  --aig_mode                              false
% 2.71/0.96  
% 2.71/0.96  ------ Instantiation Options
% 2.71/0.96  
% 2.71/0.96  --instantiation_flag                    true
% 2.71/0.96  --inst_sos_flag                         false
% 2.71/0.96  --inst_sos_phase                        true
% 2.71/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.71/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.71/0.96  --inst_lit_sel_side                     none
% 2.71/0.96  --inst_solver_per_active                1400
% 2.71/0.96  --inst_solver_calls_frac                1.
% 2.71/0.96  --inst_passive_queue_type               priority_queues
% 2.71/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.71/0.96  --inst_passive_queues_freq              [25;2]
% 2.71/0.96  --inst_dismatching                      true
% 2.71/0.96  --inst_eager_unprocessed_to_passive     true
% 2.71/0.96  --inst_prop_sim_given                   true
% 2.71/0.96  --inst_prop_sim_new                     false
% 2.71/0.96  --inst_subs_new                         false
% 2.71/0.96  --inst_eq_res_simp                      false
% 2.71/0.96  --inst_subs_given                       false
% 2.71/0.96  --inst_orphan_elimination               true
% 2.71/0.96  --inst_learning_loop_flag               true
% 2.71/0.96  --inst_learning_start                   3000
% 2.71/0.96  --inst_learning_factor                  2
% 2.71/0.96  --inst_start_prop_sim_after_learn       3
% 2.71/0.96  --inst_sel_renew                        solver
% 2.71/0.96  --inst_lit_activity_flag                true
% 2.71/0.96  --inst_restr_to_given                   false
% 2.71/0.96  --inst_activity_threshold               500
% 2.71/0.96  --inst_out_proof                        true
% 2.71/0.96  
% 2.71/0.96  ------ Resolution Options
% 2.71/0.96  
% 2.71/0.96  --resolution_flag                       false
% 2.71/0.96  --res_lit_sel                           adaptive
% 2.71/0.96  --res_lit_sel_side                      none
% 2.71/0.96  --res_ordering                          kbo
% 2.71/0.96  --res_to_prop_solver                    active
% 2.71/0.96  --res_prop_simpl_new                    false
% 2.71/0.96  --res_prop_simpl_given                  true
% 2.71/0.96  --res_passive_queue_type                priority_queues
% 2.71/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.71/0.96  --res_passive_queues_freq               [15;5]
% 2.71/0.96  --res_forward_subs                      full
% 2.71/0.96  --res_backward_subs                     full
% 2.71/0.96  --res_forward_subs_resolution           true
% 2.71/0.96  --res_backward_subs_resolution          true
% 2.71/0.96  --res_orphan_elimination                true
% 2.71/0.96  --res_time_limit                        2.
% 2.71/0.96  --res_out_proof                         true
% 2.71/0.96  
% 2.71/0.96  ------ Superposition Options
% 2.71/0.96  
% 2.71/0.96  --superposition_flag                    true
% 2.71/0.96  --sup_passive_queue_type                priority_queues
% 2.71/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.71/0.96  --sup_passive_queues_freq               [8;1;4]
% 2.71/0.96  --demod_completeness_check              fast
% 2.71/0.96  --demod_use_ground                      true
% 2.71/0.96  --sup_to_prop_solver                    passive
% 2.71/0.96  --sup_prop_simpl_new                    true
% 2.71/0.96  --sup_prop_simpl_given                  true
% 2.71/0.96  --sup_fun_splitting                     false
% 2.71/0.96  --sup_smt_interval                      50000
% 2.71/0.96  
% 2.71/0.96  ------ Superposition Simplification Setup
% 2.71/0.96  
% 2.71/0.96  --sup_indices_passive                   []
% 2.71/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.71/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.71/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.71/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 2.71/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.71/0.96  --sup_full_bw                           [BwDemod]
% 2.71/0.96  --sup_immed_triv                        [TrivRules]
% 2.71/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.71/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.71/0.96  --sup_immed_bw_main                     []
% 2.71/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.71/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 2.71/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.71/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.71/0.96  
% 2.71/0.96  ------ Combination Options
% 2.71/0.96  
% 2.71/0.96  --comb_res_mult                         3
% 2.71/0.96  --comb_sup_mult                         2
% 2.71/0.96  --comb_inst_mult                        10
% 2.71/0.96  
% 2.71/0.96  ------ Debug Options
% 2.71/0.96  
% 2.71/0.96  --dbg_backtrace                         false
% 2.71/0.96  --dbg_dump_prop_clauses                 false
% 2.71/0.96  --dbg_dump_prop_clauses_file            -
% 2.71/0.96  --dbg_out_stat                          false
% 2.71/0.96  
% 2.71/0.96  
% 2.71/0.96  
% 2.71/0.96  
% 2.71/0.96  ------ Proving...
% 2.71/0.96  
% 2.71/0.96  
% 2.71/0.96  % SZS status Theorem for theBenchmark.p
% 2.71/0.96  
% 2.71/0.96  % SZS output start CNFRefutation for theBenchmark.p
% 2.71/0.96  
% 2.71/0.96  fof(f1,axiom,(
% 2.71/0.96    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.71/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.71/0.96  
% 2.71/0.96  fof(f26,plain,(
% 2.71/0.96    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.71/0.96    inference(nnf_transformation,[],[f1])).
% 2.71/0.96  
% 2.71/0.96  fof(f27,plain,(
% 2.71/0.96    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.71/0.96    inference(flattening,[],[f26])).
% 2.71/0.96  
% 2.71/0.96  fof(f32,plain,(
% 2.71/0.96    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.71/0.96    inference(cnf_transformation,[],[f27])).
% 2.71/0.96  
% 2.71/0.96  fof(f55,plain,(
% 2.71/0.96    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.71/0.96    inference(equality_resolution,[],[f32])).
% 2.71/0.96  
% 2.71/0.96  fof(f10,conjecture,(
% 2.71/0.96    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 2.71/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.71/0.96  
% 2.71/0.96  fof(f11,negated_conjecture,(
% 2.71/0.96    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 2.71/0.96    inference(negated_conjecture,[],[f10])).
% 2.71/0.96  
% 2.71/0.96  fof(f24,plain,(
% 2.71/0.96    ? [X0] : (? [X1] : ((k2_funct_1(X0) != X1 & (k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 2.71/0.96    inference(ennf_transformation,[],[f11])).
% 2.71/0.96  
% 2.71/0.96  fof(f25,plain,(
% 2.71/0.96    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 2.71/0.96    inference(flattening,[],[f24])).
% 2.71/0.96  
% 2.71/0.96  fof(f29,plain,(
% 2.71/0.96    ( ! [X0] : (? [X1] : (k2_funct_1(X0) != X1 & k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) => (k2_funct_1(X0) != sK1 & k5_relat_1(sK1,X0) = k6_relat_1(k2_relat_1(X0)) & k2_relat_1(sK1) = k1_relat_1(X0) & v2_funct_1(X0) & v1_funct_1(sK1) & v1_relat_1(sK1))) )),
% 2.71/0.96    introduced(choice_axiom,[])).
% 2.71/0.96  
% 2.71/0.96  fof(f28,plain,(
% 2.71/0.96    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k2_funct_1(sK0) != X1 & k5_relat_1(X1,sK0) = k6_relat_1(k2_relat_1(sK0)) & k2_relat_1(X1) = k1_relat_1(sK0) & v2_funct_1(sK0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 2.71/0.96    introduced(choice_axiom,[])).
% 2.71/0.96  
% 2.71/0.96  fof(f30,plain,(
% 2.71/0.96    (k2_funct_1(sK0) != sK1 & k5_relat_1(sK1,sK0) = k6_relat_1(k2_relat_1(sK0)) & k2_relat_1(sK1) = k1_relat_1(sK0) & v2_funct_1(sK0) & v1_funct_1(sK1) & v1_relat_1(sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 2.71/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f29,f28])).
% 2.71/0.96  
% 2.71/0.96  fof(f52,plain,(
% 2.71/0.96    k2_relat_1(sK1) = k1_relat_1(sK0)),
% 2.71/0.96    inference(cnf_transformation,[],[f30])).
% 2.71/0.96  
% 2.71/0.96  fof(f2,axiom,(
% 2.71/0.96    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 2.71/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.71/0.96  
% 2.71/0.96  fof(f12,plain,(
% 2.71/0.96    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.71/0.96    inference(ennf_transformation,[],[f2])).
% 2.71/0.96  
% 2.71/0.96  fof(f13,plain,(
% 2.71/0.96    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.71/0.96    inference(flattening,[],[f12])).
% 2.71/0.96  
% 2.71/0.96  fof(f34,plain,(
% 2.71/0.96    ( ! [X0,X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.71/0.96    inference(cnf_transformation,[],[f13])).
% 2.71/0.96  
% 2.71/0.96  fof(f49,plain,(
% 2.71/0.96    v1_relat_1(sK1)),
% 2.71/0.96    inference(cnf_transformation,[],[f30])).
% 2.71/0.96  
% 2.71/0.96  fof(f53,plain,(
% 2.71/0.96    k5_relat_1(sK1,sK0) = k6_relat_1(k2_relat_1(sK0))),
% 2.71/0.96    inference(cnf_transformation,[],[f30])).
% 2.71/0.96  
% 2.71/0.96  fof(f3,axiom,(
% 2.71/0.96    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.71/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.71/0.96  
% 2.71/0.96  fof(f35,plain,(
% 2.71/0.96    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.71/0.96    inference(cnf_transformation,[],[f3])).
% 2.71/0.96  
% 2.71/0.96  fof(f47,plain,(
% 2.71/0.96    v1_relat_1(sK0)),
% 2.71/0.96    inference(cnf_transformation,[],[f30])).
% 2.71/0.96  
% 2.71/0.96  fof(f9,axiom,(
% 2.71/0.96    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 2.71/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.71/0.96  
% 2.71/0.96  fof(f22,plain,(
% 2.71/0.96    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.71/0.96    inference(ennf_transformation,[],[f9])).
% 2.71/0.96  
% 2.71/0.96  fof(f23,plain,(
% 2.71/0.96    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.71/0.96    inference(flattening,[],[f22])).
% 2.71/0.96  
% 2.71/0.96  fof(f46,plain,(
% 2.71/0.96    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.71/0.96    inference(cnf_transformation,[],[f23])).
% 2.71/0.96  
% 2.71/0.96  fof(f6,axiom,(
% 2.71/0.96    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) => v2_funct_1(X0)))),
% 2.71/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.71/0.96  
% 2.71/0.96  fof(f16,plain,(
% 2.71/0.96    ! [X0] : ((v2_funct_1(X0) | ! [X1] : (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.71/0.96    inference(ennf_transformation,[],[f6])).
% 2.71/0.96  
% 2.71/0.96  fof(f17,plain,(
% 2.71/0.96    ! [X0] : (v2_funct_1(X0) | ! [X1] : (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.71/0.96    inference(flattening,[],[f16])).
% 2.71/0.96  
% 2.71/0.96  fof(f41,plain,(
% 2.71/0.96    ( ! [X0,X1] : (v2_funct_1(X0) | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.71/0.96    inference(cnf_transformation,[],[f17])).
% 2.71/0.96  
% 2.71/0.96  fof(f48,plain,(
% 2.71/0.96    v1_funct_1(sK0)),
% 2.71/0.96    inference(cnf_transformation,[],[f30])).
% 2.71/0.96  
% 2.71/0.96  fof(f50,plain,(
% 2.71/0.96    v1_funct_1(sK1)),
% 2.71/0.96    inference(cnf_transformation,[],[f30])).
% 2.71/0.96  
% 2.71/0.96  fof(f5,axiom,(
% 2.71/0.96    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 2.71/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.71/0.96  
% 2.71/0.96  fof(f14,plain,(
% 2.71/0.96    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.71/0.96    inference(ennf_transformation,[],[f5])).
% 2.71/0.96  
% 2.71/0.96  fof(f15,plain,(
% 2.71/0.96    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.71/0.96    inference(flattening,[],[f14])).
% 2.71/0.96  
% 2.71/0.96  fof(f39,plain,(
% 2.71/0.96    ( ! [X0,X1] : (v2_funct_1(X1) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.71/0.96    inference(cnf_transformation,[],[f15])).
% 2.71/0.96  
% 2.71/0.96  fof(f8,axiom,(
% 2.71/0.96    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 2.71/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.71/0.96  
% 2.71/0.96  fof(f20,plain,(
% 2.71/0.96    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.71/0.96    inference(ennf_transformation,[],[f8])).
% 2.71/0.96  
% 2.71/0.96  fof(f21,plain,(
% 2.71/0.96    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.71/0.96    inference(flattening,[],[f20])).
% 2.71/0.96  
% 2.71/0.96  fof(f45,plain,(
% 2.71/0.96    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.71/0.96    inference(cnf_transformation,[],[f21])).
% 2.71/0.96  
% 2.71/0.96  fof(f54,plain,(
% 2.71/0.96    k2_funct_1(sK0) != sK1),
% 2.71/0.96    inference(cnf_transformation,[],[f30])).
% 2.71/0.96  
% 2.71/0.96  cnf(c_1,plain,
% 2.71/0.96      ( r1_tarski(X0,X0) ),
% 2.71/0.96      inference(cnf_transformation,[],[f55]) ).
% 2.71/0.96  
% 2.71/0.96  cnf(c_675,plain,
% 2.71/0.96      ( r1_tarski(X0,X0) = iProver_top ),
% 2.71/0.96      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.71/0.96  
% 2.71/0.96  cnf(c_18,negated_conjecture,
% 2.71/0.96      ( k2_relat_1(sK1) = k1_relat_1(sK0) ),
% 2.71/0.96      inference(cnf_transformation,[],[f52]) ).
% 2.71/0.96  
% 2.71/0.96  cnf(c_3,plain,
% 2.71/0.96      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
% 2.71/0.96      | ~ v1_relat_1(X1)
% 2.71/0.96      | ~ v1_relat_1(X0)
% 2.71/0.96      | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ),
% 2.71/0.96      inference(cnf_transformation,[],[f34]) ).
% 2.71/0.96  
% 2.71/0.96  cnf(c_674,plain,
% 2.71/0.96      ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
% 2.71/0.96      | r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) != iProver_top
% 2.71/0.96      | v1_relat_1(X0) != iProver_top
% 2.71/0.96      | v1_relat_1(X1) != iProver_top ),
% 2.71/0.96      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.71/0.96  
% 2.71/0.96  cnf(c_1664,plain,
% 2.71/0.96      ( k1_relat_1(k5_relat_1(sK1,X0)) = k1_relat_1(sK1)
% 2.71/0.96      | r1_tarski(k1_relat_1(sK0),k1_relat_1(X0)) != iProver_top
% 2.71/0.96      | v1_relat_1(X0) != iProver_top
% 2.71/0.96      | v1_relat_1(sK1) != iProver_top ),
% 2.71/0.96      inference(superposition,[status(thm)],[c_18,c_674]) ).
% 2.71/0.96  
% 2.71/0.96  cnf(c_21,negated_conjecture,
% 2.71/0.96      ( v1_relat_1(sK1) ),
% 2.71/0.96      inference(cnf_transformation,[],[f49]) ).
% 2.71/0.96  
% 2.71/0.96  cnf(c_26,plain,
% 2.71/0.96      ( v1_relat_1(sK1) = iProver_top ),
% 2.71/0.96      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.71/0.96  
% 2.71/0.96  cnf(c_1796,plain,
% 2.71/0.96      ( v1_relat_1(X0) != iProver_top
% 2.71/0.96      | r1_tarski(k1_relat_1(sK0),k1_relat_1(X0)) != iProver_top
% 2.71/0.96      | k1_relat_1(k5_relat_1(sK1,X0)) = k1_relat_1(sK1) ),
% 2.71/0.96      inference(global_propositional_subsumption,
% 2.71/0.96                [status(thm)],
% 2.71/0.96                [c_1664,c_26]) ).
% 2.71/0.96  
% 2.71/0.96  cnf(c_1797,plain,
% 2.71/0.96      ( k1_relat_1(k5_relat_1(sK1,X0)) = k1_relat_1(sK1)
% 2.71/0.96      | r1_tarski(k1_relat_1(sK0),k1_relat_1(X0)) != iProver_top
% 2.71/0.96      | v1_relat_1(X0) != iProver_top ),
% 2.71/0.96      inference(renaming,[status(thm)],[c_1796]) ).
% 2.71/0.96  
% 2.71/0.96  cnf(c_1805,plain,
% 2.71/0.96      ( k1_relat_1(k5_relat_1(sK1,sK0)) = k1_relat_1(sK1)
% 2.71/0.96      | v1_relat_1(sK0) != iProver_top ),
% 2.71/0.96      inference(superposition,[status(thm)],[c_675,c_1797]) ).
% 2.71/0.96  
% 2.71/0.96  cnf(c_17,negated_conjecture,
% 2.71/0.96      ( k5_relat_1(sK1,sK0) = k6_relat_1(k2_relat_1(sK0)) ),
% 2.71/0.96      inference(cnf_transformation,[],[f53]) ).
% 2.71/0.96  
% 2.71/0.96  cnf(c_1822,plain,
% 2.71/0.96      ( k1_relat_1(k6_relat_1(k2_relat_1(sK0))) = k1_relat_1(sK1)
% 2.71/0.96      | v1_relat_1(sK0) != iProver_top ),
% 2.71/0.96      inference(light_normalisation,[status(thm)],[c_1805,c_17]) ).
% 2.71/0.96  
% 2.71/0.96  cnf(c_5,plain,
% 2.71/0.96      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 2.71/0.96      inference(cnf_transformation,[],[f35]) ).
% 2.71/0.96  
% 2.71/0.96  cnf(c_1823,plain,
% 2.71/0.96      ( k2_relat_1(sK0) = k1_relat_1(sK1)
% 2.71/0.96      | v1_relat_1(sK0) != iProver_top ),
% 2.71/0.96      inference(demodulation,[status(thm)],[c_1822,c_5]) ).
% 2.71/0.96  
% 2.71/0.96  cnf(c_23,negated_conjecture,
% 2.71/0.96      ( v1_relat_1(sK0) ),
% 2.71/0.96      inference(cnf_transformation,[],[f47]) ).
% 2.71/0.96  
% 2.71/0.96  cnf(c_24,plain,
% 2.71/0.96      ( v1_relat_1(sK0) = iProver_top ),
% 2.71/0.96      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.71/0.96  
% 2.71/0.96  cnf(c_1832,plain,
% 2.71/0.96      ( k2_relat_1(sK0) = k1_relat_1(sK1) ),
% 2.71/0.96      inference(global_propositional_subsumption,
% 2.71/0.96                [status(thm)],
% 2.71/0.96                [c_1823,c_24]) ).
% 2.71/0.96  
% 2.71/0.96  cnf(c_15,plain,
% 2.71/0.96      ( ~ v1_funct_1(X0)
% 2.71/0.96      | ~ v1_funct_1(X1)
% 2.71/0.96      | ~ v2_funct_1(X1)
% 2.71/0.96      | ~ v1_relat_1(X0)
% 2.71/0.96      | ~ v1_relat_1(X1)
% 2.71/0.96      | k5_relat_1(X1,X0) != k6_relat_1(k1_relat_1(X1))
% 2.71/0.96      | k2_funct_1(X1) = X0
% 2.71/0.96      | k2_relat_1(X1) != k1_relat_1(X0) ),
% 2.71/0.96      inference(cnf_transformation,[],[f46]) ).
% 2.71/0.96  
% 2.71/0.96  cnf(c_10,plain,
% 2.71/0.96      ( ~ v1_funct_1(X0)
% 2.71/0.96      | ~ v1_funct_1(X1)
% 2.71/0.96      | v2_funct_1(X1)
% 2.71/0.96      | ~ v1_relat_1(X0)
% 2.71/0.96      | ~ v1_relat_1(X1)
% 2.71/0.96      | k5_relat_1(X1,X0) != k6_relat_1(k1_relat_1(X1)) ),
% 2.71/0.96      inference(cnf_transformation,[],[f41]) ).
% 2.71/0.96  
% 2.71/0.96  cnf(c_109,plain,
% 2.71/0.96      ( ~ v1_funct_1(X1)
% 2.71/0.96      | ~ v1_funct_1(X0)
% 2.71/0.96      | ~ v1_relat_1(X0)
% 2.71/0.96      | ~ v1_relat_1(X1)
% 2.71/0.96      | k5_relat_1(X1,X0) != k6_relat_1(k1_relat_1(X1))
% 2.71/0.96      | k2_funct_1(X1) = X0
% 2.71/0.96      | k2_relat_1(X1) != k1_relat_1(X0) ),
% 2.71/0.96      inference(global_propositional_subsumption,
% 2.71/0.96                [status(thm)],
% 2.71/0.96                [c_15,c_10]) ).
% 2.71/0.96  
% 2.71/0.96  cnf(c_110,plain,
% 2.71/0.96      ( ~ v1_funct_1(X0)
% 2.71/0.96      | ~ v1_funct_1(X1)
% 2.71/0.96      | ~ v1_relat_1(X0)
% 2.71/0.96      | ~ v1_relat_1(X1)
% 2.71/0.96      | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
% 2.71/0.96      | k2_funct_1(X0) = X1
% 2.71/0.96      | k2_relat_1(X0) != k1_relat_1(X1) ),
% 2.71/0.96      inference(renaming,[status(thm)],[c_109]) ).
% 2.71/0.96  
% 2.71/0.96  cnf(c_659,plain,
% 2.71/0.96      ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
% 2.71/0.96      | k2_funct_1(X0) = X1
% 2.71/0.96      | k2_relat_1(X0) != k1_relat_1(X1)
% 2.71/0.96      | v1_funct_1(X0) != iProver_top
% 2.71/0.96      | v1_funct_1(X1) != iProver_top
% 2.71/0.96      | v1_relat_1(X0) != iProver_top
% 2.71/0.96      | v1_relat_1(X1) != iProver_top ),
% 2.71/0.96      inference(predicate_to_equality,[status(thm)],[c_110]) ).
% 2.71/0.96  
% 2.71/0.96  cnf(c_1011,plain,
% 2.71/0.96      ( k2_funct_1(sK1) = sK0
% 2.71/0.96      | k6_relat_1(k1_relat_1(sK1)) != k6_relat_1(k2_relat_1(sK0))
% 2.71/0.96      | k2_relat_1(sK1) != k1_relat_1(sK0)
% 2.71/0.96      | v1_funct_1(sK1) != iProver_top
% 2.71/0.96      | v1_funct_1(sK0) != iProver_top
% 2.71/0.96      | v1_relat_1(sK1) != iProver_top
% 2.71/0.96      | v1_relat_1(sK0) != iProver_top ),
% 2.71/0.96      inference(superposition,[status(thm)],[c_17,c_659]) ).
% 2.71/0.96  
% 2.71/0.96  cnf(c_1012,plain,
% 2.71/0.96      ( k2_funct_1(sK1) = sK0
% 2.71/0.96      | k6_relat_1(k1_relat_1(sK1)) != k6_relat_1(k2_relat_1(sK0))
% 2.71/0.96      | k1_relat_1(sK0) != k1_relat_1(sK0)
% 2.71/0.96      | v1_funct_1(sK1) != iProver_top
% 2.71/0.96      | v1_funct_1(sK0) != iProver_top
% 2.71/0.96      | v1_relat_1(sK1) != iProver_top
% 2.71/0.96      | v1_relat_1(sK0) != iProver_top ),
% 2.71/0.96      inference(light_normalisation,[status(thm)],[c_1011,c_18]) ).
% 2.71/0.96  
% 2.71/0.96  cnf(c_1013,plain,
% 2.71/0.96      ( k2_funct_1(sK1) = sK0
% 2.71/0.96      | k6_relat_1(k1_relat_1(sK1)) != k6_relat_1(k2_relat_1(sK0))
% 2.71/0.96      | v1_funct_1(sK1) != iProver_top
% 2.71/0.96      | v1_funct_1(sK0) != iProver_top
% 2.71/0.96      | v1_relat_1(sK1) != iProver_top
% 2.71/0.96      | v1_relat_1(sK0) != iProver_top ),
% 2.71/0.96      inference(equality_resolution_simp,[status(thm)],[c_1012]) ).
% 2.71/0.97  
% 2.71/0.97  cnf(c_22,negated_conjecture,
% 2.71/0.97      ( v1_funct_1(sK0) ),
% 2.71/0.97      inference(cnf_transformation,[],[f48]) ).
% 2.71/0.97  
% 2.71/0.97  cnf(c_20,negated_conjecture,
% 2.71/0.97      ( v1_funct_1(sK1) ),
% 2.71/0.97      inference(cnf_transformation,[],[f50]) ).
% 2.71/0.97  
% 2.71/0.97  cnf(c_1014,plain,
% 2.71/0.97      ( ~ v1_funct_1(sK1)
% 2.71/0.97      | ~ v1_funct_1(sK0)
% 2.71/0.97      | ~ v1_relat_1(sK1)
% 2.71/0.97      | ~ v1_relat_1(sK0)
% 2.71/0.97      | k2_funct_1(sK1) = sK0
% 2.71/0.97      | k6_relat_1(k1_relat_1(sK1)) != k6_relat_1(k2_relat_1(sK0)) ),
% 2.71/0.97      inference(predicate_to_equality_rev,[status(thm)],[c_1013]) ).
% 2.71/0.97  
% 2.71/0.97  cnf(c_1160,plain,
% 2.71/0.97      ( k2_funct_1(sK1) = sK0
% 2.71/0.97      | k6_relat_1(k1_relat_1(sK1)) != k6_relat_1(k2_relat_1(sK0)) ),
% 2.71/0.97      inference(global_propositional_subsumption,
% 2.71/0.97                [status(thm)],
% 2.71/0.97                [c_1013,c_23,c_22,c_21,c_20,c_1014]) ).
% 2.71/0.97  
% 2.71/0.97  cnf(c_1836,plain,
% 2.71/0.97      ( k2_funct_1(sK1) = sK0
% 2.71/0.97      | k6_relat_1(k1_relat_1(sK1)) != k6_relat_1(k1_relat_1(sK1)) ),
% 2.71/0.97      inference(demodulation,[status(thm)],[c_1832,c_1160]) ).
% 2.71/0.97  
% 2.71/0.97  cnf(c_1840,plain,
% 2.71/0.97      ( k2_funct_1(sK1) = sK0 ),
% 2.71/0.97      inference(equality_resolution_simp,[status(thm)],[c_1836]) ).
% 2.71/0.97  
% 2.71/0.97  cnf(c_9,plain,
% 2.71/0.97      ( ~ v1_funct_1(X0)
% 2.71/0.97      | ~ v1_funct_1(X1)
% 2.71/0.97      | v2_funct_1(X0)
% 2.71/0.97      | ~ v2_funct_1(k5_relat_1(X0,X1))
% 2.71/0.97      | ~ v1_relat_1(X0)
% 2.71/0.97      | ~ v1_relat_1(X1)
% 2.71/0.97      | k2_relat_1(X0) != k1_relat_1(X1) ),
% 2.71/0.97      inference(cnf_transformation,[],[f39]) ).
% 2.71/0.97  
% 2.71/0.97  cnf(c_670,plain,
% 2.71/0.97      ( k2_relat_1(X0) != k1_relat_1(X1)
% 2.71/0.97      | v1_funct_1(X0) != iProver_top
% 2.71/0.97      | v1_funct_1(X1) != iProver_top
% 2.71/0.97      | v2_funct_1(X0) = iProver_top
% 2.71/0.97      | v2_funct_1(k5_relat_1(X0,X1)) != iProver_top
% 2.71/0.97      | v1_relat_1(X0) != iProver_top
% 2.71/0.97      | v1_relat_1(X1) != iProver_top ),
% 2.71/0.97      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.71/0.97  
% 2.71/0.97  cnf(c_2765,plain,
% 2.71/0.97      ( k1_relat_1(X0) != k1_relat_1(sK0)
% 2.71/0.97      | v1_funct_1(X0) != iProver_top
% 2.71/0.97      | v1_funct_1(sK1) != iProver_top
% 2.71/0.97      | v2_funct_1(k5_relat_1(sK1,X0)) != iProver_top
% 2.71/0.97      | v2_funct_1(sK1) = iProver_top
% 2.71/0.97      | v1_relat_1(X0) != iProver_top
% 2.71/0.97      | v1_relat_1(sK1) != iProver_top ),
% 2.71/0.97      inference(superposition,[status(thm)],[c_18,c_670]) ).
% 2.71/0.97  
% 2.71/0.97  cnf(c_25,plain,
% 2.71/0.97      ( v1_funct_1(sK0) = iProver_top ),
% 2.71/0.97      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.71/0.97  
% 2.71/0.97  cnf(c_27,plain,
% 2.71/0.97      ( v1_funct_1(sK1) = iProver_top ),
% 2.71/0.97      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.71/0.97  
% 2.71/0.97  cnf(c_334,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.71/0.97  
% 2.71/0.97  cnf(c_892,plain,
% 2.71/0.97      ( k5_relat_1(sK1,sK0) != X0
% 2.71/0.97      | k5_relat_1(sK1,sK0) = k6_relat_1(k1_relat_1(sK1))
% 2.71/0.97      | k6_relat_1(k1_relat_1(sK1)) != X0 ),
% 2.71/0.97      inference(instantiation,[status(thm)],[c_334]) ).
% 2.71/0.97  
% 2.71/0.97  cnf(c_984,plain,
% 2.71/0.97      ( k5_relat_1(sK1,sK0) != k5_relat_1(sK1,sK0)
% 2.71/0.97      | k5_relat_1(sK1,sK0) = k6_relat_1(k1_relat_1(sK1))
% 2.71/0.97      | k6_relat_1(k1_relat_1(sK1)) != k5_relat_1(sK1,sK0) ),
% 2.71/0.97      inference(instantiation,[status(thm)],[c_892]) ).
% 2.71/0.97  
% 2.71/0.97  cnf(c_333,plain,( X0 = X0 ),theory(equality) ).
% 2.71/0.97  
% 2.71/0.97  cnf(c_985,plain,
% 2.71/0.97      ( k5_relat_1(sK1,sK0) = k5_relat_1(sK1,sK0) ),
% 2.71/0.97      inference(instantiation,[status(thm)],[c_333]) ).
% 2.71/0.97  
% 2.71/0.97  cnf(c_1637,plain,
% 2.71/0.97      ( ~ v1_funct_1(X0)
% 2.71/0.97      | ~ v1_funct_1(sK1)
% 2.71/0.97      | v2_funct_1(sK1)
% 2.71/0.97      | ~ v1_relat_1(X0)
% 2.71/0.97      | ~ v1_relat_1(sK1)
% 2.71/0.97      | k5_relat_1(sK1,X0) != k6_relat_1(k1_relat_1(sK1)) ),
% 2.71/0.97      inference(instantiation,[status(thm)],[c_10]) ).
% 2.71/0.97  
% 2.71/0.97  cnf(c_1643,plain,
% 2.71/0.97      ( k5_relat_1(sK1,X0) != k6_relat_1(k1_relat_1(sK1))
% 2.71/0.97      | v1_funct_1(X0) != iProver_top
% 2.71/0.97      | v1_funct_1(sK1) != iProver_top
% 2.71/0.97      | v2_funct_1(sK1) = iProver_top
% 2.71/0.97      | v1_relat_1(X0) != iProver_top
% 2.71/0.97      | v1_relat_1(sK1) != iProver_top ),
% 2.71/0.97      inference(predicate_to_equality,[status(thm)],[c_1637]) ).
% 2.71/0.97  
% 2.71/0.97  cnf(c_1645,plain,
% 2.71/0.97      ( k5_relat_1(sK1,sK0) != k6_relat_1(k1_relat_1(sK1))
% 2.71/0.97      | v1_funct_1(sK1) != iProver_top
% 2.71/0.97      | v1_funct_1(sK0) != iProver_top
% 2.71/0.97      | v2_funct_1(sK1) = iProver_top
% 2.71/0.97      | v1_relat_1(sK1) != iProver_top
% 2.71/0.97      | v1_relat_1(sK0) != iProver_top ),
% 2.71/0.97      inference(instantiation,[status(thm)],[c_1643]) ).
% 2.71/0.97  
% 2.71/0.97  cnf(c_1837,plain,
% 2.71/0.97      ( k6_relat_1(k1_relat_1(sK1)) = k5_relat_1(sK1,sK0) ),
% 2.71/0.97      inference(demodulation,[status(thm)],[c_1832,c_17]) ).
% 2.71/0.97  
% 2.71/0.97  cnf(c_2987,plain,
% 2.71/0.97      ( v2_funct_1(sK1) = iProver_top ),
% 2.71/0.97      inference(global_propositional_subsumption,
% 2.71/0.97                [status(thm)],
% 2.71/0.97                [c_2765,c_24,c_25,c_26,c_27,c_984,c_985,c_1645,c_1837]) ).
% 2.71/0.97  
% 2.71/0.97  cnf(c_663,plain,
% 2.71/0.97      ( v1_funct_1(sK1) = iProver_top ),
% 2.71/0.97      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.71/0.97  
% 2.71/0.97  cnf(c_13,plain,
% 2.71/0.97      ( ~ v1_funct_1(X0)
% 2.71/0.97      | ~ v2_funct_1(X0)
% 2.71/0.97      | ~ v1_relat_1(X0)
% 2.71/0.97      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) ),
% 2.71/0.97      inference(cnf_transformation,[],[f45]) ).
% 2.71/0.97  
% 2.71/0.97  cnf(c_666,plain,
% 2.71/0.97      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
% 2.71/0.97      | v1_funct_1(X0) != iProver_top
% 2.71/0.97      | v2_funct_1(X0) != iProver_top
% 2.71/0.97      | v1_relat_1(X0) != iProver_top ),
% 2.71/0.97      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.71/0.97  
% 2.71/0.97  cnf(c_1544,plain,
% 2.71/0.97      ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_relat_1(k2_relat_1(sK1))
% 2.71/0.97      | v2_funct_1(sK1) != iProver_top
% 2.71/0.97      | v1_relat_1(sK1) != iProver_top ),
% 2.71/0.97      inference(superposition,[status(thm)],[c_663,c_666]) ).
% 2.71/0.97  
% 2.71/0.97  cnf(c_1555,plain,
% 2.71/0.97      ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_relat_1(k1_relat_1(sK0))
% 2.71/0.97      | v2_funct_1(sK1) != iProver_top
% 2.71/0.97      | v1_relat_1(sK1) != iProver_top ),
% 2.71/0.97      inference(light_normalisation,[status(thm)],[c_1544,c_18]) ).
% 2.71/0.97  
% 2.71/0.97  cnf(c_1652,plain,
% 2.71/0.97      ( v2_funct_1(sK1) != iProver_top
% 2.71/0.97      | k5_relat_1(k2_funct_1(sK1),sK1) = k6_relat_1(k1_relat_1(sK0)) ),
% 2.71/0.97      inference(global_propositional_subsumption,
% 2.71/0.97                [status(thm)],
% 2.71/0.97                [c_1555,c_26]) ).
% 2.71/0.97  
% 2.71/0.97  cnf(c_1653,plain,
% 2.71/0.97      ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_relat_1(k1_relat_1(sK0))
% 2.71/0.97      | v2_funct_1(sK1) != iProver_top ),
% 2.71/0.97      inference(renaming,[status(thm)],[c_1652]) ).
% 2.71/0.97  
% 2.71/0.97  cnf(c_2992,plain,
% 2.71/0.97      ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_relat_1(k1_relat_1(sK0)) ),
% 2.71/0.97      inference(superposition,[status(thm)],[c_2987,c_1653]) ).
% 2.71/0.97  
% 2.71/0.97  cnf(c_6387,plain,
% 2.71/0.97      ( k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,sK1) ),
% 2.71/0.97      inference(demodulation,[status(thm)],[c_1840,c_2992]) ).
% 2.71/0.97  
% 2.71/0.97  cnf(c_6997,plain,
% 2.71/0.97      ( k2_funct_1(sK0) = sK1
% 2.71/0.97      | k2_relat_1(sK0) != k1_relat_1(sK1)
% 2.71/0.97      | v1_funct_1(sK1) != iProver_top
% 2.71/0.97      | v1_funct_1(sK0) != iProver_top
% 2.71/0.97      | v1_relat_1(sK1) != iProver_top
% 2.71/0.97      | v1_relat_1(sK0) != iProver_top ),
% 2.71/0.97      inference(superposition,[status(thm)],[c_6387,c_659]) ).
% 2.71/0.97  
% 2.71/0.97  cnf(c_7004,plain,
% 2.71/0.97      ( k2_funct_1(sK0) = sK1
% 2.71/0.97      | k1_relat_1(sK1) != k1_relat_1(sK1)
% 2.71/0.97      | v1_funct_1(sK1) != iProver_top
% 2.71/0.97      | v1_funct_1(sK0) != iProver_top
% 2.71/0.97      | v1_relat_1(sK1) != iProver_top
% 2.71/0.97      | v1_relat_1(sK0) != iProver_top ),
% 2.71/0.97      inference(light_normalisation,[status(thm)],[c_6997,c_1832]) ).
% 2.71/0.97  
% 2.71/0.97  cnf(c_7005,plain,
% 2.71/0.97      ( k2_funct_1(sK0) = sK1
% 2.71/0.97      | v1_funct_1(sK1) != iProver_top
% 2.71/0.97      | v1_funct_1(sK0) != iProver_top
% 2.71/0.97      | v1_relat_1(sK1) != iProver_top
% 2.71/0.97      | v1_relat_1(sK0) != iProver_top ),
% 2.71/0.97      inference(equality_resolution_simp,[status(thm)],[c_7004]) ).
% 2.71/0.97  
% 2.71/0.97  cnf(c_16,negated_conjecture,
% 2.71/0.97      ( k2_funct_1(sK0) != sK1 ),
% 2.71/0.97      inference(cnf_transformation,[],[f54]) ).
% 2.71/0.97  
% 2.71/0.97  cnf(contradiction,plain,
% 2.71/0.97      ( $false ),
% 2.71/0.97      inference(minisat,[status(thm)],[c_7005,c_16,c_27,c_26,c_25,c_24]) ).
% 2.71/0.97  
% 2.71/0.97  
% 2.71/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 2.71/0.97  
% 2.71/0.97  ------                               Statistics
% 2.71/0.97  
% 2.71/0.97  ------ General
% 2.71/0.97  
% 2.71/0.97  abstr_ref_over_cycles:                  0
% 2.71/0.97  abstr_ref_under_cycles:                 0
% 2.71/0.97  gc_basic_clause_elim:                   0
% 2.71/0.97  forced_gc_time:                         0
% 2.71/0.97  parsing_time:                           0.008
% 2.71/0.97  unif_index_cands_time:                  0.
% 2.71/0.97  unif_index_add_time:                    0.
% 2.71/0.97  orderings_time:                         0.
% 2.71/0.97  out_proof_time:                         0.01
% 2.71/0.97  total_time:                             0.253
% 2.71/0.97  num_of_symbols:                         42
% 2.71/0.97  num_of_terms:                           5695
% 2.71/0.97  
% 2.71/0.97  ------ Preprocessing
% 2.71/0.97  
% 2.71/0.97  num_of_splits:                          0
% 2.71/0.97  num_of_split_atoms:                     0
% 2.71/0.97  num_of_reused_defs:                     0
% 2.71/0.97  num_eq_ax_congr_red:                    0
% 2.71/0.97  num_of_sem_filtered_clauses:            1
% 2.71/0.97  num_of_subtypes:                        0
% 2.71/0.97  monotx_restored_types:                  0
% 2.71/0.97  sat_num_of_epr_types:                   0
% 2.71/0.97  sat_num_of_non_cyclic_types:            0
% 2.71/0.97  sat_guarded_non_collapsed_types:        0
% 2.71/0.97  num_pure_diseq_elim:                    0
% 2.71/0.97  simp_replaced_by:                       0
% 2.71/0.97  res_preprocessed:                       115
% 2.71/0.97  prep_upred:                             0
% 2.71/0.97  prep_unflattend:                        0
% 2.71/0.97  smt_new_axioms:                         0
% 2.71/0.97  pred_elim_cands:                        4
% 2.71/0.97  pred_elim:                              0
% 2.71/0.97  pred_elim_cl:                           0
% 2.71/0.97  pred_elim_cycles:                       2
% 2.71/0.97  merged_defs:                            0
% 2.71/0.97  merged_defs_ncl:                        0
% 2.71/0.97  bin_hyper_res:                          0
% 2.71/0.97  prep_cycles:                            4
% 2.71/0.97  pred_elim_time:                         0.
% 2.71/0.97  splitting_time:                         0.
% 2.71/0.97  sem_filter_time:                        0.
% 2.71/0.97  monotx_time:                            0.
% 2.71/0.97  subtype_inf_time:                       0.
% 2.71/0.97  
% 2.71/0.97  ------ Problem properties
% 2.71/0.97  
% 2.71/0.97  clauses:                                23
% 2.71/0.97  conjectures:                            8
% 2.71/0.97  epr:                                    7
% 2.71/0.97  horn:                                   23
% 2.71/0.97  ground:                                 8
% 2.71/0.97  unary:                                  13
% 2.71/0.97  binary:                                 0
% 2.71/0.97  lits:                                   63
% 2.71/0.97  lits_eq:                                17
% 2.71/0.97  fd_pure:                                0
% 2.71/0.97  fd_pseudo:                              0
% 2.71/0.97  fd_cond:                                0
% 2.71/0.97  fd_pseudo_cond:                         2
% 2.71/0.97  ac_symbols:                             0
% 2.71/0.97  
% 2.71/0.97  ------ Propositional Solver
% 2.71/0.97  
% 2.71/0.97  prop_solver_calls:                      29
% 2.71/0.97  prop_fast_solver_calls:                 940
% 2.71/0.97  smt_solver_calls:                       0
% 2.71/0.97  smt_fast_solver_calls:                  0
% 2.71/0.97  prop_num_of_clauses:                    2460
% 2.71/0.97  prop_preprocess_simplified:             6850
% 2.71/0.97  prop_fo_subsumed:                       45
% 2.71/0.97  prop_solver_time:                       0.
% 2.71/0.97  smt_solver_time:                        0.
% 2.71/0.97  smt_fast_solver_time:                   0.
% 2.71/0.97  prop_fast_solver_time:                  0.
% 2.71/0.97  prop_unsat_core_time:                   0.
% 2.71/0.97  
% 2.71/0.97  ------ QBF
% 2.71/0.97  
% 2.71/0.97  qbf_q_res:                              0
% 2.71/0.97  qbf_num_tautologies:                    0
% 2.71/0.97  qbf_prep_cycles:                        0
% 2.71/0.97  
% 2.71/0.97  ------ BMC1
% 2.71/0.97  
% 2.71/0.97  bmc1_current_bound:                     -1
% 2.71/0.97  bmc1_last_solved_bound:                 -1
% 2.71/0.97  bmc1_unsat_core_size:                   -1
% 2.71/0.97  bmc1_unsat_core_parents_size:           -1
% 2.71/0.97  bmc1_merge_next_fun:                    0
% 2.71/0.97  bmc1_unsat_core_clauses_time:           0.
% 2.71/0.97  
% 2.71/0.97  ------ Instantiation
% 2.71/0.97  
% 2.71/0.97  inst_num_of_clauses:                    905
% 2.71/0.97  inst_num_in_passive:                    269
% 2.71/0.97  inst_num_in_active:                     374
% 2.71/0.97  inst_num_in_unprocessed:                263
% 2.71/0.97  inst_num_of_loops:                      390
% 2.71/0.97  inst_num_of_learning_restarts:          0
% 2.71/0.97  inst_num_moves_active_passive:          11
% 2.71/0.97  inst_lit_activity:                      0
% 2.71/0.97  inst_lit_activity_moves:                0
% 2.71/0.97  inst_num_tautologies:                   0
% 2.71/0.97  inst_num_prop_implied:                  0
% 2.71/0.97  inst_num_existing_simplified:           0
% 2.71/0.97  inst_num_eq_res_simplified:             0
% 2.71/0.97  inst_num_child_elim:                    0
% 2.71/0.97  inst_num_of_dismatching_blockings:      595
% 2.71/0.97  inst_num_of_non_proper_insts:           1128
% 2.71/0.97  inst_num_of_duplicates:                 0
% 2.71/0.97  inst_inst_num_from_inst_to_res:         0
% 2.71/0.97  inst_dismatching_checking_time:         0.
% 2.71/0.97  
% 2.71/0.97  ------ Resolution
% 2.71/0.97  
% 2.71/0.97  res_num_of_clauses:                     0
% 2.71/0.97  res_num_in_passive:                     0
% 2.71/0.97  res_num_in_active:                      0
% 2.71/0.97  res_num_of_loops:                       119
% 2.71/0.97  res_forward_subset_subsumed:            94
% 2.71/0.97  res_backward_subset_subsumed:           6
% 2.71/0.97  res_forward_subsumed:                   0
% 2.71/0.97  res_backward_subsumed:                  0
% 2.71/0.97  res_forward_subsumption_resolution:     0
% 2.71/0.97  res_backward_subsumption_resolution:    0
% 2.71/0.97  res_clause_to_clause_subsumption:       319
% 2.71/0.97  res_orphan_elimination:                 0
% 2.71/0.97  res_tautology_del:                      88
% 2.71/0.97  res_num_eq_res_simplified:              0
% 2.71/0.97  res_num_sel_changes:                    0
% 2.71/0.97  res_moves_from_active_to_pass:          0
% 2.71/0.97  
% 2.71/0.97  ------ Superposition
% 2.71/0.97  
% 2.71/0.97  sup_time_total:                         0.
% 2.71/0.97  sup_time_generating:                    0.
% 2.71/0.97  sup_time_sim_full:                      0.
% 2.71/0.97  sup_time_sim_immed:                     0.
% 2.71/0.97  
% 2.71/0.97  sup_num_of_clauses:                     129
% 2.71/0.97  sup_num_in_active:                      62
% 2.71/0.97  sup_num_in_passive:                     67
% 2.71/0.97  sup_num_of_loops:                       76
% 2.71/0.97  sup_fw_superposition:                   78
% 2.71/0.97  sup_bw_superposition:                   61
% 2.71/0.97  sup_immediate_simplified:               37
% 2.71/0.97  sup_given_eliminated:                   0
% 2.71/0.97  comparisons_done:                       0
% 2.71/0.97  comparisons_avoided:                    0
% 2.71/0.97  
% 2.71/0.97  ------ Simplifications
% 2.71/0.97  
% 2.71/0.97  
% 2.71/0.97  sim_fw_subset_subsumed:                 11
% 2.71/0.97  sim_bw_subset_subsumed:                 2
% 2.71/0.97  sim_fw_subsumed:                        8
% 2.71/0.97  sim_bw_subsumed:                        0
% 2.71/0.97  sim_fw_subsumption_res:                 4
% 2.71/0.97  sim_bw_subsumption_res:                 0
% 2.71/0.97  sim_tautology_del:                      0
% 2.71/0.97  sim_eq_tautology_del:                   11
% 2.71/0.97  sim_eq_res_simp:                        6
% 2.71/0.97  sim_fw_demodulated:                     3
% 2.71/0.97  sim_bw_demodulated:                     13
% 2.71/0.97  sim_light_normalised:                   25
% 2.71/0.97  sim_joinable_taut:                      0
% 2.71/0.97  sim_joinable_simp:                      0
% 2.71/0.97  sim_ac_normalised:                      0
% 2.71/0.97  sim_smt_subsumption:                    0
% 2.71/0.97  
%------------------------------------------------------------------------------
