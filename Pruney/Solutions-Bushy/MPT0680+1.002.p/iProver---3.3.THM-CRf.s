%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0680+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:53 EST 2020

% Result     : Theorem 23.73s
% Output     : CNFRefutation 23.73s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 527 expanded)
%              Number of clauses        :   48 ( 128 expanded)
%              Number of leaves         :    8 ( 113 expanded)
%              Depth                    :   20
%              Number of atoms          :  248 (2169 expanded)
%              Number of equality atoms :   96 ( 643 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f27,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X1,X2] :
              ( X1 = X2
              | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
              | ~ r2_hidden(X2,k1_relat_1(X0))
              | ~ r2_hidden(X1,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f28,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK0(X0) != sK1(X0)
        & k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0))
        & r2_hidden(sK1(X0),k1_relat_1(X0))
        & r2_hidden(sK0(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ( sK0(X0) != sK1(X0)
            & k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0))
            & r2_hidden(sK1(X0),k1_relat_1(X0))
            & r2_hidden(sK0(X0),k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f29])).

fof(f39,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | r2_hidden(sK0(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ! [X1,X2] : k9_relat_1(X0,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2))
       => v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( ! [X1,X2] : k9_relat_1(X0,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2))
         => v2_funct_1(X0) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f25,plain,(
    ? [X0] :
      ( ~ v2_funct_1(X0)
      & ! [X1,X2] : k9_relat_1(X0,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2))
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f26,plain,(
    ? [X0] :
      ( ~ v2_funct_1(X0)
      & ! [X1,X2] : k9_relat_1(X0,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2))
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f34,plain,
    ( ? [X0] :
        ( ~ v2_funct_1(X0)
        & ! [X1,X2] : k9_relat_1(X0,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2))
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ~ v2_funct_1(sK3)
      & ! [X2,X1] : k9_relat_1(sK3,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(sK3,X1),k9_relat_1(sK3,X2))
      & v1_funct_1(sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ~ v2_funct_1(sK3)
    & ! [X1,X2] : k9_relat_1(sK3,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(sK3,X1),k9_relat_1(sK3,X2))
    & v1_funct_1(sK3)
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f34])).

fof(f54,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f53,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f56,plain,(
    ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f40,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | r2_hidden(sK1(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f41,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f55,plain,(
    ! [X2,X1] : k9_relat_1(sK3,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(sK3,X1),k9_relat_1(sK3,X2)) ),
    inference(cnf_transformation,[],[f35])).

fof(f7,axiom,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f58,plain,(
    ! [X2,X1] : k9_relat_1(sK3,k4_xboole_0(X1,X2)) = k4_xboole_0(k9_relat_1(sK3,X1),k9_relat_1(sK3,X2)) ),
    inference(definition_unfolding,[],[f55,f46,f46])).

fof(f49,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f59,plain,(
    ! [X1] : k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f49])).

fof(f42,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | sK0(X0) != sK1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_12,plain,
    ( X0 = X1
    | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_5,plain,
    ( r2_hidden(sK0(X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_18,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_331,plain,
    ( r2_hidden(sK0(X0),k1_relat_1(X0))
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_18])).

cnf(c_332,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3))
    | v2_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_331])).

cnf(c_19,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_16,negated_conjecture,
    ( ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_49,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | v2_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_334,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_332,c_19,c_18,c_16,c_49])).

cnf(c_661,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_334])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_311,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_18])).

cnf(c_312,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | k1_tarski(k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_311])).

cnf(c_316,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | k1_tarski(k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_312,c_19])).

cnf(c_662,plain,
    ( k1_tarski(k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_316])).

cnf(c_940,plain,
    ( k1_tarski(k1_funct_1(sK3,sK0(sK3))) = k11_relat_1(sK3,sK0(sK3)) ),
    inference(superposition,[status(thm)],[c_661,c_662])).

cnf(c_4,plain,
    ( r2_hidden(sK1(X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_342,plain,
    ( r2_hidden(sK1(X0),k1_relat_1(X0))
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_18])).

cnf(c_343,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3))
    | v2_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_342])).

cnf(c_52,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | v2_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_345,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_343,c_19,c_18,c_16,c_52])).

cnf(c_660,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_345])).

cnf(c_941,plain,
    ( k1_tarski(k1_funct_1(sK3,sK1(sK3))) = k11_relat_1(sK3,sK1(sK3)) ),
    inference(superposition,[status(thm)],[c_660,c_662])).

cnf(c_3,plain,
    ( ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_353,plain,
    ( v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_18])).

cnf(c_354,plain,
    ( v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3)) ),
    inference(unflattening,[status(thm)],[c_353])).

cnf(c_356,plain,
    ( k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_354,c_19,c_16])).

cnf(c_942,plain,
    ( k1_tarski(k1_funct_1(sK3,sK0(sK3))) = k11_relat_1(sK3,sK1(sK3)) ),
    inference(light_normalisation,[status(thm)],[c_941,c_356])).

cnf(c_943,plain,
    ( k11_relat_1(sK3,sK1(sK3)) = k11_relat_1(sK3,sK0(sK3)) ),
    inference(demodulation,[status(thm)],[c_940,c_942])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_tarski(X1)) = k11_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_378,plain,
    ( k9_relat_1(X0,k1_tarski(X1)) = k11_relat_1(X0,X1)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_19])).

cnf(c_379,plain,
    ( k9_relat_1(sK3,k1_tarski(X0)) = k11_relat_1(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_378])).

cnf(c_17,negated_conjecture,
    ( k9_relat_1(sK3,k4_xboole_0(X0,X1)) = k4_xboole_0(k9_relat_1(sK3,X0),k9_relat_1(sK3,X1)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_760,plain,
    ( k4_xboole_0(k9_relat_1(sK3,X0),k11_relat_1(sK3,X1)) = k9_relat_1(sK3,k4_xboole_0(X0,k1_tarski(X1))) ),
    inference(superposition,[status(thm)],[c_379,c_17])).

cnf(c_1058,plain,
    ( k4_xboole_0(k9_relat_1(sK3,X0),k11_relat_1(sK3,sK0(sK3))) = k9_relat_1(sK3,k4_xboole_0(X0,k1_tarski(sK1(sK3)))) ),
    inference(superposition,[status(thm)],[c_943,c_760])).

cnf(c_1059,plain,
    ( k9_relat_1(sK3,k4_xboole_0(X0,k1_tarski(sK0(sK3)))) = k9_relat_1(sK3,k4_xboole_0(X0,k1_tarski(sK1(sK3)))) ),
    inference(demodulation,[status(thm)],[c_1058,c_760])).

cnf(c_1125,plain,
    ( k9_relat_1(sK3,k4_xboole_0(k1_tarski(X0),k1_tarski(sK0(sK3)))) = k9_relat_1(sK3,k1_tarski(X0))
    | sK1(sK3) = X0 ),
    inference(superposition,[status(thm)],[c_12,c_1059])).

cnf(c_1134,plain,
    ( k9_relat_1(sK3,k4_xboole_0(k1_tarski(X0),k1_tarski(sK0(sK3)))) = k11_relat_1(sK3,X0)
    | sK1(sK3) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1125,c_379])).

cnf(c_13,plain,
    ( k4_xboole_0(k1_tarski(X0),k1_tarski(X0)) != k1_tarski(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2174,plain,
    ( k4_xboole_0(k11_relat_1(sK3,sK0(sK3)),k11_relat_1(sK3,sK0(sK3))) != k1_tarski(k1_funct_1(sK3,sK0(sK3))) ),
    inference(superposition,[status(thm)],[c_940,c_13])).

cnf(c_2181,plain,
    ( k4_xboole_0(k11_relat_1(sK3,sK0(sK3)),k11_relat_1(sK3,sK0(sK3))) != k11_relat_1(sK3,sK0(sK3)) ),
    inference(demodulation,[status(thm)],[c_2174,c_940])).

cnf(c_759,plain,
    ( k4_xboole_0(k11_relat_1(sK3,X0),k9_relat_1(sK3,X1)) = k9_relat_1(sK3,k4_xboole_0(k1_tarski(X0),X1)) ),
    inference(superposition,[status(thm)],[c_379,c_17])).

cnf(c_825,plain,
    ( k4_xboole_0(k11_relat_1(sK3,X0),k11_relat_1(sK3,X1)) = k9_relat_1(sK3,k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) ),
    inference(superposition,[status(thm)],[c_379,c_759])).

cnf(c_2182,plain,
    ( k9_relat_1(sK3,k4_xboole_0(k1_tarski(sK0(sK3)),k1_tarski(sK0(sK3)))) != k11_relat_1(sK3,sK0(sK3)) ),
    inference(demodulation,[status(thm)],[c_2181,c_825])).

cnf(c_63819,plain,
    ( sK1(sK3) = sK0(sK3) ),
    inference(superposition,[status(thm)],[c_1134,c_2182])).

cnf(c_2,plain,
    ( ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | sK1(X0) != sK0(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_58,plain,
    ( ~ v1_funct_1(sK3)
    | v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | sK1(sK3) != sK0(sK3) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_63819,c_58,c_16,c_18,c_19])).


%------------------------------------------------------------------------------
