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
% DateTime   : Thu Dec  3 11:49:54 EST 2020

% Result     : Theorem 2.43s
% Output     : CNFRefutation 2.43s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 275 expanded)
%              Number of clauses        :   42 ( 103 expanded)
%              Number of leaves         :    9 (  56 expanded)
%              Depth                    :   19
%              Number of atoms          :  225 ( 734 expanded)
%              Number of equality atoms :   96 ( 278 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
       => k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
         => k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)
      & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)
      & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f28,plain,
    ( ? [X0,X1,X2] :
        ( k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)
        & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k1_funct_1(sK2,sK0) != k1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2),sK0)
      & r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( k1_funct_1(sK2,sK0) != k1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2),sK0)
    & r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f28])).

fof(f48,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k5_relat_1(k6_relat_1(X0),X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k5_relat_1(k6_relat_1(X0),X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k5_relat_1(k6_relat_1(X0),X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0)) = k1_relat_1(k5_relat_1(k6_relat_1(X0),X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f47,f30])).

fof(f49,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f41,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f50,plain,(
    r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f59,plain,(
    r2_hidden(sK0,k4_xboole_0(k1_relat_1(sK2),k4_xboole_0(k1_relat_1(sK2),sK1))) ),
    inference(definition_unfolding,[],[f50,f30])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
              | ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              | ~ r2_hidden(X0,k1_relat_1(X2)) )
            & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
                & r2_hidden(X0,k1_relat_1(X2)) )
              | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
              | ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              | ~ r2_hidden(X0,k1_relat_1(X2)) )
            & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
                & r2_hidden(X0,k1_relat_1(X2)) )
              | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_funct_1(k6_relat_1(X1),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k6_relat_1(X1),X0) = X0
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k6_relat_1(X1),X0) = X0
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
           => k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0)
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0)
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f51,plain,(
    k1_funct_1(sK2,sK0) != k1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2),sK0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_14,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_356,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),X1)) = k1_relat_1(k5_relat_1(k6_relat_1(X1),X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_359,plain,
    ( k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),X1)) = k1_relat_1(k5_relat_1(k6_relat_1(X1),X0))
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_638,plain,
    ( k4_xboole_0(k1_relat_1(sK2),k4_xboole_0(k1_relat_1(sK2),X0)) = k1_relat_1(k5_relat_1(k6_relat_1(X0),sK2))
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_356,c_359])).

cnf(c_13,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_16,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_978,plain,
    ( k4_xboole_0(k1_relat_1(sK2),k4_xboole_0(k1_relat_1(sK2),X0)) = k1_relat_1(k5_relat_1(k6_relat_1(X0),sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_638,c_16])).

cnf(c_4,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_365,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_637,plain,
    ( k4_xboole_0(k1_relat_1(k6_relat_1(X0)),k4_xboole_0(k1_relat_1(k6_relat_1(X0)),X1)) = k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)))
    | v1_funct_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_365,c_359])).

cnf(c_2,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_645,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k4_xboole_0(X1,k4_xboole_0(X1,X0))
    | v1_funct_1(k6_relat_1(X1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_637,c_2])).

cnf(c_3,plain,
    ( v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_366,plain,
    ( v1_funct_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_750,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_645,c_366])).

cnf(c_988,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(k1_relat_1(sK2)))) = k1_relat_1(k5_relat_1(k6_relat_1(X0),sK2)) ),
    inference(superposition,[status(thm)],[c_978,c_750])).

cnf(c_12,negated_conjecture,
    ( r2_hidden(sK0,k4_xboole_0(k1_relat_1(sK2),k4_xboole_0(k1_relat_1(sK2),sK1))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_358,plain,
    ( r2_hidden(sK0,k4_xboole_0(k1_relat_1(sK2),k4_xboole_0(k1_relat_1(sK2),sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_753,plain,
    ( r2_hidden(sK0,k1_relat_1(k5_relat_1(k6_relat_1(sK1),k6_relat_1(k1_relat_1(sK2))))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_750,c_358])).

cnf(c_1055,plain,
    ( r2_hidden(sK0,k1_relat_1(k5_relat_1(k6_relat_1(sK1),sK2))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_988,c_753])).

cnf(c_7,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X1,X2)))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_362,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
    | r2_hidden(X0,k1_relat_1(k5_relat_1(X1,X2))) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1066,plain,
    ( r2_hidden(sK0,k1_relat_1(k6_relat_1(sK1))) = iProver_top
    | v1_relat_1(k6_relat_1(sK1)) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(k6_relat_1(sK1)) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1055,c_362])).

cnf(c_1073,plain,
    ( r2_hidden(sK0,sK1) = iProver_top
    | v1_relat_1(k6_relat_1(sK1)) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(k6_relat_1(sK1)) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1066,c_2])).

cnf(c_15,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1670,plain,
    ( v1_funct_1(k6_relat_1(sK1)) != iProver_top
    | r2_hidden(sK0,sK1) = iProver_top
    | v1_relat_1(k6_relat_1(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1073,c_15,c_16])).

cnf(c_1671,plain,
    ( r2_hidden(sK0,sK1) = iProver_top
    | v1_relat_1(k6_relat_1(sK1)) != iProver_top
    | v1_funct_1(k6_relat_1(sK1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_1670])).

cnf(c_1677,plain,
    ( r2_hidden(sK0,sK1) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1671,c_366,c_365])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_funct_1(k6_relat_1(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_360,plain,
    ( k1_funct_1(k6_relat_1(X0),X1) = X1
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1679,plain,
    ( k1_funct_1(k6_relat_1(sK1),sK0) = sK0 ),
    inference(superposition,[status(thm)],[c_1677,c_360])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X1,X2)))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_361,plain,
    ( k1_funct_1(k5_relat_1(X0,X1),X2) = k1_funct_1(X1,k1_funct_1(X0,X2))
    | r2_hidden(X2,k1_relat_1(k5_relat_1(X0,X1))) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1267,plain,
    ( k1_funct_1(sK2,k1_funct_1(k6_relat_1(sK1),sK0)) = k1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2),sK0)
    | v1_relat_1(k6_relat_1(sK1)) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(k6_relat_1(sK1)) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1055,c_361])).

cnf(c_2526,plain,
    ( v1_funct_1(k6_relat_1(sK1)) != iProver_top
    | k1_funct_1(sK2,k1_funct_1(k6_relat_1(sK1),sK0)) = k1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2),sK0)
    | v1_relat_1(k6_relat_1(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1267,c_15,c_16])).

cnf(c_2527,plain,
    ( k1_funct_1(sK2,k1_funct_1(k6_relat_1(sK1),sK0)) = k1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2),sK0)
    | v1_relat_1(k6_relat_1(sK1)) != iProver_top
    | v1_funct_1(k6_relat_1(sK1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2526])).

cnf(c_2533,plain,
    ( k1_funct_1(sK2,k1_funct_1(k6_relat_1(sK1),sK0)) = k1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2),sK0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2527,c_366,c_365])).

cnf(c_11,negated_conjecture,
    ( k1_funct_1(sK2,sK0) != k1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2),sK0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2534,plain,
    ( k1_funct_1(sK2,k1_funct_1(k6_relat_1(sK1),sK0)) != k1_funct_1(sK2,sK0) ),
    inference(demodulation,[status(thm)],[c_2533,c_11])).

cnf(c_5497,plain,
    ( k1_funct_1(sK2,sK0) != k1_funct_1(sK2,sK0) ),
    inference(demodulation,[status(thm)],[c_1679,c_2534])).

cnf(c_5504,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_5497])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:31:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 2.43/1.05  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.43/1.05  
% 2.43/1.05  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.43/1.05  
% 2.43/1.05  ------  iProver source info
% 2.43/1.05  
% 2.43/1.05  git: date: 2020-06-30 10:37:57 +0100
% 2.43/1.05  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.43/1.05  git: non_committed_changes: false
% 2.43/1.05  git: last_make_outside_of_git: false
% 2.43/1.05  
% 2.43/1.05  ------ 
% 2.43/1.05  
% 2.43/1.05  ------ Input Options
% 2.43/1.05  
% 2.43/1.05  --out_options                           all
% 2.43/1.05  --tptp_safe_out                         true
% 2.43/1.05  --problem_path                          ""
% 2.43/1.05  --include_path                          ""
% 2.43/1.05  --clausifier                            res/vclausify_rel
% 2.43/1.05  --clausifier_options                    --mode clausify
% 2.43/1.05  --stdin                                 false
% 2.43/1.05  --stats_out                             all
% 2.43/1.05  
% 2.43/1.05  ------ General Options
% 2.43/1.05  
% 2.43/1.05  --fof                                   false
% 2.43/1.05  --time_out_real                         305.
% 2.43/1.05  --time_out_virtual                      -1.
% 2.43/1.05  --symbol_type_check                     false
% 2.43/1.05  --clausify_out                          false
% 2.43/1.05  --sig_cnt_out                           false
% 2.43/1.05  --trig_cnt_out                          false
% 2.43/1.05  --trig_cnt_out_tolerance                1.
% 2.43/1.05  --trig_cnt_out_sk_spl                   false
% 2.43/1.05  --abstr_cl_out                          false
% 2.43/1.05  
% 2.43/1.05  ------ Global Options
% 2.43/1.05  
% 2.43/1.05  --schedule                              default
% 2.43/1.05  --add_important_lit                     false
% 2.43/1.05  --prop_solver_per_cl                    1000
% 2.43/1.05  --min_unsat_core                        false
% 2.43/1.05  --soft_assumptions                      false
% 2.43/1.05  --soft_lemma_size                       3
% 2.43/1.05  --prop_impl_unit_size                   0
% 2.43/1.05  --prop_impl_unit                        []
% 2.43/1.05  --share_sel_clauses                     true
% 2.43/1.05  --reset_solvers                         false
% 2.43/1.05  --bc_imp_inh                            [conj_cone]
% 2.43/1.05  --conj_cone_tolerance                   3.
% 2.43/1.05  --extra_neg_conj                        none
% 2.43/1.05  --large_theory_mode                     true
% 2.43/1.05  --prolific_symb_bound                   200
% 2.43/1.05  --lt_threshold                          2000
% 2.43/1.05  --clause_weak_htbl                      true
% 2.43/1.05  --gc_record_bc_elim                     false
% 2.43/1.05  
% 2.43/1.05  ------ Preprocessing Options
% 2.43/1.05  
% 2.43/1.05  --preprocessing_flag                    true
% 2.43/1.05  --time_out_prep_mult                    0.1
% 2.43/1.05  --splitting_mode                        input
% 2.43/1.05  --splitting_grd                         true
% 2.43/1.05  --splitting_cvd                         false
% 2.43/1.05  --splitting_cvd_svl                     false
% 2.43/1.05  --splitting_nvd                         32
% 2.43/1.05  --sub_typing                            true
% 2.43/1.05  --prep_gs_sim                           true
% 2.43/1.05  --prep_unflatten                        true
% 2.43/1.05  --prep_res_sim                          true
% 2.43/1.05  --prep_upred                            true
% 2.43/1.05  --prep_sem_filter                       exhaustive
% 2.43/1.05  --prep_sem_filter_out                   false
% 2.43/1.05  --pred_elim                             true
% 2.43/1.05  --res_sim_input                         true
% 2.43/1.05  --eq_ax_congr_red                       true
% 2.43/1.05  --pure_diseq_elim                       true
% 2.43/1.05  --brand_transform                       false
% 2.43/1.05  --non_eq_to_eq                          false
% 2.43/1.05  --prep_def_merge                        true
% 2.43/1.05  --prep_def_merge_prop_impl              false
% 2.43/1.05  --prep_def_merge_mbd                    true
% 2.43/1.05  --prep_def_merge_tr_red                 false
% 2.43/1.05  --prep_def_merge_tr_cl                  false
% 2.43/1.05  --smt_preprocessing                     true
% 2.43/1.05  --smt_ac_axioms                         fast
% 2.43/1.05  --preprocessed_out                      false
% 2.43/1.05  --preprocessed_stats                    false
% 2.43/1.05  
% 2.43/1.05  ------ Abstraction refinement Options
% 2.43/1.05  
% 2.43/1.05  --abstr_ref                             []
% 2.43/1.05  --abstr_ref_prep                        false
% 2.43/1.05  --abstr_ref_until_sat                   false
% 2.43/1.05  --abstr_ref_sig_restrict                funpre
% 2.43/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 2.43/1.05  --abstr_ref_under                       []
% 2.43/1.05  
% 2.43/1.05  ------ SAT Options
% 2.43/1.05  
% 2.43/1.05  --sat_mode                              false
% 2.43/1.05  --sat_fm_restart_options                ""
% 2.43/1.05  --sat_gr_def                            false
% 2.43/1.05  --sat_epr_types                         true
% 2.43/1.05  --sat_non_cyclic_types                  false
% 2.43/1.05  --sat_finite_models                     false
% 2.43/1.05  --sat_fm_lemmas                         false
% 2.43/1.05  --sat_fm_prep                           false
% 2.43/1.05  --sat_fm_uc_incr                        true
% 2.43/1.05  --sat_out_model                         small
% 2.43/1.05  --sat_out_clauses                       false
% 2.43/1.05  
% 2.43/1.05  ------ QBF Options
% 2.43/1.05  
% 2.43/1.05  --qbf_mode                              false
% 2.43/1.05  --qbf_elim_univ                         false
% 2.43/1.05  --qbf_dom_inst                          none
% 2.43/1.05  --qbf_dom_pre_inst                      false
% 2.43/1.05  --qbf_sk_in                             false
% 2.43/1.05  --qbf_pred_elim                         true
% 2.43/1.05  --qbf_split                             512
% 2.43/1.05  
% 2.43/1.05  ------ BMC1 Options
% 2.43/1.05  
% 2.43/1.05  --bmc1_incremental                      false
% 2.43/1.05  --bmc1_axioms                           reachable_all
% 2.43/1.05  --bmc1_min_bound                        0
% 2.43/1.05  --bmc1_max_bound                        -1
% 2.43/1.05  --bmc1_max_bound_default                -1
% 2.43/1.05  --bmc1_symbol_reachability              true
% 2.43/1.05  --bmc1_property_lemmas                  false
% 2.43/1.05  --bmc1_k_induction                      false
% 2.43/1.05  --bmc1_non_equiv_states                 false
% 2.43/1.05  --bmc1_deadlock                         false
% 2.43/1.05  --bmc1_ucm                              false
% 2.43/1.05  --bmc1_add_unsat_core                   none
% 2.43/1.06  --bmc1_unsat_core_children              false
% 2.43/1.06  --bmc1_unsat_core_extrapolate_axioms    false
% 2.43/1.06  --bmc1_out_stat                         full
% 2.43/1.06  --bmc1_ground_init                      false
% 2.43/1.06  --bmc1_pre_inst_next_state              false
% 2.43/1.06  --bmc1_pre_inst_state                   false
% 2.43/1.06  --bmc1_pre_inst_reach_state             false
% 2.43/1.06  --bmc1_out_unsat_core                   false
% 2.43/1.06  --bmc1_aig_witness_out                  false
% 2.43/1.06  --bmc1_verbose                          false
% 2.43/1.06  --bmc1_dump_clauses_tptp                false
% 2.43/1.06  --bmc1_dump_unsat_core_tptp             false
% 2.43/1.06  --bmc1_dump_file                        -
% 2.43/1.06  --bmc1_ucm_expand_uc_limit              128
% 2.43/1.06  --bmc1_ucm_n_expand_iterations          6
% 2.43/1.06  --bmc1_ucm_extend_mode                  1
% 2.43/1.06  --bmc1_ucm_init_mode                    2
% 2.43/1.06  --bmc1_ucm_cone_mode                    none
% 2.43/1.06  --bmc1_ucm_reduced_relation_type        0
% 2.43/1.06  --bmc1_ucm_relax_model                  4
% 2.43/1.06  --bmc1_ucm_full_tr_after_sat            true
% 2.43/1.06  --bmc1_ucm_expand_neg_assumptions       false
% 2.43/1.06  --bmc1_ucm_layered_model                none
% 2.43/1.06  --bmc1_ucm_max_lemma_size               10
% 2.43/1.06  
% 2.43/1.06  ------ AIG Options
% 2.43/1.06  
% 2.43/1.06  --aig_mode                              false
% 2.43/1.06  
% 2.43/1.06  ------ Instantiation Options
% 2.43/1.06  
% 2.43/1.06  --instantiation_flag                    true
% 2.43/1.06  --inst_sos_flag                         false
% 2.43/1.06  --inst_sos_phase                        true
% 2.43/1.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.43/1.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.43/1.06  --inst_lit_sel_side                     num_symb
% 2.43/1.06  --inst_solver_per_active                1400
% 2.43/1.06  --inst_solver_calls_frac                1.
% 2.43/1.06  --inst_passive_queue_type               priority_queues
% 2.43/1.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.43/1.06  --inst_passive_queues_freq              [25;2]
% 2.43/1.06  --inst_dismatching                      true
% 2.43/1.06  --inst_eager_unprocessed_to_passive     true
% 2.43/1.06  --inst_prop_sim_given                   true
% 2.43/1.06  --inst_prop_sim_new                     false
% 2.43/1.06  --inst_subs_new                         false
% 2.43/1.06  --inst_eq_res_simp                      false
% 2.43/1.06  --inst_subs_given                       false
% 2.43/1.06  --inst_orphan_elimination               true
% 2.43/1.06  --inst_learning_loop_flag               true
% 2.43/1.06  --inst_learning_start                   3000
% 2.43/1.06  --inst_learning_factor                  2
% 2.43/1.06  --inst_start_prop_sim_after_learn       3
% 2.43/1.06  --inst_sel_renew                        solver
% 2.43/1.06  --inst_lit_activity_flag                true
% 2.43/1.06  --inst_restr_to_given                   false
% 2.43/1.06  --inst_activity_threshold               500
% 2.43/1.06  --inst_out_proof                        true
% 2.43/1.06  
% 2.43/1.06  ------ Resolution Options
% 2.43/1.06  
% 2.43/1.06  --resolution_flag                       true
% 2.43/1.06  --res_lit_sel                           adaptive
% 2.43/1.06  --res_lit_sel_side                      none
% 2.43/1.06  --res_ordering                          kbo
% 2.43/1.06  --res_to_prop_solver                    active
% 2.43/1.06  --res_prop_simpl_new                    false
% 2.43/1.06  --res_prop_simpl_given                  true
% 2.43/1.06  --res_passive_queue_type                priority_queues
% 2.43/1.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.43/1.06  --res_passive_queues_freq               [15;5]
% 2.43/1.06  --res_forward_subs                      full
% 2.43/1.06  --res_backward_subs                     full
% 2.43/1.06  --res_forward_subs_resolution           true
% 2.43/1.06  --res_backward_subs_resolution          true
% 2.43/1.06  --res_orphan_elimination                true
% 2.43/1.06  --res_time_limit                        2.
% 2.43/1.06  --res_out_proof                         true
% 2.43/1.06  
% 2.43/1.06  ------ Superposition Options
% 2.43/1.06  
% 2.43/1.06  --superposition_flag                    true
% 2.43/1.06  --sup_passive_queue_type                priority_queues
% 2.43/1.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.43/1.06  --sup_passive_queues_freq               [8;1;4]
% 2.43/1.06  --demod_completeness_check              fast
% 2.43/1.06  --demod_use_ground                      true
% 2.43/1.06  --sup_to_prop_solver                    passive
% 2.43/1.06  --sup_prop_simpl_new                    true
% 2.43/1.06  --sup_prop_simpl_given                  true
% 2.43/1.06  --sup_fun_splitting                     false
% 2.43/1.06  --sup_smt_interval                      50000
% 2.43/1.06  
% 2.43/1.06  ------ Superposition Simplification Setup
% 2.43/1.06  
% 2.43/1.06  --sup_indices_passive                   []
% 2.43/1.06  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/1.06  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/1.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/1.06  --sup_full_triv                         [TrivRules;PropSubs]
% 2.43/1.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/1.06  --sup_full_bw                           [BwDemod]
% 2.43/1.06  --sup_immed_triv                        [TrivRules]
% 2.43/1.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.43/1.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/1.06  --sup_immed_bw_main                     []
% 2.43/1.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.43/1.06  --sup_input_triv                        [Unflattening;TrivRules]
% 2.43/1.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/1.06  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.43/1.06  
% 2.43/1.06  ------ Combination Options
% 2.43/1.06  
% 2.43/1.06  --comb_res_mult                         3
% 2.43/1.06  --comb_sup_mult                         2
% 2.43/1.06  --comb_inst_mult                        10
% 2.43/1.06  
% 2.43/1.06  ------ Debug Options
% 2.43/1.06  
% 2.43/1.06  --dbg_backtrace                         false
% 2.43/1.06  --dbg_dump_prop_clauses                 false
% 2.43/1.06  --dbg_dump_prop_clauses_file            -
% 2.43/1.06  --dbg_out_stat                          false
% 2.43/1.06  ------ Parsing...
% 2.43/1.06  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.43/1.06  
% 2.43/1.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.43/1.06  
% 2.43/1.06  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.43/1.06  
% 2.43/1.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.43/1.06  ------ Proving...
% 2.43/1.06  ------ Problem Properties 
% 2.43/1.06  
% 2.43/1.06  
% 2.43/1.06  clauses                                 15
% 2.43/1.06  conjectures                             4
% 2.43/1.06  EPR                                     2
% 2.43/1.06  Horn                                    15
% 2.43/1.06  unary                                   9
% 2.43/1.06  binary                                  1
% 2.43/1.06  lits                                    39
% 2.43/1.06  lits eq                                 7
% 2.43/1.06  fd_pure                                 0
% 2.43/1.06  fd_pseudo                               0
% 2.43/1.06  fd_cond                                 0
% 2.43/1.06  fd_pseudo_cond                          0
% 2.43/1.06  AC symbols                              0
% 2.43/1.06  
% 2.43/1.06  ------ Schedule dynamic 5 is on 
% 2.43/1.06  
% 2.43/1.06  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.43/1.06  
% 2.43/1.06  
% 2.43/1.06  ------ 
% 2.43/1.06  Current options:
% 2.43/1.06  ------ 
% 2.43/1.06  
% 2.43/1.06  ------ Input Options
% 2.43/1.06  
% 2.43/1.06  --out_options                           all
% 2.43/1.06  --tptp_safe_out                         true
% 2.43/1.06  --problem_path                          ""
% 2.43/1.06  --include_path                          ""
% 2.43/1.06  --clausifier                            res/vclausify_rel
% 2.43/1.06  --clausifier_options                    --mode clausify
% 2.43/1.06  --stdin                                 false
% 2.43/1.06  --stats_out                             all
% 2.43/1.06  
% 2.43/1.06  ------ General Options
% 2.43/1.06  
% 2.43/1.06  --fof                                   false
% 2.43/1.06  --time_out_real                         305.
% 2.43/1.06  --time_out_virtual                      -1.
% 2.43/1.06  --symbol_type_check                     false
% 2.43/1.06  --clausify_out                          false
% 2.43/1.06  --sig_cnt_out                           false
% 2.43/1.06  --trig_cnt_out                          false
% 2.43/1.06  --trig_cnt_out_tolerance                1.
% 2.43/1.06  --trig_cnt_out_sk_spl                   false
% 2.43/1.06  --abstr_cl_out                          false
% 2.43/1.06  
% 2.43/1.06  ------ Global Options
% 2.43/1.06  
% 2.43/1.06  --schedule                              default
% 2.43/1.06  --add_important_lit                     false
% 2.43/1.06  --prop_solver_per_cl                    1000
% 2.43/1.06  --min_unsat_core                        false
% 2.43/1.06  --soft_assumptions                      false
% 2.43/1.06  --soft_lemma_size                       3
% 2.43/1.06  --prop_impl_unit_size                   0
% 2.43/1.06  --prop_impl_unit                        []
% 2.43/1.06  --share_sel_clauses                     true
% 2.43/1.06  --reset_solvers                         false
% 2.43/1.06  --bc_imp_inh                            [conj_cone]
% 2.43/1.06  --conj_cone_tolerance                   3.
% 2.43/1.06  --extra_neg_conj                        none
% 2.43/1.06  --large_theory_mode                     true
% 2.43/1.06  --prolific_symb_bound                   200
% 2.43/1.06  --lt_threshold                          2000
% 2.43/1.06  --clause_weak_htbl                      true
% 2.43/1.06  --gc_record_bc_elim                     false
% 2.43/1.06  
% 2.43/1.06  ------ Preprocessing Options
% 2.43/1.06  
% 2.43/1.06  --preprocessing_flag                    true
% 2.43/1.06  --time_out_prep_mult                    0.1
% 2.43/1.06  --splitting_mode                        input
% 2.43/1.06  --splitting_grd                         true
% 2.43/1.06  --splitting_cvd                         false
% 2.43/1.06  --splitting_cvd_svl                     false
% 2.43/1.06  --splitting_nvd                         32
% 2.43/1.06  --sub_typing                            true
% 2.43/1.06  --prep_gs_sim                           true
% 2.43/1.06  --prep_unflatten                        true
% 2.43/1.06  --prep_res_sim                          true
% 2.43/1.06  --prep_upred                            true
% 2.43/1.06  --prep_sem_filter                       exhaustive
% 2.43/1.06  --prep_sem_filter_out                   false
% 2.43/1.06  --pred_elim                             true
% 2.43/1.06  --res_sim_input                         true
% 2.43/1.06  --eq_ax_congr_red                       true
% 2.43/1.06  --pure_diseq_elim                       true
% 2.43/1.06  --brand_transform                       false
% 2.43/1.06  --non_eq_to_eq                          false
% 2.43/1.06  --prep_def_merge                        true
% 2.43/1.06  --prep_def_merge_prop_impl              false
% 2.43/1.06  --prep_def_merge_mbd                    true
% 2.43/1.06  --prep_def_merge_tr_red                 false
% 2.43/1.06  --prep_def_merge_tr_cl                  false
% 2.43/1.06  --smt_preprocessing                     true
% 2.43/1.06  --smt_ac_axioms                         fast
% 2.43/1.06  --preprocessed_out                      false
% 2.43/1.06  --preprocessed_stats                    false
% 2.43/1.06  
% 2.43/1.06  ------ Abstraction refinement Options
% 2.43/1.06  
% 2.43/1.06  --abstr_ref                             []
% 2.43/1.06  --abstr_ref_prep                        false
% 2.43/1.06  --abstr_ref_until_sat                   false
% 2.43/1.06  --abstr_ref_sig_restrict                funpre
% 2.43/1.06  --abstr_ref_af_restrict_to_split_sk     false
% 2.43/1.06  --abstr_ref_under                       []
% 2.43/1.06  
% 2.43/1.06  ------ SAT Options
% 2.43/1.06  
% 2.43/1.06  --sat_mode                              false
% 2.43/1.06  --sat_fm_restart_options                ""
% 2.43/1.06  --sat_gr_def                            false
% 2.43/1.06  --sat_epr_types                         true
% 2.43/1.06  --sat_non_cyclic_types                  false
% 2.43/1.06  --sat_finite_models                     false
% 2.43/1.06  --sat_fm_lemmas                         false
% 2.43/1.06  --sat_fm_prep                           false
% 2.43/1.06  --sat_fm_uc_incr                        true
% 2.43/1.06  --sat_out_model                         small
% 2.43/1.06  --sat_out_clauses                       false
% 2.43/1.06  
% 2.43/1.06  ------ QBF Options
% 2.43/1.06  
% 2.43/1.06  --qbf_mode                              false
% 2.43/1.06  --qbf_elim_univ                         false
% 2.43/1.06  --qbf_dom_inst                          none
% 2.43/1.06  --qbf_dom_pre_inst                      false
% 2.43/1.06  --qbf_sk_in                             false
% 2.43/1.06  --qbf_pred_elim                         true
% 2.43/1.06  --qbf_split                             512
% 2.43/1.06  
% 2.43/1.06  ------ BMC1 Options
% 2.43/1.06  
% 2.43/1.06  --bmc1_incremental                      false
% 2.43/1.06  --bmc1_axioms                           reachable_all
% 2.43/1.06  --bmc1_min_bound                        0
% 2.43/1.06  --bmc1_max_bound                        -1
% 2.43/1.06  --bmc1_max_bound_default                -1
% 2.43/1.06  --bmc1_symbol_reachability              true
% 2.43/1.06  --bmc1_property_lemmas                  false
% 2.43/1.06  --bmc1_k_induction                      false
% 2.43/1.06  --bmc1_non_equiv_states                 false
% 2.43/1.06  --bmc1_deadlock                         false
% 2.43/1.06  --bmc1_ucm                              false
% 2.43/1.06  --bmc1_add_unsat_core                   none
% 2.43/1.06  --bmc1_unsat_core_children              false
% 2.43/1.06  --bmc1_unsat_core_extrapolate_axioms    false
% 2.43/1.06  --bmc1_out_stat                         full
% 2.43/1.06  --bmc1_ground_init                      false
% 2.43/1.06  --bmc1_pre_inst_next_state              false
% 2.43/1.06  --bmc1_pre_inst_state                   false
% 2.43/1.06  --bmc1_pre_inst_reach_state             false
% 2.43/1.06  --bmc1_out_unsat_core                   false
% 2.43/1.06  --bmc1_aig_witness_out                  false
% 2.43/1.06  --bmc1_verbose                          false
% 2.43/1.06  --bmc1_dump_clauses_tptp                false
% 2.43/1.06  --bmc1_dump_unsat_core_tptp             false
% 2.43/1.06  --bmc1_dump_file                        -
% 2.43/1.06  --bmc1_ucm_expand_uc_limit              128
% 2.43/1.06  --bmc1_ucm_n_expand_iterations          6
% 2.43/1.06  --bmc1_ucm_extend_mode                  1
% 2.43/1.06  --bmc1_ucm_init_mode                    2
% 2.43/1.06  --bmc1_ucm_cone_mode                    none
% 2.43/1.06  --bmc1_ucm_reduced_relation_type        0
% 2.43/1.06  --bmc1_ucm_relax_model                  4
% 2.43/1.06  --bmc1_ucm_full_tr_after_sat            true
% 2.43/1.06  --bmc1_ucm_expand_neg_assumptions       false
% 2.43/1.06  --bmc1_ucm_layered_model                none
% 2.43/1.06  --bmc1_ucm_max_lemma_size               10
% 2.43/1.06  
% 2.43/1.06  ------ AIG Options
% 2.43/1.06  
% 2.43/1.06  --aig_mode                              false
% 2.43/1.06  
% 2.43/1.06  ------ Instantiation Options
% 2.43/1.06  
% 2.43/1.06  --instantiation_flag                    true
% 2.43/1.06  --inst_sos_flag                         false
% 2.43/1.06  --inst_sos_phase                        true
% 2.43/1.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.43/1.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.43/1.06  --inst_lit_sel_side                     none
% 2.43/1.06  --inst_solver_per_active                1400
% 2.43/1.06  --inst_solver_calls_frac                1.
% 2.43/1.06  --inst_passive_queue_type               priority_queues
% 2.43/1.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.43/1.06  --inst_passive_queues_freq              [25;2]
% 2.43/1.06  --inst_dismatching                      true
% 2.43/1.06  --inst_eager_unprocessed_to_passive     true
% 2.43/1.06  --inst_prop_sim_given                   true
% 2.43/1.06  --inst_prop_sim_new                     false
% 2.43/1.06  --inst_subs_new                         false
% 2.43/1.06  --inst_eq_res_simp                      false
% 2.43/1.06  --inst_subs_given                       false
% 2.43/1.06  --inst_orphan_elimination               true
% 2.43/1.06  --inst_learning_loop_flag               true
% 2.43/1.06  --inst_learning_start                   3000
% 2.43/1.06  --inst_learning_factor                  2
% 2.43/1.06  --inst_start_prop_sim_after_learn       3
% 2.43/1.06  --inst_sel_renew                        solver
% 2.43/1.06  --inst_lit_activity_flag                true
% 2.43/1.06  --inst_restr_to_given                   false
% 2.43/1.06  --inst_activity_threshold               500
% 2.43/1.06  --inst_out_proof                        true
% 2.43/1.06  
% 2.43/1.06  ------ Resolution Options
% 2.43/1.06  
% 2.43/1.06  --resolution_flag                       false
% 2.43/1.06  --res_lit_sel                           adaptive
% 2.43/1.06  --res_lit_sel_side                      none
% 2.43/1.06  --res_ordering                          kbo
% 2.43/1.06  --res_to_prop_solver                    active
% 2.43/1.06  --res_prop_simpl_new                    false
% 2.43/1.06  --res_prop_simpl_given                  true
% 2.43/1.06  --res_passive_queue_type                priority_queues
% 2.43/1.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.43/1.06  --res_passive_queues_freq               [15;5]
% 2.43/1.06  --res_forward_subs                      full
% 2.43/1.06  --res_backward_subs                     full
% 2.43/1.06  --res_forward_subs_resolution           true
% 2.43/1.06  --res_backward_subs_resolution          true
% 2.43/1.06  --res_orphan_elimination                true
% 2.43/1.06  --res_time_limit                        2.
% 2.43/1.06  --res_out_proof                         true
% 2.43/1.06  
% 2.43/1.06  ------ Superposition Options
% 2.43/1.06  
% 2.43/1.06  --superposition_flag                    true
% 2.43/1.06  --sup_passive_queue_type                priority_queues
% 2.43/1.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.43/1.06  --sup_passive_queues_freq               [8;1;4]
% 2.43/1.06  --demod_completeness_check              fast
% 2.43/1.06  --demod_use_ground                      true
% 2.43/1.06  --sup_to_prop_solver                    passive
% 2.43/1.06  --sup_prop_simpl_new                    true
% 2.43/1.06  --sup_prop_simpl_given                  true
% 2.43/1.06  --sup_fun_splitting                     false
% 2.43/1.06  --sup_smt_interval                      50000
% 2.43/1.06  
% 2.43/1.06  ------ Superposition Simplification Setup
% 2.43/1.06  
% 2.43/1.06  --sup_indices_passive                   []
% 2.43/1.06  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/1.06  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/1.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/1.06  --sup_full_triv                         [TrivRules;PropSubs]
% 2.43/1.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/1.06  --sup_full_bw                           [BwDemod]
% 2.43/1.06  --sup_immed_triv                        [TrivRules]
% 2.43/1.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.43/1.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/1.06  --sup_immed_bw_main                     []
% 2.43/1.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.43/1.06  --sup_input_triv                        [Unflattening;TrivRules]
% 2.43/1.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/1.06  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.43/1.06  
% 2.43/1.06  ------ Combination Options
% 2.43/1.06  
% 2.43/1.06  --comb_res_mult                         3
% 2.43/1.06  --comb_sup_mult                         2
% 2.43/1.06  --comb_inst_mult                        10
% 2.43/1.06  
% 2.43/1.06  ------ Debug Options
% 2.43/1.06  
% 2.43/1.06  --dbg_backtrace                         false
% 2.43/1.06  --dbg_dump_prop_clauses                 false
% 2.43/1.06  --dbg_dump_prop_clauses_file            -
% 2.43/1.06  --dbg_out_stat                          false
% 2.43/1.06  
% 2.43/1.06  
% 2.43/1.06  
% 2.43/1.06  
% 2.43/1.06  ------ Proving...
% 2.43/1.06  
% 2.43/1.06  
% 2.43/1.06  % SZS status Theorem for theBenchmark.p
% 2.43/1.06  
% 2.43/1.06   Resolution empty clause
% 2.43/1.06  
% 2.43/1.06  % SZS output start CNFRefutation for theBenchmark.p
% 2.43/1.06  
% 2.43/1.06  fof(f15,conjecture,(
% 2.43/1.06    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) => k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)))),
% 2.43/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.43/1.06  
% 2.43/1.06  fof(f16,negated_conjecture,(
% 2.43/1.06    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) => k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)))),
% 2.43/1.06    inference(negated_conjecture,[],[f15])).
% 2.43/1.06  
% 2.43/1.06  fof(f24,plain,(
% 2.43/1.06    ? [X0,X1,X2] : ((k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 2.43/1.06    inference(ennf_transformation,[],[f16])).
% 2.43/1.06  
% 2.43/1.06  fof(f25,plain,(
% 2.43/1.06    ? [X0,X1,X2] : (k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 2.43/1.06    inference(flattening,[],[f24])).
% 2.43/1.06  
% 2.43/1.06  fof(f28,plain,(
% 2.43/1.06    ? [X0,X1,X2] : (k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (k1_funct_1(sK2,sK0) != k1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2),sK0) & r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 2.43/1.06    introduced(choice_axiom,[])).
% 2.43/1.06  
% 2.43/1.06  fof(f29,plain,(
% 2.43/1.06    k1_funct_1(sK2,sK0) != k1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2),sK0) & r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 2.43/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f28])).
% 2.43/1.06  
% 2.43/1.06  fof(f48,plain,(
% 2.43/1.06    v1_relat_1(sK2)),
% 2.43/1.06    inference(cnf_transformation,[],[f29])).
% 2.43/1.06  
% 2.43/1.06  fof(f14,axiom,(
% 2.43/1.06    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)))),
% 2.43/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.43/1.06  
% 2.43/1.06  fof(f22,plain,(
% 2.43/1.06    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.43/1.06    inference(ennf_transformation,[],[f14])).
% 2.43/1.06  
% 2.43/1.06  fof(f23,plain,(
% 2.43/1.06    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.43/1.06    inference(flattening,[],[f22])).
% 2.43/1.06  
% 2.43/1.06  fof(f47,plain,(
% 2.43/1.06    ( ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.43/1.06    inference(cnf_transformation,[],[f23])).
% 2.43/1.06  
% 2.43/1.06  fof(f1,axiom,(
% 2.43/1.06    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 2.43/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.43/1.06  
% 2.43/1.06  fof(f30,plain,(
% 2.43/1.06    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 2.43/1.06    inference(cnf_transformation,[],[f1])).
% 2.43/1.06  
% 2.43/1.06  fof(f58,plain,(
% 2.43/1.06    ( ! [X0,X1] : (k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0)) = k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.43/1.06    inference(definition_unfolding,[],[f47,f30])).
% 2.43/1.06  
% 2.43/1.06  fof(f49,plain,(
% 2.43/1.06    v1_funct_1(sK2)),
% 2.43/1.06    inference(cnf_transformation,[],[f29])).
% 2.43/1.06  
% 2.43/1.06  fof(f10,axiom,(
% 2.43/1.06    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.43/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.43/1.06  
% 2.43/1.06  fof(f40,plain,(
% 2.43/1.06    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.43/1.06    inference(cnf_transformation,[],[f10])).
% 2.43/1.06  
% 2.43/1.06  fof(f9,axiom,(
% 2.43/1.06    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.43/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.43/1.06  
% 2.43/1.06  fof(f38,plain,(
% 2.43/1.06    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.43/1.06    inference(cnf_transformation,[],[f9])).
% 2.43/1.06  
% 2.43/1.06  fof(f41,plain,(
% 2.43/1.06    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 2.43/1.06    inference(cnf_transformation,[],[f10])).
% 2.43/1.06  
% 2.43/1.06  fof(f50,plain,(
% 2.43/1.06    r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1))),
% 2.43/1.06    inference(cnf_transformation,[],[f29])).
% 2.43/1.06  
% 2.43/1.06  fof(f59,plain,(
% 2.43/1.06    r2_hidden(sK0,k4_xboole_0(k1_relat_1(sK2),k4_xboole_0(k1_relat_1(sK2),sK1)))),
% 2.43/1.06    inference(definition_unfolding,[],[f50,f30])).
% 2.43/1.06  
% 2.43/1.06  fof(f11,axiom,(
% 2.43/1.06    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))))))),
% 2.43/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.43/1.06  
% 2.43/1.06  fof(f17,plain,(
% 2.43/1.06    ! [X0,X1] : (! [X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.43/1.06    inference(ennf_transformation,[],[f11])).
% 2.43/1.06  
% 2.43/1.06  fof(f18,plain,(
% 2.43/1.06    ! [X0,X1] : (! [X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.43/1.06    inference(flattening,[],[f17])).
% 2.43/1.06  
% 2.43/1.06  fof(f26,plain,(
% 2.43/1.06    ! [X0,X1] : (! [X2] : (((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | (~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X2)))) & ((r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.43/1.06    inference(nnf_transformation,[],[f18])).
% 2.43/1.06  
% 2.43/1.06  fof(f27,plain,(
% 2.43/1.06    ! [X0,X1] : (! [X2] : (((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X2))) & ((r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.43/1.06    inference(flattening,[],[f26])).
% 2.43/1.06  
% 2.43/1.06  fof(f42,plain,(
% 2.43/1.06    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.43/1.06    inference(cnf_transformation,[],[f27])).
% 2.43/1.06  
% 2.43/1.06  fof(f13,axiom,(
% 2.43/1.06    ! [X0,X1] : (r2_hidden(X0,X1) => k1_funct_1(k6_relat_1(X1),X0) = X0)),
% 2.43/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.43/1.06  
% 2.43/1.06  fof(f21,plain,(
% 2.43/1.06    ! [X0,X1] : (k1_funct_1(k6_relat_1(X1),X0) = X0 | ~r2_hidden(X0,X1))),
% 2.43/1.06    inference(ennf_transformation,[],[f13])).
% 2.43/1.06  
% 2.43/1.06  fof(f46,plain,(
% 2.43/1.06    ( ! [X0,X1] : (k1_funct_1(k6_relat_1(X1),X0) = X0 | ~r2_hidden(X0,X1)) )),
% 2.43/1.06    inference(cnf_transformation,[],[f21])).
% 2.43/1.06  
% 2.43/1.06  fof(f12,axiom,(
% 2.43/1.06    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) => k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0))))),
% 2.43/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.43/1.06  
% 2.43/1.06  fof(f19,plain,(
% 2.43/1.06    ! [X0,X1] : (! [X2] : ((k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.43/1.06    inference(ennf_transformation,[],[f12])).
% 2.43/1.06  
% 2.43/1.06  fof(f20,plain,(
% 2.43/1.06    ! [X0,X1] : (! [X2] : (k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.43/1.06    inference(flattening,[],[f19])).
% 2.43/1.06  
% 2.43/1.06  fof(f45,plain,(
% 2.43/1.06    ( ! [X2,X0,X1] : (k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.43/1.06    inference(cnf_transformation,[],[f20])).
% 2.43/1.06  
% 2.43/1.06  fof(f51,plain,(
% 2.43/1.06    k1_funct_1(sK2,sK0) != k1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2),sK0)),
% 2.43/1.06    inference(cnf_transformation,[],[f29])).
% 2.43/1.06  
% 2.43/1.06  cnf(c_14,negated_conjecture,
% 2.43/1.06      ( v1_relat_1(sK2) ),
% 2.43/1.06      inference(cnf_transformation,[],[f48]) ).
% 2.43/1.06  
% 2.43/1.06  cnf(c_356,plain,
% 2.43/1.06      ( v1_relat_1(sK2) = iProver_top ),
% 2.43/1.06      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.43/1.06  
% 2.43/1.06  cnf(c_10,plain,
% 2.43/1.06      ( ~ v1_relat_1(X0)
% 2.43/1.06      | ~ v1_funct_1(X0)
% 2.43/1.06      | k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),X1)) = k1_relat_1(k5_relat_1(k6_relat_1(X1),X0)) ),
% 2.43/1.06      inference(cnf_transformation,[],[f58]) ).
% 2.43/1.06  
% 2.43/1.06  cnf(c_359,plain,
% 2.43/1.06      ( k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),X1)) = k1_relat_1(k5_relat_1(k6_relat_1(X1),X0))
% 2.43/1.06      | v1_relat_1(X0) != iProver_top
% 2.43/1.06      | v1_funct_1(X0) != iProver_top ),
% 2.43/1.06      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.43/1.06  
% 2.43/1.06  cnf(c_638,plain,
% 2.43/1.06      ( k4_xboole_0(k1_relat_1(sK2),k4_xboole_0(k1_relat_1(sK2),X0)) = k1_relat_1(k5_relat_1(k6_relat_1(X0),sK2))
% 2.43/1.06      | v1_funct_1(sK2) != iProver_top ),
% 2.43/1.06      inference(superposition,[status(thm)],[c_356,c_359]) ).
% 2.43/1.06  
% 2.43/1.06  cnf(c_13,negated_conjecture,
% 2.43/1.06      ( v1_funct_1(sK2) ),
% 2.43/1.06      inference(cnf_transformation,[],[f49]) ).
% 2.43/1.06  
% 2.43/1.06  cnf(c_16,plain,
% 2.43/1.06      ( v1_funct_1(sK2) = iProver_top ),
% 2.43/1.06      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.43/1.06  
% 2.43/1.06  cnf(c_978,plain,
% 2.43/1.06      ( k4_xboole_0(k1_relat_1(sK2),k4_xboole_0(k1_relat_1(sK2),X0)) = k1_relat_1(k5_relat_1(k6_relat_1(X0),sK2)) ),
% 2.43/1.06      inference(global_propositional_subsumption,[status(thm)],[c_638,c_16]) ).
% 2.43/1.06  
% 2.43/1.06  cnf(c_4,plain,
% 2.43/1.06      ( v1_relat_1(k6_relat_1(X0)) ),
% 2.43/1.06      inference(cnf_transformation,[],[f40]) ).
% 2.43/1.06  
% 2.43/1.06  cnf(c_365,plain,
% 2.43/1.06      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 2.43/1.06      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.43/1.06  
% 2.43/1.06  cnf(c_637,plain,
% 2.43/1.06      ( k4_xboole_0(k1_relat_1(k6_relat_1(X0)),k4_xboole_0(k1_relat_1(k6_relat_1(X0)),X1)) = k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)))
% 2.43/1.06      | v1_funct_1(k6_relat_1(X0)) != iProver_top ),
% 2.43/1.06      inference(superposition,[status(thm)],[c_365,c_359]) ).
% 2.43/1.06  
% 2.43/1.06  cnf(c_2,plain,
% 2.43/1.06      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 2.43/1.06      inference(cnf_transformation,[],[f38]) ).
% 2.43/1.06  
% 2.43/1.06  cnf(c_645,plain,
% 2.43/1.06      ( k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k4_xboole_0(X1,k4_xboole_0(X1,X0))
% 2.43/1.06      | v1_funct_1(k6_relat_1(X1)) != iProver_top ),
% 2.43/1.06      inference(light_normalisation,[status(thm)],[c_637,c_2]) ).
% 2.43/1.06  
% 2.43/1.06  cnf(c_3,plain,
% 2.43/1.06      ( v1_funct_1(k6_relat_1(X0)) ),
% 2.43/1.06      inference(cnf_transformation,[],[f41]) ).
% 2.43/1.06  
% 2.43/1.06  cnf(c_366,plain,
% 2.43/1.06      ( v1_funct_1(k6_relat_1(X0)) = iProver_top ),
% 2.43/1.06      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.43/1.06  
% 2.43/1.06  cnf(c_750,plain,
% 2.43/1.06      ( k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 2.43/1.06      inference(forward_subsumption_resolution,[status(thm)],[c_645,c_366]) ).
% 2.43/1.06  
% 2.43/1.06  cnf(c_988,plain,
% 2.43/1.06      ( k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(k1_relat_1(sK2)))) = k1_relat_1(k5_relat_1(k6_relat_1(X0),sK2)) ),
% 2.43/1.06      inference(superposition,[status(thm)],[c_978,c_750]) ).
% 2.43/1.06  
% 2.43/1.06  cnf(c_12,negated_conjecture,
% 2.43/1.06      ( r2_hidden(sK0,k4_xboole_0(k1_relat_1(sK2),k4_xboole_0(k1_relat_1(sK2),sK1))) ),
% 2.43/1.06      inference(cnf_transformation,[],[f59]) ).
% 2.43/1.06  
% 2.43/1.06  cnf(c_358,plain,
% 2.43/1.06      ( r2_hidden(sK0,k4_xboole_0(k1_relat_1(sK2),k4_xboole_0(k1_relat_1(sK2),sK1))) = iProver_top ),
% 2.43/1.06      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.43/1.06  
% 2.43/1.06  cnf(c_753,plain,
% 2.43/1.06      ( r2_hidden(sK0,k1_relat_1(k5_relat_1(k6_relat_1(sK1),k6_relat_1(k1_relat_1(sK2))))) = iProver_top ),
% 2.43/1.06      inference(demodulation,[status(thm)],[c_750,c_358]) ).
% 2.43/1.06  
% 2.43/1.06  cnf(c_1055,plain,
% 2.43/1.06      ( r2_hidden(sK0,k1_relat_1(k5_relat_1(k6_relat_1(sK1),sK2))) = iProver_top ),
% 2.43/1.06      inference(demodulation,[status(thm)],[c_988,c_753]) ).
% 2.43/1.06  
% 2.43/1.06  cnf(c_7,plain,
% 2.43/1.06      ( r2_hidden(X0,k1_relat_1(X1))
% 2.43/1.06      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X1,X2)))
% 2.43/1.06      | ~ v1_relat_1(X1)
% 2.43/1.06      | ~ v1_relat_1(X2)
% 2.43/1.06      | ~ v1_funct_1(X1)
% 2.43/1.06      | ~ v1_funct_1(X2) ),
% 2.43/1.06      inference(cnf_transformation,[],[f42]) ).
% 2.43/1.06  
% 2.43/1.06  cnf(c_362,plain,
% 2.43/1.06      ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
% 2.43/1.06      | r2_hidden(X0,k1_relat_1(k5_relat_1(X1,X2))) != iProver_top
% 2.43/1.06      | v1_relat_1(X1) != iProver_top
% 2.43/1.06      | v1_relat_1(X2) != iProver_top
% 2.43/1.06      | v1_funct_1(X1) != iProver_top
% 2.43/1.06      | v1_funct_1(X2) != iProver_top ),
% 2.43/1.06      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.43/1.06  
% 2.43/1.06  cnf(c_1066,plain,
% 2.43/1.06      ( r2_hidden(sK0,k1_relat_1(k6_relat_1(sK1))) = iProver_top
% 2.43/1.06      | v1_relat_1(k6_relat_1(sK1)) != iProver_top
% 2.43/1.06      | v1_relat_1(sK2) != iProver_top
% 2.43/1.06      | v1_funct_1(k6_relat_1(sK1)) != iProver_top
% 2.43/1.06      | v1_funct_1(sK2) != iProver_top ),
% 2.43/1.06      inference(superposition,[status(thm)],[c_1055,c_362]) ).
% 2.43/1.06  
% 2.43/1.06  cnf(c_1073,plain,
% 2.43/1.06      ( r2_hidden(sK0,sK1) = iProver_top
% 2.43/1.06      | v1_relat_1(k6_relat_1(sK1)) != iProver_top
% 2.43/1.06      | v1_relat_1(sK2) != iProver_top
% 2.43/1.06      | v1_funct_1(k6_relat_1(sK1)) != iProver_top
% 2.43/1.06      | v1_funct_1(sK2) != iProver_top ),
% 2.43/1.06      inference(demodulation,[status(thm)],[c_1066,c_2]) ).
% 2.43/1.06  
% 2.43/1.06  cnf(c_15,plain,
% 2.43/1.06      ( v1_relat_1(sK2) = iProver_top ),
% 2.43/1.06      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.43/1.06  
% 2.43/1.06  cnf(c_1670,plain,
% 2.43/1.06      ( v1_funct_1(k6_relat_1(sK1)) != iProver_top
% 2.43/1.06      | r2_hidden(sK0,sK1) = iProver_top
% 2.43/1.06      | v1_relat_1(k6_relat_1(sK1)) != iProver_top ),
% 2.43/1.06      inference(global_propositional_subsumption,
% 2.43/1.06                [status(thm)],
% 2.43/1.06                [c_1073,c_15,c_16]) ).
% 2.43/1.06  
% 2.43/1.06  cnf(c_1671,plain,
% 2.43/1.06      ( r2_hidden(sK0,sK1) = iProver_top
% 2.43/1.06      | v1_relat_1(k6_relat_1(sK1)) != iProver_top
% 2.43/1.06      | v1_funct_1(k6_relat_1(sK1)) != iProver_top ),
% 2.43/1.06      inference(renaming,[status(thm)],[c_1670]) ).
% 2.43/1.06  
% 2.43/1.06  cnf(c_1677,plain,
% 2.43/1.06      ( r2_hidden(sK0,sK1) = iProver_top ),
% 2.43/1.06      inference(forward_subsumption_resolution,
% 2.43/1.06                [status(thm)],
% 2.43/1.06                [c_1671,c_366,c_365]) ).
% 2.43/1.06  
% 2.43/1.06  cnf(c_9,plain,
% 2.43/1.06      ( ~ r2_hidden(X0,X1) | k1_funct_1(k6_relat_1(X1),X0) = X0 ),
% 2.43/1.06      inference(cnf_transformation,[],[f46]) ).
% 2.43/1.06  
% 2.43/1.06  cnf(c_360,plain,
% 2.43/1.06      ( k1_funct_1(k6_relat_1(X0),X1) = X1 | r2_hidden(X1,X0) != iProver_top ),
% 2.43/1.06      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.43/1.06  
% 2.43/1.06  cnf(c_1679,plain,
% 2.43/1.06      ( k1_funct_1(k6_relat_1(sK1),sK0) = sK0 ),
% 2.43/1.06      inference(superposition,[status(thm)],[c_1677,c_360]) ).
% 2.43/1.06  
% 2.43/1.06  cnf(c_8,plain,
% 2.43/1.06      ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X1,X2)))
% 2.43/1.06      | ~ v1_relat_1(X1)
% 2.43/1.06      | ~ v1_relat_1(X2)
% 2.43/1.06      | ~ v1_funct_1(X1)
% 2.43/1.06      | ~ v1_funct_1(X2)
% 2.43/1.06      | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ),
% 2.43/1.06      inference(cnf_transformation,[],[f45]) ).
% 2.43/1.06  
% 2.43/1.06  cnf(c_361,plain,
% 2.43/1.06      ( k1_funct_1(k5_relat_1(X0,X1),X2) = k1_funct_1(X1,k1_funct_1(X0,X2))
% 2.43/1.06      | r2_hidden(X2,k1_relat_1(k5_relat_1(X0,X1))) != iProver_top
% 2.43/1.06      | v1_relat_1(X0) != iProver_top
% 2.43/1.06      | v1_relat_1(X1) != iProver_top
% 2.43/1.06      | v1_funct_1(X0) != iProver_top
% 2.43/1.06      | v1_funct_1(X1) != iProver_top ),
% 2.43/1.06      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.43/1.06  
% 2.43/1.06  cnf(c_1267,plain,
% 2.43/1.06      ( k1_funct_1(sK2,k1_funct_1(k6_relat_1(sK1),sK0)) = k1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2),sK0)
% 2.43/1.06      | v1_relat_1(k6_relat_1(sK1)) != iProver_top
% 2.43/1.06      | v1_relat_1(sK2) != iProver_top
% 2.43/1.06      | v1_funct_1(k6_relat_1(sK1)) != iProver_top
% 2.43/1.06      | v1_funct_1(sK2) != iProver_top ),
% 2.43/1.06      inference(superposition,[status(thm)],[c_1055,c_361]) ).
% 2.43/1.06  
% 2.43/1.06  cnf(c_2526,plain,
% 2.43/1.06      ( v1_funct_1(k6_relat_1(sK1)) != iProver_top
% 2.43/1.06      | k1_funct_1(sK2,k1_funct_1(k6_relat_1(sK1),sK0)) = k1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2),sK0)
% 2.43/1.06      | v1_relat_1(k6_relat_1(sK1)) != iProver_top ),
% 2.43/1.06      inference(global_propositional_subsumption,
% 2.43/1.06                [status(thm)],
% 2.43/1.06                [c_1267,c_15,c_16]) ).
% 2.43/1.06  
% 2.43/1.06  cnf(c_2527,plain,
% 2.43/1.06      ( k1_funct_1(sK2,k1_funct_1(k6_relat_1(sK1),sK0)) = k1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2),sK0)
% 2.43/1.06      | v1_relat_1(k6_relat_1(sK1)) != iProver_top
% 2.43/1.06      | v1_funct_1(k6_relat_1(sK1)) != iProver_top ),
% 2.43/1.06      inference(renaming,[status(thm)],[c_2526]) ).
% 2.43/1.06  
% 2.43/1.06  cnf(c_2533,plain,
% 2.43/1.06      ( k1_funct_1(sK2,k1_funct_1(k6_relat_1(sK1),sK0)) = k1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2),sK0) ),
% 2.43/1.06      inference(forward_subsumption_resolution,
% 2.43/1.06                [status(thm)],
% 2.43/1.06                [c_2527,c_366,c_365]) ).
% 2.43/1.06  
% 2.43/1.06  cnf(c_11,negated_conjecture,
% 2.43/1.06      ( k1_funct_1(sK2,sK0) != k1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2),sK0) ),
% 2.43/1.06      inference(cnf_transformation,[],[f51]) ).
% 2.43/1.06  
% 2.43/1.06  cnf(c_2534,plain,
% 2.43/1.06      ( k1_funct_1(sK2,k1_funct_1(k6_relat_1(sK1),sK0)) != k1_funct_1(sK2,sK0) ),
% 2.43/1.06      inference(demodulation,[status(thm)],[c_2533,c_11]) ).
% 2.43/1.06  
% 2.43/1.06  cnf(c_5497,plain,
% 2.43/1.06      ( k1_funct_1(sK2,sK0) != k1_funct_1(sK2,sK0) ),
% 2.43/1.06      inference(demodulation,[status(thm)],[c_1679,c_2534]) ).
% 2.43/1.06  
% 2.43/1.06  cnf(c_5504,plain,
% 2.43/1.06      ( $false ),
% 2.43/1.06      inference(equality_resolution_simp,[status(thm)],[c_5497]) ).
% 2.43/1.06  
% 2.43/1.06  
% 2.43/1.06  % SZS output end CNFRefutation for theBenchmark.p
% 2.43/1.06  
% 2.43/1.06  ------                               Statistics
% 2.43/1.06  
% 2.43/1.06  ------ General
% 2.43/1.06  
% 2.43/1.06  abstr_ref_over_cycles:                  0
% 2.43/1.06  abstr_ref_under_cycles:                 0
% 2.43/1.06  gc_basic_clause_elim:                   0
% 2.43/1.06  forced_gc_time:                         0
% 2.43/1.06  parsing_time:                           0.021
% 2.43/1.06  unif_index_cands_time:                  0.
% 2.43/1.06  unif_index_add_time:                    0.
% 2.43/1.06  orderings_time:                         0.
% 2.43/1.06  out_proof_time:                         0.008
% 2.43/1.06  total_time:                             0.275
% 2.43/1.06  num_of_symbols:                         45
% 2.43/1.06  num_of_terms:                           4984
% 2.43/1.06  
% 2.43/1.06  ------ Preprocessing
% 2.43/1.06  
% 2.43/1.06  num_of_splits:                          0
% 2.43/1.06  num_of_split_atoms:                     0
% 2.43/1.06  num_of_reused_defs:                     0
% 2.43/1.06  num_eq_ax_congr_red:                    16
% 2.43/1.06  num_of_sem_filtered_clauses:            1
% 2.43/1.06  num_of_subtypes:                        0
% 2.43/1.06  monotx_restored_types:                  0
% 2.43/1.06  sat_num_of_epr_types:                   0
% 2.43/1.06  sat_num_of_non_cyclic_types:            0
% 2.43/1.06  sat_guarded_non_collapsed_types:        0
% 2.43/1.06  num_pure_diseq_elim:                    0
% 2.43/1.06  simp_replaced_by:                       0
% 2.43/1.06  res_preprocessed:                       70
% 2.43/1.06  prep_upred:                             0
% 2.43/1.06  prep_unflattend:                        0
% 2.43/1.06  smt_new_axioms:                         0
% 2.43/1.06  pred_elim_cands:                        3
% 2.43/1.06  pred_elim:                              0
% 2.43/1.06  pred_elim_cl:                           0
% 2.43/1.06  pred_elim_cycles:                       1
% 2.43/1.06  merged_defs:                            0
% 2.43/1.06  merged_defs_ncl:                        0
% 2.43/1.06  bin_hyper_res:                          0
% 2.43/1.06  prep_cycles:                            3
% 2.43/1.06  pred_elim_time:                         0.
% 2.43/1.06  splitting_time:                         0.
% 2.43/1.06  sem_filter_time:                        0.
% 2.43/1.06  monotx_time:                            0.001
% 2.43/1.06  subtype_inf_time:                       0.
% 2.43/1.06  
% 2.43/1.06  ------ Problem properties
% 2.43/1.06  
% 2.43/1.06  clauses:                                15
% 2.43/1.06  conjectures:                            4
% 2.43/1.06  epr:                                    2
% 2.43/1.06  horn:                                   15
% 2.43/1.06  ground:                                 4
% 2.43/1.06  unary:                                  9
% 2.43/1.06  binary:                                 1
% 2.43/1.06  lits:                                   39
% 2.43/1.06  lits_eq:                                7
% 2.43/1.06  fd_pure:                                0
% 2.43/1.06  fd_pseudo:                              0
% 2.43/1.06  fd_cond:                                0
% 2.43/1.06  fd_pseudo_cond:                         0
% 2.43/1.06  ac_symbols:                             0
% 2.43/1.06  
% 2.43/1.06  ------ Propositional Solver
% 2.43/1.06  
% 2.43/1.06  prop_solver_calls:                      24
% 2.43/1.06  prop_fast_solver_calls:                 591
% 2.43/1.06  smt_solver_calls:                       0
% 2.43/1.06  smt_fast_solver_calls:                  0
% 2.43/1.06  prop_num_of_clauses:                    2160
% 2.43/1.06  prop_preprocess_simplified:             4557
% 2.43/1.06  prop_fo_subsumed:                       18
% 2.43/1.06  prop_solver_time:                       0.
% 2.43/1.06  smt_solver_time:                        0.
% 2.43/1.06  smt_fast_solver_time:                   0.
% 2.43/1.06  prop_fast_solver_time:                  0.
% 2.43/1.06  prop_unsat_core_time:                   0.
% 2.43/1.06  
% 2.43/1.06  ------ QBF
% 2.43/1.06  
% 2.43/1.06  qbf_q_res:                              0
% 2.43/1.06  qbf_num_tautologies:                    0
% 2.43/1.06  qbf_prep_cycles:                        0
% 2.43/1.06  
% 2.43/1.06  ------ BMC1
% 2.43/1.06  
% 2.43/1.06  bmc1_current_bound:                     -1
% 2.43/1.06  bmc1_last_solved_bound:                 -1
% 2.43/1.06  bmc1_unsat_core_size:                   -1
% 2.43/1.06  bmc1_unsat_core_parents_size:           -1
% 2.43/1.06  bmc1_merge_next_fun:                    0
% 2.43/1.06  bmc1_unsat_core_clauses_time:           0.
% 2.43/1.06  
% 2.43/1.06  ------ Instantiation
% 2.43/1.06  
% 2.43/1.06  inst_num_of_clauses:                    767
% 2.43/1.06  inst_num_in_passive:                    202
% 2.43/1.06  inst_num_in_active:                     295
% 2.43/1.06  inst_num_in_unprocessed:                270
% 2.43/1.06  inst_num_of_loops:                      300
% 2.43/1.06  inst_num_of_learning_restarts:          0
% 2.43/1.06  inst_num_moves_active_passive:          2
% 2.43/1.06  inst_lit_activity:                      0
% 2.43/1.06  inst_lit_activity_moves:                0
% 2.43/1.06  inst_num_tautologies:                   0
% 2.43/1.06  inst_num_prop_implied:                  0
% 2.43/1.06  inst_num_existing_simplified:           0
% 2.43/1.06  inst_num_eq_res_simplified:             0
% 2.43/1.06  inst_num_child_elim:                    0
% 2.43/1.06  inst_num_of_dismatching_blockings:      36
% 2.43/1.06  inst_num_of_non_proper_insts:           487
% 2.43/1.06  inst_num_of_duplicates:                 0
% 2.43/1.06  inst_inst_num_from_inst_to_res:         0
% 2.43/1.06  inst_dismatching_checking_time:         0.
% 2.43/1.06  
% 2.43/1.06  ------ Resolution
% 2.43/1.06  
% 2.43/1.06  res_num_of_clauses:                     0
% 2.43/1.06  res_num_in_passive:                     0
% 2.43/1.06  res_num_in_active:                      0
% 2.43/1.06  res_num_of_loops:                       73
% 2.43/1.06  res_forward_subset_subsumed:            43
% 2.43/1.06  res_backward_subset_subsumed:           0
% 2.43/1.06  res_forward_subsumed:                   0
% 2.43/1.06  res_backward_subsumed:                  0
% 2.43/1.06  res_forward_subsumption_resolution:     0
% 2.43/1.06  res_backward_subsumption_resolution:    0
% 2.43/1.06  res_clause_to_clause_subsumption:       304
% 2.43/1.06  res_orphan_elimination:                 0
% 2.43/1.06  res_tautology_del:                      37
% 2.43/1.06  res_num_eq_res_simplified:              0
% 2.43/1.06  res_num_sel_changes:                    0
% 2.43/1.06  res_moves_from_active_to_pass:          0
% 2.43/1.06  
% 2.43/1.06  ------ Superposition
% 2.43/1.06  
% 2.43/1.06  sup_time_total:                         0.
% 2.43/1.06  sup_time_generating:                    0.
% 2.43/1.06  sup_time_sim_full:                      0.
% 2.43/1.06  sup_time_sim_immed:                     0.
% 2.43/1.06  
% 2.43/1.06  sup_num_of_clauses:                     90
% 2.43/1.06  sup_num_in_active:                      46
% 2.43/1.06  sup_num_in_passive:                     44
% 2.43/1.06  sup_num_of_loops:                       59
% 2.43/1.06  sup_fw_superposition:                   138
% 2.43/1.06  sup_bw_superposition:                   161
% 2.43/1.06  sup_immediate_simplified:               164
% 2.43/1.06  sup_given_eliminated:                   0
% 2.43/1.06  comparisons_done:                       0
% 2.43/1.06  comparisons_avoided:                    0
% 2.43/1.06  
% 2.43/1.06  ------ Simplifications
% 2.43/1.06  
% 2.43/1.06  
% 2.43/1.06  sim_fw_subset_subsumed:                 6
% 2.43/1.06  sim_bw_subset_subsumed:                 4
% 2.43/1.06  sim_fw_subsumed:                        28
% 2.43/1.06  sim_bw_subsumed:                        18
% 2.43/1.06  sim_fw_subsumption_res:                 25
% 2.43/1.06  sim_bw_subsumption_res:                 0
% 2.43/1.06  sim_tautology_del:                      13
% 2.43/1.06  sim_eq_tautology_del:                   42
% 2.43/1.06  sim_eq_res_simp:                        0
% 2.43/1.06  sim_fw_demodulated:                     94
% 2.43/1.06  sim_bw_demodulated:                     13
% 2.43/1.06  sim_light_normalised:                   61
% 2.43/1.06  sim_joinable_taut:                      0
% 2.43/1.06  sim_joinable_simp:                      0
% 2.43/1.06  sim_ac_normalised:                      0
% 2.43/1.06  sim_smt_subsumption:                    0
% 2.43/1.06  
%------------------------------------------------------------------------------
