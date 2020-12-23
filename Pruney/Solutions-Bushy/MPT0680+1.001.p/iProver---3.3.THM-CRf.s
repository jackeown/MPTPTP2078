%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0680+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:52 EST 2020

% Result     : Theorem 51.61s
% Output     : CNFRefutation 51.61s
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
fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f38])).

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

fof(f19,plain,(
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

fof(f20,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f34,plain,(
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

fof(f35,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f33,f34])).

fof(f44,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | r2_hidden(sK0(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ! [X1,X2] : k9_relat_1(X0,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2))
       => v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( ! [X1,X2] : k9_relat_1(X0,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2))
         => v2_funct_1(X0) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f30,plain,(
    ? [X0] :
      ( ~ v2_funct_1(X0)
      & ! [X1,X2] : k9_relat_1(X0,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2))
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f31,plain,(
    ? [X0] :
      ( ~ v2_funct_1(X0)
      & ! [X1,X2] : k9_relat_1(X0,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2))
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f39,plain,
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

fof(f40,plain,
    ( ~ v2_funct_1(sK3)
    & ! [X1,X2] : k9_relat_1(sK3,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(sK3,X1),k9_relat_1(sK3,X2))
    & v1_funct_1(sK3)
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f39])).

fof(f61,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f60,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f63,plain,(
    ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f45,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | r2_hidden(sK1(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f46,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f62,plain,(
    ! [X2,X1] : k9_relat_1(sK3,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(sK3,X1),k9_relat_1(sK3,X2)) ),
    inference(cnf_transformation,[],[f40])).

fof(f7,axiom,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f65,plain,(
    ! [X2,X1] : k9_relat_1(sK3,k4_xboole_0(X1,X2)) = k4_xboole_0(k9_relat_1(sK3,X1),k9_relat_1(sK3,X2)) ),
    inference(definition_unfolding,[],[f62,f51,f51])).

fof(f53,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f66,plain,(
    ! [X1] : k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f53])).

fof(f47,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | sK0(X0) != sK1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_11,plain,
    ( X0 = X1
    | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_5,plain,
    ( r2_hidden(sK0(X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_241,plain,
    ( r2_hidden(sK0(X0),k1_relat_1(X0))
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_20])).

cnf(c_242,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3))
    | v2_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_241])).

cnf(c_21,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_18,negated_conjecture,
    ( ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_55,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | v2_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_244,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_242,c_21,c_20,c_18,c_55])).

cnf(c_613,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_244])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_221,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_20])).

cnf(c_222,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | k1_tarski(k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_221])).

cnf(c_226,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | k1_tarski(k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_222,c_21])).

cnf(c_614,plain,
    ( k1_tarski(k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_226])).

cnf(c_969,plain,
    ( k1_tarski(k1_funct_1(sK3,sK0(sK3))) = k11_relat_1(sK3,sK0(sK3)) ),
    inference(superposition,[status(thm)],[c_613,c_614])).

cnf(c_4,plain,
    ( r2_hidden(sK1(X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_252,plain,
    ( r2_hidden(sK1(X0),k1_relat_1(X0))
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_20])).

cnf(c_253,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3))
    | v2_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_252])).

cnf(c_58,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | v2_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_255,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_253,c_21,c_20,c_18,c_58])).

cnf(c_612,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_255])).

cnf(c_970,plain,
    ( k1_tarski(k1_funct_1(sK3,sK1(sK3))) = k11_relat_1(sK3,sK1(sK3)) ),
    inference(superposition,[status(thm)],[c_612,c_614])).

cnf(c_3,plain,
    ( ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_263,plain,
    ( v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_20])).

cnf(c_264,plain,
    ( v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3)) ),
    inference(unflattening,[status(thm)],[c_263])).

cnf(c_266,plain,
    ( k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_264,c_21,c_18])).

cnf(c_971,plain,
    ( k1_tarski(k1_funct_1(sK3,sK0(sK3))) = k11_relat_1(sK3,sK1(sK3)) ),
    inference(light_normalisation,[status(thm)],[c_970,c_266])).

cnf(c_972,plain,
    ( k11_relat_1(sK3,sK1(sK3)) = k11_relat_1(sK3,sK0(sK3)) ),
    inference(demodulation,[status(thm)],[c_969,c_971])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_tarski(X1)) = k11_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_288,plain,
    ( k9_relat_1(X0,k1_tarski(X1)) = k11_relat_1(X0,X1)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_21])).

cnf(c_289,plain,
    ( k9_relat_1(sK3,k1_tarski(X0)) = k11_relat_1(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_288])).

cnf(c_19,negated_conjecture,
    ( k9_relat_1(sK3,k4_xboole_0(X0,X1)) = k4_xboole_0(k9_relat_1(sK3,X0),k9_relat_1(sK3,X1)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_740,plain,
    ( k4_xboole_0(k9_relat_1(sK3,X0),k11_relat_1(sK3,X1)) = k9_relat_1(sK3,k4_xboole_0(X0,k1_tarski(X1))) ),
    inference(superposition,[status(thm)],[c_289,c_19])).

cnf(c_1133,plain,
    ( k4_xboole_0(k9_relat_1(sK3,X0),k11_relat_1(sK3,sK0(sK3))) = k9_relat_1(sK3,k4_xboole_0(X0,k1_tarski(sK1(sK3)))) ),
    inference(superposition,[status(thm)],[c_972,c_740])).

cnf(c_1134,plain,
    ( k9_relat_1(sK3,k4_xboole_0(X0,k1_tarski(sK0(sK3)))) = k9_relat_1(sK3,k4_xboole_0(X0,k1_tarski(sK1(sK3)))) ),
    inference(demodulation,[status(thm)],[c_1133,c_740])).

cnf(c_1217,plain,
    ( k9_relat_1(sK3,k4_xboole_0(k1_tarski(X0),k1_tarski(sK0(sK3)))) = k9_relat_1(sK3,k1_tarski(X0))
    | sK1(sK3) = X0 ),
    inference(superposition,[status(thm)],[c_11,c_1134])).

cnf(c_1226,plain,
    ( k9_relat_1(sK3,k4_xboole_0(k1_tarski(X0),k1_tarski(sK0(sK3)))) = k11_relat_1(sK3,X0)
    | sK1(sK3) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1217,c_289])).

cnf(c_12,plain,
    ( k4_xboole_0(k1_tarski(X0),k1_tarski(X0)) != k1_tarski(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2410,plain,
    ( k4_xboole_0(k11_relat_1(sK3,sK0(sK3)),k11_relat_1(sK3,sK0(sK3))) != k1_tarski(k1_funct_1(sK3,sK0(sK3))) ),
    inference(superposition,[status(thm)],[c_969,c_12])).

cnf(c_2416,plain,
    ( k4_xboole_0(k11_relat_1(sK3,sK0(sK3)),k11_relat_1(sK3,sK0(sK3))) != k11_relat_1(sK3,sK0(sK3)) ),
    inference(demodulation,[status(thm)],[c_2410,c_969])).

cnf(c_739,plain,
    ( k4_xboole_0(k11_relat_1(sK3,X0),k9_relat_1(sK3,X1)) = k9_relat_1(sK3,k4_xboole_0(k1_tarski(X0),X1)) ),
    inference(superposition,[status(thm)],[c_289,c_19])).

cnf(c_807,plain,
    ( k4_xboole_0(k11_relat_1(sK3,X0),k11_relat_1(sK3,X1)) = k9_relat_1(sK3,k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) ),
    inference(superposition,[status(thm)],[c_289,c_739])).

cnf(c_2417,plain,
    ( k9_relat_1(sK3,k4_xboole_0(k1_tarski(sK0(sK3)),k1_tarski(sK0(sK3)))) != k11_relat_1(sK3,sK0(sK3)) ),
    inference(demodulation,[status(thm)],[c_2416,c_807])).

cnf(c_84376,plain,
    ( sK1(sK3) = sK0(sK3) ),
    inference(superposition,[status(thm)],[c_1226,c_2417])).

cnf(c_2,plain,
    ( ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | sK1(X0) != sK0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_64,plain,
    ( ~ v1_funct_1(sK3)
    | v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | sK1(sK3) != sK0(sK3) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_84376,c_64,c_18,c_20,c_21])).


%------------------------------------------------------------------------------
