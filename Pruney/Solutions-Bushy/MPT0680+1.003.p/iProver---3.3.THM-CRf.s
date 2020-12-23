%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0680+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:53 EST 2020

% Result     : Theorem 3.32s
% Output     : CNFRefutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 540 expanded)
%              Number of clauses        :   46 ( 126 expanded)
%              Number of leaves         :    8 ( 117 expanded)
%              Depth                    :   20
%              Number of atoms          :  252 (2275 expanded)
%              Number of equality atoms :   97 ( 674 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
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

fof(f10,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f11,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f16,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f17,plain,(
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
    inference(rectify,[],[f16])).

fof(f18,plain,(
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

fof(f19,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f18])).

fof(f26,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | r2_hidden(sK1(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ! [X1,X2] : k9_relat_1(X0,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2))
       => v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( ! [X1,X2] : k9_relat_1(X0,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2))
         => v2_funct_1(X0) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f14,plain,(
    ? [X0] :
      ( ~ v2_funct_1(X0)
      & ! [X1,X2] : k9_relat_1(X0,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2))
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f15,plain,(
    ? [X0] :
      ( ~ v2_funct_1(X0)
      & ! [X1,X2] : k9_relat_1(X0,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2))
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f21,plain,
    ( ? [X0] :
        ( ~ v2_funct_1(X0)
        & ! [X1,X2] : k9_relat_1(X0,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2))
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ~ v2_funct_1(sK2)
      & ! [X2,X1] : k9_relat_1(sK2,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(sK2,X1),k9_relat_1(sK2,X2))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ~ v2_funct_1(sK2)
    & ! [X1,X2] : k9_relat_1(sK2,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(sK2,X1),k9_relat_1(sK2,X2))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f21])).

fof(f35,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f34,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f37,plain,(
    ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f27,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f25,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | r2_hidden(sK0(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f36,plain,(
    ! [X2,X1] : k9_relat_1(sK2,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(sK2,X1),k9_relat_1(sK2,X2)) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X2,X1] : k9_relat_1(sK2,k4_xboole_0(X1,X2)) = k4_xboole_0(k9_relat_1(sK2,X1),k9_relat_1(sK2,X2)) ),
    inference(definition_unfolding,[],[f36,f29,f29])).

fof(f31,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f39,plain,(
    ! [X1] : k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f31])).

fof(f28,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | sK0(X0) != sK1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_7,plain,
    ( X0 = X1
    | k4_xboole_0(k1_tarski(X1),k1_tarski(X0)) = k1_tarski(X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_3,plain,
    ( r2_hidden(sK1(X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_12,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_133,plain,
    ( r2_hidden(sK1(X0),k1_relat_1(X0))
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_12])).

cnf(c_134,plain,
    ( r2_hidden(sK1(sK2),k1_relat_1(sK2))
    | v2_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_133])).

cnf(c_13,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_10,negated_conjecture,
    ( ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_29,plain,
    ( r2_hidden(sK1(sK2),k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | v2_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_136,plain,
    ( r2_hidden(sK1(sK2),k1_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_134,c_13,c_12,c_10,c_29])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_160,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_12])).

cnf(c_161,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | k1_tarski(k1_funct_1(sK2,X0)) = k11_relat_1(sK2,X0) ),
    inference(unflattening,[status(thm)],[c_160])).

cnf(c_165,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK2))
    | k1_tarski(k1_funct_1(sK2,X0)) = k11_relat_1(sK2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_161,c_13])).

cnf(c_201,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | sK1(sK2) != X0
    | k1_tarski(k1_funct_1(sK2,X0)) = k11_relat_1(sK2,X0) ),
    inference(resolution_lifted,[status(thm)],[c_136,c_165])).

cnf(c_202,plain,
    ( k1_tarski(k1_funct_1(sK2,sK1(sK2))) = k11_relat_1(sK2,sK1(sK2)) ),
    inference(unflattening,[status(thm)],[c_201])).

cnf(c_2,plain,
    ( ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_144,plain,
    ( v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_12])).

cnf(c_145,plain,
    ( v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_funct_1(sK2,sK1(sK2)) = k1_funct_1(sK2,sK0(sK2)) ),
    inference(unflattening,[status(thm)],[c_144])).

cnf(c_32,plain,
    ( ~ v1_funct_1(sK2)
    | v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_funct_1(sK2,sK1(sK2)) = k1_funct_1(sK2,sK0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_147,plain,
    ( k1_funct_1(sK2,sK1(sK2)) = k1_funct_1(sK2,sK0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_145,c_13,c_12,c_10,c_32])).

cnf(c_234,plain,
    ( k1_tarski(k1_funct_1(sK2,sK0(sK2))) = k11_relat_1(sK2,sK1(sK2)) ),
    inference(light_normalisation,[status(thm)],[c_202,c_147])).

cnf(c_4,plain,
    ( r2_hidden(sK0(X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_122,plain,
    ( r2_hidden(sK0(X0),k1_relat_1(X0))
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_12])).

cnf(c_123,plain,
    ( r2_hidden(sK0(sK2),k1_relat_1(sK2))
    | v2_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_122])).

cnf(c_26,plain,
    ( r2_hidden(sK0(sK2),k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | v2_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_125,plain,
    ( r2_hidden(sK0(sK2),k1_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_123,c_13,c_12,c_10,c_26])).

cnf(c_196,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | sK0(sK2) != X0
    | k1_tarski(k1_funct_1(sK2,X0)) = k11_relat_1(sK2,X0) ),
    inference(resolution_lifted,[status(thm)],[c_125,c_165])).

cnf(c_197,plain,
    ( k1_tarski(k1_funct_1(sK2,sK0(sK2))) = k11_relat_1(sK2,sK0(sK2)) ),
    inference(unflattening,[status(thm)],[c_196])).

cnf(c_328,plain,
    ( k11_relat_1(sK2,sK1(sK2)) = k11_relat_1(sK2,sK0(sK2)) ),
    inference(superposition,[status(thm)],[c_234,c_197])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_tarski(X1)) = k11_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_189,plain,
    ( k9_relat_1(X0,k1_tarski(X1)) = k11_relat_1(X0,X1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_13])).

cnf(c_190,plain,
    ( k9_relat_1(sK2,k1_tarski(X0)) = k11_relat_1(sK2,X0) ),
    inference(unflattening,[status(thm)],[c_189])).

cnf(c_11,negated_conjecture,
    ( k9_relat_1(sK2,k4_xboole_0(X0,X1)) = k4_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_264,plain,
    ( k4_xboole_0(k9_relat_1(sK2,X0),k11_relat_1(sK2,X1)) = k9_relat_1(sK2,k4_xboole_0(X0,k1_tarski(X1))) ),
    inference(superposition,[status(thm)],[c_190,c_11])).

cnf(c_691,plain,
    ( k4_xboole_0(k9_relat_1(sK2,X0),k11_relat_1(sK2,sK0(sK2))) = k9_relat_1(sK2,k4_xboole_0(X0,k1_tarski(sK1(sK2)))) ),
    inference(superposition,[status(thm)],[c_328,c_264])).

cnf(c_692,plain,
    ( k9_relat_1(sK2,k4_xboole_0(X0,k1_tarski(sK0(sK2)))) = k9_relat_1(sK2,k4_xboole_0(X0,k1_tarski(sK1(sK2)))) ),
    inference(demodulation,[status(thm)],[c_691,c_264])).

cnf(c_700,plain,
    ( k9_relat_1(sK2,k4_xboole_0(k1_tarski(X0),k1_tarski(sK0(sK2)))) = k9_relat_1(sK2,k1_tarski(X0))
    | sK1(sK2) = X0 ),
    inference(superposition,[status(thm)],[c_7,c_692])).

cnf(c_713,plain,
    ( k9_relat_1(sK2,k4_xboole_0(k1_tarski(X0),k1_tarski(sK0(sK2)))) = k11_relat_1(sK2,X0)
    | sK1(sK2) = X0 ),
    inference(light_normalisation,[status(thm)],[c_700,c_190])).

cnf(c_8,plain,
    ( k4_xboole_0(k1_tarski(X0),k1_tarski(X0)) != k1_tarski(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_422,plain,
    ( k4_xboole_0(k11_relat_1(sK2,sK0(sK2)),k11_relat_1(sK2,sK0(sK2))) != k1_tarski(k1_funct_1(sK2,sK0(sK2))) ),
    inference(superposition,[status(thm)],[c_197,c_8])).

cnf(c_294,plain,
    ( k4_xboole_0(k11_relat_1(sK2,X0),k11_relat_1(sK2,X1)) = k9_relat_1(sK2,k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) ),
    inference(superposition,[status(thm)],[c_190,c_264])).

cnf(c_424,plain,
    ( k9_relat_1(sK2,k4_xboole_0(k1_tarski(sK0(sK2)),k1_tarski(sK0(sK2)))) != k11_relat_1(sK2,sK0(sK2)) ),
    inference(demodulation,[status(thm)],[c_422,c_197,c_294])).

cnf(c_7438,plain,
    ( sK1(sK2) = sK0(sK2) ),
    inference(superposition,[status(thm)],[c_713,c_424])).

cnf(c_1,plain,
    ( ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | sK1(X0) != sK0(X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_35,plain,
    ( ~ v1_funct_1(sK2)
    | v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK1(sK2) != sK0(sK2) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7438,c_35,c_10,c_12,c_13])).


%------------------------------------------------------------------------------
