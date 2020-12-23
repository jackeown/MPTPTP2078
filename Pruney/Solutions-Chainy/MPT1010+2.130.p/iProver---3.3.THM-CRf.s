%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:06:26 EST 2020

% Result     : Theorem 0.82s
% Output     : CNFRefutation 0.82s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 177 expanded)
%              Number of clauses        :   23 (  34 expanded)
%              Number of leaves         :   11 (  44 expanded)
%              Depth                    :   18
%              Number of atoms          :  263 ( 632 expanded)
%              Number of equality atoms :  149 ( 269 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f14])).

fof(f21,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_funct_1(X3,X2) != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
   => ( k1_funct_1(sK4,sK3) != sK2
      & r2_hidden(sK3,sK1)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))))
      & v1_funct_2(sK4,sK1,k1_tarski(sK2))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( k1_funct_1(sK4,sK3) != sK2
    & r2_hidden(sK3,sK1)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))))
    & v1_funct_2(sK4,sK1,k1_tarski(sK2))
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f15,f21])).

fof(f39,plain,(
    v1_funct_2(sK4,sK1,k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f43,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f34,f35])).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f33,f43])).

fof(f45,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f32,f44])).

fof(f56,plain,(
    v1_funct_2(sK4,sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
    inference(definition_unfolding,[],[f39,f45])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f12])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f40,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2)))) ),
    inference(cnf_transformation,[],[f22])).

fof(f55,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2)))) ),
    inference(definition_unfolding,[],[f40,f45])).

fof(f38,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f22])).

fof(f41,plain,(
    r2_hidden(sK3,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f42,plain,(
    k1_funct_1(sK4,sK3) != sK2 ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f16])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f17])).

fof(f19,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK0(X0,X1,X2,X3) != X2
            & sK0(X0,X1,X2,X3) != X1
            & sK0(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
        & ( sK0(X0,X1,X2,X3) = X2
          | sK0(X0,X1,X2,X3) = X1
          | sK0(X0,X1,X2,X3) = X0
          | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK0(X0,X1,X2,X3) != X2
              & sK0(X0,X1,X2,X3) != X1
              & sK0(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
          & ( sK0(X0,X1,X2,X3) = X2
            | sK0(X0,X1,X2,X3) = X1
            | sK0(X0,X1,X2,X3) = X0
            | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).

fof(f24,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f53,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f24,f43])).

fof(f63,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f53])).

fof(f7,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f54,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
    inference(definition_unfolding,[],[f36,f45])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_14,negated_conjecture,
    ( v1_funct_2(sK4,sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2)))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_144,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_13])).

cnf(c_145,plain,
    ( ~ v1_funct_2(sK4,X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(k1_funct_1(sK4,X2),X1)
    | ~ v1_funct_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_144])).

cnf(c_15,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_149,plain,
    ( r2_hidden(k1_funct_1(sK4,X2),X1)
    | ~ r2_hidden(X2,X0)
    | ~ v1_funct_2(sK4,X0,X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_145,c_15])).

cnf(c_150,plain,
    ( ~ v1_funct_2(sK4,X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(k1_funct_1(sK4,X2),X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(renaming,[status(thm)],[c_149])).

cnf(c_177,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k1_funct_1(sK4,X0),X2)
    | k3_enumset1(sK2,sK2,sK2,sK2,sK2) != X2
    | k1_zfmisc_1(k2_zfmisc_1(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK1 != X1
    | sK4 != sK4
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_150])).

cnf(c_178,plain,
    ( ~ r2_hidden(X0,sK1)
    | r2_hidden(k1_funct_1(sK4,X0),k3_enumset1(sK2,sK2,sK2,sK2,sK2))
    | k1_zfmisc_1(k2_zfmisc_1(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2)))
    | k1_xboole_0 = k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
    inference(unflattening,[status(thm)],[c_177])).

cnf(c_210,plain,
    ( ~ r2_hidden(X0,sK1)
    | r2_hidden(k1_funct_1(sK4,X0),k3_enumset1(sK2,sK2,sK2,sK2,sK2))
    | k1_xboole_0 = k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
    inference(equality_resolution_simp,[status(thm)],[c_178])).

cnf(c_436,plain,
    ( k1_xboole_0 = k3_enumset1(sK2,sK2,sK2,sK2,sK2)
    | r2_hidden(X0,sK1) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_210])).

cnf(c_12,negated_conjecture,
    ( r2_hidden(sK3,sK1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_11,negated_conjecture,
    ( k1_funct_1(sK4,sK3) != sK2 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_523,plain,
    ( r2_hidden(k1_funct_1(sK4,sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2))
    | ~ r2_hidden(sK3,sK1)
    | k1_xboole_0 = k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_210])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_553,plain,
    ( ~ r2_hidden(k1_funct_1(sK4,sK3),k3_enumset1(sK2,sK2,sK2,X0,X1))
    | k1_funct_1(sK4,sK3) = X0
    | k1_funct_1(sK4,sK3) = X1
    | k1_funct_1(sK4,sK3) = sK2 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_555,plain,
    ( ~ r2_hidden(k1_funct_1(sK4,sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2))
    | k1_funct_1(sK4,sK3) = sK2 ),
    inference(instantiation,[status(thm)],[c_553])).

cnf(c_559,plain,
    ( k1_xboole_0 = k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_436,c_12,c_11,c_523,c_555])).

cnf(c_9,plain,
    ( k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_911,plain,
    ( k2_xboole_0(k1_xboole_0,X0) != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_559,c_9])).

cnf(c_1026,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_0,c_911])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.08  % Command    : iproveropt_run.sh %d %s
% 0.06/0.27  % Computer   : n006.cluster.edu
% 0.06/0.27  % Model      : x86_64 x86_64
% 0.06/0.27  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.06/0.27  % Memory     : 8042.1875MB
% 0.06/0.27  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.06/0.27  % CPULimit   : 60
% 0.06/0.27  % WCLimit    : 600
% 0.06/0.27  % DateTime   : Tue Dec  1 14:24:52 EST 2020
% 0.06/0.27  % CPUTime    : 
% 0.06/0.27  % Running in FOF mode
% 0.82/0.86  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.82/0.86  
% 0.82/0.86  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.82/0.86  
% 0.82/0.86  ------  iProver source info
% 0.82/0.86  
% 0.82/0.86  git: date: 2020-06-30 10:37:57 +0100
% 0.82/0.86  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.82/0.86  git: non_committed_changes: false
% 0.82/0.86  git: last_make_outside_of_git: false
% 0.82/0.86  
% 0.82/0.86  ------ 
% 0.82/0.86  
% 0.82/0.86  ------ Input Options
% 0.82/0.86  
% 0.82/0.86  --out_options                           all
% 0.82/0.86  --tptp_safe_out                         true
% 0.82/0.86  --problem_path                          ""
% 0.82/0.86  --include_path                          ""
% 0.82/0.86  --clausifier                            res/vclausify_rel
% 0.82/0.86  --clausifier_options                    --mode clausify
% 0.82/0.86  --stdin                                 false
% 0.82/0.86  --stats_out                             all
% 0.82/0.86  
% 0.82/0.86  ------ General Options
% 0.82/0.86  
% 0.82/0.86  --fof                                   false
% 0.82/0.86  --time_out_real                         305.
% 0.82/0.86  --time_out_virtual                      -1.
% 0.82/0.86  --symbol_type_check                     false
% 0.82/0.86  --clausify_out                          false
% 0.82/0.86  --sig_cnt_out                           false
% 0.82/0.86  --trig_cnt_out                          false
% 0.82/0.86  --trig_cnt_out_tolerance                1.
% 0.82/0.86  --trig_cnt_out_sk_spl                   false
% 0.82/0.86  --abstr_cl_out                          false
% 0.82/0.86  
% 0.82/0.86  ------ Global Options
% 0.82/0.86  
% 0.82/0.86  --schedule                              default
% 0.82/0.86  --add_important_lit                     false
% 0.82/0.86  --prop_solver_per_cl                    1000
% 0.82/0.86  --min_unsat_core                        false
% 0.82/0.86  --soft_assumptions                      false
% 0.82/0.86  --soft_lemma_size                       3
% 0.82/0.86  --prop_impl_unit_size                   0
% 0.82/0.86  --prop_impl_unit                        []
% 0.82/0.86  --share_sel_clauses                     true
% 0.82/0.86  --reset_solvers                         false
% 0.82/0.86  --bc_imp_inh                            [conj_cone]
% 0.82/0.86  --conj_cone_tolerance                   3.
% 0.82/0.86  --extra_neg_conj                        none
% 0.82/0.86  --large_theory_mode                     true
% 0.82/0.86  --prolific_symb_bound                   200
% 0.82/0.86  --lt_threshold                          2000
% 0.82/0.86  --clause_weak_htbl                      true
% 0.82/0.86  --gc_record_bc_elim                     false
% 0.82/0.86  
% 0.82/0.86  ------ Preprocessing Options
% 0.82/0.86  
% 0.82/0.86  --preprocessing_flag                    true
% 0.82/0.86  --time_out_prep_mult                    0.1
% 0.82/0.86  --splitting_mode                        input
% 0.82/0.86  --splitting_grd                         true
% 0.82/0.86  --splitting_cvd                         false
% 0.82/0.86  --splitting_cvd_svl                     false
% 0.82/0.86  --splitting_nvd                         32
% 0.82/0.86  --sub_typing                            true
% 0.82/0.86  --prep_gs_sim                           true
% 0.82/0.86  --prep_unflatten                        true
% 0.82/0.86  --prep_res_sim                          true
% 0.82/0.86  --prep_upred                            true
% 0.82/0.86  --prep_sem_filter                       exhaustive
% 0.82/0.86  --prep_sem_filter_out                   false
% 0.82/0.86  --pred_elim                             true
% 0.82/0.86  --res_sim_input                         true
% 0.82/0.86  --eq_ax_congr_red                       true
% 0.82/0.86  --pure_diseq_elim                       true
% 0.82/0.86  --brand_transform                       false
% 0.82/0.86  --non_eq_to_eq                          false
% 0.82/0.86  --prep_def_merge                        true
% 0.82/0.86  --prep_def_merge_prop_impl              false
% 0.82/0.86  --prep_def_merge_mbd                    true
% 0.82/0.86  --prep_def_merge_tr_red                 false
% 0.82/0.86  --prep_def_merge_tr_cl                  false
% 0.82/0.86  --smt_preprocessing                     true
% 0.82/0.86  --smt_ac_axioms                         fast
% 0.82/0.86  --preprocessed_out                      false
% 0.82/0.86  --preprocessed_stats                    false
% 0.82/0.86  
% 0.82/0.86  ------ Abstraction refinement Options
% 0.82/0.86  
% 0.82/0.86  --abstr_ref                             []
% 0.82/0.86  --abstr_ref_prep                        false
% 0.82/0.86  --abstr_ref_until_sat                   false
% 0.82/0.86  --abstr_ref_sig_restrict                funpre
% 0.82/0.86  --abstr_ref_af_restrict_to_split_sk     false
% 0.82/0.86  --abstr_ref_under                       []
% 0.82/0.86  
% 0.82/0.86  ------ SAT Options
% 0.82/0.86  
% 0.82/0.86  --sat_mode                              false
% 0.82/0.86  --sat_fm_restart_options                ""
% 0.82/0.86  --sat_gr_def                            false
% 0.82/0.86  --sat_epr_types                         true
% 0.82/0.86  --sat_non_cyclic_types                  false
% 0.82/0.86  --sat_finite_models                     false
% 0.82/0.86  --sat_fm_lemmas                         false
% 0.82/0.86  --sat_fm_prep                           false
% 0.82/0.86  --sat_fm_uc_incr                        true
% 0.82/0.86  --sat_out_model                         small
% 0.82/0.86  --sat_out_clauses                       false
% 0.82/0.86  
% 0.82/0.86  ------ QBF Options
% 0.82/0.86  
% 0.82/0.86  --qbf_mode                              false
% 0.82/0.86  --qbf_elim_univ                         false
% 0.82/0.86  --qbf_dom_inst                          none
% 0.82/0.86  --qbf_dom_pre_inst                      false
% 0.82/0.86  --qbf_sk_in                             false
% 0.82/0.86  --qbf_pred_elim                         true
% 0.82/0.86  --qbf_split                             512
% 0.82/0.86  
% 0.82/0.86  ------ BMC1 Options
% 0.82/0.86  
% 0.82/0.86  --bmc1_incremental                      false
% 0.82/0.86  --bmc1_axioms                           reachable_all
% 0.82/0.86  --bmc1_min_bound                        0
% 0.82/0.86  --bmc1_max_bound                        -1
% 0.82/0.86  --bmc1_max_bound_default                -1
% 0.82/0.86  --bmc1_symbol_reachability              true
% 0.82/0.86  --bmc1_property_lemmas                  false
% 0.82/0.86  --bmc1_k_induction                      false
% 0.82/0.86  --bmc1_non_equiv_states                 false
% 0.82/0.86  --bmc1_deadlock                         false
% 0.82/0.86  --bmc1_ucm                              false
% 0.82/0.86  --bmc1_add_unsat_core                   none
% 0.82/0.86  --bmc1_unsat_core_children              false
% 0.82/0.86  --bmc1_unsat_core_extrapolate_axioms    false
% 0.82/0.86  --bmc1_out_stat                         full
% 0.82/0.86  --bmc1_ground_init                      false
% 0.82/0.86  --bmc1_pre_inst_next_state              false
% 0.82/0.86  --bmc1_pre_inst_state                   false
% 0.82/0.86  --bmc1_pre_inst_reach_state             false
% 0.82/0.86  --bmc1_out_unsat_core                   false
% 0.82/0.86  --bmc1_aig_witness_out                  false
% 0.82/0.86  --bmc1_verbose                          false
% 0.82/0.86  --bmc1_dump_clauses_tptp                false
% 0.82/0.86  --bmc1_dump_unsat_core_tptp             false
% 0.82/0.86  --bmc1_dump_file                        -
% 0.82/0.86  --bmc1_ucm_expand_uc_limit              128
% 0.82/0.86  --bmc1_ucm_n_expand_iterations          6
% 0.82/0.86  --bmc1_ucm_extend_mode                  1
% 0.82/0.86  --bmc1_ucm_init_mode                    2
% 0.82/0.86  --bmc1_ucm_cone_mode                    none
% 0.82/0.86  --bmc1_ucm_reduced_relation_type        0
% 0.82/0.86  --bmc1_ucm_relax_model                  4
% 0.82/0.86  --bmc1_ucm_full_tr_after_sat            true
% 0.82/0.86  --bmc1_ucm_expand_neg_assumptions       false
% 0.82/0.86  --bmc1_ucm_layered_model                none
% 0.82/0.86  --bmc1_ucm_max_lemma_size               10
% 0.82/0.86  
% 0.82/0.86  ------ AIG Options
% 0.82/0.86  
% 0.82/0.86  --aig_mode                              false
% 0.82/0.86  
% 0.82/0.86  ------ Instantiation Options
% 0.82/0.86  
% 0.82/0.86  --instantiation_flag                    true
% 0.82/0.86  --inst_sos_flag                         false
% 0.82/0.86  --inst_sos_phase                        true
% 0.82/0.86  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.82/0.86  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.82/0.86  --inst_lit_sel_side                     num_symb
% 0.82/0.86  --inst_solver_per_active                1400
% 0.82/0.86  --inst_solver_calls_frac                1.
% 0.82/0.86  --inst_passive_queue_type               priority_queues
% 0.82/0.86  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.82/0.86  --inst_passive_queues_freq              [25;2]
% 0.82/0.86  --inst_dismatching                      true
% 0.82/0.86  --inst_eager_unprocessed_to_passive     true
% 0.82/0.86  --inst_prop_sim_given                   true
% 0.82/0.86  --inst_prop_sim_new                     false
% 0.82/0.86  --inst_subs_new                         false
% 0.82/0.86  --inst_eq_res_simp                      false
% 0.82/0.86  --inst_subs_given                       false
% 0.82/0.86  --inst_orphan_elimination               true
% 0.82/0.86  --inst_learning_loop_flag               true
% 0.82/0.86  --inst_learning_start                   3000
% 0.82/0.86  --inst_learning_factor                  2
% 0.82/0.86  --inst_start_prop_sim_after_learn       3
% 0.82/0.86  --inst_sel_renew                        solver
% 0.82/0.86  --inst_lit_activity_flag                true
% 0.82/0.86  --inst_restr_to_given                   false
% 0.82/0.86  --inst_activity_threshold               500
% 0.82/0.86  --inst_out_proof                        true
% 0.82/0.86  
% 0.82/0.86  ------ Resolution Options
% 0.82/0.86  
% 0.82/0.86  --resolution_flag                       true
% 0.82/0.86  --res_lit_sel                           adaptive
% 0.82/0.86  --res_lit_sel_side                      none
% 0.82/0.86  --res_ordering                          kbo
% 0.82/0.86  --res_to_prop_solver                    active
% 0.82/0.86  --res_prop_simpl_new                    false
% 0.82/0.86  --res_prop_simpl_given                  true
% 0.82/0.86  --res_passive_queue_type                priority_queues
% 0.82/0.86  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.82/0.86  --res_passive_queues_freq               [15;5]
% 0.82/0.86  --res_forward_subs                      full
% 0.82/0.86  --res_backward_subs                     full
% 0.82/0.86  --res_forward_subs_resolution           true
% 0.82/0.86  --res_backward_subs_resolution          true
% 0.82/0.86  --res_orphan_elimination                true
% 0.82/0.86  --res_time_limit                        2.
% 0.82/0.86  --res_out_proof                         true
% 0.82/0.86  
% 0.82/0.86  ------ Superposition Options
% 0.82/0.86  
% 0.82/0.86  --superposition_flag                    true
% 0.82/0.86  --sup_passive_queue_type                priority_queues
% 0.82/0.86  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.82/0.86  --sup_passive_queues_freq               [8;1;4]
% 0.82/0.86  --demod_completeness_check              fast
% 0.82/0.86  --demod_use_ground                      true
% 0.82/0.86  --sup_to_prop_solver                    passive
% 0.82/0.86  --sup_prop_simpl_new                    true
% 0.82/0.86  --sup_prop_simpl_given                  true
% 0.82/0.86  --sup_fun_splitting                     false
% 0.82/0.86  --sup_smt_interval                      50000
% 0.82/0.86  
% 0.82/0.86  ------ Superposition Simplification Setup
% 0.82/0.86  
% 0.82/0.86  --sup_indices_passive                   []
% 0.82/0.86  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.82/0.86  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.82/0.86  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.82/0.86  --sup_full_triv                         [TrivRules;PropSubs]
% 0.82/0.86  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.82/0.86  --sup_full_bw                           [BwDemod]
% 0.82/0.86  --sup_immed_triv                        [TrivRules]
% 0.82/0.86  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.82/0.86  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.82/0.86  --sup_immed_bw_main                     []
% 0.82/0.86  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.82/0.86  --sup_input_triv                        [Unflattening;TrivRules]
% 0.82/0.86  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.82/0.86  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.82/0.86  
% 0.82/0.86  ------ Combination Options
% 0.82/0.86  
% 0.82/0.86  --comb_res_mult                         3
% 0.82/0.86  --comb_sup_mult                         2
% 0.82/0.86  --comb_inst_mult                        10
% 0.82/0.86  
% 0.82/0.86  ------ Debug Options
% 0.82/0.86  
% 0.82/0.86  --dbg_backtrace                         false
% 0.82/0.86  --dbg_dump_prop_clauses                 false
% 0.82/0.86  --dbg_dump_prop_clauses_file            -
% 0.82/0.86  --dbg_out_stat                          false
% 0.82/0.86  ------ Parsing...
% 0.82/0.86  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.82/0.86  
% 0.82/0.86  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 0.82/0.86  
% 0.82/0.86  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.82/0.86  
% 0.82/0.86  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.82/0.86  ------ Proving...
% 0.82/0.86  ------ Problem Properties 
% 0.82/0.86  
% 0.82/0.86  
% 0.82/0.86  clauses                                 13
% 0.82/0.86  conjectures                             2
% 0.82/0.86  EPR                                     1
% 0.82/0.86  Horn                                    10
% 0.82/0.86  unary                                   7
% 0.82/0.86  binary                                  0
% 0.82/0.86  lits                                    28
% 0.82/0.86  lits eq                                 17
% 0.82/0.86  fd_pure                                 0
% 0.82/0.86  fd_pseudo                               0
% 0.82/0.86  fd_cond                                 0
% 0.82/0.86  fd_pseudo_cond                          4
% 0.82/0.86  AC symbols                              0
% 0.82/0.86  
% 0.82/0.86  ------ Schedule dynamic 5 is on 
% 0.82/0.86  
% 0.82/0.86  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.82/0.86  
% 0.82/0.86  
% 0.82/0.86  ------ 
% 0.82/0.86  Current options:
% 0.82/0.86  ------ 
% 0.82/0.86  
% 0.82/0.86  ------ Input Options
% 0.82/0.86  
% 0.82/0.86  --out_options                           all
% 0.82/0.86  --tptp_safe_out                         true
% 0.82/0.86  --problem_path                          ""
% 0.82/0.86  --include_path                          ""
% 0.82/0.86  --clausifier                            res/vclausify_rel
% 0.82/0.86  --clausifier_options                    --mode clausify
% 0.82/0.86  --stdin                                 false
% 0.82/0.86  --stats_out                             all
% 0.82/0.86  
% 0.82/0.86  ------ General Options
% 0.82/0.86  
% 0.82/0.86  --fof                                   false
% 0.82/0.86  --time_out_real                         305.
% 0.82/0.86  --time_out_virtual                      -1.
% 0.82/0.86  --symbol_type_check                     false
% 0.82/0.86  --clausify_out                          false
% 0.82/0.86  --sig_cnt_out                           false
% 0.82/0.86  --trig_cnt_out                          false
% 0.82/0.86  --trig_cnt_out_tolerance                1.
% 0.82/0.86  --trig_cnt_out_sk_spl                   false
% 0.82/0.86  --abstr_cl_out                          false
% 0.82/0.86  
% 0.82/0.86  ------ Global Options
% 0.82/0.86  
% 0.82/0.86  --schedule                              default
% 0.82/0.86  --add_important_lit                     false
% 0.82/0.86  --prop_solver_per_cl                    1000
% 0.82/0.86  --min_unsat_core                        false
% 0.82/0.86  --soft_assumptions                      false
% 0.82/0.86  --soft_lemma_size                       3
% 0.82/0.86  --prop_impl_unit_size                   0
% 0.82/0.86  --prop_impl_unit                        []
% 0.82/0.86  --share_sel_clauses                     true
% 0.82/0.86  --reset_solvers                         false
% 0.82/0.86  --bc_imp_inh                            [conj_cone]
% 0.82/0.86  --conj_cone_tolerance                   3.
% 0.82/0.86  --extra_neg_conj                        none
% 0.82/0.86  --large_theory_mode                     true
% 0.82/0.86  --prolific_symb_bound                   200
% 0.82/0.86  --lt_threshold                          2000
% 0.82/0.86  --clause_weak_htbl                      true
% 0.82/0.86  --gc_record_bc_elim                     false
% 0.82/0.86  
% 0.82/0.86  ------ Preprocessing Options
% 0.82/0.86  
% 0.82/0.86  --preprocessing_flag                    true
% 0.82/0.86  --time_out_prep_mult                    0.1
% 0.82/0.86  --splitting_mode                        input
% 0.82/0.86  --splitting_grd                         true
% 0.82/0.86  --splitting_cvd                         false
% 0.82/0.86  --splitting_cvd_svl                     false
% 0.82/0.86  --splitting_nvd                         32
% 0.82/0.86  --sub_typing                            true
% 0.82/0.86  --prep_gs_sim                           true
% 0.82/0.86  --prep_unflatten                        true
% 0.82/0.86  --prep_res_sim                          true
% 0.82/0.86  --prep_upred                            true
% 0.82/0.86  --prep_sem_filter                       exhaustive
% 0.82/0.86  --prep_sem_filter_out                   false
% 0.82/0.86  --pred_elim                             true
% 0.82/0.86  --res_sim_input                         true
% 0.82/0.86  --eq_ax_congr_red                       true
% 0.82/0.86  --pure_diseq_elim                       true
% 0.82/0.86  --brand_transform                       false
% 0.82/0.86  --non_eq_to_eq                          false
% 0.82/0.86  --prep_def_merge                        true
% 0.82/0.86  --prep_def_merge_prop_impl              false
% 0.82/0.86  --prep_def_merge_mbd                    true
% 0.82/0.86  --prep_def_merge_tr_red                 false
% 0.82/0.86  --prep_def_merge_tr_cl                  false
% 0.82/0.86  --smt_preprocessing                     true
% 0.82/0.86  --smt_ac_axioms                         fast
% 0.82/0.86  --preprocessed_out                      false
% 0.82/0.86  --preprocessed_stats                    false
% 0.82/0.86  
% 0.82/0.86  ------ Abstraction refinement Options
% 0.82/0.86  
% 0.82/0.86  --abstr_ref                             []
% 0.82/0.86  --abstr_ref_prep                        false
% 0.82/0.86  --abstr_ref_until_sat                   false
% 0.82/0.86  --abstr_ref_sig_restrict                funpre
% 0.82/0.86  --abstr_ref_af_restrict_to_split_sk     false
% 0.82/0.86  --abstr_ref_under                       []
% 0.82/0.86  
% 0.82/0.86  ------ SAT Options
% 0.82/0.86  
% 0.82/0.86  --sat_mode                              false
% 0.82/0.86  --sat_fm_restart_options                ""
% 0.82/0.86  --sat_gr_def                            false
% 0.82/0.86  --sat_epr_types                         true
% 0.82/0.86  --sat_non_cyclic_types                  false
% 0.82/0.86  --sat_finite_models                     false
% 0.82/0.86  --sat_fm_lemmas                         false
% 0.82/0.86  --sat_fm_prep                           false
% 0.82/0.86  --sat_fm_uc_incr                        true
% 0.82/0.86  --sat_out_model                         small
% 0.82/0.86  --sat_out_clauses                       false
% 0.82/0.86  
% 0.82/0.86  ------ QBF Options
% 0.82/0.86  
% 0.82/0.86  --qbf_mode                              false
% 0.82/0.86  --qbf_elim_univ                         false
% 0.82/0.86  --qbf_dom_inst                          none
% 0.82/0.86  --qbf_dom_pre_inst                      false
% 0.82/0.86  --qbf_sk_in                             false
% 0.82/0.86  --qbf_pred_elim                         true
% 0.82/0.86  --qbf_split                             512
% 0.82/0.86  
% 0.82/0.86  ------ BMC1 Options
% 0.82/0.86  
% 0.82/0.86  --bmc1_incremental                      false
% 0.82/0.86  --bmc1_axioms                           reachable_all
% 0.82/0.86  --bmc1_min_bound                        0
% 0.82/0.86  --bmc1_max_bound                        -1
% 0.82/0.86  --bmc1_max_bound_default                -1
% 0.82/0.86  --bmc1_symbol_reachability              true
% 0.82/0.86  --bmc1_property_lemmas                  false
% 0.82/0.86  --bmc1_k_induction                      false
% 0.82/0.86  --bmc1_non_equiv_states                 false
% 0.82/0.86  --bmc1_deadlock                         false
% 0.82/0.86  --bmc1_ucm                              false
% 0.82/0.86  --bmc1_add_unsat_core                   none
% 0.82/0.86  --bmc1_unsat_core_children              false
% 0.82/0.86  --bmc1_unsat_core_extrapolate_axioms    false
% 0.82/0.86  --bmc1_out_stat                         full
% 0.82/0.86  --bmc1_ground_init                      false
% 0.82/0.86  --bmc1_pre_inst_next_state              false
% 0.82/0.86  --bmc1_pre_inst_state                   false
% 0.82/0.86  --bmc1_pre_inst_reach_state             false
% 0.82/0.86  --bmc1_out_unsat_core                   false
% 0.82/0.86  --bmc1_aig_witness_out                  false
% 0.82/0.86  --bmc1_verbose                          false
% 0.82/0.86  --bmc1_dump_clauses_tptp                false
% 0.82/0.86  --bmc1_dump_unsat_core_tptp             false
% 0.82/0.86  --bmc1_dump_file                        -
% 0.82/0.86  --bmc1_ucm_expand_uc_limit              128
% 0.82/0.86  --bmc1_ucm_n_expand_iterations          6
% 0.82/0.86  --bmc1_ucm_extend_mode                  1
% 0.82/0.86  --bmc1_ucm_init_mode                    2
% 0.82/0.86  --bmc1_ucm_cone_mode                    none
% 0.82/0.86  --bmc1_ucm_reduced_relation_type        0
% 0.82/0.86  --bmc1_ucm_relax_model                  4
% 0.82/0.86  --bmc1_ucm_full_tr_after_sat            true
% 0.82/0.86  --bmc1_ucm_expand_neg_assumptions       false
% 0.82/0.86  --bmc1_ucm_layered_model                none
% 0.82/0.86  --bmc1_ucm_max_lemma_size               10
% 0.82/0.86  
% 0.82/0.86  ------ AIG Options
% 0.82/0.86  
% 0.82/0.86  --aig_mode                              false
% 0.82/0.86  
% 0.82/0.86  ------ Instantiation Options
% 0.82/0.86  
% 0.82/0.86  --instantiation_flag                    true
% 0.82/0.86  --inst_sos_flag                         false
% 0.82/0.86  --inst_sos_phase                        true
% 0.82/0.86  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.82/0.86  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.82/0.86  --inst_lit_sel_side                     none
% 0.82/0.86  --inst_solver_per_active                1400
% 0.82/0.86  --inst_solver_calls_frac                1.
% 0.82/0.86  --inst_passive_queue_type               priority_queues
% 0.82/0.86  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.82/0.86  --inst_passive_queues_freq              [25;2]
% 0.82/0.86  --inst_dismatching                      true
% 0.82/0.86  --inst_eager_unprocessed_to_passive     true
% 0.82/0.86  --inst_prop_sim_given                   true
% 0.82/0.86  --inst_prop_sim_new                     false
% 0.82/0.86  --inst_subs_new                         false
% 0.82/0.86  --inst_eq_res_simp                      false
% 0.82/0.86  --inst_subs_given                       false
% 0.82/0.86  --inst_orphan_elimination               true
% 0.82/0.86  --inst_learning_loop_flag               true
% 0.82/0.86  --inst_learning_start                   3000
% 0.82/0.86  --inst_learning_factor                  2
% 0.82/0.86  --inst_start_prop_sim_after_learn       3
% 0.82/0.86  --inst_sel_renew                        solver
% 0.82/0.86  --inst_lit_activity_flag                true
% 0.82/0.86  --inst_restr_to_given                   false
% 0.82/0.86  --inst_activity_threshold               500
% 0.82/0.86  --inst_out_proof                        true
% 0.82/0.86  
% 0.82/0.86  ------ Resolution Options
% 0.82/0.86  
% 0.82/0.86  --resolution_flag                       false
% 0.82/0.86  --res_lit_sel                           adaptive
% 0.82/0.86  --res_lit_sel_side                      none
% 0.82/0.86  --res_ordering                          kbo
% 0.82/0.86  --res_to_prop_solver                    active
% 0.82/0.86  --res_prop_simpl_new                    false
% 0.82/0.86  --res_prop_simpl_given                  true
% 0.82/0.86  --res_passive_queue_type                priority_queues
% 0.82/0.86  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.82/0.86  --res_passive_queues_freq               [15;5]
% 0.82/0.86  --res_forward_subs                      full
% 0.82/0.86  --res_backward_subs                     full
% 0.82/0.86  --res_forward_subs_resolution           true
% 0.82/0.86  --res_backward_subs_resolution          true
% 0.82/0.86  --res_orphan_elimination                true
% 0.82/0.86  --res_time_limit                        2.
% 0.82/0.86  --res_out_proof                         true
% 0.82/0.86  
% 0.82/0.86  ------ Superposition Options
% 0.82/0.86  
% 0.82/0.86  --superposition_flag                    true
% 0.82/0.86  --sup_passive_queue_type                priority_queues
% 0.82/0.86  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.82/0.86  --sup_passive_queues_freq               [8;1;4]
% 0.82/0.86  --demod_completeness_check              fast
% 0.82/0.86  --demod_use_ground                      true
% 0.82/0.86  --sup_to_prop_solver                    passive
% 0.82/0.86  --sup_prop_simpl_new                    true
% 0.82/0.86  --sup_prop_simpl_given                  true
% 0.82/0.86  --sup_fun_splitting                     false
% 0.82/0.86  --sup_smt_interval                      50000
% 0.82/0.86  
% 0.82/0.86  ------ Superposition Simplification Setup
% 0.82/0.86  
% 0.82/0.86  --sup_indices_passive                   []
% 0.82/0.86  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.82/0.86  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.82/0.86  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.82/0.86  --sup_full_triv                         [TrivRules;PropSubs]
% 0.82/0.86  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.82/0.86  --sup_full_bw                           [BwDemod]
% 0.82/0.86  --sup_immed_triv                        [TrivRules]
% 0.82/0.86  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.82/0.86  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.82/0.86  --sup_immed_bw_main                     []
% 0.82/0.86  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.82/0.86  --sup_input_triv                        [Unflattening;TrivRules]
% 0.82/0.86  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.82/0.86  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.82/0.86  
% 0.82/0.86  ------ Combination Options
% 0.82/0.86  
% 0.82/0.86  --comb_res_mult                         3
% 0.82/0.86  --comb_sup_mult                         2
% 0.82/0.86  --comb_inst_mult                        10
% 0.82/0.86  
% 0.82/0.86  ------ Debug Options
% 0.82/0.86  
% 0.82/0.86  --dbg_backtrace                         false
% 0.82/0.86  --dbg_dump_prop_clauses                 false
% 0.82/0.86  --dbg_dump_prop_clauses_file            -
% 0.82/0.86  --dbg_out_stat                          false
% 0.82/0.86  
% 0.82/0.86  
% 0.82/0.86  
% 0.82/0.86  
% 0.82/0.86  ------ Proving...
% 0.82/0.86  
% 0.82/0.86  
% 0.82/0.86  % SZS status Theorem for theBenchmark.p
% 0.82/0.86  
% 0.82/0.86   Resolution empty clause
% 0.82/0.86  
% 0.82/0.86  % SZS output start CNFRefutation for theBenchmark.p
% 0.82/0.86  
% 0.82/0.86  fof(f1,axiom,(
% 0.82/0.86    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.82/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.82/0.86  
% 0.82/0.86  fof(f23,plain,(
% 0.82/0.86    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.82/0.86    inference(cnf_transformation,[],[f1])).
% 0.82/0.86  
% 0.82/0.86  fof(f9,conjecture,(
% 0.82/0.86    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 0.82/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.82/0.86  
% 0.82/0.86  fof(f10,negated_conjecture,(
% 0.82/0.86    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 0.82/0.86    inference(negated_conjecture,[],[f9])).
% 0.82/0.86  
% 0.82/0.86  fof(f14,plain,(
% 0.82/0.86    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 0.82/0.86    inference(ennf_transformation,[],[f10])).
% 0.82/0.86  
% 0.82/0.86  fof(f15,plain,(
% 0.82/0.86    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 0.82/0.86    inference(flattening,[],[f14])).
% 0.82/0.86  
% 0.82/0.86  fof(f21,plain,(
% 0.82/0.86    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (k1_funct_1(sK4,sK3) != sK2 & r2_hidden(sK3,sK1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2)))) & v1_funct_2(sK4,sK1,k1_tarski(sK2)) & v1_funct_1(sK4))),
% 0.82/0.86    introduced(choice_axiom,[])).
% 0.82/0.86  
% 0.82/0.86  fof(f22,plain,(
% 0.82/0.86    k1_funct_1(sK4,sK3) != sK2 & r2_hidden(sK3,sK1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2)))) & v1_funct_2(sK4,sK1,k1_tarski(sK2)) & v1_funct_1(sK4)),
% 0.82/0.86    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f15,f21])).
% 0.82/0.86  
% 0.82/0.86  fof(f39,plain,(
% 0.82/0.86    v1_funct_2(sK4,sK1,k1_tarski(sK2))),
% 0.82/0.86    inference(cnf_transformation,[],[f22])).
% 0.82/0.86  
% 0.82/0.86  fof(f3,axiom,(
% 0.82/0.86    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.82/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.82/0.86  
% 0.82/0.86  fof(f32,plain,(
% 0.82/0.86    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.82/0.86    inference(cnf_transformation,[],[f3])).
% 0.82/0.86  
% 0.82/0.86  fof(f4,axiom,(
% 0.82/0.86    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.82/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.82/0.86  
% 0.82/0.86  fof(f33,plain,(
% 0.82/0.86    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.82/0.86    inference(cnf_transformation,[],[f4])).
% 0.82/0.86  
% 0.82/0.86  fof(f5,axiom,(
% 0.82/0.86    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.82/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.82/0.86  
% 0.82/0.86  fof(f34,plain,(
% 0.82/0.86    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.82/0.86    inference(cnf_transformation,[],[f5])).
% 0.82/0.86  
% 0.82/0.86  fof(f6,axiom,(
% 0.82/0.86    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.82/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.82/0.86  
% 0.82/0.86  fof(f35,plain,(
% 0.82/0.86    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 0.82/0.86    inference(cnf_transformation,[],[f6])).
% 0.82/0.86  
% 0.82/0.86  fof(f43,plain,(
% 0.82/0.86    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.82/0.86    inference(definition_unfolding,[],[f34,f35])).
% 0.82/0.86  
% 0.82/0.86  fof(f44,plain,(
% 0.82/0.86    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.82/0.86    inference(definition_unfolding,[],[f33,f43])).
% 0.82/0.86  
% 0.82/0.86  fof(f45,plain,(
% 0.82/0.86    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.82/0.86    inference(definition_unfolding,[],[f32,f44])).
% 0.82/0.86  
% 0.82/0.86  fof(f56,plain,(
% 0.82/0.86    v1_funct_2(sK4,sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2))),
% 0.82/0.86    inference(definition_unfolding,[],[f39,f45])).
% 0.82/0.86  
% 0.82/0.86  fof(f8,axiom,(
% 0.82/0.86    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 0.82/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.82/0.86  
% 0.82/0.86  fof(f12,plain,(
% 0.82/0.86    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.82/0.86    inference(ennf_transformation,[],[f8])).
% 0.82/0.86  
% 0.82/0.86  fof(f13,plain,(
% 0.82/0.86    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.82/0.86    inference(flattening,[],[f12])).
% 0.82/0.86  
% 0.82/0.86  fof(f37,plain,(
% 0.82/0.86    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.82/0.86    inference(cnf_transformation,[],[f13])).
% 0.82/0.86  
% 0.82/0.86  fof(f40,plain,(
% 0.82/0.86    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))))),
% 0.82/0.86    inference(cnf_transformation,[],[f22])).
% 0.82/0.86  
% 0.82/0.86  fof(f55,plain,(
% 0.82/0.86    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2))))),
% 0.82/0.86    inference(definition_unfolding,[],[f40,f45])).
% 0.82/0.86  
% 0.82/0.86  fof(f38,plain,(
% 0.82/0.86    v1_funct_1(sK4)),
% 0.82/0.86    inference(cnf_transformation,[],[f22])).
% 0.82/0.86  
% 0.82/0.86  fof(f41,plain,(
% 0.82/0.86    r2_hidden(sK3,sK1)),
% 0.82/0.86    inference(cnf_transformation,[],[f22])).
% 0.82/0.86  
% 0.82/0.86  fof(f42,plain,(
% 0.82/0.86    k1_funct_1(sK4,sK3) != sK2),
% 0.82/0.86    inference(cnf_transformation,[],[f22])).
% 0.82/0.86  
% 0.82/0.86  fof(f2,axiom,(
% 0.82/0.86    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.82/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.82/0.86  
% 0.82/0.86  fof(f11,plain,(
% 0.82/0.86    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.82/0.86    inference(ennf_transformation,[],[f2])).
% 0.82/0.86  
% 0.82/0.86  fof(f16,plain,(
% 0.82/0.86    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.82/0.86    inference(nnf_transformation,[],[f11])).
% 0.82/0.86  
% 0.82/0.86  fof(f17,plain,(
% 0.82/0.86    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.82/0.86    inference(flattening,[],[f16])).
% 0.82/0.86  
% 0.82/0.86  fof(f18,plain,(
% 0.82/0.86    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.82/0.86    inference(rectify,[],[f17])).
% 0.82/0.86  
% 0.82/0.86  fof(f19,plain,(
% 0.82/0.86    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3))))),
% 0.82/0.86    introduced(choice_axiom,[])).
% 0.82/0.86  
% 0.82/0.86  fof(f20,plain,(
% 0.82/0.86    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.82/0.86    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).
% 0.82/0.86  
% 0.82/0.86  fof(f24,plain,(
% 0.82/0.86    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.82/0.86    inference(cnf_transformation,[],[f20])).
% 0.82/0.86  
% 0.82/0.86  fof(f53,plain,(
% 0.82/0.86    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 0.82/0.86    inference(definition_unfolding,[],[f24,f43])).
% 0.82/0.86  
% 0.82/0.86  fof(f63,plain,(
% 0.82/0.86    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X2))) )),
% 0.82/0.86    inference(equality_resolution,[],[f53])).
% 0.82/0.86  
% 0.82/0.86  fof(f7,axiom,(
% 0.82/0.86    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.82/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.82/0.86  
% 0.82/0.86  fof(f36,plain,(
% 0.82/0.86    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 0.82/0.86    inference(cnf_transformation,[],[f7])).
% 0.82/0.86  
% 0.82/0.86  fof(f54,plain,(
% 0.82/0.86    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)) )),
% 0.82/0.86    inference(definition_unfolding,[],[f36,f45])).
% 0.82/0.86  
% 0.82/0.86  cnf(c_0,plain,
% 0.82/0.86      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 0.82/0.86      inference(cnf_transformation,[],[f23]) ).
% 0.82/0.86  
% 0.82/0.86  cnf(c_14,negated_conjecture,
% 0.82/0.86      ( v1_funct_2(sK4,sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
% 0.82/0.86      inference(cnf_transformation,[],[f56]) ).
% 0.82/0.86  
% 0.82/0.86  cnf(c_10,plain,
% 0.82/0.86      ( ~ v1_funct_2(X0,X1,X2)
% 0.82/0.86      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.82/0.86      | ~ r2_hidden(X3,X1)
% 0.82/0.86      | r2_hidden(k1_funct_1(X0,X3),X2)
% 0.82/0.86      | ~ v1_funct_1(X0)
% 0.82/0.86      | k1_xboole_0 = X2 ),
% 0.82/0.86      inference(cnf_transformation,[],[f37]) ).
% 0.82/0.86  
% 0.82/0.86  cnf(c_13,negated_conjecture,
% 0.82/0.86      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2)))) ),
% 0.82/0.86      inference(cnf_transformation,[],[f55]) ).
% 0.82/0.86  
% 0.82/0.86  cnf(c_144,plain,
% 0.82/0.86      ( ~ v1_funct_2(X0,X1,X2)
% 0.82/0.86      | ~ r2_hidden(X3,X1)
% 0.82/0.86      | r2_hidden(k1_funct_1(X0,X3),X2)
% 0.82/0.86      | ~ v1_funct_1(X0)
% 0.82/0.86      | k1_zfmisc_1(k2_zfmisc_1(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 0.82/0.86      | sK4 != X0
% 0.82/0.86      | k1_xboole_0 = X2 ),
% 0.82/0.86      inference(resolution_lifted,[status(thm)],[c_10,c_13]) ).
% 0.82/0.86  
% 0.82/0.86  cnf(c_145,plain,
% 0.82/0.86      ( ~ v1_funct_2(sK4,X0,X1)
% 0.82/0.86      | ~ r2_hidden(X2,X0)
% 0.82/0.86      | r2_hidden(k1_funct_1(sK4,X2),X1)
% 0.82/0.86      | ~ v1_funct_1(sK4)
% 0.82/0.86      | k1_zfmisc_1(k2_zfmisc_1(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 0.82/0.86      | k1_xboole_0 = X1 ),
% 0.82/0.86      inference(unflattening,[status(thm)],[c_144]) ).
% 0.82/0.86  
% 0.82/0.86  cnf(c_15,negated_conjecture,
% 0.82/0.86      ( v1_funct_1(sK4) ),
% 0.82/0.86      inference(cnf_transformation,[],[f38]) ).
% 0.82/0.86  
% 0.82/0.86  cnf(c_149,plain,
% 0.82/0.86      ( r2_hidden(k1_funct_1(sK4,X2),X1)
% 0.82/0.86      | ~ r2_hidden(X2,X0)
% 0.82/0.86      | ~ v1_funct_2(sK4,X0,X1)
% 0.82/0.86      | k1_zfmisc_1(k2_zfmisc_1(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 0.82/0.86      | k1_xboole_0 = X1 ),
% 0.82/0.86      inference(global_propositional_subsumption,[status(thm)],[c_145,c_15]) ).
% 0.82/0.86  
% 0.82/0.86  cnf(c_150,plain,
% 0.82/0.86      ( ~ v1_funct_2(sK4,X0,X1)
% 0.82/0.86      | ~ r2_hidden(X2,X0)
% 0.82/0.86      | r2_hidden(k1_funct_1(sK4,X2),X1)
% 0.82/0.86      | k1_zfmisc_1(k2_zfmisc_1(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 0.82/0.86      | k1_xboole_0 = X1 ),
% 0.82/0.86      inference(renaming,[status(thm)],[c_149]) ).
% 0.82/0.86  
% 0.82/0.86  cnf(c_177,plain,
% 0.82/0.86      ( ~ r2_hidden(X0,X1)
% 0.82/0.86      | r2_hidden(k1_funct_1(sK4,X0),X2)
% 0.82/0.86      | k3_enumset1(sK2,sK2,sK2,sK2,sK2) != X2
% 0.82/0.86      | k1_zfmisc_1(k2_zfmisc_1(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 0.82/0.86      | sK1 != X1
% 0.82/0.86      | sK4 != sK4
% 0.82/0.86      | k1_xboole_0 = X2 ),
% 0.82/0.86      inference(resolution_lifted,[status(thm)],[c_14,c_150]) ).
% 0.82/0.86  
% 0.82/0.86  cnf(c_178,plain,
% 0.82/0.86      ( ~ r2_hidden(X0,sK1)
% 0.82/0.86      | r2_hidden(k1_funct_1(sK4,X0),k3_enumset1(sK2,sK2,sK2,sK2,sK2))
% 0.82/0.86      | k1_zfmisc_1(k2_zfmisc_1(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2)))
% 0.82/0.86      | k1_xboole_0 = k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
% 0.82/0.86      inference(unflattening,[status(thm)],[c_177]) ).
% 0.82/0.86  
% 0.82/0.86  cnf(c_210,plain,
% 0.82/0.86      ( ~ r2_hidden(X0,sK1)
% 0.82/0.86      | r2_hidden(k1_funct_1(sK4,X0),k3_enumset1(sK2,sK2,sK2,sK2,sK2))
% 0.82/0.86      | k1_xboole_0 = k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
% 0.82/0.86      inference(equality_resolution_simp,[status(thm)],[c_178]) ).
% 0.82/0.86  
% 0.82/0.86  cnf(c_436,plain,
% 0.82/0.86      ( k1_xboole_0 = k3_enumset1(sK2,sK2,sK2,sK2,sK2)
% 0.82/0.86      | r2_hidden(X0,sK1) != iProver_top
% 0.82/0.86      | r2_hidden(k1_funct_1(sK4,X0),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
% 0.82/0.86      inference(predicate_to_equality,[status(thm)],[c_210]) ).
% 0.82/0.86  
% 0.82/0.86  cnf(c_12,negated_conjecture,
% 0.82/0.86      ( r2_hidden(sK3,sK1) ),
% 0.82/0.86      inference(cnf_transformation,[],[f41]) ).
% 0.82/0.86  
% 0.82/0.86  cnf(c_11,negated_conjecture,
% 0.82/0.86      ( k1_funct_1(sK4,sK3) != sK2 ),
% 0.82/0.86      inference(cnf_transformation,[],[f42]) ).
% 0.82/0.86  
% 0.82/0.86  cnf(c_523,plain,
% 0.82/0.86      ( r2_hidden(k1_funct_1(sK4,sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2))
% 0.82/0.86      | ~ r2_hidden(sK3,sK1)
% 0.82/0.86      | k1_xboole_0 = k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
% 0.82/0.86      inference(instantiation,[status(thm)],[c_210]) ).
% 0.82/0.86  
% 0.82/0.86  cnf(c_8,plain,
% 0.82/0.86      ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X3))
% 0.82/0.86      | X0 = X1
% 0.82/0.86      | X0 = X2
% 0.82/0.86      | X0 = X3 ),
% 0.82/0.86      inference(cnf_transformation,[],[f63]) ).
% 0.82/0.86  
% 0.82/0.86  cnf(c_553,plain,
% 0.82/0.86      ( ~ r2_hidden(k1_funct_1(sK4,sK3),k3_enumset1(sK2,sK2,sK2,X0,X1))
% 0.82/0.86      | k1_funct_1(sK4,sK3) = X0
% 0.82/0.86      | k1_funct_1(sK4,sK3) = X1
% 0.82/0.86      | k1_funct_1(sK4,sK3) = sK2 ),
% 0.82/0.86      inference(instantiation,[status(thm)],[c_8]) ).
% 0.82/0.86  
% 0.82/0.86  cnf(c_555,plain,
% 0.82/0.86      ( ~ r2_hidden(k1_funct_1(sK4,sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2))
% 0.82/0.86      | k1_funct_1(sK4,sK3) = sK2 ),
% 0.82/0.86      inference(instantiation,[status(thm)],[c_553]) ).
% 0.82/0.86  
% 0.82/0.86  cnf(c_559,plain,
% 0.82/0.86      ( k1_xboole_0 = k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
% 0.82/0.86      inference(global_propositional_subsumption,
% 0.82/0.86                [status(thm)],
% 0.82/0.86                [c_436,c_12,c_11,c_523,c_555]) ).
% 0.82/0.86  
% 0.82/0.86  cnf(c_9,plain,
% 0.82/0.86      ( k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) != k1_xboole_0 ),
% 0.82/0.86      inference(cnf_transformation,[],[f54]) ).
% 0.82/0.86  
% 0.82/0.86  cnf(c_911,plain,
% 0.82/0.86      ( k2_xboole_0(k1_xboole_0,X0) != k1_xboole_0 ),
% 0.82/0.86      inference(superposition,[status(thm)],[c_559,c_9]) ).
% 0.82/0.86  
% 0.82/0.86  cnf(c_1026,plain,
% 0.82/0.86      ( $false ),
% 0.82/0.86      inference(superposition,[status(thm)],[c_0,c_911]) ).
% 0.82/0.86  
% 0.82/0.86  
% 0.82/0.86  % SZS output end CNFRefutation for theBenchmark.p
% 0.82/0.86  
% 0.82/0.86  ------                               Statistics
% 0.82/0.86  
% 0.82/0.86  ------ General
% 0.82/0.86  
% 0.82/0.86  abstr_ref_over_cycles:                  0
% 0.82/0.86  abstr_ref_under_cycles:                 0
% 0.82/0.86  gc_basic_clause_elim:                   0
% 0.82/0.86  forced_gc_time:                         0
% 0.82/0.86  parsing_time:                           0.006
% 0.82/0.86  unif_index_cands_time:                  0.
% 0.82/0.86  unif_index_add_time:                    0.
% 0.82/0.86  orderings_time:                         0.
% 0.82/0.86  out_proof_time:                         0.009
% 0.82/0.86  total_time:                             0.055
% 0.82/0.86  num_of_symbols:                         46
% 0.82/0.86  num_of_terms:                           1246
% 0.82/0.86  
% 0.82/0.86  ------ Preprocessing
% 0.82/0.86  
% 0.82/0.86  num_of_splits:                          0
% 0.82/0.86  num_of_split_atoms:                     0
% 0.82/0.86  num_of_reused_defs:                     0
% 0.82/0.86  num_eq_ax_congr_red:                    12
% 0.82/0.86  num_of_sem_filtered_clauses:            1
% 0.82/0.86  num_of_subtypes:                        0
% 0.82/0.86  monotx_restored_types:                  0
% 0.82/0.86  sat_num_of_epr_types:                   0
% 0.82/0.86  sat_num_of_non_cyclic_types:            0
% 0.82/0.86  sat_guarded_non_collapsed_types:        0
% 0.82/0.86  num_pure_diseq_elim:                    0
% 0.82/0.86  simp_replaced_by:                       0
% 0.82/0.86  res_preprocessed:                       68
% 0.82/0.86  prep_upred:                             0
% 0.82/0.86  prep_unflattend:                        3
% 0.82/0.86  smt_new_axioms:                         0
% 0.82/0.86  pred_elim_cands:                        1
% 0.82/0.86  pred_elim:                              3
% 0.82/0.86  pred_elim_cl:                           3
% 0.82/0.86  pred_elim_cycles:                       5
% 0.82/0.86  merged_defs:                            0
% 0.82/0.86  merged_defs_ncl:                        0
% 0.82/0.86  bin_hyper_res:                          0
% 0.82/0.86  prep_cycles:                            4
% 0.82/0.86  pred_elim_time:                         0.001
% 0.82/0.86  splitting_time:                         0.
% 0.82/0.86  sem_filter_time:                        0.
% 0.82/0.86  monotx_time:                            0.
% 0.82/0.86  subtype_inf_time:                       0.
% 0.82/0.86  
% 0.82/0.86  ------ Problem properties
% 0.82/0.86  
% 0.82/0.86  clauses:                                13
% 0.82/0.86  conjectures:                            2
% 0.82/0.86  epr:                                    1
% 0.82/0.86  horn:                                   10
% 0.82/0.86  ground:                                 2
% 0.82/0.86  unary:                                  7
% 0.82/0.86  binary:                                 0
% 0.82/0.86  lits:                                   28
% 0.82/0.86  lits_eq:                                17
% 0.82/0.86  fd_pure:                                0
% 0.82/0.86  fd_pseudo:                              0
% 0.82/0.86  fd_cond:                                0
% 0.82/0.86  fd_pseudo_cond:                         4
% 0.82/0.86  ac_symbols:                             0
% 0.82/0.86  
% 0.82/0.86  ------ Propositional Solver
% 0.82/0.86  
% 0.82/0.86  prop_solver_calls:                      25
% 0.82/0.86  prop_fast_solver_calls:                 350
% 0.82/0.86  smt_solver_calls:                       0
% 0.82/0.86  smt_fast_solver_calls:                  0
% 0.82/0.86  prop_num_of_clauses:                    328
% 0.82/0.86  prop_preprocess_simplified:             2161
% 0.82/0.86  prop_fo_subsumed:                       3
% 0.82/0.86  prop_solver_time:                       0.
% 0.82/0.86  smt_solver_time:                        0.
% 0.82/0.86  smt_fast_solver_time:                   0.
% 0.82/0.86  prop_fast_solver_time:                  0.
% 0.82/0.86  prop_unsat_core_time:                   0.
% 0.82/0.86  
% 0.82/0.86  ------ QBF
% 0.82/0.86  
% 0.82/0.86  qbf_q_res:                              0
% 0.82/0.86  qbf_num_tautologies:                    0
% 0.82/0.86  qbf_prep_cycles:                        0
% 0.82/0.86  
% 0.82/0.86  ------ BMC1
% 0.82/0.86  
% 0.82/0.86  bmc1_current_bound:                     -1
% 0.82/0.86  bmc1_last_solved_bound:                 -1
% 0.82/0.86  bmc1_unsat_core_size:                   -1
% 0.82/0.86  bmc1_unsat_core_parents_size:           -1
% 0.82/0.86  bmc1_merge_next_fun:                    0
% 0.82/0.86  bmc1_unsat_core_clauses_time:           0.
% 0.82/0.86  
% 0.82/0.86  ------ Instantiation
% 0.82/0.86  
% 0.82/0.86  inst_num_of_clauses:                    115
% 0.82/0.86  inst_num_in_passive:                    43
% 0.82/0.86  inst_num_in_active:                     54
% 0.82/0.86  inst_num_in_unprocessed:                18
% 0.82/0.86  inst_num_of_loops:                      60
% 0.82/0.86  inst_num_of_learning_restarts:          0
% 0.82/0.86  inst_num_moves_active_passive:          5
% 0.82/0.86  inst_lit_activity:                      0
% 0.82/0.86  inst_lit_activity_moves:                0
% 0.82/0.86  inst_num_tautologies:                   0
% 0.82/0.86  inst_num_prop_implied:                  0
% 0.82/0.86  inst_num_existing_simplified:           0
% 0.82/0.86  inst_num_eq_res_simplified:             0
% 0.82/0.86  inst_num_child_elim:                    0
% 0.82/0.86  inst_num_of_dismatching_blockings:      16
% 0.82/0.86  inst_num_of_non_proper_insts:           88
% 0.82/0.86  inst_num_of_duplicates:                 0
% 0.82/0.86  inst_inst_num_from_inst_to_res:         0
% 0.82/0.86  inst_dismatching_checking_time:         0.
% 0.82/0.86  
% 0.82/0.86  ------ Resolution
% 0.82/0.86  
% 0.82/0.86  res_num_of_clauses:                     0
% 0.82/0.86  res_num_in_passive:                     0
% 0.82/0.86  res_num_in_active:                      0
% 0.82/0.86  res_num_of_loops:                       72
% 0.82/0.86  res_forward_subset_subsumed:            13
% 0.82/0.86  res_backward_subset_subsumed:           0
% 0.82/0.86  res_forward_subsumed:                   0
% 0.82/0.86  res_backward_subsumed:                  0
% 0.82/0.86  res_forward_subsumption_resolution:     0
% 0.82/0.86  res_backward_subsumption_resolution:    0
% 0.82/0.86  res_clause_to_clause_subsumption:       59
% 0.82/0.86  res_orphan_elimination:                 0
% 0.82/0.86  res_tautology_del:                      4
% 0.82/0.86  res_num_eq_res_simplified:              1
% 0.82/0.86  res_num_sel_changes:                    0
% 0.82/0.86  res_moves_from_active_to_pass:          0
% 0.82/0.86  
% 0.82/0.86  ------ Superposition
% 0.82/0.86  
% 0.82/0.86  sup_time_total:                         0.
% 0.82/0.86  sup_time_generating:                    0.
% 0.82/0.86  sup_time_sim_full:                      0.
% 0.82/0.86  sup_time_sim_immed:                     0.
% 0.82/0.86  
% 0.82/0.86  sup_num_of_clauses:                     17
% 0.82/0.86  sup_num_in_active:                      11
% 0.82/0.86  sup_num_in_passive:                     6
% 0.82/0.86  sup_num_of_loops:                       10
% 0.82/0.86  sup_fw_superposition:                   9
% 0.82/0.86  sup_bw_superposition:                   0
% 0.82/0.86  sup_immediate_simplified:               0
% 0.82/0.86  sup_given_eliminated:                   0
% 0.82/0.86  comparisons_done:                       0
% 0.82/0.86  comparisons_avoided:                    0
% 0.82/0.86  
% 0.82/0.86  ------ Simplifications
% 0.82/0.86  
% 0.82/0.86  
% 0.82/0.86  sim_fw_subset_subsumed:                 0
% 0.82/0.86  sim_bw_subset_subsumed:                 0
% 0.82/0.86  sim_fw_subsumed:                        0
% 0.82/0.86  sim_bw_subsumed:                        0
% 0.82/0.86  sim_fw_subsumption_res:                 0
% 0.82/0.86  sim_bw_subsumption_res:                 0
% 0.82/0.86  sim_tautology_del:                      0
% 0.82/0.86  sim_eq_tautology_del:                   1
% 0.82/0.86  sim_eq_res_simp:                        0
% 0.82/0.86  sim_fw_demodulated:                     0
% 0.82/0.86  sim_bw_demodulated:                     0
% 0.82/0.86  sim_light_normalised:                   0
% 0.82/0.86  sim_joinable_taut:                      0
% 0.82/0.86  sim_joinable_simp:                      0
% 0.82/0.86  sim_ac_normalised:                      0
% 0.82/0.86  sim_smt_subsumption:                    0
% 0.82/0.86  
%------------------------------------------------------------------------------
