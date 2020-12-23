%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:37:55 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 204 expanded)
%              Number of clauses        :   49 (  74 expanded)
%              Number of leaves         :   15 (  47 expanded)
%              Depth                    :   21
%              Number of atoms          :  230 ( 574 expanded)
%              Number of equality atoms :  111 ( 209 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1,X2,X3] :
          ( ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
            | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
         => r1_tarski(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1,X2,X3] :
            ( ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
              | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
           => r1_tarski(X1,X3) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1,X2,X3] :
          ( ~ r1_tarski(X1,X3)
          & ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
            | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1,X2,X3] :
          ( ~ r1_tarski(X1,X3)
          & ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
            | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) )
     => ( ~ r1_tarski(sK3,sK5)
        & ( r1_tarski(k2_zfmisc_1(sK3,X0),k2_zfmisc_1(sK5,sK4))
          | r1_tarski(k2_zfmisc_1(X0,sK3),k2_zfmisc_1(sK4,sK5)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1,X2,X3] :
            ( ~ r1_tarski(X1,X3)
            & ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
              | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X3,X2,X1] :
          ( ~ r1_tarski(X1,X3)
          & ( r1_tarski(k2_zfmisc_1(X1,sK2),k2_zfmisc_1(X3,X2))
            | r1_tarski(k2_zfmisc_1(sK2,X1),k2_zfmisc_1(X2,X3)) ) )
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ~ r1_tarski(sK3,sK5)
    & ( r1_tarski(k2_zfmisc_1(sK3,sK2),k2_zfmisc_1(sK5,sK4))
      | r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5)) )
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f21,f30,f29])).

fof(f49,plain,
    ( r1_tarski(k2_zfmisc_1(sK3,sK2),k2_zfmisc_1(sK5,sK4))
    | r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f36,f37])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X1,X3)
        & r1_tarski(X0,X2) )
      | k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X1,X3)
        & r1_tarski(X0,X2) )
      | k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f19])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X0,X2)
      | k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f50,plain,(
    ~ r1_tarski(sK3,sK5) ),
    inference(cnf_transformation,[],[f31])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f35,f37])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X1,X3)
      | k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f27])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
     => v1_xboole_0(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f15,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ? [X1] : r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f22])).

fof(f32,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f48,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f41,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f53,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f41])).

fof(f6,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f24])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_16,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5))
    | r1_tarski(k2_zfmisc_1(sK3,sK2),k2_zfmisc_1(sK5,sK4)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_788,plain,
    ( r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5)) = iProver_top
    | r1_tarski(k2_zfmisc_1(sK3,sK2),k2_zfmisc_1(sK5,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_796,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1356,plain,
    ( k5_xboole_0(k2_zfmisc_1(sK2,sK3),k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5))) = k1_xboole_0
    | r1_tarski(k2_zfmisc_1(sK3,sK2),k2_zfmisc_1(sK5,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_788,c_796])).

cnf(c_14,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
    | k2_zfmisc_1(X0,X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_790,plain,
    ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X2) = iProver_top
    | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1406,plain,
    ( k2_zfmisc_1(sK3,sK2) = k1_xboole_0
    | k5_xboole_0(k2_zfmisc_1(sK2,sK3),k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5))) = k1_xboole_0
    | r1_tarski(sK3,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1356,c_790])).

cnf(c_15,negated_conjecture,
    ( ~ r1_tarski(sK3,sK5) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_20,plain,
    ( r1_tarski(sK3,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1821,plain,
    ( k5_xboole_0(k2_zfmisc_1(sK2,sK3),k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5))) = k1_xboole_0
    | k2_zfmisc_1(sK3,sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1406,c_20])).

cnf(c_1822,plain,
    ( k2_zfmisc_1(sK3,sK2) = k1_xboole_0
    | k5_xboole_0(k2_zfmisc_1(sK2,sK3),k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5))) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_1821])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_795,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1825,plain,
    ( k2_zfmisc_1(sK3,sK2) = k1_xboole_0
    | r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1822,c_795])).

cnf(c_13,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X3,X1))
    | k2_zfmisc_1(X2,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_791,plain,
    ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    | r1_tarski(X1,X2) = iProver_top
    | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X3,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2170,plain,
    ( k2_zfmisc_1(sK2,sK3) = k1_xboole_0
    | k2_zfmisc_1(sK3,sK2) = k1_xboole_0
    | r1_tarski(sK3,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1825,c_791])).

cnf(c_2203,plain,
    ( r1_tarski(sK3,sK5)
    | k2_zfmisc_1(sK2,sK3) = k1_xboole_0
    | k2_zfmisc_1(sK3,sK2) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2170])).

cnf(c_2438,plain,
    ( k2_zfmisc_1(sK3,sK2) = k1_xboole_0
    | k2_zfmisc_1(sK2,sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2170,c_15,c_2203])).

cnf(c_2439,plain,
    ( k2_zfmisc_1(sK2,sK3) = k1_xboole_0
    | k2_zfmisc_1(sK3,sK2) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_2438])).

cnf(c_12,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_2446,plain,
    ( k2_zfmisc_1(sK3,sK2) = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2439,c_12])).

cnf(c_2551,plain,
    ( sK2 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2446,c_12])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_17,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_192,plain,
    ( r2_hidden(sK0(X0),X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_17])).

cnf(c_193,plain,
    ( r2_hidden(sK0(sK2),sK2) ),
    inference(unflattening,[status(thm)],[c_192])).

cnf(c_787,plain,
    ( r2_hidden(sK0(sK2),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_193])).

cnf(c_2630,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK0(k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2551,c_787])).

cnf(c_9,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_792,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_6,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_798,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,k3_xboole_0(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1579,plain,
    ( r1_xboole_0(X0,k1_xboole_0) != iProver_top
    | r2_hidden(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_798])).

cnf(c_1590,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_792,c_1579])).

cnf(c_2683,plain,
    ( sK3 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2630,c_1590])).

cnf(c_789,plain,
    ( r1_tarski(sK3,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2694,plain,
    ( r1_tarski(k1_xboole_0,sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2683,c_789])).

cnf(c_1263,plain,
    ( k5_xboole_0(X0,k1_xboole_0) != k1_xboole_0
    | r1_tarski(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_795])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1264,plain,
    ( k1_xboole_0 != X0
    | r1_tarski(X0,k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1263,c_7])).

cnf(c_1271,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1264])).

cnf(c_5,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_794,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k3_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1163,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_794])).

cnf(c_1298,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1271,c_1163])).

cnf(c_2759,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2694,c_1298])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:44:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 0.67/1.05  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.67/1.05  
% 0.67/1.05  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.67/1.05  
% 0.67/1.05  ------  iProver source info
% 0.67/1.05  
% 0.67/1.05  git: date: 2020-06-30 10:37:57 +0100
% 0.67/1.05  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.67/1.05  git: non_committed_changes: false
% 0.67/1.05  git: last_make_outside_of_git: false
% 0.67/1.05  
% 0.67/1.05  ------ 
% 0.67/1.05  
% 0.67/1.05  ------ Input Options
% 0.67/1.05  
% 0.67/1.05  --out_options                           all
% 0.67/1.05  --tptp_safe_out                         true
% 0.67/1.05  --problem_path                          ""
% 0.67/1.05  --include_path                          ""
% 0.67/1.05  --clausifier                            res/vclausify_rel
% 0.67/1.05  --clausifier_options                    --mode clausify
% 0.67/1.05  --stdin                                 false
% 0.67/1.05  --stats_out                             all
% 0.67/1.05  
% 0.67/1.05  ------ General Options
% 0.67/1.05  
% 0.67/1.05  --fof                                   false
% 0.67/1.05  --time_out_real                         305.
% 0.67/1.05  --time_out_virtual                      -1.
% 0.67/1.05  --symbol_type_check                     false
% 0.67/1.05  --clausify_out                          false
% 0.67/1.05  --sig_cnt_out                           false
% 0.67/1.05  --trig_cnt_out                          false
% 0.67/1.05  --trig_cnt_out_tolerance                1.
% 0.67/1.05  --trig_cnt_out_sk_spl                   false
% 0.67/1.05  --abstr_cl_out                          false
% 0.67/1.05  
% 0.67/1.05  ------ Global Options
% 0.67/1.05  
% 0.67/1.05  --schedule                              default
% 0.67/1.05  --add_important_lit                     false
% 0.67/1.05  --prop_solver_per_cl                    1000
% 0.67/1.05  --min_unsat_core                        false
% 0.67/1.05  --soft_assumptions                      false
% 0.67/1.05  --soft_lemma_size                       3
% 0.67/1.05  --prop_impl_unit_size                   0
% 0.67/1.05  --prop_impl_unit                        []
% 0.67/1.05  --share_sel_clauses                     true
% 0.67/1.05  --reset_solvers                         false
% 0.67/1.05  --bc_imp_inh                            [conj_cone]
% 0.67/1.05  --conj_cone_tolerance                   3.
% 0.67/1.05  --extra_neg_conj                        none
% 0.67/1.05  --large_theory_mode                     true
% 0.67/1.05  --prolific_symb_bound                   200
% 0.67/1.05  --lt_threshold                          2000
% 0.67/1.05  --clause_weak_htbl                      true
% 0.67/1.05  --gc_record_bc_elim                     false
% 0.67/1.05  
% 0.67/1.05  ------ Preprocessing Options
% 0.67/1.05  
% 0.67/1.05  --preprocessing_flag                    true
% 0.67/1.05  --time_out_prep_mult                    0.1
% 0.67/1.05  --splitting_mode                        input
% 0.67/1.05  --splitting_grd                         true
% 0.67/1.05  --splitting_cvd                         false
% 0.67/1.05  --splitting_cvd_svl                     false
% 0.67/1.05  --splitting_nvd                         32
% 0.67/1.05  --sub_typing                            true
% 0.67/1.05  --prep_gs_sim                           true
% 0.67/1.05  --prep_unflatten                        true
% 0.67/1.05  --prep_res_sim                          true
% 0.67/1.05  --prep_upred                            true
% 0.67/1.05  --prep_sem_filter                       exhaustive
% 0.67/1.05  --prep_sem_filter_out                   false
% 0.67/1.05  --pred_elim                             true
% 0.67/1.05  --res_sim_input                         true
% 0.67/1.05  --eq_ax_congr_red                       true
% 0.67/1.05  --pure_diseq_elim                       true
% 0.67/1.05  --brand_transform                       false
% 0.67/1.05  --non_eq_to_eq                          false
% 0.67/1.05  --prep_def_merge                        true
% 0.67/1.05  --prep_def_merge_prop_impl              false
% 0.67/1.05  --prep_def_merge_mbd                    true
% 0.67/1.05  --prep_def_merge_tr_red                 false
% 0.67/1.05  --prep_def_merge_tr_cl                  false
% 0.67/1.05  --smt_preprocessing                     true
% 0.67/1.05  --smt_ac_axioms                         fast
% 0.67/1.05  --preprocessed_out                      false
% 0.67/1.05  --preprocessed_stats                    false
% 0.67/1.05  
% 0.67/1.05  ------ Abstraction refinement Options
% 0.67/1.05  
% 0.67/1.05  --abstr_ref                             []
% 0.67/1.05  --abstr_ref_prep                        false
% 0.67/1.05  --abstr_ref_until_sat                   false
% 0.67/1.05  --abstr_ref_sig_restrict                funpre
% 0.67/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 0.67/1.05  --abstr_ref_under                       []
% 0.67/1.05  
% 0.67/1.05  ------ SAT Options
% 0.67/1.05  
% 0.67/1.05  --sat_mode                              false
% 0.67/1.05  --sat_fm_restart_options                ""
% 0.67/1.05  --sat_gr_def                            false
% 0.67/1.05  --sat_epr_types                         true
% 0.67/1.05  --sat_non_cyclic_types                  false
% 0.67/1.05  --sat_finite_models                     false
% 0.67/1.05  --sat_fm_lemmas                         false
% 0.67/1.05  --sat_fm_prep                           false
% 0.67/1.05  --sat_fm_uc_incr                        true
% 0.67/1.05  --sat_out_model                         small
% 0.67/1.05  --sat_out_clauses                       false
% 0.67/1.05  
% 0.67/1.05  ------ QBF Options
% 0.67/1.05  
% 0.67/1.05  --qbf_mode                              false
% 0.67/1.05  --qbf_elim_univ                         false
% 0.67/1.05  --qbf_dom_inst                          none
% 0.67/1.05  --qbf_dom_pre_inst                      false
% 0.67/1.05  --qbf_sk_in                             false
% 0.67/1.05  --qbf_pred_elim                         true
% 0.67/1.05  --qbf_split                             512
% 0.67/1.05  
% 0.67/1.05  ------ BMC1 Options
% 0.67/1.05  
% 0.67/1.05  --bmc1_incremental                      false
% 0.67/1.05  --bmc1_axioms                           reachable_all
% 0.67/1.05  --bmc1_min_bound                        0
% 0.67/1.05  --bmc1_max_bound                        -1
% 0.67/1.05  --bmc1_max_bound_default                -1
% 0.67/1.05  --bmc1_symbol_reachability              true
% 0.67/1.05  --bmc1_property_lemmas                  false
% 0.67/1.05  --bmc1_k_induction                      false
% 0.67/1.05  --bmc1_non_equiv_states                 false
% 0.67/1.05  --bmc1_deadlock                         false
% 0.67/1.05  --bmc1_ucm                              false
% 0.67/1.05  --bmc1_add_unsat_core                   none
% 0.67/1.05  --bmc1_unsat_core_children              false
% 0.67/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 0.67/1.05  --bmc1_out_stat                         full
% 0.67/1.05  --bmc1_ground_init                      false
% 0.67/1.05  --bmc1_pre_inst_next_state              false
% 0.67/1.05  --bmc1_pre_inst_state                   false
% 0.67/1.05  --bmc1_pre_inst_reach_state             false
% 0.67/1.05  --bmc1_out_unsat_core                   false
% 0.67/1.05  --bmc1_aig_witness_out                  false
% 0.67/1.05  --bmc1_verbose                          false
% 0.67/1.05  --bmc1_dump_clauses_tptp                false
% 0.67/1.05  --bmc1_dump_unsat_core_tptp             false
% 0.67/1.05  --bmc1_dump_file                        -
% 0.67/1.05  --bmc1_ucm_expand_uc_limit              128
% 0.67/1.05  --bmc1_ucm_n_expand_iterations          6
% 0.67/1.05  --bmc1_ucm_extend_mode                  1
% 0.67/1.05  --bmc1_ucm_init_mode                    2
% 0.67/1.05  --bmc1_ucm_cone_mode                    none
% 0.67/1.05  --bmc1_ucm_reduced_relation_type        0
% 0.67/1.05  --bmc1_ucm_relax_model                  4
% 0.67/1.05  --bmc1_ucm_full_tr_after_sat            true
% 0.67/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 0.67/1.05  --bmc1_ucm_layered_model                none
% 1.65/1.05  --bmc1_ucm_max_lemma_size               10
% 1.65/1.05  
% 1.65/1.05  ------ AIG Options
% 1.65/1.05  
% 1.65/1.05  --aig_mode                              false
% 1.65/1.05  
% 1.65/1.05  ------ Instantiation Options
% 1.65/1.05  
% 1.65/1.05  --instantiation_flag                    true
% 1.65/1.05  --inst_sos_flag                         false
% 1.65/1.05  --inst_sos_phase                        true
% 1.65/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.65/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.65/1.05  --inst_lit_sel_side                     num_symb
% 1.65/1.05  --inst_solver_per_active                1400
% 1.65/1.05  --inst_solver_calls_frac                1.
% 1.65/1.05  --inst_passive_queue_type               priority_queues
% 1.65/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.65/1.05  --inst_passive_queues_freq              [25;2]
% 1.65/1.05  --inst_dismatching                      true
% 1.65/1.05  --inst_eager_unprocessed_to_passive     true
% 1.65/1.05  --inst_prop_sim_given                   true
% 1.65/1.05  --inst_prop_sim_new                     false
% 1.65/1.05  --inst_subs_new                         false
% 1.65/1.05  --inst_eq_res_simp                      false
% 1.65/1.05  --inst_subs_given                       false
% 1.65/1.05  --inst_orphan_elimination               true
% 1.65/1.05  --inst_learning_loop_flag               true
% 1.65/1.05  --inst_learning_start                   3000
% 1.65/1.05  --inst_learning_factor                  2
% 1.65/1.05  --inst_start_prop_sim_after_learn       3
% 1.65/1.05  --inst_sel_renew                        solver
% 1.65/1.05  --inst_lit_activity_flag                true
% 1.65/1.05  --inst_restr_to_given                   false
% 1.65/1.05  --inst_activity_threshold               500
% 1.65/1.05  --inst_out_proof                        true
% 1.65/1.05  
% 1.65/1.05  ------ Resolution Options
% 1.65/1.05  
% 1.65/1.05  --resolution_flag                       true
% 1.65/1.05  --res_lit_sel                           adaptive
% 1.65/1.05  --res_lit_sel_side                      none
% 1.65/1.05  --res_ordering                          kbo
% 1.65/1.05  --res_to_prop_solver                    active
% 1.65/1.05  --res_prop_simpl_new                    false
% 1.65/1.05  --res_prop_simpl_given                  true
% 1.65/1.05  --res_passive_queue_type                priority_queues
% 1.65/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.65/1.05  --res_passive_queues_freq               [15;5]
% 1.65/1.05  --res_forward_subs                      full
% 1.65/1.05  --res_backward_subs                     full
% 1.65/1.05  --res_forward_subs_resolution           true
% 1.65/1.05  --res_backward_subs_resolution          true
% 1.65/1.05  --res_orphan_elimination                true
% 1.65/1.05  --res_time_limit                        2.
% 1.65/1.05  --res_out_proof                         true
% 1.65/1.05  
% 1.65/1.05  ------ Superposition Options
% 1.65/1.05  
% 1.65/1.05  --superposition_flag                    true
% 1.65/1.05  --sup_passive_queue_type                priority_queues
% 1.65/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.65/1.05  --sup_passive_queues_freq               [8;1;4]
% 1.65/1.05  --demod_completeness_check              fast
% 1.65/1.05  --demod_use_ground                      true
% 1.65/1.05  --sup_to_prop_solver                    passive
% 1.65/1.05  --sup_prop_simpl_new                    true
% 1.65/1.05  --sup_prop_simpl_given                  true
% 1.65/1.05  --sup_fun_splitting                     false
% 1.65/1.05  --sup_smt_interval                      50000
% 1.65/1.05  
% 1.65/1.05  ------ Superposition Simplification Setup
% 1.65/1.05  
% 1.65/1.05  --sup_indices_passive                   []
% 1.65/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.65/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.65/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.65/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 1.65/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.65/1.05  --sup_full_bw                           [BwDemod]
% 1.65/1.05  --sup_immed_triv                        [TrivRules]
% 1.65/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.65/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.65/1.05  --sup_immed_bw_main                     []
% 1.65/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.65/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 1.65/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.65/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.65/1.05  
% 1.65/1.05  ------ Combination Options
% 1.65/1.05  
% 1.65/1.05  --comb_res_mult                         3
% 1.65/1.05  --comb_sup_mult                         2
% 1.65/1.05  --comb_inst_mult                        10
% 1.65/1.05  
% 1.65/1.05  ------ Debug Options
% 1.65/1.05  
% 1.65/1.05  --dbg_backtrace                         false
% 1.65/1.05  --dbg_dump_prop_clauses                 false
% 1.65/1.05  --dbg_dump_prop_clauses_file            -
% 1.65/1.05  --dbg_out_stat                          false
% 1.65/1.05  ------ Parsing...
% 1.65/1.05  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.65/1.05  
% 1.65/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 1.65/1.05  
% 1.65/1.05  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.65/1.05  
% 1.65/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.65/1.05  ------ Proving...
% 1.65/1.05  ------ Problem Properties 
% 1.65/1.05  
% 1.65/1.05  
% 1.65/1.05  clauses                                 17
% 1.65/1.05  conjectures                             2
% 1.65/1.05  EPR                                     3
% 1.65/1.05  Horn                                    12
% 1.65/1.05  unary                                   7
% 1.65/1.05  binary                                  7
% 1.65/1.05  lits                                    30
% 1.65/1.05  lits eq                                 12
% 1.65/1.05  fd_pure                                 0
% 1.65/1.05  fd_pseudo                               0
% 1.65/1.05  fd_cond                                 2
% 1.65/1.05  fd_pseudo_cond                          0
% 1.65/1.05  AC symbols                              0
% 1.65/1.05  
% 1.65/1.05  ------ Schedule dynamic 5 is on 
% 1.65/1.05  
% 1.65/1.05  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.65/1.05  
% 1.65/1.05  
% 1.65/1.05  ------ 
% 1.65/1.05  Current options:
% 1.65/1.05  ------ 
% 1.65/1.05  
% 1.65/1.05  ------ Input Options
% 1.65/1.05  
% 1.65/1.05  --out_options                           all
% 1.65/1.05  --tptp_safe_out                         true
% 1.65/1.05  --problem_path                          ""
% 1.65/1.05  --include_path                          ""
% 1.65/1.05  --clausifier                            res/vclausify_rel
% 1.65/1.05  --clausifier_options                    --mode clausify
% 1.65/1.05  --stdin                                 false
% 1.65/1.05  --stats_out                             all
% 1.65/1.05  
% 1.65/1.05  ------ General Options
% 1.65/1.05  
% 1.65/1.05  --fof                                   false
% 1.65/1.05  --time_out_real                         305.
% 1.65/1.05  --time_out_virtual                      -1.
% 1.65/1.05  --symbol_type_check                     false
% 1.65/1.05  --clausify_out                          false
% 1.65/1.05  --sig_cnt_out                           false
% 1.65/1.05  --trig_cnt_out                          false
% 1.65/1.05  --trig_cnt_out_tolerance                1.
% 1.65/1.05  --trig_cnt_out_sk_spl                   false
% 1.65/1.05  --abstr_cl_out                          false
% 1.65/1.05  
% 1.65/1.05  ------ Global Options
% 1.65/1.05  
% 1.65/1.05  --schedule                              default
% 1.65/1.05  --add_important_lit                     false
% 1.65/1.05  --prop_solver_per_cl                    1000
% 1.65/1.05  --min_unsat_core                        false
% 1.65/1.05  --soft_assumptions                      false
% 1.65/1.05  --soft_lemma_size                       3
% 1.65/1.05  --prop_impl_unit_size                   0
% 1.65/1.05  --prop_impl_unit                        []
% 1.65/1.05  --share_sel_clauses                     true
% 1.65/1.05  --reset_solvers                         false
% 1.65/1.05  --bc_imp_inh                            [conj_cone]
% 1.65/1.05  --conj_cone_tolerance                   3.
% 1.65/1.05  --extra_neg_conj                        none
% 1.65/1.05  --large_theory_mode                     true
% 1.65/1.05  --prolific_symb_bound                   200
% 1.65/1.05  --lt_threshold                          2000
% 1.65/1.05  --clause_weak_htbl                      true
% 1.65/1.05  --gc_record_bc_elim                     false
% 1.65/1.05  
% 1.65/1.05  ------ Preprocessing Options
% 1.65/1.05  
% 1.65/1.05  --preprocessing_flag                    true
% 1.65/1.05  --time_out_prep_mult                    0.1
% 1.65/1.05  --splitting_mode                        input
% 1.65/1.05  --splitting_grd                         true
% 1.65/1.05  --splitting_cvd                         false
% 1.65/1.05  --splitting_cvd_svl                     false
% 1.65/1.05  --splitting_nvd                         32
% 1.65/1.05  --sub_typing                            true
% 1.65/1.05  --prep_gs_sim                           true
% 1.65/1.05  --prep_unflatten                        true
% 1.65/1.05  --prep_res_sim                          true
% 1.65/1.05  --prep_upred                            true
% 1.65/1.05  --prep_sem_filter                       exhaustive
% 1.65/1.05  --prep_sem_filter_out                   false
% 1.65/1.05  --pred_elim                             true
% 1.65/1.05  --res_sim_input                         true
% 1.65/1.05  --eq_ax_congr_red                       true
% 1.65/1.05  --pure_diseq_elim                       true
% 1.65/1.05  --brand_transform                       false
% 1.65/1.05  --non_eq_to_eq                          false
% 1.65/1.05  --prep_def_merge                        true
% 1.65/1.05  --prep_def_merge_prop_impl              false
% 1.65/1.05  --prep_def_merge_mbd                    true
% 1.65/1.05  --prep_def_merge_tr_red                 false
% 1.65/1.05  --prep_def_merge_tr_cl                  false
% 1.65/1.05  --smt_preprocessing                     true
% 1.65/1.05  --smt_ac_axioms                         fast
% 1.65/1.05  --preprocessed_out                      false
% 1.65/1.05  --preprocessed_stats                    false
% 1.65/1.05  
% 1.65/1.05  ------ Abstraction refinement Options
% 1.65/1.05  
% 1.65/1.05  --abstr_ref                             []
% 1.65/1.05  --abstr_ref_prep                        false
% 1.65/1.05  --abstr_ref_until_sat                   false
% 1.65/1.05  --abstr_ref_sig_restrict                funpre
% 1.65/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 1.65/1.05  --abstr_ref_under                       []
% 1.65/1.05  
% 1.65/1.05  ------ SAT Options
% 1.65/1.05  
% 1.65/1.05  --sat_mode                              false
% 1.65/1.05  --sat_fm_restart_options                ""
% 1.65/1.05  --sat_gr_def                            false
% 1.65/1.05  --sat_epr_types                         true
% 1.65/1.05  --sat_non_cyclic_types                  false
% 1.65/1.05  --sat_finite_models                     false
% 1.65/1.05  --sat_fm_lemmas                         false
% 1.65/1.05  --sat_fm_prep                           false
% 1.65/1.05  --sat_fm_uc_incr                        true
% 1.65/1.05  --sat_out_model                         small
% 1.65/1.05  --sat_out_clauses                       false
% 1.65/1.05  
% 1.65/1.05  ------ QBF Options
% 1.65/1.05  
% 1.65/1.05  --qbf_mode                              false
% 1.65/1.05  --qbf_elim_univ                         false
% 1.65/1.05  --qbf_dom_inst                          none
% 1.65/1.05  --qbf_dom_pre_inst                      false
% 1.65/1.05  --qbf_sk_in                             false
% 1.65/1.05  --qbf_pred_elim                         true
% 1.65/1.05  --qbf_split                             512
% 1.65/1.05  
% 1.65/1.05  ------ BMC1 Options
% 1.65/1.05  
% 1.65/1.05  --bmc1_incremental                      false
% 1.65/1.05  --bmc1_axioms                           reachable_all
% 1.65/1.05  --bmc1_min_bound                        0
% 1.65/1.05  --bmc1_max_bound                        -1
% 1.65/1.05  --bmc1_max_bound_default                -1
% 1.65/1.05  --bmc1_symbol_reachability              true
% 1.65/1.05  --bmc1_property_lemmas                  false
% 1.65/1.05  --bmc1_k_induction                      false
% 1.65/1.05  --bmc1_non_equiv_states                 false
% 1.65/1.05  --bmc1_deadlock                         false
% 1.65/1.05  --bmc1_ucm                              false
% 1.65/1.05  --bmc1_add_unsat_core                   none
% 1.65/1.05  --bmc1_unsat_core_children              false
% 1.65/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 1.65/1.05  --bmc1_out_stat                         full
% 1.65/1.05  --bmc1_ground_init                      false
% 1.65/1.05  --bmc1_pre_inst_next_state              false
% 1.65/1.05  --bmc1_pre_inst_state                   false
% 1.65/1.05  --bmc1_pre_inst_reach_state             false
% 1.65/1.05  --bmc1_out_unsat_core                   false
% 1.65/1.05  --bmc1_aig_witness_out                  false
% 1.65/1.05  --bmc1_verbose                          false
% 1.65/1.05  --bmc1_dump_clauses_tptp                false
% 1.65/1.05  --bmc1_dump_unsat_core_tptp             false
% 1.65/1.05  --bmc1_dump_file                        -
% 1.65/1.05  --bmc1_ucm_expand_uc_limit              128
% 1.65/1.05  --bmc1_ucm_n_expand_iterations          6
% 1.65/1.05  --bmc1_ucm_extend_mode                  1
% 1.65/1.05  --bmc1_ucm_init_mode                    2
% 1.65/1.05  --bmc1_ucm_cone_mode                    none
% 1.65/1.05  --bmc1_ucm_reduced_relation_type        0
% 1.65/1.05  --bmc1_ucm_relax_model                  4
% 1.65/1.05  --bmc1_ucm_full_tr_after_sat            true
% 1.65/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 1.65/1.05  --bmc1_ucm_layered_model                none
% 1.65/1.05  --bmc1_ucm_max_lemma_size               10
% 1.65/1.05  
% 1.65/1.05  ------ AIG Options
% 1.65/1.05  
% 1.65/1.05  --aig_mode                              false
% 1.65/1.05  
% 1.65/1.05  ------ Instantiation Options
% 1.65/1.05  
% 1.65/1.05  --instantiation_flag                    true
% 1.65/1.05  --inst_sos_flag                         false
% 1.65/1.05  --inst_sos_phase                        true
% 1.65/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.65/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.65/1.05  --inst_lit_sel_side                     none
% 1.65/1.05  --inst_solver_per_active                1400
% 1.65/1.05  --inst_solver_calls_frac                1.
% 1.65/1.05  --inst_passive_queue_type               priority_queues
% 1.65/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.65/1.05  --inst_passive_queues_freq              [25;2]
% 1.65/1.05  --inst_dismatching                      true
% 1.65/1.05  --inst_eager_unprocessed_to_passive     true
% 1.65/1.05  --inst_prop_sim_given                   true
% 1.65/1.05  --inst_prop_sim_new                     false
% 1.65/1.05  --inst_subs_new                         false
% 1.65/1.05  --inst_eq_res_simp                      false
% 1.65/1.05  --inst_subs_given                       false
% 1.65/1.05  --inst_orphan_elimination               true
% 1.65/1.05  --inst_learning_loop_flag               true
% 1.65/1.05  --inst_learning_start                   3000
% 1.65/1.05  --inst_learning_factor                  2
% 1.65/1.05  --inst_start_prop_sim_after_learn       3
% 1.65/1.05  --inst_sel_renew                        solver
% 1.65/1.05  --inst_lit_activity_flag                true
% 1.65/1.05  --inst_restr_to_given                   false
% 1.65/1.05  --inst_activity_threshold               500
% 1.65/1.05  --inst_out_proof                        true
% 1.65/1.05  
% 1.65/1.05  ------ Resolution Options
% 1.65/1.05  
% 1.65/1.05  --resolution_flag                       false
% 1.65/1.05  --res_lit_sel                           adaptive
% 1.65/1.05  --res_lit_sel_side                      none
% 1.65/1.05  --res_ordering                          kbo
% 1.65/1.05  --res_to_prop_solver                    active
% 1.65/1.05  --res_prop_simpl_new                    false
% 1.65/1.05  --res_prop_simpl_given                  true
% 1.65/1.05  --res_passive_queue_type                priority_queues
% 1.65/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.65/1.05  --res_passive_queues_freq               [15;5]
% 1.65/1.05  --res_forward_subs                      full
% 1.65/1.05  --res_backward_subs                     full
% 1.65/1.05  --res_forward_subs_resolution           true
% 1.65/1.05  --res_backward_subs_resolution          true
% 1.65/1.05  --res_orphan_elimination                true
% 1.65/1.05  --res_time_limit                        2.
% 1.65/1.05  --res_out_proof                         true
% 1.65/1.05  
% 1.65/1.05  ------ Superposition Options
% 1.65/1.05  
% 1.65/1.05  --superposition_flag                    true
% 1.65/1.05  --sup_passive_queue_type                priority_queues
% 1.65/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.65/1.05  --sup_passive_queues_freq               [8;1;4]
% 1.65/1.05  --demod_completeness_check              fast
% 1.65/1.05  --demod_use_ground                      true
% 1.65/1.05  --sup_to_prop_solver                    passive
% 1.65/1.05  --sup_prop_simpl_new                    true
% 1.65/1.05  --sup_prop_simpl_given                  true
% 1.65/1.05  --sup_fun_splitting                     false
% 1.65/1.05  --sup_smt_interval                      50000
% 1.65/1.05  
% 1.65/1.05  ------ Superposition Simplification Setup
% 1.65/1.05  
% 1.65/1.05  --sup_indices_passive                   []
% 1.65/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.65/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.65/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.65/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 1.65/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.65/1.05  --sup_full_bw                           [BwDemod]
% 1.65/1.05  --sup_immed_triv                        [TrivRules]
% 1.65/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.65/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.65/1.05  --sup_immed_bw_main                     []
% 1.65/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.65/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 1.65/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.65/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.65/1.05  
% 1.65/1.05  ------ Combination Options
% 1.65/1.05  
% 1.65/1.05  --comb_res_mult                         3
% 1.65/1.05  --comb_sup_mult                         2
% 1.65/1.05  --comb_inst_mult                        10
% 1.65/1.05  
% 1.65/1.05  ------ Debug Options
% 1.65/1.05  
% 1.65/1.05  --dbg_backtrace                         false
% 1.65/1.05  --dbg_dump_prop_clauses                 false
% 1.65/1.05  --dbg_dump_prop_clauses_file            -
% 1.65/1.05  --dbg_out_stat                          false
% 1.65/1.05  
% 1.65/1.05  
% 1.65/1.05  
% 1.65/1.05  
% 1.65/1.05  ------ Proving...
% 1.65/1.05  
% 1.65/1.05  
% 1.65/1.05  % SZS status Theorem for theBenchmark.p
% 1.65/1.05  
% 1.65/1.05   Resolution empty clause
% 1.65/1.05  
% 1.65/1.05  % SZS output start CNFRefutation for theBenchmark.p
% 1.65/1.05  
% 1.65/1.05  fof(f11,conjecture,(
% 1.65/1.05    ! [X0] : (~v1_xboole_0(X0) => ! [X1,X2,X3] : ((r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2)) | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => r1_tarski(X1,X3)))),
% 1.65/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.65/1.05  
% 1.65/1.05  fof(f12,negated_conjecture,(
% 1.65/1.05    ~! [X0] : (~v1_xboole_0(X0) => ! [X1,X2,X3] : ((r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2)) | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => r1_tarski(X1,X3)))),
% 1.65/1.05    inference(negated_conjecture,[],[f11])).
% 1.65/1.05  
% 1.65/1.05  fof(f21,plain,(
% 1.65/1.05    ? [X0] : (? [X1,X2,X3] : (~r1_tarski(X1,X3) & (r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2)) | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))) & ~v1_xboole_0(X0))),
% 1.65/1.05    inference(ennf_transformation,[],[f12])).
% 1.65/1.05  
% 1.65/1.05  fof(f30,plain,(
% 1.65/1.05    ( ! [X0] : (? [X1,X2,X3] : (~r1_tarski(X1,X3) & (r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2)) | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))) => (~r1_tarski(sK3,sK5) & (r1_tarski(k2_zfmisc_1(sK3,X0),k2_zfmisc_1(sK5,sK4)) | r1_tarski(k2_zfmisc_1(X0,sK3),k2_zfmisc_1(sK4,sK5))))) )),
% 1.65/1.05    introduced(choice_axiom,[])).
% 1.65/1.05  
% 1.65/1.05  fof(f29,plain,(
% 1.65/1.05    ? [X0] : (? [X1,X2,X3] : (~r1_tarski(X1,X3) & (r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2)) | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))) & ~v1_xboole_0(X0)) => (? [X3,X2,X1] : (~r1_tarski(X1,X3) & (r1_tarski(k2_zfmisc_1(X1,sK2),k2_zfmisc_1(X3,X2)) | r1_tarski(k2_zfmisc_1(sK2,X1),k2_zfmisc_1(X2,X3)))) & ~v1_xboole_0(sK2))),
% 1.65/1.05    introduced(choice_axiom,[])).
% 1.65/1.05  
% 1.65/1.05  fof(f31,plain,(
% 1.65/1.05    (~r1_tarski(sK3,sK5) & (r1_tarski(k2_zfmisc_1(sK3,sK2),k2_zfmisc_1(sK5,sK4)) | r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5)))) & ~v1_xboole_0(sK2)),
% 1.65/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f21,f30,f29])).
% 1.65/1.05  
% 1.65/1.05  fof(f49,plain,(
% 1.65/1.05    r1_tarski(k2_zfmisc_1(sK3,sK2),k2_zfmisc_1(sK5,sK4)) | r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5))),
% 1.65/1.05    inference(cnf_transformation,[],[f31])).
% 1.65/1.05  
% 1.65/1.05  fof(f3,axiom,(
% 1.65/1.05    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.65/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.65/1.05  
% 1.65/1.05  fof(f26,plain,(
% 1.65/1.05    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.65/1.05    inference(nnf_transformation,[],[f3])).
% 1.65/1.05  
% 1.65/1.05  fof(f36,plain,(
% 1.65/1.05    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 1.65/1.05    inference(cnf_transformation,[],[f26])).
% 1.65/1.05  
% 1.65/1.05  fof(f4,axiom,(
% 1.65/1.05    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.65/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.65/1.05  
% 1.65/1.05  fof(f37,plain,(
% 1.65/1.05    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.65/1.05    inference(cnf_transformation,[],[f4])).
% 1.65/1.05  
% 1.65/1.05  fof(f51,plain,(
% 1.65/1.05    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) )),
% 1.65/1.05    inference(definition_unfolding,[],[f36,f37])).
% 1.65/1.05  
% 1.65/1.05  fof(f10,axiom,(
% 1.65/1.05    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 1.65/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.65/1.05  
% 1.65/1.05  fof(f19,plain,(
% 1.65/1.05    ! [X0,X1,X2,X3] : (((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)) | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 1.65/1.05    inference(ennf_transformation,[],[f10])).
% 1.65/1.05  
% 1.65/1.05  fof(f20,plain,(
% 1.65/1.05    ! [X0,X1,X2,X3] : ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1) | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 1.65/1.05    inference(flattening,[],[f19])).
% 1.65/1.05  
% 1.65/1.05  fof(f46,plain,(
% 1.65/1.05    ( ! [X2,X0,X3,X1] : (r1_tarski(X0,X2) | k1_xboole_0 = k2_zfmisc_1(X0,X1) | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 1.65/1.05    inference(cnf_transformation,[],[f20])).
% 1.65/1.05  
% 1.65/1.05  fof(f50,plain,(
% 1.65/1.05    ~r1_tarski(sK3,sK5)),
% 1.65/1.05    inference(cnf_transformation,[],[f31])).
% 1.65/1.05  
% 1.65/1.05  fof(f35,plain,(
% 1.65/1.05    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.65/1.05    inference(cnf_transformation,[],[f26])).
% 1.65/1.05  
% 1.65/1.05  fof(f52,plain,(
% 1.65/1.05    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.65/1.05    inference(definition_unfolding,[],[f35,f37])).
% 1.65/1.05  
% 1.65/1.05  fof(f47,plain,(
% 1.65/1.05    ( ! [X2,X0,X3,X1] : (r1_tarski(X1,X3) | k1_xboole_0 = k2_zfmisc_1(X0,X1) | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 1.65/1.05    inference(cnf_transformation,[],[f20])).
% 1.65/1.05  
% 1.65/1.05  fof(f9,axiom,(
% 1.65/1.05    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.65/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.65/1.05  
% 1.65/1.05  fof(f27,plain,(
% 1.65/1.05    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.65/1.05    inference(nnf_transformation,[],[f9])).
% 1.65/1.05  
% 1.65/1.05  fof(f28,plain,(
% 1.65/1.05    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.65/1.05    inference(flattening,[],[f27])).
% 1.65/1.05  
% 1.65/1.05  fof(f43,plain,(
% 1.65/1.05    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 1.65/1.05    inference(cnf_transformation,[],[f28])).
% 1.65/1.05  
% 1.65/1.05  fof(f1,axiom,(
% 1.65/1.05    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.65/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.65/1.05  
% 1.65/1.05  fof(f14,plain,(
% 1.65/1.05    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) => v1_xboole_0(X0))),
% 1.65/1.05    inference(unused_predicate_definition_removal,[],[f1])).
% 1.65/1.05  
% 1.65/1.05  fof(f15,plain,(
% 1.65/1.05    ! [X0] : (v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0))),
% 1.65/1.05    inference(ennf_transformation,[],[f14])).
% 1.65/1.05  
% 1.65/1.05  fof(f22,plain,(
% 1.65/1.05    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 1.65/1.05    introduced(choice_axiom,[])).
% 1.65/1.05  
% 1.65/1.05  fof(f23,plain,(
% 1.65/1.05    ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0))),
% 1.65/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f22])).
% 1.65/1.05  
% 1.65/1.05  fof(f32,plain,(
% 1.65/1.05    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 1.65/1.05    inference(cnf_transformation,[],[f23])).
% 1.65/1.05  
% 1.65/1.05  fof(f48,plain,(
% 1.65/1.05    ~v1_xboole_0(sK2)),
% 1.65/1.05    inference(cnf_transformation,[],[f31])).
% 1.65/1.05  
% 1.65/1.05  fof(f8,axiom,(
% 1.65/1.05    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 1.65/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.65/1.05  
% 1.65/1.05  fof(f18,plain,(
% 1.65/1.05    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 1.65/1.05    inference(ennf_transformation,[],[f8])).
% 1.65/1.05  
% 1.65/1.05  fof(f41,plain,(
% 1.65/1.05    ( ! [X0] : (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)) )),
% 1.65/1.05    inference(cnf_transformation,[],[f18])).
% 1.65/1.05  
% 1.65/1.05  fof(f53,plain,(
% 1.65/1.05    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.65/1.05    inference(equality_resolution,[],[f41])).
% 1.65/1.05  
% 1.65/1.05  fof(f6,axiom,(
% 1.65/1.05    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 1.65/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.65/1.05  
% 1.65/1.05  fof(f39,plain,(
% 1.65/1.05    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 1.65/1.05    inference(cnf_transformation,[],[f6])).
% 1.65/1.05  
% 1.65/1.05  fof(f2,axiom,(
% 1.65/1.05    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.65/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.65/1.05  
% 1.65/1.05  fof(f13,plain,(
% 1.65/1.05    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.65/1.05    inference(rectify,[],[f2])).
% 1.65/1.05  
% 1.65/1.05  fof(f16,plain,(
% 1.65/1.05    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.65/1.05    inference(ennf_transformation,[],[f13])).
% 1.65/1.05  
% 1.65/1.05  fof(f24,plain,(
% 1.65/1.05    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 1.65/1.05    introduced(choice_axiom,[])).
% 1.65/1.05  
% 1.65/1.05  fof(f25,plain,(
% 1.65/1.05    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.65/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f24])).
% 1.65/1.05  
% 1.65/1.05  fof(f34,plain,(
% 1.65/1.05    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.65/1.05    inference(cnf_transformation,[],[f25])).
% 1.65/1.05  
% 1.65/1.05  fof(f7,axiom,(
% 1.65/1.05    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.65/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.65/1.05  
% 1.65/1.05  fof(f40,plain,(
% 1.65/1.05    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.65/1.05    inference(cnf_transformation,[],[f7])).
% 1.65/1.05  
% 1.65/1.05  fof(f5,axiom,(
% 1.65/1.05    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 1.65/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.65/1.05  
% 1.65/1.05  fof(f17,plain,(
% 1.65/1.05    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 1.65/1.05    inference(ennf_transformation,[],[f5])).
% 1.65/1.05  
% 1.65/1.05  fof(f38,plain,(
% 1.65/1.05    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 1.65/1.05    inference(cnf_transformation,[],[f17])).
% 1.65/1.05  
% 1.65/1.05  cnf(c_16,negated_conjecture,
% 1.65/1.05      ( r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5))
% 1.65/1.05      | r1_tarski(k2_zfmisc_1(sK3,sK2),k2_zfmisc_1(sK5,sK4)) ),
% 1.65/1.05      inference(cnf_transformation,[],[f49]) ).
% 1.65/1.05  
% 1.65/1.05  cnf(c_788,plain,
% 1.65/1.05      ( r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5)) = iProver_top
% 1.65/1.05      | r1_tarski(k2_zfmisc_1(sK3,sK2),k2_zfmisc_1(sK5,sK4)) = iProver_top ),
% 1.65/1.05      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.65/1.05  
% 1.65/1.05  cnf(c_3,plain,
% 1.65/1.05      ( ~ r1_tarski(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
% 1.65/1.05      inference(cnf_transformation,[],[f51]) ).
% 1.65/1.05  
% 1.65/1.05  cnf(c_796,plain,
% 1.65/1.05      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
% 1.65/1.05      | r1_tarski(X0,X1) != iProver_top ),
% 1.65/1.05      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 1.65/1.05  
% 1.65/1.05  cnf(c_1356,plain,
% 1.65/1.05      ( k5_xboole_0(k2_zfmisc_1(sK2,sK3),k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5))) = k1_xboole_0
% 1.65/1.05      | r1_tarski(k2_zfmisc_1(sK3,sK2),k2_zfmisc_1(sK5,sK4)) = iProver_top ),
% 1.65/1.05      inference(superposition,[status(thm)],[c_788,c_796]) ).
% 1.65/1.05  
% 1.65/1.05  cnf(c_14,plain,
% 1.65/1.05      ( r1_tarski(X0,X1)
% 1.65/1.05      | ~ r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
% 1.65/1.05      | k2_zfmisc_1(X0,X2) = k1_xboole_0 ),
% 1.65/1.05      inference(cnf_transformation,[],[f46]) ).
% 1.65/1.05  
% 1.65/1.05  cnf(c_790,plain,
% 1.65/1.05      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
% 1.65/1.05      | r1_tarski(X0,X2) = iProver_top
% 1.65/1.05      | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) != iProver_top ),
% 1.65/1.05      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 1.65/1.05  
% 1.65/1.05  cnf(c_1406,plain,
% 1.65/1.05      ( k2_zfmisc_1(sK3,sK2) = k1_xboole_0
% 1.65/1.05      | k5_xboole_0(k2_zfmisc_1(sK2,sK3),k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5))) = k1_xboole_0
% 1.65/1.05      | r1_tarski(sK3,sK5) = iProver_top ),
% 1.65/1.05      inference(superposition,[status(thm)],[c_1356,c_790]) ).
% 1.65/1.05  
% 1.65/1.05  cnf(c_15,negated_conjecture,
% 1.65/1.05      ( ~ r1_tarski(sK3,sK5) ),
% 1.65/1.05      inference(cnf_transformation,[],[f50]) ).
% 1.65/1.05  
% 1.65/1.05  cnf(c_20,plain,
% 1.65/1.05      ( r1_tarski(sK3,sK5) != iProver_top ),
% 1.65/1.05      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.65/1.05  
% 1.65/1.05  cnf(c_1821,plain,
% 1.65/1.05      ( k5_xboole_0(k2_zfmisc_1(sK2,sK3),k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5))) = k1_xboole_0
% 1.65/1.05      | k2_zfmisc_1(sK3,sK2) = k1_xboole_0 ),
% 1.65/1.05      inference(global_propositional_subsumption,[status(thm)],[c_1406,c_20]) ).
% 1.65/1.05  
% 1.65/1.05  cnf(c_1822,plain,
% 1.65/1.05      ( k2_zfmisc_1(sK3,sK2) = k1_xboole_0
% 1.65/1.05      | k5_xboole_0(k2_zfmisc_1(sK2,sK3),k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5))) = k1_xboole_0 ),
% 1.65/1.05      inference(renaming,[status(thm)],[c_1821]) ).
% 1.65/1.05  
% 1.65/1.05  cnf(c_4,plain,
% 1.65/1.05      ( r1_tarski(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
% 1.65/1.05      inference(cnf_transformation,[],[f52]) ).
% 1.65/1.05  
% 1.65/1.05  cnf(c_795,plain,
% 1.65/1.05      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
% 1.65/1.05      | r1_tarski(X0,X1) = iProver_top ),
% 1.65/1.05      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 1.65/1.05  
% 1.65/1.05  cnf(c_1825,plain,
% 1.65/1.05      ( k2_zfmisc_1(sK3,sK2) = k1_xboole_0
% 1.65/1.05      | r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5)) = iProver_top ),
% 1.65/1.05      inference(superposition,[status(thm)],[c_1822,c_795]) ).
% 1.65/1.05  
% 1.65/1.05  cnf(c_13,plain,
% 1.65/1.05      ( r1_tarski(X0,X1)
% 1.65/1.05      | ~ r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X3,X1))
% 1.65/1.05      | k2_zfmisc_1(X2,X0) = k1_xboole_0 ),
% 1.65/1.05      inference(cnf_transformation,[],[f47]) ).
% 1.65/1.05  
% 1.65/1.05  cnf(c_791,plain,
% 1.65/1.05      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
% 1.65/1.05      | r1_tarski(X1,X2) = iProver_top
% 1.65/1.05      | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X3,X2)) != iProver_top ),
% 1.65/1.05      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 1.65/1.05  
% 1.65/1.05  cnf(c_2170,plain,
% 1.65/1.05      ( k2_zfmisc_1(sK2,sK3) = k1_xboole_0
% 1.65/1.05      | k2_zfmisc_1(sK3,sK2) = k1_xboole_0
% 1.65/1.05      | r1_tarski(sK3,sK5) = iProver_top ),
% 1.65/1.05      inference(superposition,[status(thm)],[c_1825,c_791]) ).
% 1.65/1.05  
% 1.65/1.05  cnf(c_2203,plain,
% 1.65/1.05      ( r1_tarski(sK3,sK5)
% 1.65/1.05      | k2_zfmisc_1(sK2,sK3) = k1_xboole_0
% 1.65/1.05      | k2_zfmisc_1(sK3,sK2) = k1_xboole_0 ),
% 1.65/1.05      inference(predicate_to_equality_rev,[status(thm)],[c_2170]) ).
% 1.65/1.05  
% 1.65/1.05  cnf(c_2438,plain,
% 1.65/1.05      ( k2_zfmisc_1(sK3,sK2) = k1_xboole_0
% 1.65/1.05      | k2_zfmisc_1(sK2,sK3) = k1_xboole_0 ),
% 1.65/1.05      inference(global_propositional_subsumption,
% 1.65/1.05                [status(thm)],
% 1.65/1.05                [c_2170,c_15,c_2203]) ).
% 1.65/1.05  
% 1.65/1.05  cnf(c_2439,plain,
% 1.65/1.05      ( k2_zfmisc_1(sK2,sK3) = k1_xboole_0
% 1.65/1.05      | k2_zfmisc_1(sK3,sK2) = k1_xboole_0 ),
% 1.65/1.05      inference(renaming,[status(thm)],[c_2438]) ).
% 1.65/1.05  
% 1.65/1.05  cnf(c_12,plain,
% 1.65/1.05      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 1.65/1.05      | k1_xboole_0 = X0
% 1.65/1.05      | k1_xboole_0 = X1 ),
% 1.65/1.05      inference(cnf_transformation,[],[f43]) ).
% 1.65/1.05  
% 1.65/1.05  cnf(c_2446,plain,
% 1.65/1.05      ( k2_zfmisc_1(sK3,sK2) = k1_xboole_0
% 1.65/1.05      | sK2 = k1_xboole_0
% 1.65/1.05      | sK3 = k1_xboole_0 ),
% 1.65/1.05      inference(superposition,[status(thm)],[c_2439,c_12]) ).
% 1.65/1.05  
% 1.65/1.05  cnf(c_2551,plain,
% 1.65/1.05      ( sK2 = k1_xboole_0 | sK3 = k1_xboole_0 ),
% 1.65/1.05      inference(superposition,[status(thm)],[c_2446,c_12]) ).
% 1.65/1.05  
% 1.65/1.05  cnf(c_0,plain,
% 1.65/1.05      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 1.65/1.05      inference(cnf_transformation,[],[f32]) ).
% 1.65/1.05  
% 1.65/1.05  cnf(c_17,negated_conjecture,
% 1.65/1.05      ( ~ v1_xboole_0(sK2) ),
% 1.65/1.05      inference(cnf_transformation,[],[f48]) ).
% 1.65/1.05  
% 1.65/1.05  cnf(c_192,plain,
% 1.65/1.05      ( r2_hidden(sK0(X0),X0) | sK2 != X0 ),
% 1.65/1.05      inference(resolution_lifted,[status(thm)],[c_0,c_17]) ).
% 1.65/1.05  
% 1.65/1.05  cnf(c_193,plain,
% 1.65/1.05      ( r2_hidden(sK0(sK2),sK2) ),
% 1.65/1.05      inference(unflattening,[status(thm)],[c_192]) ).
% 1.65/1.05  
% 1.65/1.05  cnf(c_787,plain,
% 1.65/1.05      ( r2_hidden(sK0(sK2),sK2) = iProver_top ),
% 1.65/1.05      inference(predicate_to_equality,[status(thm)],[c_193]) ).
% 1.65/1.05  
% 1.65/1.05  cnf(c_2630,plain,
% 1.65/1.05      ( sK3 = k1_xboole_0
% 1.65/1.05      | r2_hidden(sK0(k1_xboole_0),k1_xboole_0) = iProver_top ),
% 1.65/1.05      inference(superposition,[status(thm)],[c_2551,c_787]) ).
% 1.65/1.05  
% 1.65/1.05  cnf(c_9,plain,
% 1.65/1.05      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 1.65/1.05      inference(cnf_transformation,[],[f53]) ).
% 1.65/1.05  
% 1.65/1.05  cnf(c_792,plain,
% 1.65/1.05      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 1.65/1.05      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 1.65/1.05  
% 1.65/1.05  cnf(c_6,plain,
% 1.65/1.05      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 1.65/1.05      inference(cnf_transformation,[],[f39]) ).
% 1.65/1.05  
% 1.65/1.05  cnf(c_1,plain,
% 1.65/1.05      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
% 1.65/1.05      inference(cnf_transformation,[],[f34]) ).
% 1.65/1.05  
% 1.65/1.05  cnf(c_798,plain,
% 1.65/1.05      ( r1_xboole_0(X0,X1) != iProver_top
% 1.65/1.05      | r2_hidden(X2,k3_xboole_0(X0,X1)) != iProver_top ),
% 1.65/1.05      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 1.65/1.05  
% 1.65/1.05  cnf(c_1579,plain,
% 1.65/1.05      ( r1_xboole_0(X0,k1_xboole_0) != iProver_top
% 1.65/1.05      | r2_hidden(X1,k1_xboole_0) != iProver_top ),
% 1.65/1.05      inference(superposition,[status(thm)],[c_6,c_798]) ).
% 1.65/1.05  
% 1.65/1.05  cnf(c_1590,plain,
% 1.65/1.05      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 1.65/1.05      inference(superposition,[status(thm)],[c_792,c_1579]) ).
% 1.65/1.05  
% 1.65/1.05  cnf(c_2683,plain,
% 1.65/1.05      ( sK3 = k1_xboole_0 ),
% 1.65/1.05      inference(forward_subsumption_resolution,[status(thm)],[c_2630,c_1590]) ).
% 1.65/1.05  
% 1.65/1.05  cnf(c_789,plain,
% 1.65/1.05      ( r1_tarski(sK3,sK5) != iProver_top ),
% 1.65/1.05      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.65/1.05  
% 1.65/1.05  cnf(c_2694,plain,
% 1.65/1.05      ( r1_tarski(k1_xboole_0,sK5) != iProver_top ),
% 1.65/1.05      inference(demodulation,[status(thm)],[c_2683,c_789]) ).
% 1.65/1.05  
% 1.65/1.05  cnf(c_1263,plain,
% 1.65/1.05      ( k5_xboole_0(X0,k1_xboole_0) != k1_xboole_0
% 1.65/1.05      | r1_tarski(X0,k1_xboole_0) = iProver_top ),
% 1.65/1.05      inference(superposition,[status(thm)],[c_6,c_795]) ).
% 1.65/1.05  
% 1.65/1.05  cnf(c_7,plain,
% 1.65/1.05      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 1.65/1.05      inference(cnf_transformation,[],[f40]) ).
% 1.65/1.05  
% 1.65/1.05  cnf(c_1264,plain,
% 1.65/1.05      ( k1_xboole_0 != X0 | r1_tarski(X0,k1_xboole_0) = iProver_top ),
% 1.65/1.05      inference(light_normalisation,[status(thm)],[c_1263,c_7]) ).
% 1.65/1.05  
% 1.65/1.05  cnf(c_1271,plain,
% 1.65/1.05      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 1.65/1.05      inference(equality_resolution,[status(thm)],[c_1264]) ).
% 1.65/1.05  
% 1.65/1.05  cnf(c_5,plain,
% 1.65/1.05      ( r1_tarski(X0,X1) | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ),
% 1.65/1.05      inference(cnf_transformation,[],[f38]) ).
% 1.65/1.05  
% 1.65/1.05  cnf(c_794,plain,
% 1.65/1.05      ( r1_tarski(X0,X1) = iProver_top
% 1.65/1.05      | r1_tarski(X0,k3_xboole_0(X1,X2)) != iProver_top ),
% 1.65/1.05      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 1.65/1.05  
% 1.65/1.05  cnf(c_1163,plain,
% 1.65/1.05      ( r1_tarski(X0,X1) = iProver_top
% 1.65/1.05      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 1.65/1.05      inference(superposition,[status(thm)],[c_6,c_794]) ).
% 1.65/1.05  
% 1.65/1.05  cnf(c_1298,plain,
% 1.65/1.05      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 1.65/1.05      inference(superposition,[status(thm)],[c_1271,c_1163]) ).
% 1.65/1.05  
% 1.65/1.05  cnf(c_2759,plain,
% 1.65/1.05      ( $false ),
% 1.65/1.05      inference(forward_subsumption_resolution,[status(thm)],[c_2694,c_1298]) ).
% 1.65/1.05  
% 1.65/1.05  
% 1.65/1.05  % SZS output end CNFRefutation for theBenchmark.p
% 1.65/1.05  
% 1.65/1.05  ------                               Statistics
% 1.65/1.05  
% 1.65/1.05  ------ General
% 1.65/1.05  
% 1.65/1.05  abstr_ref_over_cycles:                  0
% 1.65/1.05  abstr_ref_under_cycles:                 0
% 1.65/1.05  gc_basic_clause_elim:                   0
% 1.65/1.05  forced_gc_time:                         0
% 1.65/1.05  parsing_time:                           0.02
% 1.65/1.05  unif_index_cands_time:                  0.
% 1.65/1.05  unif_index_add_time:                    0.
% 1.65/1.05  orderings_time:                         0.
% 1.65/1.05  out_proof_time:                         0.006
% 1.65/1.05  total_time:                             0.122
% 1.65/1.05  num_of_symbols:                         45
% 1.65/1.05  num_of_terms:                           1917
% 1.65/1.05  
% 1.65/1.05  ------ Preprocessing
% 1.65/1.05  
% 1.65/1.05  num_of_splits:                          0
% 1.65/1.05  num_of_split_atoms:                     0
% 1.65/1.05  num_of_reused_defs:                     0
% 1.65/1.05  num_eq_ax_congr_red:                    13
% 1.65/1.05  num_of_sem_filtered_clauses:            1
% 1.65/1.05  num_of_subtypes:                        0
% 1.65/1.05  monotx_restored_types:                  0
% 1.65/1.05  sat_num_of_epr_types:                   0
% 1.65/1.05  sat_num_of_non_cyclic_types:            0
% 1.65/1.05  sat_guarded_non_collapsed_types:        0
% 1.65/1.05  num_pure_diseq_elim:                    0
% 1.65/1.05  simp_replaced_by:                       0
% 1.65/1.05  res_preprocessed:                       88
% 1.65/1.05  prep_upred:                             0
% 1.65/1.05  prep_unflattend:                        15
% 1.65/1.05  smt_new_axioms:                         0
% 1.65/1.05  pred_elim_cands:                        3
% 1.65/1.05  pred_elim:                              1
% 1.65/1.05  pred_elim_cl:                           1
% 1.65/1.05  pred_elim_cycles:                       5
% 1.65/1.05  merged_defs:                            8
% 1.65/1.05  merged_defs_ncl:                        0
% 1.65/1.05  bin_hyper_res:                          8
% 1.65/1.05  prep_cycles:                            4
% 1.65/1.05  pred_elim_time:                         0.001
% 1.65/1.05  splitting_time:                         0.
% 1.65/1.05  sem_filter_time:                        0.
% 1.65/1.05  monotx_time:                            0.
% 1.65/1.05  subtype_inf_time:                       0.
% 1.65/1.05  
% 1.65/1.05  ------ Problem properties
% 1.65/1.05  
% 1.65/1.05  clauses:                                17
% 1.65/1.05  conjectures:                            2
% 1.65/1.05  epr:                                    3
% 1.65/1.05  horn:                                   12
% 1.65/1.05  ground:                                 4
% 1.65/1.05  unary:                                  7
% 1.65/1.05  binary:                                 7
% 1.65/1.05  lits:                                   30
% 1.65/1.05  lits_eq:                                12
% 1.65/1.05  fd_pure:                                0
% 1.65/1.05  fd_pseudo:                              0
% 1.65/1.05  fd_cond:                                2
% 1.65/1.05  fd_pseudo_cond:                         0
% 1.65/1.05  ac_symbols:                             0
% 1.65/1.05  
% 1.65/1.05  ------ Propositional Solver
% 1.65/1.05  
% 1.65/1.05  prop_solver_calls:                      27
% 1.65/1.05  prop_fast_solver_calls:                 485
% 1.65/1.05  smt_solver_calls:                       0
% 1.65/1.05  smt_fast_solver_calls:                  0
% 1.65/1.05  prop_num_of_clauses:                    764
% 1.65/1.05  prop_preprocess_simplified:             3272
% 1.65/1.05  prop_fo_subsumed:                       9
% 1.65/1.05  prop_solver_time:                       0.
% 1.65/1.05  smt_solver_time:                        0.
% 1.65/1.05  smt_fast_solver_time:                   0.
% 1.65/1.05  prop_fast_solver_time:                  0.
% 1.65/1.05  prop_unsat_core_time:                   0.
% 1.65/1.05  
% 1.65/1.05  ------ QBF
% 1.65/1.05  
% 1.65/1.05  qbf_q_res:                              0
% 1.65/1.05  qbf_num_tautologies:                    0
% 1.65/1.05  qbf_prep_cycles:                        0
% 1.65/1.05  
% 1.65/1.05  ------ BMC1
% 1.65/1.05  
% 1.65/1.05  bmc1_current_bound:                     -1
% 1.65/1.05  bmc1_last_solved_bound:                 -1
% 1.65/1.05  bmc1_unsat_core_size:                   -1
% 1.65/1.05  bmc1_unsat_core_parents_size:           -1
% 1.65/1.05  bmc1_merge_next_fun:                    0
% 1.65/1.05  bmc1_unsat_core_clauses_time:           0.
% 1.65/1.05  
% 1.65/1.05  ------ Instantiation
% 1.65/1.05  
% 1.65/1.05  inst_num_of_clauses:                    318
% 1.65/1.05  inst_num_in_passive:                    85
% 1.65/1.05  inst_num_in_active:                     177
% 1.65/1.05  inst_num_in_unprocessed:                56
% 1.65/1.05  inst_num_of_loops:                      230
% 1.65/1.05  inst_num_of_learning_restarts:          0
% 1.65/1.05  inst_num_moves_active_passive:          50
% 1.65/1.05  inst_lit_activity:                      0
% 1.65/1.05  inst_lit_activity_moves:                0
% 1.65/1.05  inst_num_tautologies:                   0
% 1.65/1.05  inst_num_prop_implied:                  0
% 1.65/1.05  inst_num_existing_simplified:           0
% 1.65/1.05  inst_num_eq_res_simplified:             0
% 1.65/1.05  inst_num_child_elim:                    0
% 1.65/1.05  inst_num_of_dismatching_blockings:      47
% 1.65/1.05  inst_num_of_non_proper_insts:           269
% 1.65/1.05  inst_num_of_duplicates:                 0
% 1.65/1.05  inst_inst_num_from_inst_to_res:         0
% 1.65/1.05  inst_dismatching_checking_time:         0.
% 1.65/1.05  
% 1.65/1.05  ------ Resolution
% 1.65/1.05  
% 1.65/1.05  res_num_of_clauses:                     0
% 1.65/1.05  res_num_in_passive:                     0
% 1.65/1.05  res_num_in_active:                      0
% 1.65/1.05  res_num_of_loops:                       92
% 1.65/1.05  res_forward_subset_subsumed:            12
% 1.65/1.05  res_backward_subset_subsumed:           0
% 1.65/1.05  res_forward_subsumed:                   0
% 1.65/1.05  res_backward_subsumed:                  0
% 1.65/1.05  res_forward_subsumption_resolution:     0
% 1.65/1.05  res_backward_subsumption_resolution:    0
% 1.65/1.05  res_clause_to_clause_subsumption:       161
% 1.65/1.05  res_orphan_elimination:                 0
% 1.65/1.05  res_tautology_del:                      59
% 1.65/1.05  res_num_eq_res_simplified:              0
% 1.65/1.05  res_num_sel_changes:                    0
% 1.65/1.05  res_moves_from_active_to_pass:          0
% 1.65/1.05  
% 1.65/1.05  ------ Superposition
% 1.65/1.05  
% 1.65/1.05  sup_time_total:                         0.
% 1.65/1.05  sup_time_generating:                    0.
% 1.65/1.05  sup_time_sim_full:                      0.
% 1.65/1.05  sup_time_sim_immed:                     0.
% 1.65/1.05  
% 1.65/1.05  sup_num_of_clauses:                     31
% 1.65/1.05  sup_num_in_active:                      27
% 1.65/1.05  sup_num_in_passive:                     4
% 1.65/1.05  sup_num_of_loops:                       45
% 1.65/1.05  sup_fw_superposition:                   32
% 1.65/1.05  sup_bw_superposition:                   63
% 1.65/1.05  sup_immediate_simplified:               52
% 1.65/1.05  sup_given_eliminated:                   1
% 1.65/1.05  comparisons_done:                       0
% 1.65/1.05  comparisons_avoided:                    0
% 1.65/1.05  
% 1.65/1.05  ------ Simplifications
% 1.65/1.05  
% 1.65/1.05  
% 1.65/1.05  sim_fw_subset_subsumed:                 22
% 1.65/1.05  sim_bw_subset_subsumed:                 7
% 1.65/1.05  sim_fw_subsumed:                        21
% 1.65/1.05  sim_bw_subsumed:                        4
% 1.65/1.05  sim_fw_subsumption_res:                 2
% 1.65/1.05  sim_bw_subsumption_res:                 0
% 1.65/1.05  sim_tautology_del:                      1
% 1.65/1.05  sim_eq_tautology_del:                   8
% 1.65/1.05  sim_eq_res_simp:                        0
% 1.65/1.05  sim_fw_demodulated:                     19
% 1.65/1.05  sim_bw_demodulated:                     11
% 1.65/1.05  sim_light_normalised:                   1
% 1.65/1.05  sim_joinable_taut:                      0
% 1.65/1.05  sim_joinable_simp:                      0
% 1.65/1.05  sim_ac_normalised:                      0
% 1.65/1.05  sim_smt_subsumption:                    0
% 1.65/1.05  
%------------------------------------------------------------------------------
