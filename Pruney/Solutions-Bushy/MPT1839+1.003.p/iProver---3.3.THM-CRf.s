%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1839+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:37 EST 2020

% Result     : Theorem 3.32s
% Output     : CNFRefutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 537 expanded)
%              Number of clauses        :   59 ( 184 expanded)
%              Number of leaves         :   16 ( 121 expanded)
%              Depth                    :   19
%              Number of atoms          :  281 (1678 expanded)
%              Number of equality atoms :  106 ( 364 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK1(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).

fof(f46,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK1(X0),X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( ~ v1_xboole_0(k3_xboole_0(X0,X1))
         => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_zfmisc_1(X0)
          & ~ v1_xboole_0(X0) )
       => ! [X1] :
            ( ~ v1_xboole_0(k3_xboole_0(X0,X1))
           => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X0,X1)
          & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
      & v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X0,X1)
          & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
      & v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X0,X1)
          & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
     => ( ~ r1_tarski(X0,sK4)
        & ~ v1_xboole_0(k3_xboole_0(X0,sK4)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(X0,X1)
            & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
        & v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(sK3,X1)
          & ~ v1_xboole_0(k3_xboole_0(sK3,X1)) )
      & v1_zfmisc_1(sK3)
      & ~ v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ~ r1_tarski(sK3,sK4)
    & ~ v1_xboole_0(k3_xboole_0(sK3,sK4))
    & v1_zfmisc_1(sK3)
    & ~ v1_xboole_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f25,f39,f38])).

fof(f59,plain,(
    v1_zfmisc_1(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f2,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f26,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X1] :
              ( k6_domain_1(X0,X1) = X0
              & m1_subset_1(X1,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f27,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X2] :
              ( k6_domain_1(X0,X2) = X0
              & m1_subset_1(X2,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k6_domain_1(X0,X2) = X0
          & m1_subset_1(X2,X0) )
     => ( k6_domain_1(X0,sK0(X0)) = X0
        & m1_subset_1(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ( k6_domain_1(X0,sK0(X0)) = X0
            & m1_subset_1(sK0(X0),X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f42,plain,(
    ! [X0] :
      ( m1_subset_1(sK0(X0),X0)
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f43,plain,(
    ! [X0] :
      ( k6_domain_1(X0,sK0(X0)) = X0
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f58,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f50,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f60,plain,(
    ~ v1_xboole_0(k3_xboole_0(sK3,sK4)) ),
    inference(cnf_transformation,[],[f40])).

fof(f61,plain,(
    ~ r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_4,plain,
    ( r2_hidden(sK1(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1471,plain,
    ( r2_hidden(sK1(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_8,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1467,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1462,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1460,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2933,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | m1_subset_1(X2,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1462,c_1460])).

cnf(c_4133,plain,
    ( r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top
    | m1_subset_1(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1467,c_2933])).

cnf(c_4161,plain,
    ( m1_subset_1(sK1(k3_xboole_0(X0,X1)),X0) = iProver_top
    | v1_xboole_0(k3_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1471,c_4133])).

cnf(c_10,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1465,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4840,plain,
    ( r2_hidden(sK1(k3_xboole_0(X0,X1)),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k3_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4161,c_1465])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1459,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2324,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1462,c_1459])).

cnf(c_3048,plain,
    ( r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1467,c_2324])).

cnf(c_3137,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k3_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1471,c_3048])).

cnf(c_11209,plain,
    ( r2_hidden(sK1(k3_xboole_0(X0,X1)),X0) = iProver_top
    | v1_xboole_0(k3_xboole_0(X0,X1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4840,c_3137])).

cnf(c_11217,plain,
    ( r2_hidden(sK1(k3_xboole_0(X0,X1)),X1) = iProver_top
    | v1_xboole_0(k3_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_11209])).

cnf(c_19,negated_conjecture,
    ( v1_zfmisc_1(sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1456,plain,
    ( v1_zfmisc_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3,plain,
    ( m1_subset_1(sK0(X0),X0)
    | v1_xboole_0(X0)
    | ~ v1_zfmisc_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1472,plain,
    ( m1_subset_1(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_zfmisc_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1468,plain,
    ( k6_domain_1(X0,X1) = k1_tarski(X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2820,plain,
    ( k6_domain_1(X0,sK0(X0)) = k1_tarski(sK0(X0))
    | v1_xboole_0(X0) = iProver_top
    | v1_zfmisc_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1472,c_1468])).

cnf(c_7695,plain,
    ( k6_domain_1(sK3,sK0(sK3)) = k1_tarski(sK0(sK3))
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1456,c_2820])).

cnf(c_2,plain,
    ( v1_xboole_0(X0)
    | ~ v1_zfmisc_1(X0)
    | k6_domain_1(X0,sK0(X0)) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1473,plain,
    ( k6_domain_1(X0,sK0(X0)) = X0
    | v1_xboole_0(X0) = iProver_top
    | v1_zfmisc_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2814,plain,
    ( k6_domain_1(sK3,sK0(sK3)) = sK3
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1456,c_1473])).

cnf(c_20,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_64,plain,
    ( v1_xboole_0(sK3)
    | ~ v1_zfmisc_1(sK3)
    | k6_domain_1(sK3,sK0(sK3)) = sK3 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2962,plain,
    ( k6_domain_1(sK3,sK0(sK3)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2814,c_20,c_19,c_64])).

cnf(c_7696,plain,
    ( k1_tarski(sK0(sK3)) = sK3
    | v1_xboole_0(sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7695,c_2962])).

cnf(c_21,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_7699,plain,
    ( k1_tarski(sK0(sK3)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7696,c_21])).

cnf(c_11,plain,
    ( r1_tarski(k1_tarski(X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1464,plain,
    ( r1_tarski(k1_tarski(X0),X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_9,plain,
    ( ~ r1_tarski(k1_tarski(X0),k1_tarski(X1))
    | X1 = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1466,plain,
    ( X0 = X1
    | r1_tarski(k1_tarski(X1),k1_tarski(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2474,plain,
    ( X0 = X1
    | r2_hidden(X1,k1_tarski(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1464,c_1466])).

cnf(c_7707,plain,
    ( sK0(sK3) = X0
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7699,c_2474])).

cnf(c_11404,plain,
    ( sK1(k3_xboole_0(X0,sK3)) = sK0(sK3)
    | v1_xboole_0(k3_xboole_0(sK3,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_11217,c_7707])).

cnf(c_18,negated_conjecture,
    ( ~ v1_xboole_0(k3_xboole_0(sK3,sK4)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1457,plain,
    ( v1_xboole_0(k3_xboole_0(sK3,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_12638,plain,
    ( sK1(k3_xboole_0(sK4,sK3)) = sK0(sK3) ),
    inference(superposition,[status(thm)],[c_11404,c_1457])).

cnf(c_12806,plain,
    ( r2_hidden(sK0(sK3),k3_xboole_0(sK4,sK3)) = iProver_top
    | v1_xboole_0(k3_xboole_0(sK4,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_12638,c_1471])).

cnf(c_17,negated_conjecture,
    ( ~ r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_24,plain,
    ( r1_tarski(sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_12808,plain,
    ( r2_hidden(sK0(sK3),sK4) = iProver_top
    | v1_xboole_0(k3_xboole_0(sK4,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_12638,c_11209])).

cnf(c_7708,plain,
    ( r1_tarski(sK3,X0) = iProver_top
    | r2_hidden(sK0(sK3),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7699,c_1464])).

cnf(c_12992,plain,
    ( r1_tarski(sK3,sK4) = iProver_top
    | v1_xboole_0(k3_xboole_0(sK4,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_12808,c_7708])).

cnf(c_13136,plain,
    ( v1_xboole_0(k3_xboole_0(sK4,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12806,c_24,c_12992])).

cnf(c_13141,plain,
    ( v1_xboole_0(k3_xboole_0(sK3,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_13136])).

cnf(c_23,plain,
    ( v1_xboole_0(k3_xboole_0(sK3,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13141,c_23])).


%------------------------------------------------------------------------------
