%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1839+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:37 EST 2020

% Result     : Theorem 3.11s
% Output     : CNFRefutation 3.11s
% Verified   : 
% Statistics : Number of formulae       :  135 (1353 expanded)
%              Number of clauses        :   82 ( 489 expanded)
%              Number of leaves         :   16 ( 300 expanded)
%              Depth                    :   29
%              Number of atoms          :  312 (3936 expanded)
%              Number of equality atoms :  137 ( 852 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] : m1_subset_1(sK1(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f4,f31])).

fof(f42,plain,(
    ! [X0] : m1_subset_1(sK1(X0),X0) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( ~ v1_xboole_0(k3_xboole_0(X0,X1))
         => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_zfmisc_1(X0)
          & ~ v1_xboole_0(X0) )
       => ! [X1] :
            ( ~ v1_xboole_0(k3_xboole_0(X0,X1))
           => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X0,X1)
          & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
      & v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X0,X1)
          & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
      & v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X0,X1)
          & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
     => ( ~ r1_tarski(X0,sK3)
        & ~ v1_xboole_0(k3_xboole_0(X0,sK3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(X0,X1)
            & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
        & v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(sK2,X1)
          & ~ v1_xboole_0(k3_xboole_0(sK2,X1)) )
      & v1_zfmisc_1(sK2)
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ~ r1_tarski(sK2,sK3)
    & ~ v1_xboole_0(k3_xboole_0(sK2,sK3))
    & v1_zfmisc_1(sK2)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f26,f35,f34])).

fof(f53,plain,(
    ~ v1_xboole_0(k3_xboole_0(sK2,sK3)) ),
    inference(cnf_transformation,[],[f36])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
     => r2_hidden(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f8])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f51,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f52,plain,(
    v1_zfmisc_1(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f2,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f27,plain,(
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

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k6_domain_1(X0,X2) = X0
          & m1_subset_1(X2,X0) )
     => ( k6_domain_1(X0,sK0(X0)) = X0
        & m1_subset_1(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ( k6_domain_1(X0,sK0(X0)) = X0
            & m1_subset_1(sK0(X0),X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).

fof(f38,plain,(
    ! [X0] :
      ( m1_subset_1(sK0(X0),X0)
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f39,plain,(
    ! [X0] :
      ( k6_domain_1(X0,sK0(X0)) = X0
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f45,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f54,plain,(
    ~ r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_5,plain,
    ( m1_subset_1(sK1(X0),X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1600,plain,
    ( m1_subset_1(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1599,plain,
    ( k6_domain_1(X0,X1) = k1_tarski(X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2669,plain,
    ( k6_domain_1(X0,sK1(X0)) = k1_tarski(sK1(X0))
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1600,c_1599])).

cnf(c_15,negated_conjecture,
    ( ~ v1_xboole_0(k3_xboole_0(sK2,sK3)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1593,plain,
    ( v1_xboole_0(k3_xboole_0(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2963,plain,
    ( k6_domain_1(k3_xboole_0(sK2,sK3),sK1(k3_xboole_0(sK2,sK3))) = k1_tarski(sK1(k3_xboole_0(sK2,sK3))) ),
    inference(superposition,[status(thm)],[c_2669,c_1593])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1601,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3036,plain,
    ( m1_subset_1(k1_tarski(sK1(k3_xboole_0(sK2,sK3))),k1_zfmisc_1(k3_xboole_0(sK2,sK3))) = iProver_top
    | m1_subset_1(sK1(k3_xboole_0(sK2,sK3)),k3_xboole_0(sK2,sK3)) != iProver_top
    | v1_xboole_0(k3_xboole_0(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2963,c_1601])).

cnf(c_20,plain,
    ( v1_xboole_0(k3_xboole_0(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3271,plain,
    ( m1_subset_1(sK1(k3_xboole_0(sK2,sK3)),k3_xboole_0(sK2,sK3)) != iProver_top
    | m1_subset_1(k1_tarski(sK1(k3_xboole_0(sK2,sK3))),k1_zfmisc_1(k3_xboole_0(sK2,sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3036,c_20])).

cnf(c_3272,plain,
    ( m1_subset_1(k1_tarski(sK1(k3_xboole_0(sK2,sK3))),k1_zfmisc_1(k3_xboole_0(sK2,sK3))) = iProver_top
    | m1_subset_1(sK1(k3_xboole_0(sK2,sK3)),k3_xboole_0(sK2,sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3271])).

cnf(c_3277,plain,
    ( m1_subset_1(k1_tarski(sK1(k3_xboole_0(sK2,sK3))),k1_zfmisc_1(k3_xboole_0(sK2,sK3))) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3272,c_1600])).

cnf(c_11,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1595,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3280,plain,
    ( r1_tarski(k1_tarski(sK1(k3_xboole_0(sK2,sK3))),k3_xboole_0(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3277,c_1595])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1596,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_9,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_237,plain,
    ( ~ r1_tarski(k1_tarski(X0),X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(resolution,[status(thm)],[c_9,c_12])).

cnf(c_1589,plain,
    ( r1_tarski(k1_tarski(X0),X1) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_237])).

cnf(c_2081,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_tarski(X2),X0) != iProver_top
    | m1_subset_1(X2,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1596,c_1589])).

cnf(c_3400,plain,
    ( r1_tarski(k3_xboole_0(sK2,sK3),X0) != iProver_top
    | m1_subset_1(sK1(k3_xboole_0(sK2,sK3)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3280,c_2081])).

cnf(c_7,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1598,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_6116,plain,
    ( k6_domain_1(X0,sK1(k3_xboole_0(sK2,sK3))) = k1_tarski(sK1(k3_xboole_0(sK2,sK3)))
    | r1_tarski(k3_xboole_0(sK2,sK3),X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3400,c_1599])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_225,plain,
    ( ~ r1_tarski(k1_tarski(X0),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(resolution,[status(thm)],[c_9,c_13])).

cnf(c_1590,plain,
    ( r1_tarski(k1_tarski(X0),X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_225])).

cnf(c_2502,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_tarski(X2),X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1596,c_1590])).

cnf(c_3399,plain,
    ( r1_tarski(k3_xboole_0(sK2,sK3),X0) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3280,c_2502])).

cnf(c_6796,plain,
    ( r1_tarski(k3_xboole_0(sK2,sK3),X0) != iProver_top
    | k6_domain_1(X0,sK1(k3_xboole_0(sK2,sK3))) = k1_tarski(sK1(k3_xboole_0(sK2,sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6116,c_3399])).

cnf(c_6797,plain,
    ( k6_domain_1(X0,sK1(k3_xboole_0(sK2,sK3))) = k1_tarski(sK1(k3_xboole_0(sK2,sK3)))
    | r1_tarski(k3_xboole_0(sK2,sK3),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6796])).

cnf(c_6804,plain,
    ( k6_domain_1(sK2,sK1(k3_xboole_0(sK2,sK3))) = k1_tarski(sK1(k3_xboole_0(sK2,sK3))) ),
    inference(superposition,[status(thm)],[c_1598,c_6797])).

cnf(c_6814,plain,
    ( m1_subset_1(k1_tarski(sK1(k3_xboole_0(sK2,sK3))),k1_zfmisc_1(sK2)) = iProver_top
    | m1_subset_1(sK1(k3_xboole_0(sK2,sK3)),sK2) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_6804,c_1601])).

cnf(c_17,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_18,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_7113,plain,
    ( m1_subset_1(sK1(k3_xboole_0(sK2,sK3)),sK2) != iProver_top
    | m1_subset_1(k1_tarski(sK1(k3_xboole_0(sK2,sK3))),k1_zfmisc_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6814,c_18])).

cnf(c_7114,plain,
    ( m1_subset_1(k1_tarski(sK1(k3_xboole_0(sK2,sK3))),k1_zfmisc_1(sK2)) = iProver_top
    | m1_subset_1(sK1(k3_xboole_0(sK2,sK3)),sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_7113])).

cnf(c_7122,plain,
    ( r1_tarski(k1_tarski(sK1(k3_xboole_0(sK2,sK3))),sK2) = iProver_top
    | m1_subset_1(sK1(k3_xboole_0(sK2,sK3)),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_7114,c_1595])).

cnf(c_16,negated_conjecture,
    ( v1_zfmisc_1(sK2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1592,plain,
    ( v1_zfmisc_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3,plain,
    ( m1_subset_1(sK0(X0),X0)
    | v1_xboole_0(X0)
    | ~ v1_zfmisc_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1602,plain,
    ( m1_subset_1(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_zfmisc_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2668,plain,
    ( k6_domain_1(X0,sK0(X0)) = k1_tarski(sK0(X0))
    | v1_xboole_0(X0) = iProver_top
    | v1_zfmisc_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1602,c_1599])).

cnf(c_3558,plain,
    ( k6_domain_1(sK2,sK0(sK2)) = k1_tarski(sK0(sK2))
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1592,c_2668])).

cnf(c_2,plain,
    ( v1_xboole_0(X0)
    | ~ v1_zfmisc_1(X0)
    | k6_domain_1(X0,sK0(X0)) = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1603,plain,
    ( k6_domain_1(X0,sK0(X0)) = X0
    | v1_xboole_0(X0) = iProver_top
    | v1_zfmisc_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2662,plain,
    ( k6_domain_1(sK2,sK0(sK2)) = sK2
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1592,c_1603])).

cnf(c_54,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_zfmisc_1(sK2)
    | k6_domain_1(sK2,sK0(sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2948,plain,
    ( k6_domain_1(sK2,sK0(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2662,c_17,c_16,c_54])).

cnf(c_3559,plain,
    ( k1_tarski(sK0(sK2)) = sK2
    | v1_xboole_0(sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3558,c_2948])).

cnf(c_3562,plain,
    ( k1_tarski(sK0(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3559,c_18])).

cnf(c_8,plain,
    ( ~ r1_tarski(k1_tarski(X0),k1_tarski(X1))
    | X1 = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1597,plain,
    ( X0 = X1
    | r1_tarski(k1_tarski(X1),k1_tarski(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3569,plain,
    ( sK0(sK2) = X0
    | r1_tarski(k1_tarski(X0),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3562,c_1597])).

cnf(c_7821,plain,
    ( sK1(k3_xboole_0(sK2,sK3)) = sK0(sK2)
    | m1_subset_1(sK1(k3_xboole_0(sK2,sK3)),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_7122,c_3569])).

cnf(c_8093,plain,
    ( sK1(k3_xboole_0(sK2,sK3)) = sK0(sK2)
    | r1_tarski(k3_xboole_0(sK2,sK3),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3400,c_7821])).

cnf(c_8320,plain,
    ( sK1(k3_xboole_0(sK2,sK3)) = sK0(sK2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8093,c_1598])).

cnf(c_8341,plain,
    ( r1_tarski(k1_tarski(sK0(sK2)),k3_xboole_0(sK2,sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8320,c_3280])).

cnf(c_8357,plain,
    ( r1_tarski(sK2,k3_xboole_0(sK2,sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8341,c_3562])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1913,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_1598])).

cnf(c_3571,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | m1_subset_1(sK0(sK2),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3562,c_2081])).

cnf(c_4427,plain,
    ( r1_tarski(sK2,k3_xboole_0(X0,X1)) != iProver_top
    | m1_subset_1(sK0(sK2),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1913,c_3571])).

cnf(c_8586,plain,
    ( m1_subset_1(sK0(sK2),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_8357,c_4427])).

cnf(c_6805,plain,
    ( k6_domain_1(sK3,sK1(k3_xboole_0(sK2,sK3))) = k1_tarski(sK1(k3_xboole_0(sK2,sK3))) ),
    inference(superposition,[status(thm)],[c_1913,c_6797])).

cnf(c_7067,plain,
    ( m1_subset_1(k1_tarski(sK1(k3_xboole_0(sK2,sK3))),k1_zfmisc_1(sK3)) = iProver_top
    | m1_subset_1(sK1(k3_xboole_0(sK2,sK3)),sK3) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_6805,c_1601])).

cnf(c_6006,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1913,c_3399])).

cnf(c_7951,plain,
    ( m1_subset_1(sK1(k3_xboole_0(sK2,sK3)),sK3) != iProver_top
    | m1_subset_1(k1_tarski(sK1(k3_xboole_0(sK2,sK3))),k1_zfmisc_1(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7067,c_6006])).

cnf(c_7952,plain,
    ( m1_subset_1(k1_tarski(sK1(k3_xboole_0(sK2,sK3))),k1_zfmisc_1(sK3)) = iProver_top
    | m1_subset_1(sK1(k3_xboole_0(sK2,sK3)),sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_7951])).

cnf(c_8323,plain,
    ( m1_subset_1(k1_tarski(sK0(sK2)),k1_zfmisc_1(sK3)) = iProver_top
    | m1_subset_1(sK0(sK2),sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8320,c_7952])).

cnf(c_8438,plain,
    ( m1_subset_1(sK0(sK2),sK3) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8323,c_3562])).

cnf(c_130,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_11])).

cnf(c_14,negated_conjecture,
    ( ~ r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_417,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_130,c_14])).

cnf(c_418,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK3)) ),
    inference(unflattening,[status(thm)],[c_417])).

cnf(c_419,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_418])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8586,c_8438,c_419])).


%------------------------------------------------------------------------------
