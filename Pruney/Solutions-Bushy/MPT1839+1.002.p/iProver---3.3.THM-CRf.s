%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1839+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:37 EST 2020

% Result     : Theorem 3.00s
% Output     : CNFRefutation 3.00s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 491 expanded)
%              Number of clauses        :   95 ( 178 expanded)
%              Number of leaves         :   21 ( 111 expanded)
%              Depth                    :   21
%              Number of atoms          :  380 (1510 expanded)
%              Number of equality atoms :  160 ( 316 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK1(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).

fof(f48,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK1(X0),X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( ~ v1_xboole_0(k3_xboole_0(X0,X1))
         => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_zfmisc_1(X0)
          & ~ v1_xboole_0(X0) )
       => ! [X1] :
            ( ~ v1_xboole_0(k3_xboole_0(X0,X1))
           => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X0,X1)
          & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
      & v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X0,X1)
          & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
      & v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X0,X1)
          & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
     => ( ~ r1_tarski(X0,sK3)
        & ~ v1_xboole_0(k3_xboole_0(X0,sK3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
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

fof(f42,plain,
    ( ~ r1_tarski(sK2,sK3)
    & ~ v1_xboole_0(k3_xboole_0(sK2,sK3))
    & v1_zfmisc_1(sK2)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f29,f41,f40])).

fof(f63,plain,(
    ~ v1_xboole_0(k3_xboole_0(sK2,sK3)) ),
    inference(cnf_transformation,[],[f42])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f61,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f62,plain,(
    v1_zfmisc_1(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f2,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k6_domain_1(X0,X2) = X0
          & m1_subset_1(X2,X0) )
     => ( k6_domain_1(X0,sK0(X0)) = X0
        & m1_subset_1(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ( k6_domain_1(X0,sK0(X0)) = X0
            & m1_subset_1(sK0(X0),X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).

fof(f44,plain,(
    ! [X0] :
      ( m1_subset_1(sK0(X0),X0)
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f45,plain,(
    ! [X0] :
      ( k6_domain_1(X0,sK0(X0)) = X0
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f53,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f64,plain,(
    ~ r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_4,plain,
    ( r2_hidden(sK1(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1598,plain,
    ( r2_hidden(sK1(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1593,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2184,plain,
    ( m1_subset_1(sK1(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1598,c_1593])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1595,plain,
    ( k6_domain_1(X0,X1) = k1_tarski(X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3787,plain,
    ( k6_domain_1(X0,sK1(X0)) = k1_tarski(sK1(X0))
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2184,c_1595])).

cnf(c_19,negated_conjecture,
    ( ~ v1_xboole_0(k3_xboole_0(sK2,sK3)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1583,plain,
    ( v1_xboole_0(k3_xboole_0(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3912,plain,
    ( k6_domain_1(k3_xboole_0(sK2,sK3),sK1(k3_xboole_0(sK2,sK3))) = k1_tarski(sK1(k3_xboole_0(sK2,sK3))) ),
    inference(superposition,[status(thm)],[c_3787,c_1583])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1596,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4032,plain,
    ( m1_subset_1(k1_tarski(sK1(k3_xboole_0(sK2,sK3))),k1_zfmisc_1(k3_xboole_0(sK2,sK3))) = iProver_top
    | m1_subset_1(sK1(k3_xboole_0(sK2,sK3)),k3_xboole_0(sK2,sK3)) != iProver_top
    | v1_xboole_0(k3_xboole_0(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3912,c_1596])).

cnf(c_24,plain,
    ( v1_xboole_0(k3_xboole_0(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4329,plain,
    ( m1_subset_1(sK1(k3_xboole_0(sK2,sK3)),k3_xboole_0(sK2,sK3)) != iProver_top
    | m1_subset_1(k1_tarski(sK1(k3_xboole_0(sK2,sK3))),k1_zfmisc_1(k3_xboole_0(sK2,sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4032,c_24])).

cnf(c_4330,plain,
    ( m1_subset_1(k1_tarski(sK1(k3_xboole_0(sK2,sK3))),k1_zfmisc_1(k3_xboole_0(sK2,sK3))) = iProver_top
    | m1_subset_1(sK1(k3_xboole_0(sK2,sK3)),k3_xboole_0(sK2,sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4329])).

cnf(c_15,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1587,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4337,plain,
    ( r1_tarski(k1_tarski(sK1(k3_xboole_0(sK2,sK3))),k3_xboole_0(sK2,sK3)) = iProver_top
    | m1_subset_1(sK1(k3_xboole_0(sK2,sK3)),k3_xboole_0(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4330,c_1587])).

cnf(c_13,plain,
    ( ~ r1_tarski(k1_tarski(X0),X1)
    | r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1589,plain,
    ( r1_tarski(k1_tarski(X0),X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_5193,plain,
    ( r2_hidden(sK1(k3_xboole_0(sK2,sK3)),k3_xboole_0(sK2,sK3)) = iProver_top
    | m1_subset_1(sK1(k3_xboole_0(sK2,sK3)),k3_xboole_0(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4337,c_1589])).

cnf(c_786,plain,
    ( r2_hidden(sK1(X0),X0)
    | k3_xboole_0(sK2,sK3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_19])).

cnf(c_787,plain,
    ( r2_hidden(sK1(k3_xboole_0(sK2,sK3)),k3_xboole_0(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_786])).

cnf(c_788,plain,
    ( r2_hidden(sK1(k3_xboole_0(sK2,sK3)),k3_xboole_0(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_787])).

cnf(c_6617,plain,
    ( r2_hidden(sK1(k3_xboole_0(sK2,sK3)),k3_xboole_0(sK2,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5193,c_788])).

cnf(c_8,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1594,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1588,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1586,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3322,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | m1_subset_1(X2,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1588,c_1586])).

cnf(c_3345,plain,
    ( r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top
    | m1_subset_1(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1594,c_3322])).

cnf(c_6625,plain,
    ( m1_subset_1(sK1(k3_xboole_0(sK2,sK3)),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_6617,c_3345])).

cnf(c_11,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1591,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_7641,plain,
    ( r2_hidden(sK1(k3_xboole_0(sK2,sK3)),sK2) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_6625,c_1591])).

cnf(c_21,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_22,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_7864,plain,
    ( r2_hidden(sK1(k3_xboole_0(sK2,sK3)),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7641,c_22])).

cnf(c_20,negated_conjecture,
    ( v1_zfmisc_1(sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1582,plain,
    ( v1_zfmisc_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3,plain,
    ( m1_subset_1(sK0(X0),X0)
    | v1_xboole_0(X0)
    | ~ v1_zfmisc_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1599,plain,
    ( m1_subset_1(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_zfmisc_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3054,plain,
    ( k6_domain_1(X0,sK0(X0)) = k1_tarski(sK0(X0))
    | v1_xboole_0(X0) = iProver_top
    | v1_zfmisc_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1599,c_1595])).

cnf(c_8823,plain,
    ( k6_domain_1(sK2,sK0(sK2)) = k1_tarski(sK0(sK2))
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1582,c_3054])).

cnf(c_2,plain,
    ( v1_xboole_0(X0)
    | ~ v1_zfmisc_1(X0)
    | k6_domain_1(X0,sK0(X0)) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1600,plain,
    ( k6_domain_1(X0,sK0(X0)) = X0
    | v1_xboole_0(X0) = iProver_top
    | v1_zfmisc_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2961,plain,
    ( k6_domain_1(sK2,sK0(sK2)) = sK2
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1582,c_1600])).

cnf(c_68,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_zfmisc_1(sK2)
    | k6_domain_1(sK2,sK0(sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3228,plain,
    ( k6_domain_1(sK2,sK0(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2961,c_21,c_20,c_68])).

cnf(c_8824,plain,
    ( k1_tarski(sK0(sK2)) = sK2
    | v1_xboole_0(sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8823,c_3228])).

cnf(c_9435,plain,
    ( k1_tarski(sK0(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8824,c_22])).

cnf(c_12,plain,
    ( r1_tarski(k1_tarski(X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1590,plain,
    ( r1_tarski(k1_tarski(X0),X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_10,plain,
    ( ~ r1_tarski(k1_tarski(X0),k1_tarski(X1))
    | X1 = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1592,plain,
    ( X0 = X1
    | r1_tarski(k1_tarski(X1),k1_tarski(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2379,plain,
    ( X0 = X1
    | r2_hidden(X1,k1_tarski(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1590,c_1592])).

cnf(c_9441,plain,
    ( sK0(sK2) = X0
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_9435,c_2379])).

cnf(c_9731,plain,
    ( sK1(k3_xboole_0(sK2,sK3)) = sK0(sK2) ),
    inference(superposition,[status(thm)],[c_7864,c_9441])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1805,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_1594])).

cnf(c_3347,plain,
    ( r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1805,c_3322])).

cnf(c_6624,plain,
    ( m1_subset_1(sK1(k3_xboole_0(sK2,sK3)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_6617,c_3347])).

cnf(c_7627,plain,
    ( r2_hidden(sK1(k3_xboole_0(sK2,sK3)),sK3) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_6624,c_1591])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1585,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2294,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1588,c_1585])).

cnf(c_2505,plain,
    ( r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1594,c_2294])).

cnf(c_2666,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k3_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1598,c_2505])).

cnf(c_2677,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k3_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_2666])).

cnf(c_2844,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2677,c_1583])).

cnf(c_7856,plain,
    ( r2_hidden(sK1(k3_xboole_0(sK2,sK3)),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7627,c_2844])).

cnf(c_11078,plain,
    ( r2_hidden(sK0(sK2),sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9731,c_7856])).

cnf(c_2571,plain,
    ( r1_tarski(k1_tarski(sK0(X0)),X1)
    | ~ r2_hidden(sK0(X0),X1) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_6086,plain,
    ( r1_tarski(k1_tarski(sK0(X0)),sK3)
    | ~ r2_hidden(sK0(X0),sK3) ),
    inference(instantiation,[status(thm)],[c_2571])).

cnf(c_6091,plain,
    ( r1_tarski(k1_tarski(sK0(X0)),sK3) = iProver_top
    | r2_hidden(sK0(X0),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6086])).

cnf(c_6093,plain,
    ( r1_tarski(k1_tarski(sK0(sK2)),sK3) = iProver_top
    | r2_hidden(sK0(sK2),sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6091])).

cnf(c_1080,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3515,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK2,sK3)
    | sK3 != X1
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_1080])).

cnf(c_5287,plain,
    ( ~ r1_tarski(X0,sK3)
    | r1_tarski(sK2,sK3)
    | sK3 != sK3
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_3515])).

cnf(c_6084,plain,
    ( ~ r1_tarski(k1_tarski(sK0(X0)),sK3)
    | r1_tarski(sK2,sK3)
    | sK3 != sK3
    | sK2 != k1_tarski(sK0(X0)) ),
    inference(instantiation,[status(thm)],[c_5287])).

cnf(c_6087,plain,
    ( sK3 != sK3
    | sK2 != k1_tarski(sK0(X0))
    | r1_tarski(k1_tarski(sK0(X0)),sK3) != iProver_top
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6084])).

cnf(c_6089,plain,
    ( sK3 != sK3
    | sK2 != k1_tarski(sK0(sK2))
    | r1_tarski(k1_tarski(sK0(sK2)),sK3) != iProver_top
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_6087])).

cnf(c_1072,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_5288,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1072])).

cnf(c_1073,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2768,plain,
    ( X0 != X1
    | X0 = k1_tarski(sK0(X2))
    | k1_tarski(sK0(X2)) != X1 ),
    inference(instantiation,[status(thm)],[c_1073])).

cnf(c_2769,plain,
    ( k1_tarski(sK0(sK2)) != sK2
    | sK2 = k1_tarski(sK0(sK2))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2768])).

cnf(c_1088,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1072])).

cnf(c_18,negated_conjecture,
    ( ~ r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_25,plain,
    ( r1_tarski(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11078,c_8824,c_6093,c_6089,c_5288,c_2769,c_1088,c_25,c_22])).


%------------------------------------------------------------------------------
