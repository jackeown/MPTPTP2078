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
% DateTime   : Thu Dec  3 12:12:18 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 269 expanded)
%              Number of clauses        :   44 (  62 expanded)
%              Number of leaves         :   13 (  75 expanded)
%              Depth                    :   14
%              Number of atoms          :  361 (1493 expanded)
%              Number of equality atoms :   73 (  76 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ~ r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] :
          ( r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( r2_hidden(sK2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),sK2)))
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( r2_hidden(X1,k1_orders_2(sK1,k6_domain_1(u1_struct_0(sK1),X1)))
          & m1_subset_1(X1,u1_struct_0(sK1)) )
      & l1_orders_2(sK1)
      & v5_orders_2(sK1)
      & v4_orders_2(sK1)
      & v3_orders_2(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( r2_hidden(sK2,k1_orders_2(sK1,k6_domain_1(u1_struct_0(sK1),sK2)))
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_orders_2(sK1)
    & v5_orders_2(sK1)
    & v4_orders_2(sK1)
    & v3_orders_2(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f21,f27,f26])).

fof(f45,plain,(
    r2_hidden(sK2,k1_orders_2(sK1,k6_domain_1(u1_struct_0(sK1),sK2))) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f43,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f39,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f40,plain,(
    v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f42,plain,(
    v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f41,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f44,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k2_tarski(X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f36,f33])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f22])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK0(X0,X1) != X0
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( sK0(X0,X1) = X0
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK0(X0,X1) != X0
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( sK0(X0,X1) = X0
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f30,f33])).

fof(f51,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_tarski(X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f48])).

fof(f52,plain,(
    ! [X3] : r2_hidden(X3,k2_tarski(X3,X3)) ),
    inference(equality_resolution,[],[f51])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ ( r2_hidden(X1,k1_orders_2(X0,X2))
                  & r2_hidden(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_hidden(X1,k1_orders_2(X0,X2))
              | ~ r2_hidden(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_hidden(X1,k1_orders_2(X0,X2))
              | ~ r2_hidden(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k1_orders_2(X0,X2))
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_369,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_669,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k2_tarski(X2,X2))
    | X0 != X2
    | X1 != k2_tarski(X2,X2) ),
    inference(instantiation,[status(thm)],[c_369])).

cnf(c_859,plain,
    ( r2_hidden(X0,k6_domain_1(u1_struct_0(sK1),sK2))
    | ~ r2_hidden(sK2,k2_tarski(sK2,sK2))
    | X0 != sK2
    | k6_domain_1(u1_struct_0(sK1),sK2) != k2_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_669])).

cnf(c_1734,plain,
    ( r2_hidden(sK2,k6_domain_1(u1_struct_0(sK1),sK2))
    | ~ r2_hidden(sK2,k2_tarski(sK2,sK2))
    | k6_domain_1(u1_struct_0(sK1),sK2) != k2_tarski(sK2,sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_859])).

cnf(c_9,negated_conjecture,
    ( r2_hidden(sK2,k1_orders_2(sK1,k6_domain_1(u1_struct_0(sK1),sK2))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_573,plain,
    ( r2_hidden(sK2,k1_orders_2(sK1,k6_domain_1(u1_struct_0(sK1),sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k6_domain_1(u1_struct_0(X1),X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_11,negated_conjecture,
    ( l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_248,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k6_domain_1(u1_struct_0(X1),X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_11])).

cnf(c_249,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | m1_subset_1(k6_domain_1(u1_struct_0(sK1),X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_248])).

cnf(c_15,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_14,negated_conjecture,
    ( v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_253,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | m1_subset_1(k6_domain_1(u1_struct_0(sK1),X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_249,c_15,c_14])).

cnf(c_569,plain,
    ( m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k6_domain_1(u1_struct_0(sK1),X0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_253])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_12,negated_conjecture,
    ( v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_222,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_12])).

cnf(c_223,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k1_orders_2(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_222])).

cnf(c_13,negated_conjecture,
    ( v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_227,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k1_orders_2(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_223,c_15,c_14,c_13,c_11])).

cnf(c_570,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k1_orders_2(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_227])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_575,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1041,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(X1,k1_orders_2(sK1,X0)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_570,c_575])).

cnf(c_1389,plain,
    ( m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(X1,k1_orders_2(sK1,k6_domain_1(u1_struct_0(sK1),X0))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_569,c_1041])).

cnf(c_1615,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_573,c_1389])).

cnf(c_10,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_572,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_574,plain,
    ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1117,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK2) = k2_tarski(sK2,sK2)
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_572,c_574])).

cnf(c_2,plain,
    ( r2_hidden(X0,k2_tarski(X0,X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1063,plain,
    ( r2_hidden(sK2,k2_tarski(sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_367,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_727,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_367])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k1_orders_2(X1,X2))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_198,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k1_orders_2(X1,X2))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_12])).

cnf(c_199,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_orders_2(sK1,X1))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_198])).

cnf(c_203,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_orders_2(sK1,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_199,c_15,c_14,c_13,c_11])).

cnf(c_657,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ r2_hidden(sK2,X0)
    | ~ r2_hidden(sK2,k1_orders_2(sK1,X0)) ),
    inference(instantiation,[status(thm)],[c_203])).

cnf(c_706,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ r2_hidden(sK2,k6_domain_1(u1_struct_0(sK1),sK2))
    | ~ r2_hidden(sK2,k1_orders_2(sK1,k6_domain_1(u1_struct_0(sK1),sK2))) ),
    inference(instantiation,[status(thm)],[c_657])).

cnf(c_654,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_253])).

cnf(c_21,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1734,c_1615,c_1117,c_1063,c_727,c_706,c_654,c_9,c_21,c_10])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:52:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.19/1.07  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.07  
% 2.19/1.07  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.19/1.07  
% 2.19/1.07  ------  iProver source info
% 2.19/1.07  
% 2.19/1.07  git: date: 2020-06-30 10:37:57 +0100
% 2.19/1.07  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.19/1.07  git: non_committed_changes: false
% 2.19/1.07  git: last_make_outside_of_git: false
% 2.19/1.07  
% 2.19/1.07  ------ 
% 2.19/1.07  
% 2.19/1.07  ------ Input Options
% 2.19/1.07  
% 2.19/1.07  --out_options                           all
% 2.19/1.07  --tptp_safe_out                         true
% 2.19/1.07  --problem_path                          ""
% 2.19/1.07  --include_path                          ""
% 2.19/1.07  --clausifier                            res/vclausify_rel
% 2.19/1.07  --clausifier_options                    --mode clausify
% 2.19/1.07  --stdin                                 false
% 2.19/1.07  --stats_out                             all
% 2.19/1.07  
% 2.19/1.07  ------ General Options
% 2.19/1.07  
% 2.19/1.07  --fof                                   false
% 2.19/1.07  --time_out_real                         305.
% 2.19/1.07  --time_out_virtual                      -1.
% 2.19/1.07  --symbol_type_check                     false
% 2.19/1.07  --clausify_out                          false
% 2.19/1.07  --sig_cnt_out                           false
% 2.19/1.07  --trig_cnt_out                          false
% 2.19/1.07  --trig_cnt_out_tolerance                1.
% 2.19/1.07  --trig_cnt_out_sk_spl                   false
% 2.19/1.07  --abstr_cl_out                          false
% 2.19/1.07  
% 2.19/1.07  ------ Global Options
% 2.19/1.07  
% 2.19/1.07  --schedule                              default
% 2.19/1.07  --add_important_lit                     false
% 2.19/1.07  --prop_solver_per_cl                    1000
% 2.19/1.07  --min_unsat_core                        false
% 2.19/1.07  --soft_assumptions                      false
% 2.19/1.07  --soft_lemma_size                       3
% 2.19/1.07  --prop_impl_unit_size                   0
% 2.19/1.07  --prop_impl_unit                        []
% 2.19/1.07  --share_sel_clauses                     true
% 2.19/1.07  --reset_solvers                         false
% 2.19/1.07  --bc_imp_inh                            [conj_cone]
% 2.19/1.07  --conj_cone_tolerance                   3.
% 2.19/1.07  --extra_neg_conj                        none
% 2.19/1.07  --large_theory_mode                     true
% 2.19/1.07  --prolific_symb_bound                   200
% 2.19/1.07  --lt_threshold                          2000
% 2.19/1.07  --clause_weak_htbl                      true
% 2.19/1.07  --gc_record_bc_elim                     false
% 2.19/1.07  
% 2.19/1.07  ------ Preprocessing Options
% 2.19/1.07  
% 2.19/1.07  --preprocessing_flag                    true
% 2.19/1.07  --time_out_prep_mult                    0.1
% 2.19/1.07  --splitting_mode                        input
% 2.19/1.07  --splitting_grd                         true
% 2.19/1.07  --splitting_cvd                         false
% 2.19/1.07  --splitting_cvd_svl                     false
% 2.19/1.07  --splitting_nvd                         32
% 2.19/1.07  --sub_typing                            true
% 2.19/1.07  --prep_gs_sim                           true
% 2.19/1.07  --prep_unflatten                        true
% 2.19/1.07  --prep_res_sim                          true
% 2.19/1.07  --prep_upred                            true
% 2.19/1.07  --prep_sem_filter                       exhaustive
% 2.19/1.07  --prep_sem_filter_out                   false
% 2.19/1.07  --pred_elim                             true
% 2.19/1.07  --res_sim_input                         true
% 2.19/1.07  --eq_ax_congr_red                       true
% 2.19/1.07  --pure_diseq_elim                       true
% 2.19/1.07  --brand_transform                       false
% 2.19/1.07  --non_eq_to_eq                          false
% 2.19/1.07  --prep_def_merge                        true
% 2.19/1.07  --prep_def_merge_prop_impl              false
% 2.19/1.07  --prep_def_merge_mbd                    true
% 2.19/1.07  --prep_def_merge_tr_red                 false
% 2.19/1.07  --prep_def_merge_tr_cl                  false
% 2.19/1.07  --smt_preprocessing                     true
% 2.19/1.07  --smt_ac_axioms                         fast
% 2.19/1.07  --preprocessed_out                      false
% 2.19/1.07  --preprocessed_stats                    false
% 2.19/1.07  
% 2.19/1.07  ------ Abstraction refinement Options
% 2.19/1.07  
% 2.19/1.07  --abstr_ref                             []
% 2.19/1.07  --abstr_ref_prep                        false
% 2.19/1.07  --abstr_ref_until_sat                   false
% 2.19/1.07  --abstr_ref_sig_restrict                funpre
% 2.19/1.07  --abstr_ref_af_restrict_to_split_sk     false
% 2.19/1.07  --abstr_ref_under                       []
% 2.19/1.07  
% 2.19/1.07  ------ SAT Options
% 2.19/1.07  
% 2.19/1.07  --sat_mode                              false
% 2.19/1.07  --sat_fm_restart_options                ""
% 2.19/1.07  --sat_gr_def                            false
% 2.19/1.07  --sat_epr_types                         true
% 2.19/1.07  --sat_non_cyclic_types                  false
% 2.19/1.07  --sat_finite_models                     false
% 2.19/1.07  --sat_fm_lemmas                         false
% 2.19/1.07  --sat_fm_prep                           false
% 2.19/1.07  --sat_fm_uc_incr                        true
% 2.19/1.07  --sat_out_model                         small
% 2.19/1.07  --sat_out_clauses                       false
% 2.19/1.07  
% 2.19/1.07  ------ QBF Options
% 2.19/1.07  
% 2.19/1.07  --qbf_mode                              false
% 2.19/1.07  --qbf_elim_univ                         false
% 2.19/1.07  --qbf_dom_inst                          none
% 2.19/1.07  --qbf_dom_pre_inst                      false
% 2.19/1.07  --qbf_sk_in                             false
% 2.19/1.07  --qbf_pred_elim                         true
% 2.19/1.07  --qbf_split                             512
% 2.19/1.07  
% 2.19/1.07  ------ BMC1 Options
% 2.19/1.07  
% 2.19/1.07  --bmc1_incremental                      false
% 2.19/1.07  --bmc1_axioms                           reachable_all
% 2.19/1.07  --bmc1_min_bound                        0
% 2.19/1.07  --bmc1_max_bound                        -1
% 2.19/1.07  --bmc1_max_bound_default                -1
% 2.19/1.07  --bmc1_symbol_reachability              true
% 2.19/1.07  --bmc1_property_lemmas                  false
% 2.19/1.07  --bmc1_k_induction                      false
% 2.19/1.07  --bmc1_non_equiv_states                 false
% 2.19/1.07  --bmc1_deadlock                         false
% 2.19/1.07  --bmc1_ucm                              false
% 2.19/1.07  --bmc1_add_unsat_core                   none
% 2.19/1.07  --bmc1_unsat_core_children              false
% 2.19/1.07  --bmc1_unsat_core_extrapolate_axioms    false
% 2.19/1.07  --bmc1_out_stat                         full
% 2.19/1.07  --bmc1_ground_init                      false
% 2.19/1.07  --bmc1_pre_inst_next_state              false
% 2.19/1.07  --bmc1_pre_inst_state                   false
% 2.19/1.07  --bmc1_pre_inst_reach_state             false
% 2.19/1.07  --bmc1_out_unsat_core                   false
% 2.19/1.07  --bmc1_aig_witness_out                  false
% 2.19/1.07  --bmc1_verbose                          false
% 2.19/1.07  --bmc1_dump_clauses_tptp                false
% 2.19/1.07  --bmc1_dump_unsat_core_tptp             false
% 2.19/1.07  --bmc1_dump_file                        -
% 2.19/1.07  --bmc1_ucm_expand_uc_limit              128
% 2.19/1.07  --bmc1_ucm_n_expand_iterations          6
% 2.19/1.07  --bmc1_ucm_extend_mode                  1
% 2.19/1.07  --bmc1_ucm_init_mode                    2
% 2.19/1.07  --bmc1_ucm_cone_mode                    none
% 2.19/1.07  --bmc1_ucm_reduced_relation_type        0
% 2.19/1.07  --bmc1_ucm_relax_model                  4
% 2.19/1.07  --bmc1_ucm_full_tr_after_sat            true
% 2.19/1.07  --bmc1_ucm_expand_neg_assumptions       false
% 2.19/1.07  --bmc1_ucm_layered_model                none
% 2.19/1.07  --bmc1_ucm_max_lemma_size               10
% 2.19/1.07  
% 2.19/1.07  ------ AIG Options
% 2.19/1.07  
% 2.19/1.07  --aig_mode                              false
% 2.19/1.07  
% 2.19/1.07  ------ Instantiation Options
% 2.19/1.07  
% 2.19/1.07  --instantiation_flag                    true
% 2.19/1.07  --inst_sos_flag                         false
% 2.19/1.07  --inst_sos_phase                        true
% 2.19/1.07  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.19/1.07  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.19/1.07  --inst_lit_sel_side                     num_symb
% 2.19/1.07  --inst_solver_per_active                1400
% 2.19/1.07  --inst_solver_calls_frac                1.
% 2.19/1.07  --inst_passive_queue_type               priority_queues
% 2.19/1.07  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.19/1.07  --inst_passive_queues_freq              [25;2]
% 2.19/1.07  --inst_dismatching                      true
% 2.19/1.07  --inst_eager_unprocessed_to_passive     true
% 2.19/1.07  --inst_prop_sim_given                   true
% 2.19/1.07  --inst_prop_sim_new                     false
% 2.19/1.07  --inst_subs_new                         false
% 2.19/1.07  --inst_eq_res_simp                      false
% 2.19/1.07  --inst_subs_given                       false
% 2.19/1.07  --inst_orphan_elimination               true
% 2.19/1.07  --inst_learning_loop_flag               true
% 2.19/1.07  --inst_learning_start                   3000
% 2.19/1.07  --inst_learning_factor                  2
% 2.19/1.07  --inst_start_prop_sim_after_learn       3
% 2.19/1.07  --inst_sel_renew                        solver
% 2.19/1.07  --inst_lit_activity_flag                true
% 2.19/1.07  --inst_restr_to_given                   false
% 2.19/1.07  --inst_activity_threshold               500
% 2.19/1.07  --inst_out_proof                        true
% 2.19/1.07  
% 2.19/1.07  ------ Resolution Options
% 2.19/1.07  
% 2.19/1.07  --resolution_flag                       true
% 2.19/1.07  --res_lit_sel                           adaptive
% 2.19/1.07  --res_lit_sel_side                      none
% 2.19/1.07  --res_ordering                          kbo
% 2.19/1.07  --res_to_prop_solver                    active
% 2.19/1.07  --res_prop_simpl_new                    false
% 2.19/1.07  --res_prop_simpl_given                  true
% 2.19/1.07  --res_passive_queue_type                priority_queues
% 2.19/1.07  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.19/1.07  --res_passive_queues_freq               [15;5]
% 2.19/1.07  --res_forward_subs                      full
% 2.19/1.07  --res_backward_subs                     full
% 2.19/1.07  --res_forward_subs_resolution           true
% 2.19/1.07  --res_backward_subs_resolution          true
% 2.19/1.07  --res_orphan_elimination                true
% 2.19/1.07  --res_time_limit                        2.
% 2.19/1.07  --res_out_proof                         true
% 2.19/1.07  
% 2.19/1.07  ------ Superposition Options
% 2.19/1.07  
% 2.19/1.07  --superposition_flag                    true
% 2.19/1.07  --sup_passive_queue_type                priority_queues
% 2.19/1.07  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.19/1.07  --sup_passive_queues_freq               [8;1;4]
% 2.19/1.07  --demod_completeness_check              fast
% 2.19/1.07  --demod_use_ground                      true
% 2.19/1.07  --sup_to_prop_solver                    passive
% 2.19/1.07  --sup_prop_simpl_new                    true
% 2.19/1.07  --sup_prop_simpl_given                  true
% 2.19/1.07  --sup_fun_splitting                     false
% 2.19/1.07  --sup_smt_interval                      50000
% 2.19/1.07  
% 2.19/1.07  ------ Superposition Simplification Setup
% 2.19/1.07  
% 2.19/1.07  --sup_indices_passive                   []
% 2.19/1.07  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/1.07  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/1.07  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/1.07  --sup_full_triv                         [TrivRules;PropSubs]
% 2.19/1.07  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/1.07  --sup_full_bw                           [BwDemod]
% 2.19/1.07  --sup_immed_triv                        [TrivRules]
% 2.19/1.07  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.19/1.07  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/1.07  --sup_immed_bw_main                     []
% 2.19/1.07  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.19/1.07  --sup_input_triv                        [Unflattening;TrivRules]
% 2.19/1.07  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/1.07  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.19/1.07  
% 2.19/1.07  ------ Combination Options
% 2.19/1.07  
% 2.19/1.07  --comb_res_mult                         3
% 2.19/1.07  --comb_sup_mult                         2
% 2.19/1.07  --comb_inst_mult                        10
% 2.19/1.07  
% 2.19/1.07  ------ Debug Options
% 2.19/1.07  
% 2.19/1.07  --dbg_backtrace                         false
% 2.19/1.07  --dbg_dump_prop_clauses                 false
% 2.19/1.07  --dbg_dump_prop_clauses_file            -
% 2.19/1.07  --dbg_out_stat                          false
% 2.19/1.07  ------ Parsing...
% 2.19/1.07  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.19/1.07  
% 2.19/1.07  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 2.19/1.07  
% 2.19/1.07  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.19/1.07  
% 2.19/1.07  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.19/1.07  ------ Proving...
% 2.19/1.07  ------ Problem Properties 
% 2.19/1.07  
% 2.19/1.07  
% 2.19/1.07  clauses                                 11
% 2.19/1.07  conjectures                             2
% 2.19/1.07  EPR                                     0
% 2.19/1.07  Horn                                    9
% 2.19/1.07  unary                                   3
% 2.19/1.07  binary                                  3
% 2.19/1.07  lits                                    25
% 2.19/1.07  lits eq                                 6
% 2.19/1.07  fd_pure                                 0
% 2.19/1.07  fd_pseudo                               0
% 2.19/1.07  fd_cond                                 0
% 2.19/1.07  fd_pseudo_cond                          2
% 2.19/1.07  AC symbols                              0
% 2.19/1.07  
% 2.19/1.07  ------ Schedule dynamic 5 is on 
% 2.19/1.07  
% 2.19/1.07  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.19/1.07  
% 2.19/1.07  
% 2.19/1.07  ------ 
% 2.19/1.07  Current options:
% 2.19/1.07  ------ 
% 2.19/1.07  
% 2.19/1.07  ------ Input Options
% 2.19/1.07  
% 2.19/1.07  --out_options                           all
% 2.19/1.07  --tptp_safe_out                         true
% 2.19/1.07  --problem_path                          ""
% 2.19/1.07  --include_path                          ""
% 2.19/1.07  --clausifier                            res/vclausify_rel
% 2.19/1.07  --clausifier_options                    --mode clausify
% 2.19/1.07  --stdin                                 false
% 2.19/1.07  --stats_out                             all
% 2.19/1.07  
% 2.19/1.07  ------ General Options
% 2.19/1.07  
% 2.19/1.07  --fof                                   false
% 2.19/1.07  --time_out_real                         305.
% 2.19/1.07  --time_out_virtual                      -1.
% 2.19/1.07  --symbol_type_check                     false
% 2.19/1.07  --clausify_out                          false
% 2.19/1.07  --sig_cnt_out                           false
% 2.19/1.07  --trig_cnt_out                          false
% 2.19/1.07  --trig_cnt_out_tolerance                1.
% 2.19/1.07  --trig_cnt_out_sk_spl                   false
% 2.19/1.07  --abstr_cl_out                          false
% 2.19/1.07  
% 2.19/1.07  ------ Global Options
% 2.19/1.07  
% 2.19/1.07  --schedule                              default
% 2.19/1.07  --add_important_lit                     false
% 2.19/1.07  --prop_solver_per_cl                    1000
% 2.19/1.07  --min_unsat_core                        false
% 2.19/1.07  --soft_assumptions                      false
% 2.19/1.07  --soft_lemma_size                       3
% 2.19/1.07  --prop_impl_unit_size                   0
% 2.19/1.07  --prop_impl_unit                        []
% 2.19/1.07  --share_sel_clauses                     true
% 2.19/1.07  --reset_solvers                         false
% 2.19/1.07  --bc_imp_inh                            [conj_cone]
% 2.19/1.07  --conj_cone_tolerance                   3.
% 2.19/1.07  --extra_neg_conj                        none
% 2.19/1.07  --large_theory_mode                     true
% 2.19/1.07  --prolific_symb_bound                   200
% 2.19/1.07  --lt_threshold                          2000
% 2.19/1.07  --clause_weak_htbl                      true
% 2.19/1.07  --gc_record_bc_elim                     false
% 2.19/1.07  
% 2.19/1.07  ------ Preprocessing Options
% 2.19/1.07  
% 2.19/1.07  --preprocessing_flag                    true
% 2.19/1.07  --time_out_prep_mult                    0.1
% 2.19/1.07  --splitting_mode                        input
% 2.19/1.07  --splitting_grd                         true
% 2.19/1.07  --splitting_cvd                         false
% 2.19/1.07  --splitting_cvd_svl                     false
% 2.19/1.07  --splitting_nvd                         32
% 2.19/1.07  --sub_typing                            true
% 2.19/1.07  --prep_gs_sim                           true
% 2.19/1.07  --prep_unflatten                        true
% 2.19/1.07  --prep_res_sim                          true
% 2.19/1.07  --prep_upred                            true
% 2.19/1.07  --prep_sem_filter                       exhaustive
% 2.19/1.07  --prep_sem_filter_out                   false
% 2.19/1.07  --pred_elim                             true
% 2.19/1.07  --res_sim_input                         true
% 2.19/1.07  --eq_ax_congr_red                       true
% 2.19/1.07  --pure_diseq_elim                       true
% 2.19/1.07  --brand_transform                       false
% 2.19/1.07  --non_eq_to_eq                          false
% 2.19/1.07  --prep_def_merge                        true
% 2.19/1.07  --prep_def_merge_prop_impl              false
% 2.19/1.07  --prep_def_merge_mbd                    true
% 2.19/1.07  --prep_def_merge_tr_red                 false
% 2.19/1.07  --prep_def_merge_tr_cl                  false
% 2.19/1.07  --smt_preprocessing                     true
% 2.19/1.07  --smt_ac_axioms                         fast
% 2.19/1.07  --preprocessed_out                      false
% 2.19/1.07  --preprocessed_stats                    false
% 2.19/1.07  
% 2.19/1.07  ------ Abstraction refinement Options
% 2.19/1.07  
% 2.19/1.07  --abstr_ref                             []
% 2.19/1.07  --abstr_ref_prep                        false
% 2.19/1.07  --abstr_ref_until_sat                   false
% 2.19/1.07  --abstr_ref_sig_restrict                funpre
% 2.19/1.07  --abstr_ref_af_restrict_to_split_sk     false
% 2.19/1.07  --abstr_ref_under                       []
% 2.19/1.07  
% 2.19/1.07  ------ SAT Options
% 2.19/1.07  
% 2.19/1.07  --sat_mode                              false
% 2.19/1.07  --sat_fm_restart_options                ""
% 2.19/1.07  --sat_gr_def                            false
% 2.19/1.07  --sat_epr_types                         true
% 2.19/1.07  --sat_non_cyclic_types                  false
% 2.19/1.07  --sat_finite_models                     false
% 2.19/1.07  --sat_fm_lemmas                         false
% 2.19/1.07  --sat_fm_prep                           false
% 2.19/1.07  --sat_fm_uc_incr                        true
% 2.19/1.07  --sat_out_model                         small
% 2.19/1.07  --sat_out_clauses                       false
% 2.19/1.07  
% 2.19/1.07  ------ QBF Options
% 2.19/1.07  
% 2.19/1.07  --qbf_mode                              false
% 2.19/1.07  --qbf_elim_univ                         false
% 2.19/1.07  --qbf_dom_inst                          none
% 2.19/1.07  --qbf_dom_pre_inst                      false
% 2.19/1.07  --qbf_sk_in                             false
% 2.19/1.07  --qbf_pred_elim                         true
% 2.19/1.07  --qbf_split                             512
% 2.19/1.07  
% 2.19/1.07  ------ BMC1 Options
% 2.19/1.07  
% 2.19/1.07  --bmc1_incremental                      false
% 2.19/1.07  --bmc1_axioms                           reachable_all
% 2.19/1.07  --bmc1_min_bound                        0
% 2.19/1.07  --bmc1_max_bound                        -1
% 2.19/1.07  --bmc1_max_bound_default                -1
% 2.19/1.07  --bmc1_symbol_reachability              true
% 2.19/1.07  --bmc1_property_lemmas                  false
% 2.19/1.07  --bmc1_k_induction                      false
% 2.19/1.07  --bmc1_non_equiv_states                 false
% 2.19/1.07  --bmc1_deadlock                         false
% 2.19/1.07  --bmc1_ucm                              false
% 2.19/1.07  --bmc1_add_unsat_core                   none
% 2.19/1.07  --bmc1_unsat_core_children              false
% 2.19/1.07  --bmc1_unsat_core_extrapolate_axioms    false
% 2.19/1.07  --bmc1_out_stat                         full
% 2.19/1.07  --bmc1_ground_init                      false
% 2.19/1.07  --bmc1_pre_inst_next_state              false
% 2.19/1.07  --bmc1_pre_inst_state                   false
% 2.19/1.07  --bmc1_pre_inst_reach_state             false
% 2.19/1.07  --bmc1_out_unsat_core                   false
% 2.19/1.07  --bmc1_aig_witness_out                  false
% 2.19/1.07  --bmc1_verbose                          false
% 2.19/1.07  --bmc1_dump_clauses_tptp                false
% 2.19/1.07  --bmc1_dump_unsat_core_tptp             false
% 2.19/1.07  --bmc1_dump_file                        -
% 2.19/1.07  --bmc1_ucm_expand_uc_limit              128
% 2.19/1.07  --bmc1_ucm_n_expand_iterations          6
% 2.19/1.07  --bmc1_ucm_extend_mode                  1
% 2.19/1.07  --bmc1_ucm_init_mode                    2
% 2.19/1.07  --bmc1_ucm_cone_mode                    none
% 2.19/1.07  --bmc1_ucm_reduced_relation_type        0
% 2.19/1.07  --bmc1_ucm_relax_model                  4
% 2.19/1.07  --bmc1_ucm_full_tr_after_sat            true
% 2.19/1.07  --bmc1_ucm_expand_neg_assumptions       false
% 2.19/1.07  --bmc1_ucm_layered_model                none
% 2.19/1.07  --bmc1_ucm_max_lemma_size               10
% 2.19/1.07  
% 2.19/1.07  ------ AIG Options
% 2.19/1.07  
% 2.19/1.07  --aig_mode                              false
% 2.19/1.07  
% 2.19/1.07  ------ Instantiation Options
% 2.19/1.07  
% 2.19/1.07  --instantiation_flag                    true
% 2.19/1.07  --inst_sos_flag                         false
% 2.19/1.07  --inst_sos_phase                        true
% 2.19/1.07  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.19/1.07  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.19/1.07  --inst_lit_sel_side                     none
% 2.19/1.07  --inst_solver_per_active                1400
% 2.19/1.07  --inst_solver_calls_frac                1.
% 2.19/1.07  --inst_passive_queue_type               priority_queues
% 2.19/1.07  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.19/1.07  --inst_passive_queues_freq              [25;2]
% 2.19/1.07  --inst_dismatching                      true
% 2.19/1.07  --inst_eager_unprocessed_to_passive     true
% 2.19/1.07  --inst_prop_sim_given                   true
% 2.19/1.07  --inst_prop_sim_new                     false
% 2.19/1.07  --inst_subs_new                         false
% 2.19/1.07  --inst_eq_res_simp                      false
% 2.19/1.07  --inst_subs_given                       false
% 2.19/1.07  --inst_orphan_elimination               true
% 2.19/1.07  --inst_learning_loop_flag               true
% 2.19/1.07  --inst_learning_start                   3000
% 2.19/1.07  --inst_learning_factor                  2
% 2.19/1.07  --inst_start_prop_sim_after_learn       3
% 2.19/1.07  --inst_sel_renew                        solver
% 2.19/1.07  --inst_lit_activity_flag                true
% 2.19/1.07  --inst_restr_to_given                   false
% 2.19/1.07  --inst_activity_threshold               500
% 2.19/1.07  --inst_out_proof                        true
% 2.19/1.07  
% 2.19/1.07  ------ Resolution Options
% 2.19/1.07  
% 2.19/1.07  --resolution_flag                       false
% 2.19/1.07  --res_lit_sel                           adaptive
% 2.19/1.07  --res_lit_sel_side                      none
% 2.19/1.07  --res_ordering                          kbo
% 2.19/1.07  --res_to_prop_solver                    active
% 2.19/1.07  --res_prop_simpl_new                    false
% 2.19/1.07  --res_prop_simpl_given                  true
% 2.19/1.07  --res_passive_queue_type                priority_queues
% 2.19/1.07  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.19/1.07  --res_passive_queues_freq               [15;5]
% 2.19/1.07  --res_forward_subs                      full
% 2.19/1.07  --res_backward_subs                     full
% 2.19/1.07  --res_forward_subs_resolution           true
% 2.19/1.07  --res_backward_subs_resolution          true
% 2.19/1.07  --res_orphan_elimination                true
% 2.19/1.07  --res_time_limit                        2.
% 2.19/1.07  --res_out_proof                         true
% 2.19/1.07  
% 2.19/1.07  ------ Superposition Options
% 2.19/1.07  
% 2.19/1.07  --superposition_flag                    true
% 2.19/1.07  --sup_passive_queue_type                priority_queues
% 2.19/1.07  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.19/1.07  --sup_passive_queues_freq               [8;1;4]
% 2.19/1.07  --demod_completeness_check              fast
% 2.19/1.07  --demod_use_ground                      true
% 2.19/1.07  --sup_to_prop_solver                    passive
% 2.19/1.07  --sup_prop_simpl_new                    true
% 2.19/1.07  --sup_prop_simpl_given                  true
% 2.19/1.07  --sup_fun_splitting                     false
% 2.19/1.07  --sup_smt_interval                      50000
% 2.19/1.07  
% 2.19/1.07  ------ Superposition Simplification Setup
% 2.19/1.07  
% 2.19/1.07  --sup_indices_passive                   []
% 2.19/1.07  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/1.07  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/1.07  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/1.07  --sup_full_triv                         [TrivRules;PropSubs]
% 2.19/1.07  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/1.07  --sup_full_bw                           [BwDemod]
% 2.19/1.07  --sup_immed_triv                        [TrivRules]
% 2.19/1.07  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.19/1.07  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/1.07  --sup_immed_bw_main                     []
% 2.19/1.07  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.19/1.07  --sup_input_triv                        [Unflattening;TrivRules]
% 2.19/1.07  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/1.07  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.19/1.07  
% 2.19/1.07  ------ Combination Options
% 2.19/1.07  
% 2.19/1.07  --comb_res_mult                         3
% 2.19/1.07  --comb_sup_mult                         2
% 2.19/1.07  --comb_inst_mult                        10
% 2.19/1.07  
% 2.19/1.07  ------ Debug Options
% 2.19/1.07  
% 2.19/1.07  --dbg_backtrace                         false
% 2.19/1.07  --dbg_dump_prop_clauses                 false
% 2.19/1.07  --dbg_dump_prop_clauses_file            -
% 2.19/1.07  --dbg_out_stat                          false
% 2.19/1.07  
% 2.19/1.07  
% 2.19/1.07  
% 2.19/1.07  
% 2.19/1.07  ------ Proving...
% 2.19/1.07  
% 2.19/1.07  
% 2.19/1.07  % SZS status Theorem for theBenchmark.p
% 2.19/1.07  
% 2.19/1.07  % SZS output start CNFRefutation for theBenchmark.p
% 2.19/1.07  
% 2.19/1.07  fof(f8,conjecture,(
% 2.19/1.07    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))),
% 2.19/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/1.07  
% 2.19/1.07  fof(f9,negated_conjecture,(
% 2.19/1.07    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))),
% 2.19/1.07    inference(negated_conjecture,[],[f8])).
% 2.19/1.07  
% 2.19/1.07  fof(f20,plain,(
% 2.19/1.07    ? [X0] : (? [X1] : (r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 2.19/1.07    inference(ennf_transformation,[],[f9])).
% 2.19/1.07  
% 2.19/1.07  fof(f21,plain,(
% 2.19/1.07    ? [X0] : (? [X1] : (r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 2.19/1.07    inference(flattening,[],[f20])).
% 2.19/1.07  
% 2.19/1.07  fof(f27,plain,(
% 2.19/1.07    ( ! [X0] : (? [X1] : (r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,u1_struct_0(X0))) => (r2_hidden(sK2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),sK2))) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 2.19/1.07    introduced(choice_axiom,[])).
% 2.19/1.07  
% 2.19/1.07  fof(f26,plain,(
% 2.19/1.07    ? [X0] : (? [X1] : (r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (r2_hidden(X1,k1_orders_2(sK1,k6_domain_1(u1_struct_0(sK1),X1))) & m1_subset_1(X1,u1_struct_0(sK1))) & l1_orders_2(sK1) & v5_orders_2(sK1) & v4_orders_2(sK1) & v3_orders_2(sK1) & ~v2_struct_0(sK1))),
% 2.19/1.07    introduced(choice_axiom,[])).
% 2.19/1.07  
% 2.19/1.07  fof(f28,plain,(
% 2.19/1.07    (r2_hidden(sK2,k1_orders_2(sK1,k6_domain_1(u1_struct_0(sK1),sK2))) & m1_subset_1(sK2,u1_struct_0(sK1))) & l1_orders_2(sK1) & v5_orders_2(sK1) & v4_orders_2(sK1) & v3_orders_2(sK1) & ~v2_struct_0(sK1)),
% 2.19/1.07    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f21,f27,f26])).
% 2.19/1.07  
% 2.19/1.07  fof(f45,plain,(
% 2.19/1.07    r2_hidden(sK2,k1_orders_2(sK1,k6_domain_1(u1_struct_0(sK1),sK2)))),
% 2.19/1.07    inference(cnf_transformation,[],[f28])).
% 2.19/1.07  
% 2.19/1.07  fof(f6,axiom,(
% 2.19/1.07    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0))))),
% 2.19/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/1.07  
% 2.19/1.07  fof(f10,plain,(
% 2.19/1.07    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.19/1.07    inference(pure_predicate_removal,[],[f6])).
% 2.19/1.07  
% 2.19/1.07  fof(f16,plain,(
% 2.19/1.07    ! [X0] : (! [X1] : (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.19/1.07    inference(ennf_transformation,[],[f10])).
% 2.19/1.07  
% 2.19/1.07  fof(f17,plain,(
% 2.19/1.07    ! [X0] : (! [X1] : (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.19/1.07    inference(flattening,[],[f16])).
% 2.19/1.07  
% 2.19/1.07  fof(f37,plain,(
% 2.19/1.07    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.19/1.07    inference(cnf_transformation,[],[f17])).
% 2.19/1.07  
% 2.19/1.07  fof(f43,plain,(
% 2.19/1.07    l1_orders_2(sK1)),
% 2.19/1.07    inference(cnf_transformation,[],[f28])).
% 2.19/1.07  
% 2.19/1.07  fof(f39,plain,(
% 2.19/1.07    ~v2_struct_0(sK1)),
% 2.19/1.07    inference(cnf_transformation,[],[f28])).
% 2.19/1.07  
% 2.19/1.07  fof(f40,plain,(
% 2.19/1.07    v3_orders_2(sK1)),
% 2.19/1.07    inference(cnf_transformation,[],[f28])).
% 2.19/1.07  
% 2.19/1.07  fof(f4,axiom,(
% 2.19/1.07    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.19/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/1.07  
% 2.19/1.07  fof(f12,plain,(
% 2.19/1.07    ! [X0,X1] : (m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.19/1.07    inference(ennf_transformation,[],[f4])).
% 2.19/1.07  
% 2.19/1.07  fof(f13,plain,(
% 2.19/1.07    ! [X0,X1] : (m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.19/1.07    inference(flattening,[],[f12])).
% 2.19/1.07  
% 2.19/1.07  fof(f35,plain,(
% 2.19/1.07    ( ! [X0,X1] : (m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.19/1.07    inference(cnf_transformation,[],[f13])).
% 2.19/1.07  
% 2.19/1.07  fof(f42,plain,(
% 2.19/1.07    v5_orders_2(sK1)),
% 2.19/1.07    inference(cnf_transformation,[],[f28])).
% 2.19/1.07  
% 2.19/1.07  fof(f41,plain,(
% 2.19/1.07    v4_orders_2(sK1)),
% 2.19/1.07    inference(cnf_transformation,[],[f28])).
% 2.19/1.07  
% 2.19/1.07  fof(f3,axiom,(
% 2.19/1.07    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.19/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/1.07  
% 2.19/1.07  fof(f11,plain,(
% 2.19/1.07    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.19/1.07    inference(ennf_transformation,[],[f3])).
% 2.19/1.07  
% 2.19/1.07  fof(f34,plain,(
% 2.19/1.07    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.19/1.07    inference(cnf_transformation,[],[f11])).
% 2.19/1.07  
% 2.19/1.07  fof(f44,plain,(
% 2.19/1.07    m1_subset_1(sK2,u1_struct_0(sK1))),
% 2.19/1.07    inference(cnf_transformation,[],[f28])).
% 2.19/1.07  
% 2.19/1.07  fof(f5,axiom,(
% 2.19/1.07    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 2.19/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/1.07  
% 2.19/1.07  fof(f14,plain,(
% 2.19/1.07    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.19/1.07    inference(ennf_transformation,[],[f5])).
% 2.19/1.07  
% 2.19/1.07  fof(f15,plain,(
% 2.19/1.07    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.19/1.07    inference(flattening,[],[f14])).
% 2.19/1.07  
% 2.19/1.07  fof(f36,plain,(
% 2.19/1.07    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.19/1.07    inference(cnf_transformation,[],[f15])).
% 2.19/1.07  
% 2.19/1.07  fof(f2,axiom,(
% 2.19/1.07    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 2.19/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/1.07  
% 2.19/1.07  fof(f33,plain,(
% 2.19/1.07    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 2.19/1.07    inference(cnf_transformation,[],[f2])).
% 2.19/1.07  
% 2.19/1.07  fof(f50,plain,(
% 2.19/1.07    ( ! [X0,X1] : (k2_tarski(X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.19/1.07    inference(definition_unfolding,[],[f36,f33])).
% 2.19/1.07  
% 2.19/1.07  fof(f1,axiom,(
% 2.19/1.07    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.19/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/1.07  
% 2.19/1.07  fof(f22,plain,(
% 2.19/1.07    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 2.19/1.07    inference(nnf_transformation,[],[f1])).
% 2.19/1.07  
% 2.19/1.07  fof(f23,plain,(
% 2.19/1.07    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.19/1.07    inference(rectify,[],[f22])).
% 2.19/1.07  
% 2.19/1.07  fof(f24,plain,(
% 2.19/1.07    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1))))),
% 2.19/1.07    introduced(choice_axiom,[])).
% 2.19/1.07  
% 2.19/1.07  fof(f25,plain,(
% 2.19/1.07    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.19/1.07    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).
% 2.19/1.07  
% 2.19/1.07  fof(f30,plain,(
% 2.19/1.07    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 2.19/1.07    inference(cnf_transformation,[],[f25])).
% 2.19/1.07  
% 2.19/1.07  fof(f48,plain,(
% 2.19/1.07    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_tarski(X0,X0) != X1) )),
% 2.19/1.07    inference(definition_unfolding,[],[f30,f33])).
% 2.19/1.07  
% 2.19/1.07  fof(f51,plain,(
% 2.19/1.07    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_tarski(X3,X3) != X1) )),
% 2.19/1.07    inference(equality_resolution,[],[f48])).
% 2.19/1.07  
% 2.19/1.07  fof(f52,plain,(
% 2.19/1.07    ( ! [X3] : (r2_hidden(X3,k2_tarski(X3,X3))) )),
% 2.19/1.07    inference(equality_resolution,[],[f51])).
% 2.19/1.07  
% 2.19/1.07  fof(f7,axiom,(
% 2.19/1.07    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(r2_hidden(X1,k1_orders_2(X0,X2)) & r2_hidden(X1,X2)))))),
% 2.19/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/1.07  
% 2.19/1.07  fof(f18,plain,(
% 2.19/1.07    ! [X0] : (! [X1] : (! [X2] : ((~r2_hidden(X1,k1_orders_2(X0,X2)) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.19/1.07    inference(ennf_transformation,[],[f7])).
% 2.19/1.07  
% 2.19/1.07  fof(f19,plain,(
% 2.19/1.07    ! [X0] : (! [X1] : (! [X2] : (~r2_hidden(X1,k1_orders_2(X0,X2)) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.19/1.07    inference(flattening,[],[f18])).
% 2.19/1.07  
% 2.19/1.07  fof(f38,plain,(
% 2.19/1.07    ( ! [X2,X0,X1] : (~r2_hidden(X1,k1_orders_2(X0,X2)) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.19/1.07    inference(cnf_transformation,[],[f19])).
% 2.19/1.07  
% 2.19/1.07  cnf(c_369,plain,
% 2.19/1.07      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.19/1.07      theory(equality) ).
% 2.19/1.07  
% 2.19/1.07  cnf(c_669,plain,
% 2.19/1.07      ( r2_hidden(X0,X1)
% 2.19/1.07      | ~ r2_hidden(X2,k2_tarski(X2,X2))
% 2.19/1.07      | X0 != X2
% 2.19/1.07      | X1 != k2_tarski(X2,X2) ),
% 2.19/1.07      inference(instantiation,[status(thm)],[c_369]) ).
% 2.19/1.07  
% 2.19/1.07  cnf(c_859,plain,
% 2.19/1.07      ( r2_hidden(X0,k6_domain_1(u1_struct_0(sK1),sK2))
% 2.19/1.07      | ~ r2_hidden(sK2,k2_tarski(sK2,sK2))
% 2.19/1.07      | X0 != sK2
% 2.19/1.07      | k6_domain_1(u1_struct_0(sK1),sK2) != k2_tarski(sK2,sK2) ),
% 2.19/1.07      inference(instantiation,[status(thm)],[c_669]) ).
% 2.19/1.07  
% 2.19/1.07  cnf(c_1734,plain,
% 2.19/1.07      ( r2_hidden(sK2,k6_domain_1(u1_struct_0(sK1),sK2))
% 2.19/1.07      | ~ r2_hidden(sK2,k2_tarski(sK2,sK2))
% 2.19/1.07      | k6_domain_1(u1_struct_0(sK1),sK2) != k2_tarski(sK2,sK2)
% 2.19/1.07      | sK2 != sK2 ),
% 2.19/1.07      inference(instantiation,[status(thm)],[c_859]) ).
% 2.19/1.07  
% 2.19/1.07  cnf(c_9,negated_conjecture,
% 2.19/1.07      ( r2_hidden(sK2,k1_orders_2(sK1,k6_domain_1(u1_struct_0(sK1),sK2))) ),
% 2.19/1.07      inference(cnf_transformation,[],[f45]) ).
% 2.19/1.07  
% 2.19/1.07  cnf(c_573,plain,
% 2.19/1.07      ( r2_hidden(sK2,k1_orders_2(sK1,k6_domain_1(u1_struct_0(sK1),sK2))) = iProver_top ),
% 2.19/1.07      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.19/1.07  
% 2.19/1.07  cnf(c_7,plain,
% 2.19/1.07      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.19/1.07      | m1_subset_1(k6_domain_1(u1_struct_0(X1),X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.19/1.07      | v2_struct_0(X1)
% 2.19/1.07      | ~ v3_orders_2(X1)
% 2.19/1.07      | ~ l1_orders_2(X1) ),
% 2.19/1.07      inference(cnf_transformation,[],[f37]) ).
% 2.19/1.07  
% 2.19/1.07  cnf(c_11,negated_conjecture,
% 2.19/1.07      ( l1_orders_2(sK1) ),
% 2.19/1.07      inference(cnf_transformation,[],[f43]) ).
% 2.19/1.07  
% 2.19/1.07  cnf(c_248,plain,
% 2.19/1.07      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.19/1.07      | m1_subset_1(k6_domain_1(u1_struct_0(X1),X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.19/1.07      | v2_struct_0(X1)
% 2.19/1.07      | ~ v3_orders_2(X1)
% 2.19/1.07      | sK1 != X1 ),
% 2.19/1.07      inference(resolution_lifted,[status(thm)],[c_7,c_11]) ).
% 2.19/1.07  
% 2.19/1.07  cnf(c_249,plain,
% 2.19/1.07      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.19/1.07      | m1_subset_1(k6_domain_1(u1_struct_0(sK1),X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.19/1.07      | v2_struct_0(sK1)
% 2.19/1.07      | ~ v3_orders_2(sK1) ),
% 2.19/1.07      inference(unflattening,[status(thm)],[c_248]) ).
% 2.19/1.07  
% 2.19/1.07  cnf(c_15,negated_conjecture,
% 2.19/1.07      ( ~ v2_struct_0(sK1) ),
% 2.19/1.07      inference(cnf_transformation,[],[f39]) ).
% 2.19/1.07  
% 2.19/1.07  cnf(c_14,negated_conjecture,
% 2.19/1.07      ( v3_orders_2(sK1) ),
% 2.19/1.07      inference(cnf_transformation,[],[f40]) ).
% 2.19/1.07  
% 2.19/1.07  cnf(c_253,plain,
% 2.19/1.07      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.19/1.07      | m1_subset_1(k6_domain_1(u1_struct_0(sK1),X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.19/1.07      inference(global_propositional_subsumption,
% 2.19/1.07                [status(thm)],
% 2.19/1.07                [c_249,c_15,c_14]) ).
% 2.19/1.07  
% 2.19/1.07  cnf(c_569,plain,
% 2.19/1.07      ( m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 2.19/1.07      | m1_subset_1(k6_domain_1(u1_struct_0(sK1),X0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.19/1.07      inference(predicate_to_equality,[status(thm)],[c_253]) ).
% 2.19/1.07  
% 2.19/1.07  cnf(c_5,plain,
% 2.19/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.19/1.07      | m1_subset_1(k1_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.19/1.07      | v2_struct_0(X1)
% 2.19/1.07      | ~ v3_orders_2(X1)
% 2.19/1.07      | ~ v4_orders_2(X1)
% 2.19/1.07      | ~ v5_orders_2(X1)
% 2.19/1.07      | ~ l1_orders_2(X1) ),
% 2.19/1.07      inference(cnf_transformation,[],[f35]) ).
% 2.19/1.07  
% 2.19/1.07  cnf(c_12,negated_conjecture,
% 2.19/1.07      ( v5_orders_2(sK1) ),
% 2.19/1.07      inference(cnf_transformation,[],[f42]) ).
% 2.19/1.07  
% 2.19/1.07  cnf(c_222,plain,
% 2.19/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.19/1.07      | m1_subset_1(k1_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.19/1.07      | v2_struct_0(X1)
% 2.19/1.07      | ~ v3_orders_2(X1)
% 2.19/1.07      | ~ v4_orders_2(X1)
% 2.19/1.07      | ~ l1_orders_2(X1)
% 2.19/1.07      | sK1 != X1 ),
% 2.19/1.07      inference(resolution_lifted,[status(thm)],[c_5,c_12]) ).
% 2.19/1.07  
% 2.19/1.07  cnf(c_223,plain,
% 2.19/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.19/1.07      | m1_subset_1(k1_orders_2(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.19/1.07      | v2_struct_0(sK1)
% 2.19/1.07      | ~ v3_orders_2(sK1)
% 2.19/1.07      | ~ v4_orders_2(sK1)
% 2.19/1.07      | ~ l1_orders_2(sK1) ),
% 2.19/1.07      inference(unflattening,[status(thm)],[c_222]) ).
% 2.19/1.07  
% 2.19/1.07  cnf(c_13,negated_conjecture,
% 2.19/1.07      ( v4_orders_2(sK1) ),
% 2.19/1.07      inference(cnf_transformation,[],[f41]) ).
% 2.19/1.07  
% 2.19/1.07  cnf(c_227,plain,
% 2.19/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.19/1.07      | m1_subset_1(k1_orders_2(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.19/1.07      inference(global_propositional_subsumption,
% 2.19/1.07                [status(thm)],
% 2.19/1.07                [c_223,c_15,c_14,c_13,c_11]) ).
% 2.19/1.07  
% 2.19/1.07  cnf(c_570,plain,
% 2.19/1.07      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.19/1.07      | m1_subset_1(k1_orders_2(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.19/1.07      inference(predicate_to_equality,[status(thm)],[c_227]) ).
% 2.19/1.07  
% 2.19/1.07  cnf(c_4,plain,
% 2.19/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.19/1.07      | ~ r2_hidden(X2,X0)
% 2.19/1.07      | ~ v1_xboole_0(X1) ),
% 2.19/1.07      inference(cnf_transformation,[],[f34]) ).
% 2.19/1.07  
% 2.19/1.07  cnf(c_575,plain,
% 2.19/1.07      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.19/1.07      | r2_hidden(X2,X0) != iProver_top
% 2.19/1.07      | v1_xboole_0(X1) != iProver_top ),
% 2.19/1.07      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.19/1.07  
% 2.19/1.07  cnf(c_1041,plain,
% 2.19/1.07      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.19/1.07      | r2_hidden(X1,k1_orders_2(sK1,X0)) != iProver_top
% 2.19/1.07      | v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
% 2.19/1.07      inference(superposition,[status(thm)],[c_570,c_575]) ).
% 2.19/1.07  
% 2.19/1.07  cnf(c_1389,plain,
% 2.19/1.07      ( m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 2.19/1.07      | r2_hidden(X1,k1_orders_2(sK1,k6_domain_1(u1_struct_0(sK1),X0))) != iProver_top
% 2.19/1.07      | v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
% 2.19/1.07      inference(superposition,[status(thm)],[c_569,c_1041]) ).
% 2.19/1.07  
% 2.19/1.07  cnf(c_1615,plain,
% 2.19/1.07      ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 2.19/1.07      | v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
% 2.19/1.07      inference(superposition,[status(thm)],[c_573,c_1389]) ).
% 2.19/1.07  
% 2.19/1.07  cnf(c_10,negated_conjecture,
% 2.19/1.07      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 2.19/1.07      inference(cnf_transformation,[],[f44]) ).
% 2.19/1.07  
% 2.19/1.07  cnf(c_572,plain,
% 2.19/1.07      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 2.19/1.07      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.19/1.07  
% 2.19/1.07  cnf(c_6,plain,
% 2.19/1.07      ( ~ m1_subset_1(X0,X1)
% 2.19/1.07      | v1_xboole_0(X1)
% 2.19/1.07      | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
% 2.19/1.07      inference(cnf_transformation,[],[f50]) ).
% 2.19/1.07  
% 2.19/1.07  cnf(c_574,plain,
% 2.19/1.07      ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
% 2.19/1.07      | m1_subset_1(X1,X0) != iProver_top
% 2.19/1.07      | v1_xboole_0(X0) = iProver_top ),
% 2.19/1.07      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.19/1.07  
% 2.19/1.07  cnf(c_1117,plain,
% 2.19/1.07      ( k6_domain_1(u1_struct_0(sK1),sK2) = k2_tarski(sK2,sK2)
% 2.19/1.07      | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
% 2.19/1.07      inference(superposition,[status(thm)],[c_572,c_574]) ).
% 2.19/1.07  
% 2.19/1.07  cnf(c_2,plain,
% 2.19/1.07      ( r2_hidden(X0,k2_tarski(X0,X0)) ),
% 2.19/1.07      inference(cnf_transformation,[],[f52]) ).
% 2.19/1.07  
% 2.19/1.07  cnf(c_1063,plain,
% 2.19/1.07      ( r2_hidden(sK2,k2_tarski(sK2,sK2)) ),
% 2.19/1.07      inference(instantiation,[status(thm)],[c_2]) ).
% 2.19/1.07  
% 2.19/1.07  cnf(c_367,plain,( X0 = X0 ),theory(equality) ).
% 2.19/1.07  
% 2.19/1.07  cnf(c_727,plain,
% 2.19/1.07      ( sK2 = sK2 ),
% 2.19/1.07      inference(instantiation,[status(thm)],[c_367]) ).
% 2.19/1.07  
% 2.19/1.07  cnf(c_8,plain,
% 2.19/1.07      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.19/1.07      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.19/1.07      | ~ r2_hidden(X0,X2)
% 2.19/1.07      | ~ r2_hidden(X0,k1_orders_2(X1,X2))
% 2.19/1.07      | v2_struct_0(X1)
% 2.19/1.07      | ~ v3_orders_2(X1)
% 2.19/1.07      | ~ v4_orders_2(X1)
% 2.19/1.07      | ~ v5_orders_2(X1)
% 2.19/1.07      | ~ l1_orders_2(X1) ),
% 2.19/1.07      inference(cnf_transformation,[],[f38]) ).
% 2.19/1.07  
% 2.19/1.07  cnf(c_198,plain,
% 2.19/1.07      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.19/1.07      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.19/1.07      | ~ r2_hidden(X0,X2)
% 2.19/1.07      | ~ r2_hidden(X0,k1_orders_2(X1,X2))
% 2.19/1.07      | v2_struct_0(X1)
% 2.19/1.07      | ~ v3_orders_2(X1)
% 2.19/1.07      | ~ v4_orders_2(X1)
% 2.19/1.07      | ~ l1_orders_2(X1)
% 2.19/1.07      | sK1 != X1 ),
% 2.19/1.07      inference(resolution_lifted,[status(thm)],[c_8,c_12]) ).
% 2.19/1.07  
% 2.19/1.07  cnf(c_199,plain,
% 2.19/1.07      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.19/1.07      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.19/1.07      | ~ r2_hidden(X0,X1)
% 2.19/1.07      | ~ r2_hidden(X0,k1_orders_2(sK1,X1))
% 2.19/1.07      | v2_struct_0(sK1)
% 2.19/1.07      | ~ v3_orders_2(sK1)
% 2.19/1.07      | ~ v4_orders_2(sK1)
% 2.19/1.07      | ~ l1_orders_2(sK1) ),
% 2.19/1.07      inference(unflattening,[status(thm)],[c_198]) ).
% 2.19/1.07  
% 2.19/1.07  cnf(c_203,plain,
% 2.19/1.07      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.19/1.07      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.19/1.07      | ~ r2_hidden(X0,X1)
% 2.19/1.07      | ~ r2_hidden(X0,k1_orders_2(sK1,X1)) ),
% 2.19/1.07      inference(global_propositional_subsumption,
% 2.19/1.07                [status(thm)],
% 2.19/1.07                [c_199,c_15,c_14,c_13,c_11]) ).
% 2.19/1.07  
% 2.19/1.07  cnf(c_657,plain,
% 2.19/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.19/1.07      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 2.19/1.07      | ~ r2_hidden(sK2,X0)
% 2.19/1.07      | ~ r2_hidden(sK2,k1_orders_2(sK1,X0)) ),
% 2.19/1.07      inference(instantiation,[status(thm)],[c_203]) ).
% 2.19/1.07  
% 2.19/1.07  cnf(c_706,plain,
% 2.19/1.07      ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.19/1.07      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 2.19/1.07      | ~ r2_hidden(sK2,k6_domain_1(u1_struct_0(sK1),sK2))
% 2.19/1.07      | ~ r2_hidden(sK2,k1_orders_2(sK1,k6_domain_1(u1_struct_0(sK1),sK2))) ),
% 2.19/1.07      inference(instantiation,[status(thm)],[c_657]) ).
% 2.19/1.07  
% 2.19/1.07  cnf(c_654,plain,
% 2.19/1.07      ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.19/1.07      | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 2.19/1.07      inference(instantiation,[status(thm)],[c_253]) ).
% 2.19/1.07  
% 2.19/1.07  cnf(c_21,plain,
% 2.19/1.07      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 2.19/1.07      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.19/1.07  
% 2.19/1.07  cnf(contradiction,plain,
% 2.19/1.07      ( $false ),
% 2.19/1.07      inference(minisat,
% 2.19/1.07                [status(thm)],
% 2.19/1.07                [c_1734,c_1615,c_1117,c_1063,c_727,c_706,c_654,c_9,c_21,
% 2.19/1.07                 c_10]) ).
% 2.19/1.07  
% 2.19/1.07  
% 2.19/1.07  % SZS output end CNFRefutation for theBenchmark.p
% 2.19/1.07  
% 2.19/1.07  ------                               Statistics
% 2.19/1.07  
% 2.19/1.07  ------ General
% 2.19/1.07  
% 2.19/1.07  abstr_ref_over_cycles:                  0
% 2.19/1.07  abstr_ref_under_cycles:                 0
% 2.19/1.07  gc_basic_clause_elim:                   0
% 2.19/1.07  forced_gc_time:                         0
% 2.19/1.07  parsing_time:                           0.022
% 2.19/1.07  unif_index_cands_time:                  0.
% 2.19/1.07  unif_index_add_time:                    0.
% 2.19/1.07  orderings_time:                         0.
% 2.19/1.07  out_proof_time:                         0.012
% 2.19/1.07  total_time:                             0.183
% 2.19/1.07  num_of_symbols:                         47
% 2.19/1.07  num_of_terms:                           1774
% 2.19/1.07  
% 2.19/1.07  ------ Preprocessing
% 2.19/1.07  
% 2.19/1.07  num_of_splits:                          0
% 2.19/1.07  num_of_split_atoms:                     0
% 2.19/1.07  num_of_reused_defs:                     0
% 2.19/1.07  num_eq_ax_congr_red:                    15
% 2.19/1.07  num_of_sem_filtered_clauses:            1
% 2.19/1.07  num_of_subtypes:                        0
% 2.19/1.07  monotx_restored_types:                  0
% 2.19/1.07  sat_num_of_epr_types:                   0
% 2.19/1.07  sat_num_of_non_cyclic_types:            0
% 2.19/1.07  sat_guarded_non_collapsed_types:        0
% 2.19/1.07  num_pure_diseq_elim:                    0
% 2.19/1.07  simp_replaced_by:                       0
% 2.19/1.07  res_preprocessed:                       66
% 2.19/1.07  prep_upred:                             0
% 2.19/1.07  prep_unflattend:                        3
% 2.19/1.07  smt_new_axioms:                         0
% 2.19/1.07  pred_elim_cands:                        3
% 2.19/1.07  pred_elim:                              5
% 2.19/1.07  pred_elim_cl:                           5
% 2.19/1.07  pred_elim_cycles:                       8
% 2.19/1.07  merged_defs:                            0
% 2.19/1.07  merged_defs_ncl:                        0
% 2.19/1.07  bin_hyper_res:                          0
% 2.19/1.07  prep_cycles:                            4
% 2.19/1.07  pred_elim_time:                         0.004
% 2.19/1.07  splitting_time:                         0.
% 2.19/1.07  sem_filter_time:                        0.
% 2.19/1.07  monotx_time:                            0.001
% 2.19/1.07  subtype_inf_time:                       0.
% 2.19/1.07  
% 2.19/1.07  ------ Problem properties
% 2.19/1.07  
% 2.19/1.07  clauses:                                11
% 2.19/1.07  conjectures:                            2
% 2.19/1.07  epr:                                    0
% 2.19/1.07  horn:                                   9
% 2.19/1.07  ground:                                 2
% 2.19/1.07  unary:                                  3
% 2.19/1.07  binary:                                 3
% 2.19/1.07  lits:                                   25
% 2.19/1.07  lits_eq:                                6
% 2.19/1.07  fd_pure:                                0
% 2.19/1.07  fd_pseudo:                              0
% 2.19/1.07  fd_cond:                                0
% 2.19/1.07  fd_pseudo_cond:                         2
% 2.19/1.07  ac_symbols:                             0
% 2.19/1.07  
% 2.19/1.07  ------ Propositional Solver
% 2.19/1.07  
% 2.19/1.07  prop_solver_calls:                      27
% 2.19/1.07  prop_fast_solver_calls:                 407
% 2.19/1.07  smt_solver_calls:                       0
% 2.19/1.07  smt_fast_solver_calls:                  0
% 2.19/1.07  prop_num_of_clauses:                    651
% 2.19/1.07  prop_preprocess_simplified:             2644
% 2.19/1.07  prop_fo_subsumed:                       11
% 2.19/1.07  prop_solver_time:                       0.
% 2.19/1.07  smt_solver_time:                        0.
% 2.19/1.07  smt_fast_solver_time:                   0.
% 2.19/1.07  prop_fast_solver_time:                  0.
% 2.19/1.07  prop_unsat_core_time:                   0.
% 2.19/1.07  
% 2.19/1.07  ------ QBF
% 2.19/1.07  
% 2.19/1.07  qbf_q_res:                              0
% 2.19/1.07  qbf_num_tautologies:                    0
% 2.19/1.07  qbf_prep_cycles:                        0
% 2.19/1.07  
% 2.19/1.07  ------ BMC1
% 2.19/1.07  
% 2.19/1.07  bmc1_current_bound:                     -1
% 2.19/1.07  bmc1_last_solved_bound:                 -1
% 2.19/1.07  bmc1_unsat_core_size:                   -1
% 2.19/1.07  bmc1_unsat_core_parents_size:           -1
% 2.19/1.07  bmc1_merge_next_fun:                    0
% 2.19/1.07  bmc1_unsat_core_clauses_time:           0.
% 2.19/1.07  
% 2.19/1.07  ------ Instantiation
% 2.19/1.07  
% 2.19/1.07  inst_num_of_clauses:                    189
% 2.19/1.07  inst_num_in_passive:                    95
% 2.19/1.07  inst_num_in_active:                     89
% 2.19/1.07  inst_num_in_unprocessed:                4
% 2.19/1.07  inst_num_of_loops:                      96
% 2.19/1.07  inst_num_of_learning_restarts:          0
% 2.19/1.07  inst_num_moves_active_passive:          4
% 2.19/1.07  inst_lit_activity:                      0
% 2.19/1.07  inst_lit_activity_moves:                0
% 2.19/1.07  inst_num_tautologies:                   0
% 2.19/1.07  inst_num_prop_implied:                  0
% 2.19/1.07  inst_num_existing_simplified:           0
% 2.19/1.07  inst_num_eq_res_simplified:             0
% 2.19/1.07  inst_num_child_elim:                    0
% 2.19/1.07  inst_num_of_dismatching_blockings:      5
% 2.19/1.07  inst_num_of_non_proper_insts:           137
% 2.19/1.07  inst_num_of_duplicates:                 0
% 2.19/1.07  inst_inst_num_from_inst_to_res:         0
% 2.19/1.07  inst_dismatching_checking_time:         0.
% 2.19/1.07  
% 2.19/1.07  ------ Resolution
% 2.19/1.07  
% 2.19/1.07  res_num_of_clauses:                     0
% 2.19/1.07  res_num_in_passive:                     0
% 2.19/1.07  res_num_in_active:                      0
% 2.19/1.07  res_num_of_loops:                       70
% 2.19/1.07  res_forward_subset_subsumed:            20
% 2.19/1.07  res_backward_subset_subsumed:           0
% 2.19/1.07  res_forward_subsumed:                   0
% 2.19/1.07  res_backward_subsumed:                  0
% 2.19/1.07  res_forward_subsumption_resolution:     0
% 2.19/1.07  res_backward_subsumption_resolution:    0
% 2.19/1.07  res_clause_to_clause_subsumption:       46
% 2.19/1.07  res_orphan_elimination:                 0
% 2.19/1.07  res_tautology_del:                      11
% 2.19/1.07  res_num_eq_res_simplified:              0
% 2.19/1.07  res_num_sel_changes:                    0
% 2.19/1.07  res_moves_from_active_to_pass:          0
% 2.19/1.07  
% 2.19/1.07  ------ Superposition
% 2.19/1.07  
% 2.19/1.07  sup_time_total:                         0.
% 2.19/1.07  sup_time_generating:                    0.
% 2.19/1.07  sup_time_sim_full:                      0.
% 2.19/1.07  sup_time_sim_immed:                     0.
% 2.19/1.07  
% 2.19/1.07  sup_num_of_clauses:                     29
% 2.19/1.07  sup_num_in_active:                      18
% 2.19/1.07  sup_num_in_passive:                     11
% 2.19/1.07  sup_num_of_loops:                       18
% 2.19/1.07  sup_fw_superposition:                   15
% 2.19/1.07  sup_bw_superposition:                   3
% 2.19/1.07  sup_immediate_simplified:               0
% 2.19/1.07  sup_given_eliminated:                   0
% 2.19/1.07  comparisons_done:                       0
% 2.19/1.07  comparisons_avoided:                    2
% 2.19/1.07  
% 2.19/1.07  ------ Simplifications
% 2.19/1.07  
% 2.19/1.07  
% 2.19/1.07  sim_fw_subset_subsumed:                 0
% 2.19/1.07  sim_bw_subset_subsumed:                 0
% 2.19/1.07  sim_fw_subsumed:                        0
% 2.19/1.07  sim_bw_subsumed:                        0
% 2.19/1.07  sim_fw_subsumption_res:                 0
% 2.19/1.07  sim_bw_subsumption_res:                 0
% 2.19/1.07  sim_tautology_del:                      0
% 2.19/1.07  sim_eq_tautology_del:                   0
% 2.19/1.07  sim_eq_res_simp:                        0
% 2.19/1.07  sim_fw_demodulated:                     0
% 2.19/1.07  sim_bw_demodulated:                     0
% 2.19/1.07  sim_light_normalised:                   0
% 2.19/1.07  sim_joinable_taut:                      0
% 2.19/1.07  sim_joinable_simp:                      0
% 2.19/1.07  sim_ac_normalised:                      0
% 2.19/1.07  sim_smt_subsumption:                    0
% 2.19/1.07  
%------------------------------------------------------------------------------
