%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:12:25 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.02s
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
         => ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
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
          ( r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
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
          ( r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( r2_hidden(sK2,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),sK2)))
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( r2_hidden(X1,k2_orders_2(sK1,k6_domain_1(u1_struct_0(sK1),X1)))
          & m1_subset_1(X1,u1_struct_0(sK1)) )
      & l1_orders_2(sK1)
      & v5_orders_2(sK1)
      & v4_orders_2(sK1)
      & v3_orders_2(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( r2_hidden(sK2,k2_orders_2(sK1,k6_domain_1(u1_struct_0(sK1),sK2)))
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_orders_2(sK1)
    & v5_orders_2(sK1)
    & v4_orders_2(sK1)
    & v3_orders_2(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f21,f27,f26])).

fof(f45,plain,(
    r2_hidden(sK2,k2_orders_2(sK1,k6_domain_1(u1_struct_0(sK1),sK2))) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
     => m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
             => ~ ( r2_hidden(X1,k2_orders_2(X0,X2))
                  & r2_hidden(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_hidden(X1,k2_orders_2(X0,X2))
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
              ( ~ r2_hidden(X1,k2_orders_2(X0,X2))
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
      ( ~ r2_hidden(X1,k2_orders_2(X0,X2))
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
    ( r2_hidden(sK2,k2_orders_2(sK1,k6_domain_1(u1_struct_0(sK1),sK2))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_573,plain,
    ( r2_hidden(sK2,k2_orders_2(sK1,k6_domain_1(u1_struct_0(sK1),sK2))) = iProver_top ),
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
    | m1_subset_1(k2_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
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
    | m1_subset_1(k2_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_12])).

cnf(c_223,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k2_orders_2(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
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
    | m1_subset_1(k2_orders_2(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_223,c_15,c_14,c_13,c_11])).

cnf(c_570,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k2_orders_2(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
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
    | r2_hidden(X1,k2_orders_2(sK1,X0)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_570,c_575])).

cnf(c_1389,plain,
    ( m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(X1,k2_orders_2(sK1,k6_domain_1(u1_struct_0(sK1),X0))) != iProver_top
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
    | ~ r2_hidden(X0,k2_orders_2(X1,X2))
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
    | ~ r2_hidden(X0,k2_orders_2(X1,X2))
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
    | ~ r2_hidden(X0,k2_orders_2(sK1,X1))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_198])).

cnf(c_203,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k2_orders_2(sK1,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_199,c_15,c_14,c_13,c_11])).

cnf(c_657,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ r2_hidden(sK2,X0)
    | ~ r2_hidden(sK2,k2_orders_2(sK1,X0)) ),
    inference(instantiation,[status(thm)],[c_203])).

cnf(c_706,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ r2_hidden(sK2,k6_domain_1(u1_struct_0(sK1),sK2))
    | ~ r2_hidden(sK2,k2_orders_2(sK1,k6_domain_1(u1_struct_0(sK1),sK2))) ),
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
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:20:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.02/0.94  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/0.94  
% 2.02/0.94  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.02/0.94  
% 2.02/0.94  ------  iProver source info
% 2.02/0.94  
% 2.02/0.94  git: date: 2020-06-30 10:37:57 +0100
% 2.02/0.94  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.02/0.94  git: non_committed_changes: false
% 2.02/0.94  git: last_make_outside_of_git: false
% 2.02/0.94  
% 2.02/0.94  ------ 
% 2.02/0.94  
% 2.02/0.94  ------ Input Options
% 2.02/0.94  
% 2.02/0.94  --out_options                           all
% 2.02/0.94  --tptp_safe_out                         true
% 2.02/0.94  --problem_path                          ""
% 2.02/0.94  --include_path                          ""
% 2.02/0.94  --clausifier                            res/vclausify_rel
% 2.02/0.94  --clausifier_options                    --mode clausify
% 2.02/0.94  --stdin                                 false
% 2.02/0.94  --stats_out                             all
% 2.02/0.94  
% 2.02/0.94  ------ General Options
% 2.02/0.94  
% 2.02/0.94  --fof                                   false
% 2.02/0.94  --time_out_real                         305.
% 2.02/0.94  --time_out_virtual                      -1.
% 2.02/0.94  --symbol_type_check                     false
% 2.02/0.94  --clausify_out                          false
% 2.02/0.94  --sig_cnt_out                           false
% 2.02/0.94  --trig_cnt_out                          false
% 2.02/0.94  --trig_cnt_out_tolerance                1.
% 2.02/0.94  --trig_cnt_out_sk_spl                   false
% 2.02/0.94  --abstr_cl_out                          false
% 2.02/0.94  
% 2.02/0.94  ------ Global Options
% 2.02/0.94  
% 2.02/0.94  --schedule                              default
% 2.02/0.94  --add_important_lit                     false
% 2.02/0.94  --prop_solver_per_cl                    1000
% 2.02/0.94  --min_unsat_core                        false
% 2.02/0.94  --soft_assumptions                      false
% 2.02/0.94  --soft_lemma_size                       3
% 2.02/0.94  --prop_impl_unit_size                   0
% 2.02/0.94  --prop_impl_unit                        []
% 2.02/0.94  --share_sel_clauses                     true
% 2.02/0.94  --reset_solvers                         false
% 2.02/0.94  --bc_imp_inh                            [conj_cone]
% 2.02/0.94  --conj_cone_tolerance                   3.
% 2.02/0.94  --extra_neg_conj                        none
% 2.02/0.94  --large_theory_mode                     true
% 2.02/0.94  --prolific_symb_bound                   200
% 2.02/0.94  --lt_threshold                          2000
% 2.02/0.94  --clause_weak_htbl                      true
% 2.02/0.94  --gc_record_bc_elim                     false
% 2.02/0.94  
% 2.02/0.94  ------ Preprocessing Options
% 2.02/0.94  
% 2.02/0.94  --preprocessing_flag                    true
% 2.02/0.94  --time_out_prep_mult                    0.1
% 2.02/0.94  --splitting_mode                        input
% 2.02/0.94  --splitting_grd                         true
% 2.02/0.94  --splitting_cvd                         false
% 2.02/0.94  --splitting_cvd_svl                     false
% 2.02/0.94  --splitting_nvd                         32
% 2.02/0.94  --sub_typing                            true
% 2.02/0.94  --prep_gs_sim                           true
% 2.02/0.94  --prep_unflatten                        true
% 2.02/0.94  --prep_res_sim                          true
% 2.02/0.94  --prep_upred                            true
% 2.02/0.94  --prep_sem_filter                       exhaustive
% 2.02/0.94  --prep_sem_filter_out                   false
% 2.02/0.94  --pred_elim                             true
% 2.02/0.94  --res_sim_input                         true
% 2.02/0.94  --eq_ax_congr_red                       true
% 2.02/0.94  --pure_diseq_elim                       true
% 2.02/0.94  --brand_transform                       false
% 2.02/0.94  --non_eq_to_eq                          false
% 2.02/0.94  --prep_def_merge                        true
% 2.02/0.94  --prep_def_merge_prop_impl              false
% 2.02/0.94  --prep_def_merge_mbd                    true
% 2.02/0.94  --prep_def_merge_tr_red                 false
% 2.02/0.94  --prep_def_merge_tr_cl                  false
% 2.02/0.94  --smt_preprocessing                     true
% 2.02/0.94  --smt_ac_axioms                         fast
% 2.02/0.94  --preprocessed_out                      false
% 2.02/0.94  --preprocessed_stats                    false
% 2.02/0.94  
% 2.02/0.94  ------ Abstraction refinement Options
% 2.02/0.94  
% 2.02/0.94  --abstr_ref                             []
% 2.02/0.94  --abstr_ref_prep                        false
% 2.02/0.94  --abstr_ref_until_sat                   false
% 2.02/0.94  --abstr_ref_sig_restrict                funpre
% 2.02/0.94  --abstr_ref_af_restrict_to_split_sk     false
% 2.02/0.94  --abstr_ref_under                       []
% 2.02/0.94  
% 2.02/0.94  ------ SAT Options
% 2.02/0.94  
% 2.02/0.94  --sat_mode                              false
% 2.02/0.94  --sat_fm_restart_options                ""
% 2.02/0.94  --sat_gr_def                            false
% 2.02/0.94  --sat_epr_types                         true
% 2.02/0.94  --sat_non_cyclic_types                  false
% 2.02/0.94  --sat_finite_models                     false
% 2.02/0.94  --sat_fm_lemmas                         false
% 2.02/0.94  --sat_fm_prep                           false
% 2.02/0.94  --sat_fm_uc_incr                        true
% 2.02/0.94  --sat_out_model                         small
% 2.02/0.94  --sat_out_clauses                       false
% 2.02/0.94  
% 2.02/0.94  ------ QBF Options
% 2.02/0.94  
% 2.02/0.94  --qbf_mode                              false
% 2.02/0.94  --qbf_elim_univ                         false
% 2.02/0.94  --qbf_dom_inst                          none
% 2.02/0.94  --qbf_dom_pre_inst                      false
% 2.02/0.94  --qbf_sk_in                             false
% 2.02/0.94  --qbf_pred_elim                         true
% 2.02/0.94  --qbf_split                             512
% 2.02/0.94  
% 2.02/0.94  ------ BMC1 Options
% 2.02/0.94  
% 2.02/0.94  --bmc1_incremental                      false
% 2.02/0.94  --bmc1_axioms                           reachable_all
% 2.02/0.94  --bmc1_min_bound                        0
% 2.02/0.94  --bmc1_max_bound                        -1
% 2.02/0.94  --bmc1_max_bound_default                -1
% 2.02/0.94  --bmc1_symbol_reachability              true
% 2.02/0.94  --bmc1_property_lemmas                  false
% 2.02/0.94  --bmc1_k_induction                      false
% 2.02/0.94  --bmc1_non_equiv_states                 false
% 2.02/0.94  --bmc1_deadlock                         false
% 2.02/0.94  --bmc1_ucm                              false
% 2.02/0.94  --bmc1_add_unsat_core                   none
% 2.02/0.94  --bmc1_unsat_core_children              false
% 2.02/0.94  --bmc1_unsat_core_extrapolate_axioms    false
% 2.02/0.94  --bmc1_out_stat                         full
% 2.02/0.94  --bmc1_ground_init                      false
% 2.02/0.94  --bmc1_pre_inst_next_state              false
% 2.02/0.94  --bmc1_pre_inst_state                   false
% 2.02/0.94  --bmc1_pre_inst_reach_state             false
% 2.02/0.94  --bmc1_out_unsat_core                   false
% 2.02/0.94  --bmc1_aig_witness_out                  false
% 2.02/0.94  --bmc1_verbose                          false
% 2.02/0.94  --bmc1_dump_clauses_tptp                false
% 2.02/0.94  --bmc1_dump_unsat_core_tptp             false
% 2.02/0.94  --bmc1_dump_file                        -
% 2.02/0.94  --bmc1_ucm_expand_uc_limit              128
% 2.02/0.94  --bmc1_ucm_n_expand_iterations          6
% 2.02/0.94  --bmc1_ucm_extend_mode                  1
% 2.02/0.94  --bmc1_ucm_init_mode                    2
% 2.02/0.94  --bmc1_ucm_cone_mode                    none
% 2.02/0.94  --bmc1_ucm_reduced_relation_type        0
% 2.02/0.94  --bmc1_ucm_relax_model                  4
% 2.02/0.94  --bmc1_ucm_full_tr_after_sat            true
% 2.02/0.94  --bmc1_ucm_expand_neg_assumptions       false
% 2.02/0.94  --bmc1_ucm_layered_model                none
% 2.02/0.94  --bmc1_ucm_max_lemma_size               10
% 2.02/0.94  
% 2.02/0.94  ------ AIG Options
% 2.02/0.94  
% 2.02/0.94  --aig_mode                              false
% 2.02/0.94  
% 2.02/0.94  ------ Instantiation Options
% 2.02/0.94  
% 2.02/0.94  --instantiation_flag                    true
% 2.02/0.94  --inst_sos_flag                         false
% 2.02/0.94  --inst_sos_phase                        true
% 2.02/0.94  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.02/0.94  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.02/0.94  --inst_lit_sel_side                     num_symb
% 2.02/0.94  --inst_solver_per_active                1400
% 2.02/0.94  --inst_solver_calls_frac                1.
% 2.02/0.94  --inst_passive_queue_type               priority_queues
% 2.02/0.94  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.02/0.94  --inst_passive_queues_freq              [25;2]
% 2.02/0.94  --inst_dismatching                      true
% 2.02/0.94  --inst_eager_unprocessed_to_passive     true
% 2.02/0.94  --inst_prop_sim_given                   true
% 2.02/0.94  --inst_prop_sim_new                     false
% 2.02/0.94  --inst_subs_new                         false
% 2.02/0.94  --inst_eq_res_simp                      false
% 2.02/0.94  --inst_subs_given                       false
% 2.02/0.94  --inst_orphan_elimination               true
% 2.02/0.94  --inst_learning_loop_flag               true
% 2.02/0.94  --inst_learning_start                   3000
% 2.02/0.94  --inst_learning_factor                  2
% 2.02/0.94  --inst_start_prop_sim_after_learn       3
% 2.02/0.94  --inst_sel_renew                        solver
% 2.02/0.94  --inst_lit_activity_flag                true
% 2.02/0.94  --inst_restr_to_given                   false
% 2.02/0.94  --inst_activity_threshold               500
% 2.02/0.94  --inst_out_proof                        true
% 2.02/0.94  
% 2.02/0.94  ------ Resolution Options
% 2.02/0.94  
% 2.02/0.94  --resolution_flag                       true
% 2.02/0.94  --res_lit_sel                           adaptive
% 2.02/0.94  --res_lit_sel_side                      none
% 2.02/0.94  --res_ordering                          kbo
% 2.02/0.94  --res_to_prop_solver                    active
% 2.02/0.94  --res_prop_simpl_new                    false
% 2.02/0.94  --res_prop_simpl_given                  true
% 2.02/0.94  --res_passive_queue_type                priority_queues
% 2.02/0.94  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.02/0.94  --res_passive_queues_freq               [15;5]
% 2.02/0.94  --res_forward_subs                      full
% 2.02/0.94  --res_backward_subs                     full
% 2.02/0.94  --res_forward_subs_resolution           true
% 2.02/0.94  --res_backward_subs_resolution          true
% 2.02/0.94  --res_orphan_elimination                true
% 2.02/0.94  --res_time_limit                        2.
% 2.02/0.94  --res_out_proof                         true
% 2.02/0.94  
% 2.02/0.94  ------ Superposition Options
% 2.02/0.94  
% 2.02/0.94  --superposition_flag                    true
% 2.02/0.94  --sup_passive_queue_type                priority_queues
% 2.02/0.94  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.02/0.94  --sup_passive_queues_freq               [8;1;4]
% 2.02/0.94  --demod_completeness_check              fast
% 2.02/0.94  --demod_use_ground                      true
% 2.02/0.94  --sup_to_prop_solver                    passive
% 2.02/0.94  --sup_prop_simpl_new                    true
% 2.02/0.94  --sup_prop_simpl_given                  true
% 2.02/0.94  --sup_fun_splitting                     false
% 2.02/0.94  --sup_smt_interval                      50000
% 2.02/0.94  
% 2.02/0.94  ------ Superposition Simplification Setup
% 2.02/0.94  
% 2.02/0.94  --sup_indices_passive                   []
% 2.02/0.94  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.02/0.94  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.02/0.94  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.02/0.94  --sup_full_triv                         [TrivRules;PropSubs]
% 2.02/0.94  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.02/0.94  --sup_full_bw                           [BwDemod]
% 2.02/0.94  --sup_immed_triv                        [TrivRules]
% 2.02/0.94  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.02/0.94  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.02/0.94  --sup_immed_bw_main                     []
% 2.02/0.94  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.02/0.94  --sup_input_triv                        [Unflattening;TrivRules]
% 2.02/0.94  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.02/0.94  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.02/0.94  
% 2.02/0.94  ------ Combination Options
% 2.02/0.94  
% 2.02/0.94  --comb_res_mult                         3
% 2.02/0.94  --comb_sup_mult                         2
% 2.02/0.94  --comb_inst_mult                        10
% 2.02/0.94  
% 2.02/0.94  ------ Debug Options
% 2.02/0.94  
% 2.02/0.94  --dbg_backtrace                         false
% 2.02/0.94  --dbg_dump_prop_clauses                 false
% 2.02/0.94  --dbg_dump_prop_clauses_file            -
% 2.02/0.94  --dbg_out_stat                          false
% 2.02/0.94  ------ Parsing...
% 2.02/0.94  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.02/0.94  
% 2.02/0.94  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 2.02/0.94  
% 2.02/0.94  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.02/0.94  
% 2.02/0.94  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.02/0.94  ------ Proving...
% 2.02/0.94  ------ Problem Properties 
% 2.02/0.94  
% 2.02/0.94  
% 2.02/0.94  clauses                                 11
% 2.02/0.94  conjectures                             2
% 2.02/0.94  EPR                                     0
% 2.02/0.94  Horn                                    9
% 2.02/0.94  unary                                   3
% 2.02/0.94  binary                                  3
% 2.02/0.94  lits                                    25
% 2.02/0.94  lits eq                                 6
% 2.02/0.94  fd_pure                                 0
% 2.02/0.94  fd_pseudo                               0
% 2.02/0.94  fd_cond                                 0
% 2.02/0.94  fd_pseudo_cond                          2
% 2.02/0.94  AC symbols                              0
% 2.02/0.94  
% 2.02/0.94  ------ Schedule dynamic 5 is on 
% 2.02/0.94  
% 2.02/0.94  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.02/0.94  
% 2.02/0.94  
% 2.02/0.94  ------ 
% 2.02/0.94  Current options:
% 2.02/0.94  ------ 
% 2.02/0.94  
% 2.02/0.94  ------ Input Options
% 2.02/0.94  
% 2.02/0.94  --out_options                           all
% 2.02/0.94  --tptp_safe_out                         true
% 2.02/0.94  --problem_path                          ""
% 2.02/0.94  --include_path                          ""
% 2.02/0.94  --clausifier                            res/vclausify_rel
% 2.02/0.94  --clausifier_options                    --mode clausify
% 2.02/0.94  --stdin                                 false
% 2.02/0.94  --stats_out                             all
% 2.02/0.94  
% 2.02/0.94  ------ General Options
% 2.02/0.94  
% 2.02/0.94  --fof                                   false
% 2.02/0.94  --time_out_real                         305.
% 2.02/0.94  --time_out_virtual                      -1.
% 2.02/0.94  --symbol_type_check                     false
% 2.02/0.94  --clausify_out                          false
% 2.02/0.94  --sig_cnt_out                           false
% 2.02/0.94  --trig_cnt_out                          false
% 2.02/0.94  --trig_cnt_out_tolerance                1.
% 2.02/0.94  --trig_cnt_out_sk_spl                   false
% 2.02/0.94  --abstr_cl_out                          false
% 2.02/0.94  
% 2.02/0.94  ------ Global Options
% 2.02/0.94  
% 2.02/0.94  --schedule                              default
% 2.02/0.94  --add_important_lit                     false
% 2.02/0.94  --prop_solver_per_cl                    1000
% 2.02/0.94  --min_unsat_core                        false
% 2.02/0.94  --soft_assumptions                      false
% 2.02/0.94  --soft_lemma_size                       3
% 2.02/0.94  --prop_impl_unit_size                   0
% 2.02/0.94  --prop_impl_unit                        []
% 2.02/0.94  --share_sel_clauses                     true
% 2.02/0.94  --reset_solvers                         false
% 2.02/0.94  --bc_imp_inh                            [conj_cone]
% 2.02/0.94  --conj_cone_tolerance                   3.
% 2.02/0.95  --extra_neg_conj                        none
% 2.02/0.95  --large_theory_mode                     true
% 2.02/0.95  --prolific_symb_bound                   200
% 2.02/0.95  --lt_threshold                          2000
% 2.02/0.95  --clause_weak_htbl                      true
% 2.02/0.95  --gc_record_bc_elim                     false
% 2.02/0.95  
% 2.02/0.95  ------ Preprocessing Options
% 2.02/0.95  
% 2.02/0.95  --preprocessing_flag                    true
% 2.02/0.95  --time_out_prep_mult                    0.1
% 2.02/0.95  --splitting_mode                        input
% 2.02/0.95  --splitting_grd                         true
% 2.02/0.95  --splitting_cvd                         false
% 2.02/0.95  --splitting_cvd_svl                     false
% 2.02/0.95  --splitting_nvd                         32
% 2.02/0.95  --sub_typing                            true
% 2.02/0.95  --prep_gs_sim                           true
% 2.02/0.95  --prep_unflatten                        true
% 2.02/0.95  --prep_res_sim                          true
% 2.02/0.95  --prep_upred                            true
% 2.02/0.95  --prep_sem_filter                       exhaustive
% 2.02/0.95  --prep_sem_filter_out                   false
% 2.02/0.95  --pred_elim                             true
% 2.02/0.95  --res_sim_input                         true
% 2.02/0.95  --eq_ax_congr_red                       true
% 2.02/0.95  --pure_diseq_elim                       true
% 2.02/0.95  --brand_transform                       false
% 2.02/0.95  --non_eq_to_eq                          false
% 2.02/0.95  --prep_def_merge                        true
% 2.02/0.95  --prep_def_merge_prop_impl              false
% 2.02/0.95  --prep_def_merge_mbd                    true
% 2.02/0.95  --prep_def_merge_tr_red                 false
% 2.02/0.95  --prep_def_merge_tr_cl                  false
% 2.02/0.95  --smt_preprocessing                     true
% 2.02/0.95  --smt_ac_axioms                         fast
% 2.02/0.95  --preprocessed_out                      false
% 2.02/0.95  --preprocessed_stats                    false
% 2.02/0.95  
% 2.02/0.95  ------ Abstraction refinement Options
% 2.02/0.95  
% 2.02/0.95  --abstr_ref                             []
% 2.02/0.95  --abstr_ref_prep                        false
% 2.02/0.95  --abstr_ref_until_sat                   false
% 2.02/0.95  --abstr_ref_sig_restrict                funpre
% 2.02/0.95  --abstr_ref_af_restrict_to_split_sk     false
% 2.02/0.95  --abstr_ref_under                       []
% 2.02/0.95  
% 2.02/0.95  ------ SAT Options
% 2.02/0.95  
% 2.02/0.95  --sat_mode                              false
% 2.02/0.95  --sat_fm_restart_options                ""
% 2.02/0.95  --sat_gr_def                            false
% 2.02/0.95  --sat_epr_types                         true
% 2.02/0.95  --sat_non_cyclic_types                  false
% 2.02/0.95  --sat_finite_models                     false
% 2.02/0.95  --sat_fm_lemmas                         false
% 2.02/0.95  --sat_fm_prep                           false
% 2.02/0.95  --sat_fm_uc_incr                        true
% 2.02/0.95  --sat_out_model                         small
% 2.02/0.95  --sat_out_clauses                       false
% 2.02/0.95  
% 2.02/0.95  ------ QBF Options
% 2.02/0.95  
% 2.02/0.95  --qbf_mode                              false
% 2.02/0.95  --qbf_elim_univ                         false
% 2.02/0.95  --qbf_dom_inst                          none
% 2.02/0.95  --qbf_dom_pre_inst                      false
% 2.02/0.95  --qbf_sk_in                             false
% 2.02/0.95  --qbf_pred_elim                         true
% 2.02/0.95  --qbf_split                             512
% 2.02/0.95  
% 2.02/0.95  ------ BMC1 Options
% 2.02/0.95  
% 2.02/0.95  --bmc1_incremental                      false
% 2.02/0.95  --bmc1_axioms                           reachable_all
% 2.02/0.95  --bmc1_min_bound                        0
% 2.02/0.95  --bmc1_max_bound                        -1
% 2.02/0.95  --bmc1_max_bound_default                -1
% 2.02/0.95  --bmc1_symbol_reachability              true
% 2.02/0.95  --bmc1_property_lemmas                  false
% 2.02/0.95  --bmc1_k_induction                      false
% 2.02/0.95  --bmc1_non_equiv_states                 false
% 2.02/0.95  --bmc1_deadlock                         false
% 2.02/0.95  --bmc1_ucm                              false
% 2.02/0.95  --bmc1_add_unsat_core                   none
% 2.02/0.95  --bmc1_unsat_core_children              false
% 2.02/0.95  --bmc1_unsat_core_extrapolate_axioms    false
% 2.02/0.95  --bmc1_out_stat                         full
% 2.02/0.95  --bmc1_ground_init                      false
% 2.02/0.95  --bmc1_pre_inst_next_state              false
% 2.02/0.95  --bmc1_pre_inst_state                   false
% 2.02/0.95  --bmc1_pre_inst_reach_state             false
% 2.02/0.95  --bmc1_out_unsat_core                   false
% 2.02/0.95  --bmc1_aig_witness_out                  false
% 2.02/0.95  --bmc1_verbose                          false
% 2.02/0.95  --bmc1_dump_clauses_tptp                false
% 2.02/0.95  --bmc1_dump_unsat_core_tptp             false
% 2.02/0.95  --bmc1_dump_file                        -
% 2.02/0.95  --bmc1_ucm_expand_uc_limit              128
% 2.02/0.95  --bmc1_ucm_n_expand_iterations          6
% 2.02/0.95  --bmc1_ucm_extend_mode                  1
% 2.02/0.95  --bmc1_ucm_init_mode                    2
% 2.02/0.95  --bmc1_ucm_cone_mode                    none
% 2.02/0.95  --bmc1_ucm_reduced_relation_type        0
% 2.02/0.95  --bmc1_ucm_relax_model                  4
% 2.02/0.95  --bmc1_ucm_full_tr_after_sat            true
% 2.02/0.95  --bmc1_ucm_expand_neg_assumptions       false
% 2.02/0.95  --bmc1_ucm_layered_model                none
% 2.02/0.95  --bmc1_ucm_max_lemma_size               10
% 2.02/0.95  
% 2.02/0.95  ------ AIG Options
% 2.02/0.95  
% 2.02/0.95  --aig_mode                              false
% 2.02/0.95  
% 2.02/0.95  ------ Instantiation Options
% 2.02/0.95  
% 2.02/0.95  --instantiation_flag                    true
% 2.02/0.95  --inst_sos_flag                         false
% 2.02/0.95  --inst_sos_phase                        true
% 2.02/0.95  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.02/0.95  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.02/0.95  --inst_lit_sel_side                     none
% 2.02/0.95  --inst_solver_per_active                1400
% 2.02/0.95  --inst_solver_calls_frac                1.
% 2.02/0.95  --inst_passive_queue_type               priority_queues
% 2.02/0.95  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.02/0.95  --inst_passive_queues_freq              [25;2]
% 2.02/0.95  --inst_dismatching                      true
% 2.02/0.95  --inst_eager_unprocessed_to_passive     true
% 2.02/0.95  --inst_prop_sim_given                   true
% 2.02/0.95  --inst_prop_sim_new                     false
% 2.02/0.95  --inst_subs_new                         false
% 2.02/0.95  --inst_eq_res_simp                      false
% 2.02/0.95  --inst_subs_given                       false
% 2.02/0.95  --inst_orphan_elimination               true
% 2.02/0.95  --inst_learning_loop_flag               true
% 2.02/0.95  --inst_learning_start                   3000
% 2.02/0.95  --inst_learning_factor                  2
% 2.02/0.95  --inst_start_prop_sim_after_learn       3
% 2.02/0.95  --inst_sel_renew                        solver
% 2.02/0.95  --inst_lit_activity_flag                true
% 2.02/0.95  --inst_restr_to_given                   false
% 2.02/0.95  --inst_activity_threshold               500
% 2.02/0.95  --inst_out_proof                        true
% 2.02/0.95  
% 2.02/0.95  ------ Resolution Options
% 2.02/0.95  
% 2.02/0.95  --resolution_flag                       false
% 2.02/0.95  --res_lit_sel                           adaptive
% 2.02/0.95  --res_lit_sel_side                      none
% 2.02/0.95  --res_ordering                          kbo
% 2.02/0.95  --res_to_prop_solver                    active
% 2.02/0.95  --res_prop_simpl_new                    false
% 2.02/0.95  --res_prop_simpl_given                  true
% 2.02/0.95  --res_passive_queue_type                priority_queues
% 2.02/0.95  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.02/0.95  --res_passive_queues_freq               [15;5]
% 2.02/0.95  --res_forward_subs                      full
% 2.02/0.95  --res_backward_subs                     full
% 2.02/0.95  --res_forward_subs_resolution           true
% 2.02/0.95  --res_backward_subs_resolution          true
% 2.02/0.95  --res_orphan_elimination                true
% 2.02/0.95  --res_time_limit                        2.
% 2.02/0.95  --res_out_proof                         true
% 2.02/0.95  
% 2.02/0.95  ------ Superposition Options
% 2.02/0.95  
% 2.02/0.95  --superposition_flag                    true
% 2.02/0.95  --sup_passive_queue_type                priority_queues
% 2.02/0.95  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.02/0.95  --sup_passive_queues_freq               [8;1;4]
% 2.02/0.95  --demod_completeness_check              fast
% 2.02/0.95  --demod_use_ground                      true
% 2.02/0.95  --sup_to_prop_solver                    passive
% 2.02/0.95  --sup_prop_simpl_new                    true
% 2.02/0.95  --sup_prop_simpl_given                  true
% 2.02/0.95  --sup_fun_splitting                     false
% 2.02/0.95  --sup_smt_interval                      50000
% 2.02/0.95  
% 2.02/0.95  ------ Superposition Simplification Setup
% 2.02/0.95  
% 2.02/0.95  --sup_indices_passive                   []
% 2.02/0.95  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.02/0.95  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.02/0.95  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.02/0.95  --sup_full_triv                         [TrivRules;PropSubs]
% 2.02/0.95  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.02/0.95  --sup_full_bw                           [BwDemod]
% 2.02/0.95  --sup_immed_triv                        [TrivRules]
% 2.02/0.95  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.02/0.95  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.02/0.95  --sup_immed_bw_main                     []
% 2.02/0.95  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.02/0.95  --sup_input_triv                        [Unflattening;TrivRules]
% 2.02/0.95  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.02/0.95  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.02/0.95  
% 2.02/0.95  ------ Combination Options
% 2.02/0.95  
% 2.02/0.95  --comb_res_mult                         3
% 2.02/0.95  --comb_sup_mult                         2
% 2.02/0.95  --comb_inst_mult                        10
% 2.02/0.95  
% 2.02/0.95  ------ Debug Options
% 2.02/0.95  
% 2.02/0.95  --dbg_backtrace                         false
% 2.02/0.95  --dbg_dump_prop_clauses                 false
% 2.02/0.95  --dbg_dump_prop_clauses_file            -
% 2.02/0.95  --dbg_out_stat                          false
% 2.02/0.95  
% 2.02/0.95  
% 2.02/0.95  
% 2.02/0.95  
% 2.02/0.95  ------ Proving...
% 2.02/0.95  
% 2.02/0.95  
% 2.02/0.95  % SZS status Theorem for theBenchmark.p
% 2.02/0.95  
% 2.02/0.95  % SZS output start CNFRefutation for theBenchmark.p
% 2.02/0.95  
% 2.02/0.95  fof(f8,conjecture,(
% 2.02/0.95    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))),
% 2.02/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/0.95  
% 2.02/0.95  fof(f9,negated_conjecture,(
% 2.02/0.95    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))),
% 2.02/0.95    inference(negated_conjecture,[],[f8])).
% 2.02/0.95  
% 2.02/0.95  fof(f20,plain,(
% 2.02/0.95    ? [X0] : (? [X1] : (r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 2.02/0.95    inference(ennf_transformation,[],[f9])).
% 2.02/0.95  
% 2.02/0.95  fof(f21,plain,(
% 2.02/0.95    ? [X0] : (? [X1] : (r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 2.02/0.95    inference(flattening,[],[f20])).
% 2.02/0.95  
% 2.02/0.95  fof(f27,plain,(
% 2.02/0.95    ( ! [X0] : (? [X1] : (r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,u1_struct_0(X0))) => (r2_hidden(sK2,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),sK2))) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 2.02/0.95    introduced(choice_axiom,[])).
% 2.02/0.95  
% 2.02/0.95  fof(f26,plain,(
% 2.02/0.95    ? [X0] : (? [X1] : (r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (r2_hidden(X1,k2_orders_2(sK1,k6_domain_1(u1_struct_0(sK1),X1))) & m1_subset_1(X1,u1_struct_0(sK1))) & l1_orders_2(sK1) & v5_orders_2(sK1) & v4_orders_2(sK1) & v3_orders_2(sK1) & ~v2_struct_0(sK1))),
% 2.02/0.95    introduced(choice_axiom,[])).
% 2.02/0.95  
% 2.02/0.95  fof(f28,plain,(
% 2.02/0.95    (r2_hidden(sK2,k2_orders_2(sK1,k6_domain_1(u1_struct_0(sK1),sK2))) & m1_subset_1(sK2,u1_struct_0(sK1))) & l1_orders_2(sK1) & v5_orders_2(sK1) & v4_orders_2(sK1) & v3_orders_2(sK1) & ~v2_struct_0(sK1)),
% 2.02/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f21,f27,f26])).
% 2.02/0.95  
% 2.02/0.95  fof(f45,plain,(
% 2.02/0.95    r2_hidden(sK2,k2_orders_2(sK1,k6_domain_1(u1_struct_0(sK1),sK2)))),
% 2.02/0.95    inference(cnf_transformation,[],[f28])).
% 2.02/0.95  
% 2.02/0.95  fof(f6,axiom,(
% 2.02/0.95    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0))))),
% 2.02/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/0.95  
% 2.02/0.95  fof(f10,plain,(
% 2.02/0.95    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.02/0.95    inference(pure_predicate_removal,[],[f6])).
% 2.02/0.95  
% 2.02/0.95  fof(f16,plain,(
% 2.02/0.95    ! [X0] : (! [X1] : (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.02/0.95    inference(ennf_transformation,[],[f10])).
% 2.02/0.95  
% 2.02/0.95  fof(f17,plain,(
% 2.02/0.95    ! [X0] : (! [X1] : (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.02/0.95    inference(flattening,[],[f16])).
% 2.02/0.95  
% 2.02/0.95  fof(f37,plain,(
% 2.02/0.95    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.02/0.95    inference(cnf_transformation,[],[f17])).
% 2.02/0.95  
% 2.02/0.95  fof(f43,plain,(
% 2.02/0.95    l1_orders_2(sK1)),
% 2.02/0.95    inference(cnf_transformation,[],[f28])).
% 2.02/0.95  
% 2.02/0.95  fof(f39,plain,(
% 2.02/0.95    ~v2_struct_0(sK1)),
% 2.02/0.95    inference(cnf_transformation,[],[f28])).
% 2.02/0.95  
% 2.02/0.95  fof(f40,plain,(
% 2.02/0.95    v3_orders_2(sK1)),
% 2.02/0.95    inference(cnf_transformation,[],[f28])).
% 2.02/0.95  
% 2.02/0.95  fof(f4,axiom,(
% 2.02/0.95    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.02/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/0.95  
% 2.02/0.95  fof(f12,plain,(
% 2.02/0.95    ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.02/0.95    inference(ennf_transformation,[],[f4])).
% 2.02/0.95  
% 2.02/0.95  fof(f13,plain,(
% 2.02/0.95    ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.02/0.95    inference(flattening,[],[f12])).
% 2.02/0.95  
% 2.02/0.95  fof(f35,plain,(
% 2.02/0.95    ( ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.02/0.95    inference(cnf_transformation,[],[f13])).
% 2.02/0.95  
% 2.02/0.95  fof(f42,plain,(
% 2.02/0.95    v5_orders_2(sK1)),
% 2.02/0.95    inference(cnf_transformation,[],[f28])).
% 2.02/0.95  
% 2.02/0.95  fof(f41,plain,(
% 2.02/0.95    v4_orders_2(sK1)),
% 2.02/0.95    inference(cnf_transformation,[],[f28])).
% 2.02/0.95  
% 2.02/0.95  fof(f3,axiom,(
% 2.02/0.95    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.02/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/0.95  
% 2.02/0.95  fof(f11,plain,(
% 2.02/0.95    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.02/0.95    inference(ennf_transformation,[],[f3])).
% 2.02/0.95  
% 2.02/0.95  fof(f34,plain,(
% 2.02/0.95    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.02/0.95    inference(cnf_transformation,[],[f11])).
% 2.02/0.95  
% 2.02/0.95  fof(f44,plain,(
% 2.02/0.95    m1_subset_1(sK2,u1_struct_0(sK1))),
% 2.02/0.95    inference(cnf_transformation,[],[f28])).
% 2.02/0.95  
% 2.02/0.95  fof(f5,axiom,(
% 2.02/0.95    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 2.02/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/0.95  
% 2.02/0.95  fof(f14,plain,(
% 2.02/0.95    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.02/0.95    inference(ennf_transformation,[],[f5])).
% 2.02/0.95  
% 2.02/0.95  fof(f15,plain,(
% 2.02/0.95    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.02/0.95    inference(flattening,[],[f14])).
% 2.02/0.95  
% 2.02/0.95  fof(f36,plain,(
% 2.02/0.95    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.02/0.95    inference(cnf_transformation,[],[f15])).
% 2.02/0.95  
% 2.02/0.95  fof(f2,axiom,(
% 2.02/0.95    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 2.02/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/0.95  
% 2.02/0.95  fof(f33,plain,(
% 2.02/0.95    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 2.02/0.95    inference(cnf_transformation,[],[f2])).
% 2.02/0.95  
% 2.02/0.95  fof(f50,plain,(
% 2.02/0.95    ( ! [X0,X1] : (k2_tarski(X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.02/0.95    inference(definition_unfolding,[],[f36,f33])).
% 2.02/0.95  
% 2.02/0.95  fof(f1,axiom,(
% 2.02/0.95    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.02/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/0.95  
% 2.02/0.95  fof(f22,plain,(
% 2.02/0.95    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 2.02/0.95    inference(nnf_transformation,[],[f1])).
% 2.02/0.95  
% 2.02/0.95  fof(f23,plain,(
% 2.02/0.95    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.02/0.95    inference(rectify,[],[f22])).
% 2.02/0.95  
% 2.02/0.95  fof(f24,plain,(
% 2.02/0.95    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1))))),
% 2.02/0.95    introduced(choice_axiom,[])).
% 2.02/0.95  
% 2.02/0.95  fof(f25,plain,(
% 2.02/0.95    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.02/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).
% 2.02/0.95  
% 2.02/0.95  fof(f30,plain,(
% 2.02/0.95    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 2.02/0.95    inference(cnf_transformation,[],[f25])).
% 2.02/0.95  
% 2.02/0.95  fof(f48,plain,(
% 2.02/0.95    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_tarski(X0,X0) != X1) )),
% 2.02/0.95    inference(definition_unfolding,[],[f30,f33])).
% 2.02/0.95  
% 2.02/0.95  fof(f51,plain,(
% 2.02/0.95    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_tarski(X3,X3) != X1) )),
% 2.02/0.95    inference(equality_resolution,[],[f48])).
% 2.02/0.95  
% 2.02/0.95  fof(f52,plain,(
% 2.02/0.95    ( ! [X3] : (r2_hidden(X3,k2_tarski(X3,X3))) )),
% 2.02/0.95    inference(equality_resolution,[],[f51])).
% 2.02/0.95  
% 2.02/0.95  fof(f7,axiom,(
% 2.02/0.95    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(r2_hidden(X1,k2_orders_2(X0,X2)) & r2_hidden(X1,X2)))))),
% 2.02/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/0.95  
% 2.02/0.95  fof(f18,plain,(
% 2.02/0.95    ! [X0] : (! [X1] : (! [X2] : ((~r2_hidden(X1,k2_orders_2(X0,X2)) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.02/0.95    inference(ennf_transformation,[],[f7])).
% 2.02/0.95  
% 2.02/0.95  fof(f19,plain,(
% 2.02/0.95    ! [X0] : (! [X1] : (! [X2] : (~r2_hidden(X1,k2_orders_2(X0,X2)) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.02/0.95    inference(flattening,[],[f18])).
% 2.02/0.95  
% 2.02/0.95  fof(f38,plain,(
% 2.02/0.95    ( ! [X2,X0,X1] : (~r2_hidden(X1,k2_orders_2(X0,X2)) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.02/0.95    inference(cnf_transformation,[],[f19])).
% 2.02/0.95  
% 2.02/0.95  cnf(c_369,plain,
% 2.02/0.95      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.02/0.95      theory(equality) ).
% 2.02/0.95  
% 2.02/0.95  cnf(c_669,plain,
% 2.02/0.95      ( r2_hidden(X0,X1)
% 2.02/0.95      | ~ r2_hidden(X2,k2_tarski(X2,X2))
% 2.02/0.95      | X0 != X2
% 2.02/0.95      | X1 != k2_tarski(X2,X2) ),
% 2.02/0.95      inference(instantiation,[status(thm)],[c_369]) ).
% 2.02/0.95  
% 2.02/0.95  cnf(c_859,plain,
% 2.02/0.95      ( r2_hidden(X0,k6_domain_1(u1_struct_0(sK1),sK2))
% 2.02/0.95      | ~ r2_hidden(sK2,k2_tarski(sK2,sK2))
% 2.02/0.95      | X0 != sK2
% 2.02/0.95      | k6_domain_1(u1_struct_0(sK1),sK2) != k2_tarski(sK2,sK2) ),
% 2.02/0.95      inference(instantiation,[status(thm)],[c_669]) ).
% 2.02/0.95  
% 2.02/0.95  cnf(c_1734,plain,
% 2.02/0.95      ( r2_hidden(sK2,k6_domain_1(u1_struct_0(sK1),sK2))
% 2.02/0.95      | ~ r2_hidden(sK2,k2_tarski(sK2,sK2))
% 2.02/0.95      | k6_domain_1(u1_struct_0(sK1),sK2) != k2_tarski(sK2,sK2)
% 2.02/0.95      | sK2 != sK2 ),
% 2.02/0.95      inference(instantiation,[status(thm)],[c_859]) ).
% 2.02/0.95  
% 2.02/0.95  cnf(c_9,negated_conjecture,
% 2.02/0.95      ( r2_hidden(sK2,k2_orders_2(sK1,k6_domain_1(u1_struct_0(sK1),sK2))) ),
% 2.02/0.95      inference(cnf_transformation,[],[f45]) ).
% 2.02/0.95  
% 2.02/0.95  cnf(c_573,plain,
% 2.02/0.95      ( r2_hidden(sK2,k2_orders_2(sK1,k6_domain_1(u1_struct_0(sK1),sK2))) = iProver_top ),
% 2.02/0.95      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.02/0.95  
% 2.02/0.95  cnf(c_7,plain,
% 2.02/0.95      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.02/0.95      | m1_subset_1(k6_domain_1(u1_struct_0(X1),X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.02/0.95      | v2_struct_0(X1)
% 2.02/0.95      | ~ v3_orders_2(X1)
% 2.02/0.95      | ~ l1_orders_2(X1) ),
% 2.02/0.95      inference(cnf_transformation,[],[f37]) ).
% 2.02/0.95  
% 2.02/0.95  cnf(c_11,negated_conjecture,
% 2.02/0.95      ( l1_orders_2(sK1) ),
% 2.02/0.95      inference(cnf_transformation,[],[f43]) ).
% 2.02/0.95  
% 2.02/0.95  cnf(c_248,plain,
% 2.02/0.95      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.02/0.95      | m1_subset_1(k6_domain_1(u1_struct_0(X1),X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.02/0.95      | v2_struct_0(X1)
% 2.02/0.95      | ~ v3_orders_2(X1)
% 2.02/0.95      | sK1 != X1 ),
% 2.02/0.95      inference(resolution_lifted,[status(thm)],[c_7,c_11]) ).
% 2.02/0.95  
% 2.02/0.95  cnf(c_249,plain,
% 2.02/0.95      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.02/0.95      | m1_subset_1(k6_domain_1(u1_struct_0(sK1),X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.02/0.95      | v2_struct_0(sK1)
% 2.02/0.95      | ~ v3_orders_2(sK1) ),
% 2.02/0.95      inference(unflattening,[status(thm)],[c_248]) ).
% 2.02/0.95  
% 2.02/0.95  cnf(c_15,negated_conjecture,
% 2.02/0.95      ( ~ v2_struct_0(sK1) ),
% 2.02/0.95      inference(cnf_transformation,[],[f39]) ).
% 2.02/0.95  
% 2.02/0.95  cnf(c_14,negated_conjecture,
% 2.02/0.95      ( v3_orders_2(sK1) ),
% 2.02/0.95      inference(cnf_transformation,[],[f40]) ).
% 2.02/0.95  
% 2.02/0.95  cnf(c_253,plain,
% 2.02/0.95      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.02/0.95      | m1_subset_1(k6_domain_1(u1_struct_0(sK1),X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.02/0.95      inference(global_propositional_subsumption,
% 2.02/0.95                [status(thm)],
% 2.02/0.95                [c_249,c_15,c_14]) ).
% 2.02/0.95  
% 2.02/0.95  cnf(c_569,plain,
% 2.02/0.95      ( m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 2.02/0.95      | m1_subset_1(k6_domain_1(u1_struct_0(sK1),X0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.02/0.95      inference(predicate_to_equality,[status(thm)],[c_253]) ).
% 2.02/0.95  
% 2.02/0.95  cnf(c_5,plain,
% 2.02/0.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.02/0.95      | m1_subset_1(k2_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.02/0.95      | v2_struct_0(X1)
% 2.02/0.95      | ~ v3_orders_2(X1)
% 2.02/0.95      | ~ v4_orders_2(X1)
% 2.02/0.95      | ~ v5_orders_2(X1)
% 2.02/0.95      | ~ l1_orders_2(X1) ),
% 2.02/0.95      inference(cnf_transformation,[],[f35]) ).
% 2.02/0.95  
% 2.02/0.95  cnf(c_12,negated_conjecture,
% 2.02/0.95      ( v5_orders_2(sK1) ),
% 2.02/0.95      inference(cnf_transformation,[],[f42]) ).
% 2.02/0.95  
% 2.02/0.95  cnf(c_222,plain,
% 2.02/0.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.02/0.95      | m1_subset_1(k2_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.02/0.95      | v2_struct_0(X1)
% 2.02/0.95      | ~ v3_orders_2(X1)
% 2.02/0.95      | ~ v4_orders_2(X1)
% 2.02/0.95      | ~ l1_orders_2(X1)
% 2.02/0.95      | sK1 != X1 ),
% 2.02/0.95      inference(resolution_lifted,[status(thm)],[c_5,c_12]) ).
% 2.02/0.95  
% 2.02/0.95  cnf(c_223,plain,
% 2.02/0.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.02/0.95      | m1_subset_1(k2_orders_2(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.02/0.95      | v2_struct_0(sK1)
% 2.02/0.95      | ~ v3_orders_2(sK1)
% 2.02/0.95      | ~ v4_orders_2(sK1)
% 2.02/0.95      | ~ l1_orders_2(sK1) ),
% 2.02/0.95      inference(unflattening,[status(thm)],[c_222]) ).
% 2.02/0.95  
% 2.02/0.95  cnf(c_13,negated_conjecture,
% 2.02/0.95      ( v4_orders_2(sK1) ),
% 2.02/0.95      inference(cnf_transformation,[],[f41]) ).
% 2.02/0.95  
% 2.02/0.95  cnf(c_227,plain,
% 2.02/0.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.02/0.95      | m1_subset_1(k2_orders_2(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.02/0.95      inference(global_propositional_subsumption,
% 2.02/0.95                [status(thm)],
% 2.02/0.95                [c_223,c_15,c_14,c_13,c_11]) ).
% 2.02/0.95  
% 2.02/0.95  cnf(c_570,plain,
% 2.02/0.95      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.02/0.95      | m1_subset_1(k2_orders_2(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.02/0.95      inference(predicate_to_equality,[status(thm)],[c_227]) ).
% 2.02/0.95  
% 2.02/0.95  cnf(c_4,plain,
% 2.02/0.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.02/0.95      | ~ r2_hidden(X2,X0)
% 2.02/0.95      | ~ v1_xboole_0(X1) ),
% 2.02/0.95      inference(cnf_transformation,[],[f34]) ).
% 2.02/0.95  
% 2.02/0.95  cnf(c_575,plain,
% 2.02/0.95      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.02/0.95      | r2_hidden(X2,X0) != iProver_top
% 2.02/0.95      | v1_xboole_0(X1) != iProver_top ),
% 2.02/0.95      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.02/0.95  
% 2.02/0.95  cnf(c_1041,plain,
% 2.02/0.95      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.02/0.95      | r2_hidden(X1,k2_orders_2(sK1,X0)) != iProver_top
% 2.02/0.95      | v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
% 2.02/0.95      inference(superposition,[status(thm)],[c_570,c_575]) ).
% 2.02/0.95  
% 2.02/0.95  cnf(c_1389,plain,
% 2.02/0.95      ( m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 2.02/0.95      | r2_hidden(X1,k2_orders_2(sK1,k6_domain_1(u1_struct_0(sK1),X0))) != iProver_top
% 2.02/0.95      | v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
% 2.02/0.95      inference(superposition,[status(thm)],[c_569,c_1041]) ).
% 2.02/0.95  
% 2.02/0.95  cnf(c_1615,plain,
% 2.02/0.95      ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 2.02/0.95      | v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
% 2.02/0.95      inference(superposition,[status(thm)],[c_573,c_1389]) ).
% 2.02/0.95  
% 2.02/0.95  cnf(c_10,negated_conjecture,
% 2.02/0.95      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 2.02/0.95      inference(cnf_transformation,[],[f44]) ).
% 2.02/0.95  
% 2.02/0.95  cnf(c_572,plain,
% 2.02/0.95      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 2.02/0.95      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.02/0.95  
% 2.02/0.95  cnf(c_6,plain,
% 2.02/0.95      ( ~ m1_subset_1(X0,X1)
% 2.02/0.95      | v1_xboole_0(X1)
% 2.02/0.95      | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
% 2.02/0.95      inference(cnf_transformation,[],[f50]) ).
% 2.02/0.95  
% 2.02/0.95  cnf(c_574,plain,
% 2.02/0.95      ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
% 2.02/0.95      | m1_subset_1(X1,X0) != iProver_top
% 2.02/0.95      | v1_xboole_0(X0) = iProver_top ),
% 2.02/0.95      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.02/0.95  
% 2.02/0.95  cnf(c_1117,plain,
% 2.02/0.95      ( k6_domain_1(u1_struct_0(sK1),sK2) = k2_tarski(sK2,sK2)
% 2.02/0.95      | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
% 2.02/0.95      inference(superposition,[status(thm)],[c_572,c_574]) ).
% 2.02/0.95  
% 2.02/0.95  cnf(c_2,plain,
% 2.02/0.95      ( r2_hidden(X0,k2_tarski(X0,X0)) ),
% 2.02/0.95      inference(cnf_transformation,[],[f52]) ).
% 2.02/0.95  
% 2.02/0.95  cnf(c_1063,plain,
% 2.02/0.95      ( r2_hidden(sK2,k2_tarski(sK2,sK2)) ),
% 2.02/0.95      inference(instantiation,[status(thm)],[c_2]) ).
% 2.02/0.95  
% 2.02/0.95  cnf(c_367,plain,( X0 = X0 ),theory(equality) ).
% 2.02/0.95  
% 2.02/0.95  cnf(c_727,plain,
% 2.02/0.95      ( sK2 = sK2 ),
% 2.02/0.95      inference(instantiation,[status(thm)],[c_367]) ).
% 2.02/0.95  
% 2.02/0.95  cnf(c_8,plain,
% 2.02/0.95      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.02/0.95      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.02/0.95      | ~ r2_hidden(X0,X2)
% 2.02/0.95      | ~ r2_hidden(X0,k2_orders_2(X1,X2))
% 2.02/0.95      | v2_struct_0(X1)
% 2.02/0.95      | ~ v3_orders_2(X1)
% 2.02/0.95      | ~ v4_orders_2(X1)
% 2.02/0.95      | ~ v5_orders_2(X1)
% 2.02/0.95      | ~ l1_orders_2(X1) ),
% 2.02/0.95      inference(cnf_transformation,[],[f38]) ).
% 2.02/0.95  
% 2.02/0.95  cnf(c_198,plain,
% 2.02/0.95      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.02/0.95      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.02/0.95      | ~ r2_hidden(X0,X2)
% 2.02/0.95      | ~ r2_hidden(X0,k2_orders_2(X1,X2))
% 2.02/0.95      | v2_struct_0(X1)
% 2.02/0.95      | ~ v3_orders_2(X1)
% 2.02/0.95      | ~ v4_orders_2(X1)
% 2.02/0.95      | ~ l1_orders_2(X1)
% 2.02/0.95      | sK1 != X1 ),
% 2.02/0.95      inference(resolution_lifted,[status(thm)],[c_8,c_12]) ).
% 2.02/0.95  
% 2.02/0.95  cnf(c_199,plain,
% 2.02/0.95      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.02/0.95      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.02/0.95      | ~ r2_hidden(X0,X1)
% 2.02/0.95      | ~ r2_hidden(X0,k2_orders_2(sK1,X1))
% 2.02/0.95      | v2_struct_0(sK1)
% 2.02/0.95      | ~ v3_orders_2(sK1)
% 2.02/0.95      | ~ v4_orders_2(sK1)
% 2.02/0.95      | ~ l1_orders_2(sK1) ),
% 2.02/0.95      inference(unflattening,[status(thm)],[c_198]) ).
% 2.02/0.95  
% 2.02/0.95  cnf(c_203,plain,
% 2.02/0.95      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.02/0.95      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.02/0.95      | ~ r2_hidden(X0,X1)
% 2.02/0.95      | ~ r2_hidden(X0,k2_orders_2(sK1,X1)) ),
% 2.02/0.95      inference(global_propositional_subsumption,
% 2.02/0.95                [status(thm)],
% 2.02/0.95                [c_199,c_15,c_14,c_13,c_11]) ).
% 2.02/0.95  
% 2.02/0.95  cnf(c_657,plain,
% 2.02/0.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.02/0.95      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 2.02/0.95      | ~ r2_hidden(sK2,X0)
% 2.02/0.95      | ~ r2_hidden(sK2,k2_orders_2(sK1,X0)) ),
% 2.02/0.95      inference(instantiation,[status(thm)],[c_203]) ).
% 2.02/0.95  
% 2.02/0.95  cnf(c_706,plain,
% 2.02/0.95      ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.02/0.95      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 2.02/0.95      | ~ r2_hidden(sK2,k6_domain_1(u1_struct_0(sK1),sK2))
% 2.02/0.95      | ~ r2_hidden(sK2,k2_orders_2(sK1,k6_domain_1(u1_struct_0(sK1),sK2))) ),
% 2.02/0.95      inference(instantiation,[status(thm)],[c_657]) ).
% 2.02/0.95  
% 2.02/0.95  cnf(c_654,plain,
% 2.02/0.95      ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.02/0.95      | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 2.02/0.95      inference(instantiation,[status(thm)],[c_253]) ).
% 2.02/0.95  
% 2.02/0.95  cnf(c_21,plain,
% 2.02/0.95      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 2.02/0.95      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.02/0.95  
% 2.02/0.95  cnf(contradiction,plain,
% 2.02/0.95      ( $false ),
% 2.02/0.95      inference(minisat,
% 2.02/0.95                [status(thm)],
% 2.02/0.95                [c_1734,c_1615,c_1117,c_1063,c_727,c_706,c_654,c_9,c_21,
% 2.02/0.95                 c_10]) ).
% 2.02/0.95  
% 2.02/0.95  
% 2.02/0.95  % SZS output end CNFRefutation for theBenchmark.p
% 2.02/0.95  
% 2.02/0.95  ------                               Statistics
% 2.02/0.95  
% 2.02/0.95  ------ General
% 2.02/0.95  
% 2.02/0.95  abstr_ref_over_cycles:                  0
% 2.02/0.95  abstr_ref_under_cycles:                 0
% 2.02/0.95  gc_basic_clause_elim:                   0
% 2.02/0.95  forced_gc_time:                         0
% 2.02/0.95  parsing_time:                           0.018
% 2.02/0.95  unif_index_cands_time:                  0.
% 2.02/0.95  unif_index_add_time:                    0.
% 2.02/0.95  orderings_time:                         0.
% 2.02/0.95  out_proof_time:                         0.011
% 2.02/0.95  total_time:                             0.093
% 2.02/0.95  num_of_symbols:                         47
% 2.02/0.95  num_of_terms:                           1774
% 2.02/0.95  
% 2.02/0.95  ------ Preprocessing
% 2.02/0.95  
% 2.02/0.95  num_of_splits:                          0
% 2.02/0.95  num_of_split_atoms:                     0
% 2.02/0.95  num_of_reused_defs:                     0
% 2.02/0.95  num_eq_ax_congr_red:                    15
% 2.02/0.95  num_of_sem_filtered_clauses:            1
% 2.02/0.95  num_of_subtypes:                        0
% 2.02/0.95  monotx_restored_types:                  0
% 2.02/0.95  sat_num_of_epr_types:                   0
% 2.02/0.95  sat_num_of_non_cyclic_types:            0
% 2.02/0.95  sat_guarded_non_collapsed_types:        0
% 2.02/0.95  num_pure_diseq_elim:                    0
% 2.02/0.95  simp_replaced_by:                       0
% 2.02/0.95  res_preprocessed:                       66
% 2.02/0.95  prep_upred:                             0
% 2.02/0.95  prep_unflattend:                        3
% 2.02/0.95  smt_new_axioms:                         0
% 2.02/0.95  pred_elim_cands:                        3
% 2.02/0.95  pred_elim:                              5
% 2.02/0.95  pred_elim_cl:                           5
% 2.02/0.95  pred_elim_cycles:                       8
% 2.02/0.95  merged_defs:                            0
% 2.02/0.95  merged_defs_ncl:                        0
% 2.02/0.95  bin_hyper_res:                          0
% 2.02/0.95  prep_cycles:                            4
% 2.02/0.95  pred_elim_time:                         0.002
% 2.02/0.95  splitting_time:                         0.
% 2.02/0.95  sem_filter_time:                        0.
% 2.02/0.95  monotx_time:                            0.
% 2.02/0.95  subtype_inf_time:                       0.
% 2.02/0.95  
% 2.02/0.95  ------ Problem properties
% 2.02/0.95  
% 2.02/0.95  clauses:                                11
% 2.02/0.95  conjectures:                            2
% 2.02/0.95  epr:                                    0
% 2.02/0.95  horn:                                   9
% 2.02/0.95  ground:                                 2
% 2.02/0.95  unary:                                  3
% 2.02/0.95  binary:                                 3
% 2.02/0.95  lits:                                   25
% 2.02/0.95  lits_eq:                                6
% 2.02/0.95  fd_pure:                                0
% 2.02/0.95  fd_pseudo:                              0
% 2.02/0.95  fd_cond:                                0
% 2.02/0.95  fd_pseudo_cond:                         2
% 2.02/0.95  ac_symbols:                             0
% 2.02/0.95  
% 2.02/0.95  ------ Propositional Solver
% 2.02/0.95  
% 2.02/0.95  prop_solver_calls:                      27
% 2.02/0.95  prop_fast_solver_calls:                 407
% 2.02/0.95  smt_solver_calls:                       0
% 2.02/0.95  smt_fast_solver_calls:                  0
% 2.02/0.95  prop_num_of_clauses:                    651
% 2.02/0.95  prop_preprocess_simplified:             2644
% 2.02/0.95  prop_fo_subsumed:                       11
% 2.02/0.95  prop_solver_time:                       0.
% 2.02/0.95  smt_solver_time:                        0.
% 2.02/0.95  smt_fast_solver_time:                   0.
% 2.02/0.95  prop_fast_solver_time:                  0.
% 2.02/0.95  prop_unsat_core_time:                   0.
% 2.02/0.95  
% 2.02/0.95  ------ QBF
% 2.02/0.95  
% 2.02/0.95  qbf_q_res:                              0
% 2.02/0.95  qbf_num_tautologies:                    0
% 2.02/0.95  qbf_prep_cycles:                        0
% 2.02/0.95  
% 2.02/0.95  ------ BMC1
% 2.02/0.95  
% 2.02/0.95  bmc1_current_bound:                     -1
% 2.02/0.95  bmc1_last_solved_bound:                 -1
% 2.02/0.95  bmc1_unsat_core_size:                   -1
% 2.02/0.95  bmc1_unsat_core_parents_size:           -1
% 2.02/0.95  bmc1_merge_next_fun:                    0
% 2.02/0.95  bmc1_unsat_core_clauses_time:           0.
% 2.02/0.95  
% 2.02/0.95  ------ Instantiation
% 2.02/0.95  
% 2.02/0.95  inst_num_of_clauses:                    189
% 2.02/0.95  inst_num_in_passive:                    95
% 2.02/0.95  inst_num_in_active:                     89
% 2.02/0.95  inst_num_in_unprocessed:                4
% 2.02/0.95  inst_num_of_loops:                      96
% 2.02/0.95  inst_num_of_learning_restarts:          0
% 2.02/0.95  inst_num_moves_active_passive:          4
% 2.02/0.95  inst_lit_activity:                      0
% 2.02/0.95  inst_lit_activity_moves:                0
% 2.02/0.95  inst_num_tautologies:                   0
% 2.02/0.95  inst_num_prop_implied:                  0
% 2.02/0.95  inst_num_existing_simplified:           0
% 2.02/0.95  inst_num_eq_res_simplified:             0
% 2.02/0.95  inst_num_child_elim:                    0
% 2.02/0.95  inst_num_of_dismatching_blockings:      5
% 2.02/0.95  inst_num_of_non_proper_insts:           137
% 2.02/0.95  inst_num_of_duplicates:                 0
% 2.02/0.95  inst_inst_num_from_inst_to_res:         0
% 2.02/0.95  inst_dismatching_checking_time:         0.
% 2.02/0.95  
% 2.02/0.95  ------ Resolution
% 2.02/0.95  
% 2.02/0.95  res_num_of_clauses:                     0
% 2.02/0.95  res_num_in_passive:                     0
% 2.02/0.95  res_num_in_active:                      0
% 2.02/0.95  res_num_of_loops:                       70
% 2.02/0.95  res_forward_subset_subsumed:            20
% 2.02/0.95  res_backward_subset_subsumed:           0
% 2.02/0.95  res_forward_subsumed:                   0
% 2.02/0.95  res_backward_subsumed:                  0
% 2.02/0.95  res_forward_subsumption_resolution:     0
% 2.02/0.95  res_backward_subsumption_resolution:    0
% 2.02/0.95  res_clause_to_clause_subsumption:       46
% 2.02/0.95  res_orphan_elimination:                 0
% 2.02/0.95  res_tautology_del:                      11
% 2.02/0.95  res_num_eq_res_simplified:              0
% 2.02/0.95  res_num_sel_changes:                    0
% 2.02/0.95  res_moves_from_active_to_pass:          0
% 2.02/0.95  
% 2.02/0.95  ------ Superposition
% 2.02/0.95  
% 2.02/0.95  sup_time_total:                         0.
% 2.02/0.95  sup_time_generating:                    0.
% 2.02/0.95  sup_time_sim_full:                      0.
% 2.02/0.95  sup_time_sim_immed:                     0.
% 2.02/0.95  
% 2.02/0.95  sup_num_of_clauses:                     29
% 2.02/0.95  sup_num_in_active:                      18
% 2.02/0.95  sup_num_in_passive:                     11
% 2.02/0.95  sup_num_of_loops:                       18
% 2.02/0.95  sup_fw_superposition:                   15
% 2.02/0.95  sup_bw_superposition:                   3
% 2.02/0.95  sup_immediate_simplified:               0
% 2.02/0.95  sup_given_eliminated:                   0
% 2.02/0.95  comparisons_done:                       0
% 2.02/0.95  comparisons_avoided:                    2
% 2.02/0.95  
% 2.02/0.95  ------ Simplifications
% 2.02/0.95  
% 2.02/0.95  
% 2.02/0.95  sim_fw_subset_subsumed:                 0
% 2.02/0.95  sim_bw_subset_subsumed:                 0
% 2.02/0.95  sim_fw_subsumed:                        0
% 2.02/0.95  sim_bw_subsumed:                        0
% 2.02/0.95  sim_fw_subsumption_res:                 0
% 2.02/0.95  sim_bw_subsumption_res:                 0
% 2.02/0.95  sim_tautology_del:                      0
% 2.02/0.95  sim_eq_tautology_del:                   0
% 2.02/0.95  sim_eq_res_simp:                        0
% 2.02/0.95  sim_fw_demodulated:                     0
% 2.02/0.95  sim_bw_demodulated:                     0
% 2.02/0.95  sim_light_normalised:                   0
% 2.02/0.95  sim_joinable_taut:                      0
% 2.02/0.95  sim_joinable_simp:                      0
% 2.02/0.95  sim_ac_normalised:                      0
% 2.02/0.95  sim_smt_subsumption:                    0
% 2.02/0.95  
%------------------------------------------------------------------------------
