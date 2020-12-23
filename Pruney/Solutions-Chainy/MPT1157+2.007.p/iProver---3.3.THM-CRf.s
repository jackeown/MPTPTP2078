%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:12:29 EST 2020

% Result     : Theorem 19.68s
% Output     : CNFRefutation 19.68s
% Verified   : 
% Statistics : Number of formulae       :  184 (51754 expanded)
%              Number of clauses        :  114 (10345 expanded)
%              Number of leaves         :   15 (13957 expanded)
%              Depth                    :   43
%              Number of atoms          : 1002 (434676 expanded)
%              Number of equality atoms :  481 (28571 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   22 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f25])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK0(X0,X1,X2) != X1
            & sK0(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( sK0(X0,X1,X2) = X1
          | sK0(X0,X1,X2) = X0
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK0(X0,X1,X2) != X1
              & sK0(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( sK0(X0,X1,X2) = X1
            | sK0(X0,X1,X2) = X0
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f69,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f43])).

fof(f70,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f69])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = X2
      | sK0(X0,X1,X2) = X1
      | sK0(X0,X1,X2) = X0
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_orders_2(X0,X1,X2)
              <=> r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_orders_2(X0,X1,X2)
                <=> r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <~> r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <~> r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
                | ~ r2_orders_2(X0,X1,X2) )
              & ( r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
                | r2_orders_2(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
                | ~ r2_orders_2(X0,X1,X2) )
              & ( r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
                | r2_orders_2(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
            | ~ r2_orders_2(X0,X1,X2) )
          & ( r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
            | r2_orders_2(X0,X1,X2) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( ~ r2_hidden(sK5,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
          | ~ r2_orders_2(X0,X1,sK5) )
        & ( r2_hidden(sK5,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
          | r2_orders_2(X0,X1,sK5) )
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
                | ~ r2_orders_2(X0,X1,X2) )
              & ( r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
                | r2_orders_2(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ( ~ r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),sK4)))
              | ~ r2_orders_2(X0,sK4,X2) )
            & ( r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),sK4)))
              | r2_orders_2(X0,sK4,X2) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
                  | ~ r2_orders_2(X0,X1,X2) )
                & ( r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
                  | r2_orders_2(X0,X1,X2) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_hidden(X2,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X1)))
                | ~ r2_orders_2(sK3,X1,X2) )
              & ( r2_hidden(X2,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X1)))
                | r2_orders_2(sK3,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(sK3)) )
          & m1_subset_1(X1,u1_struct_0(sK3)) )
      & l1_orders_2(sK3)
      & v5_orders_2(sK3)
      & v4_orders_2(sK3)
      & v3_orders_2(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ( ~ r2_hidden(sK5,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4)))
      | ~ r2_orders_2(sK3,sK4,sK5) )
    & ( r2_hidden(sK5,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4)))
      | r2_orders_2(sK3,sK4,sK5) )
    & m1_subset_1(sK5,u1_struct_0(sK3))
    & m1_subset_1(sK4,u1_struct_0(sK3))
    & l1_orders_2(sK3)
    & v5_orders_2(sK3)
    & v4_orders_2(sK3)
    & v3_orders_2(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f36,f39,f38,f37])).

fof(f64,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f40])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k2_tarski(X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f56,f47])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f59,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f60,plain,(
    v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f61,plain,(
    v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f62,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f63,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & l1_orders_2(X1)
        & v5_orders_2(X1)
        & v4_orders_2(X1)
        & v3_orders_2(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r2_orders_2(X1,X4,X3) ) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X4,X3)
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X4,X3)
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f15])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
          | ! [X3] :
              ( ? [X4] :
                  ( ~ r2_orders_2(X1,X4,X3)
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( ! [X4] :
                  ( r2_orders_2(X1,X4,X3)
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
          | ! [X3] :
              ( ? [X4] :
                  ( ~ r2_orders_2(X1,X4,X3)
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X5] :
              ( ! [X6] :
                  ( r2_orders_2(X1,X6,X5)
                  | ~ r2_hidden(X6,X2)
                  | ~ m1_subset_1(X6,u1_struct_0(X1)) )
              & X0 = X5
              & m1_subset_1(X5,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f30])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_orders_2(X1,X6,X5)
              | ~ r2_hidden(X6,X2)
              | ~ m1_subset_1(X6,u1_struct_0(X1)) )
          & X0 = X5
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ! [X6] :
            ( r2_orders_2(X1,X6,sK2(X0,X1,X2))
            | ~ r2_hidden(X6,X2)
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        & sK2(X0,X1,X2) = X0
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ~ r2_orders_2(X1,X4,X3)
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_orders_2(X1,sK1(X1,X2,X3),X3)
        & r2_hidden(sK1(X1,X2,X3),X2)
        & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
          | ! [X3] :
              ( ( ~ r2_orders_2(X1,sK1(X1,X2,X3),X3)
                & r2_hidden(sK1(X1,X2,X3),X2)
                & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( ! [X6] :
                ( r2_orders_2(X1,X6,sK2(X0,X1,X2))
                | ~ r2_hidden(X6,X2)
                | ~ m1_subset_1(X6,u1_struct_0(X1)) )
            & sK2(X0,X1,X2) = X0
            & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f31,f33,f32])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | r2_hidden(sK1(X1,X2,X3),X2)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f75,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,a_2_0_orders_2(X1,X2))
      | r2_hidden(sK1(X1,X2,X3),X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f54])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f65,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f40])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f66,plain,
    ( r2_hidden(sK5,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4)))
    | r2_orders_2(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f40])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( sK2(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1))
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f76,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,a_2_0_orders_2(X1,X2))
      | m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f53])).

fof(f67,plain,
    ( ~ r2_hidden(sK5,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4)))
    | ~ r2_orders_2(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f40])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f73,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_tarski(X0,X1)) ) ),
    inference(equality_resolution,[],[f41])).

fof(f52,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_orders_2(X1,X6,sK2(X0,X1,X2))
      | ~ r2_hidden(X6,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | ~ r2_orders_2(X1,sK1(X1,X2,X3),X3)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f74,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,a_2_0_orders_2(X1,X2))
      | ~ r2_orders_2(X1,sK1(X1,X2,X3),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f55])).

cnf(c_3,plain,
    ( r2_hidden(X0,k2_tarski(X1,X0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_967,plain,
    ( r2_hidden(X0,k2_tarski(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X2)
    | sK0(X0,X1,X2) = X1
    | sK0(X0,X1,X2) = X0
    | k2_tarski(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_968,plain,
    ( sK0(X0,X1,X2) = X1
    | sK0(X0,X1,X2) = X0
    | k2_tarski(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_950,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_956,plain,
    ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1689,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK4) = k2_tarski(sK4,sK4)
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_950,c_956])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k6_domain_1(u1_struct_0(X1),X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_955,plain,
    ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(k6_domain_1(u1_struct_0(X1),X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v3_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | a_2_0_orders_2(X1,X0) = k1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_963,plain,
    ( a_2_0_orders_2(X0,X1) = k1_orders_2(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v3_orders_2(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2350,plain,
    ( a_2_0_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)) = k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v3_orders_2(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_955,c_963])).

cnf(c_6486,plain,
    ( a_2_0_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4)) = k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_950,c_2350])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_24,negated_conjecture,
    ( v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_23,negated_conjecture,
    ( v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_22,negated_conjecture,
    ( v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_21,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1296,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1429,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ v5_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | a_2_0_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4)) = k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_7321,plain,
    ( a_2_0_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4)) = k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6486,c_25,c_24,c_23,c_22,c_21,c_20,c_1296,c_1429])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,a_2_0_orders_2(X1,X2))
    | r2_hidden(sK1(X1,X2,X0),X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_961,plain,
    ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r2_hidden(X0,a_2_0_orders_2(X1,X2)) = iProver_top
    | r2_hidden(sK1(X1,X2,X0),X2) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v3_orders_2(X1) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v5_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_964,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2092,plain,
    ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | r2_hidden(X2,k6_domain_1(u1_struct_0(X1),X0)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v3_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top
    | v1_xboole_0(u1_struct_0(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_955,c_964])).

cnf(c_4237,plain,
    ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X3)) != iProver_top
    | m1_subset_1(k6_domain_1(u1_struct_0(X3),X2),k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r2_hidden(X0,a_2_0_orders_2(X1,k6_domain_1(u1_struct_0(X3),X2))) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X3) = iProver_top
    | v3_orders_2(X1) != iProver_top
    | v3_orders_2(X3) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v5_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top
    | l1_orders_2(X3) != iProver_top
    | v1_xboole_0(u1_struct_0(X3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_961,c_2092])).

cnf(c_17712,plain,
    ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | r2_hidden(X2,a_2_0_orders_2(X1,k6_domain_1(u1_struct_0(X1),X0))) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v3_orders_2(X1) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v5_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top
    | v1_xboole_0(u1_struct_0(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_955,c_4237])).

cnf(c_21206,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7321,c_17712])).

cnf(c_26,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_27,plain,
    ( v3_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_28,plain,
    ( v4_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_29,plain,
    ( v5_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_30,plain,
    ( l1_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_32,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_951,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_6485,plain,
    ( a_2_0_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)) = k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_951,c_2350])).

cnf(c_1293,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1383,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ v5_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | a_2_0_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)) = k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_7317,plain,
    ( a_2_0_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)) = k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6485,c_25,c_24,c_23,c_22,c_21,c_19,c_1293,c_1383])).

cnf(c_21205,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7317,c_17712])).

cnf(c_22249,plain,
    ( r2_hidden(X0,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_21205,c_26,c_27,c_28,c_29,c_30,c_32])).

cnf(c_22250,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_22249])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ r2_hidden(X0,k1_orders_2(X1,k6_domain_1(u1_struct_0(X1),X0)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_954,plain,
    ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | r2_hidden(X0,k1_orders_2(X1,k6_domain_1(u1_struct_0(X1),X0))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v3_orders_2(X1) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v5_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_22258,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_22250,c_954])).

cnf(c_22791,plain,
    ( v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_21206,c_26,c_27,c_28,c_29,c_30,c_32,c_22258])).

cnf(c_22797,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK4) = k2_tarski(sK4,sK4) ),
    inference(superposition,[status(thm)],[c_1689,c_22791])).

cnf(c_18,negated_conjecture,
    ( r2_orders_2(sK3,sK4,sK5)
    | r2_hidden(sK5,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_952,plain,
    ( r2_orders_2(sK3,sK4,sK5) = iProver_top
    | r2_hidden(sK5,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK2(X2,X1,X0) = X2 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_958,plain,
    ( sK2(X0,X1,X2) = X0
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r2_hidden(X0,a_2_0_orders_2(X1,X2)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v3_orders_2(X1) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v5_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2470,plain,
    ( sK2(X0,X1,k6_domain_1(u1_struct_0(X1),X2)) = X0
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | r2_hidden(X0,a_2_0_orders_2(X1,k6_domain_1(u1_struct_0(X1),X2))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v3_orders_2(X1) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v5_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_955,c_958])).

cnf(c_8707,plain,
    ( sK2(X0,sK3,k6_domain_1(u1_struct_0(sK3),sK4)) = X0
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7321,c_2470])).

cnf(c_31,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_9596,plain,
    ( r2_hidden(X0,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) != iProver_top
    | sK2(X0,sK3,k6_domain_1(u1_struct_0(sK3),sK4)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8707,c_26,c_27,c_28,c_29,c_30,c_31])).

cnf(c_9597,plain,
    ( sK2(X0,sK3,k6_domain_1(u1_struct_0(sK3),sK4)) = X0
    | r2_hidden(X0,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) != iProver_top ),
    inference(renaming,[status(thm)],[c_9596])).

cnf(c_9606,plain,
    ( sK2(sK5,sK3,k6_domain_1(u1_struct_0(sK3),sK4)) = sK5
    | r2_orders_2(sK3,sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_952,c_9597])).

cnf(c_22835,plain,
    ( sK2(sK5,sK3,k2_tarski(sK4,sK4)) = sK5
    | r2_orders_2(sK3,sK4,sK5) = iProver_top ),
    inference(demodulation,[status(thm)],[c_22797,c_9606])).

cnf(c_22960,plain,
    ( m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_22797,c_955])).

cnf(c_24442,plain,
    ( m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_22960,c_26,c_27,c_30,c_31])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X2,X0),u1_struct_0(X1))
    | r2_hidden(X0,a_2_0_orders_2(X1,X2))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_960,plain,
    ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(sK1(X1,X2,X0),u1_struct_0(X1)) = iProver_top
    | r2_hidden(X0,a_2_0_orders_2(X1,X2)) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v3_orders_2(X1) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v5_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4300,plain,
    ( k2_tarski(sK1(X0,X1,X2),sK1(X0,X1,X2)) = k6_domain_1(u1_struct_0(X0),sK1(X0,X1,X2))
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r2_hidden(X2,a_2_0_orders_2(X0,X1)) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v3_orders_2(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_960,c_956])).

cnf(c_24448,plain,
    ( k2_tarski(sK1(sK3,k2_tarski(sK4,sK4),X0),sK1(sK3,k2_tarski(sK4,sK4),X0)) = k6_domain_1(u1_struct_0(sK3),sK1(sK3,k2_tarski(sK4,sK4),X0))
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,a_2_0_orders_2(sK3,k2_tarski(sK4,sK4))) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_24442,c_4300])).

cnf(c_22837,plain,
    ( a_2_0_orders_2(sK3,k2_tarski(sK4,sK4)) = k1_orders_2(sK3,k2_tarski(sK4,sK4)) ),
    inference(demodulation,[status(thm)],[c_22797,c_7321])).

cnf(c_24539,plain,
    ( k2_tarski(sK1(sK3,k2_tarski(sK4,sK4),X0),sK1(sK3,k2_tarski(sK4,sK4),X0)) = k6_domain_1(u1_struct_0(sK3),sK1(sK3,k2_tarski(sK4,sK4),X0))
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,k1_orders_2(sK3,k2_tarski(sK4,sK4))) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_24448,c_22837])).

cnf(c_45926,plain,
    ( k2_tarski(sK1(sK3,k2_tarski(sK4,sK4),X0),sK1(sK3,k2_tarski(sK4,sK4),X0)) = k6_domain_1(u1_struct_0(sK3),sK1(sK3,k2_tarski(sK4,sK4),X0))
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,k1_orders_2(sK3,k2_tarski(sK4,sK4))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_24539,c_26,c_27,c_28,c_29,c_30,c_32,c_22258])).

cnf(c_17,negated_conjecture,
    ( ~ r2_orders_2(sK3,sK4,sK5)
    | ~ r2_hidden(sK5,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_953,plain,
    ( r2_orders_2(sK3,sK4,sK5) != iProver_top
    | r2_hidden(sK5,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_22840,plain,
    ( r2_orders_2(sK3,sK4,sK5) != iProver_top
    | r2_hidden(sK5,k1_orders_2(sK3,k2_tarski(sK4,sK4))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_22797,c_953])).

cnf(c_45938,plain,
    ( k2_tarski(sK1(sK3,k2_tarski(sK4,sK4),sK5),sK1(sK3,k2_tarski(sK4,sK4),sK5)) = k6_domain_1(u1_struct_0(sK3),sK1(sK3,k2_tarski(sK4,sK4),sK5))
    | r2_orders_2(sK3,sK4,sK5) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_45926,c_22840])).

cnf(c_45980,plain,
    ( r2_orders_2(sK3,sK4,sK5) != iProver_top
    | k2_tarski(sK1(sK3,k2_tarski(sK4,sK4),sK5),sK1(sK3,k2_tarski(sK4,sK4),sK5)) = k6_domain_1(u1_struct_0(sK3),sK1(sK3,k2_tarski(sK4,sK4),sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_45938,c_32])).

cnf(c_45981,plain,
    ( k2_tarski(sK1(sK3,k2_tarski(sK4,sK4),sK5),sK1(sK3,k2_tarski(sK4,sK4),sK5)) = k6_domain_1(u1_struct_0(sK3),sK1(sK3,k2_tarski(sK4,sK4),sK5))
    | r2_orders_2(sK3,sK4,sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_45980])).

cnf(c_45988,plain,
    ( sK2(sK5,sK3,k2_tarski(sK4,sK4)) = sK5
    | k2_tarski(sK1(sK3,k2_tarski(sK4,sK4),sK5),sK1(sK3,k2_tarski(sK4,sK4),sK5)) = k6_domain_1(u1_struct_0(sK3),sK1(sK3,k2_tarski(sK4,sK4),sK5)) ),
    inference(superposition,[status(thm)],[c_22835,c_45981])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k2_tarski(X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_965,plain,
    ( X0 = X1
    | X0 = X2
    | r2_hidden(X0,k2_tarski(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_46673,plain,
    ( sK2(sK5,sK3,k2_tarski(sK4,sK4)) = sK5
    | sK1(sK3,k2_tarski(sK4,sK4),sK5) = X0
    | r2_hidden(X0,k6_domain_1(u1_struct_0(sK3),sK1(sK3,k2_tarski(sK4,sK4),sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_45988,c_965])).

cnf(c_48726,plain,
    ( sK2(sK5,sK3,k2_tarski(sK4,sK4)) = sK5
    | sK0(X0,X1,k6_domain_1(u1_struct_0(sK3),sK1(sK3,k2_tarski(sK4,sK4),sK5))) = X0
    | sK0(X0,X1,k6_domain_1(u1_struct_0(sK3),sK1(sK3,k2_tarski(sK4,sK4),sK5))) = X1
    | sK0(X0,X1,k6_domain_1(u1_struct_0(sK3),sK1(sK3,k2_tarski(sK4,sK4),sK5))) = sK1(sK3,k2_tarski(sK4,sK4),sK5)
    | k6_domain_1(u1_struct_0(sK3),sK1(sK3,k2_tarski(sK4,sK4),sK5)) = k2_tarski(X0,X1) ),
    inference(superposition,[status(thm)],[c_968,c_46673])).

cnf(c_4236,plain,
    ( sK1(X0,k2_tarski(X1,X2),X3) = X1
    | sK1(X0,k2_tarski(X1,X2),X3) = X2
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r2_hidden(X3,a_2_0_orders_2(X0,k2_tarski(X1,X2))) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v3_orders_2(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_961,c_965])).

cnf(c_24453,plain,
    ( sK1(sK3,k2_tarski(sK4,sK4),X0) = sK4
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,a_2_0_orders_2(sK3,k2_tarski(sK4,sK4))) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_24442,c_4236])).

cnf(c_24496,plain,
    ( sK1(sK3,k2_tarski(sK4,sK4),X0) = sK4
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,k1_orders_2(sK3,k2_tarski(sK4,sK4))) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_24453,c_22837])).

cnf(c_28417,plain,
    ( r2_hidden(X0,k1_orders_2(sK3,k2_tarski(sK4,sK4))) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | sK1(sK3,k2_tarski(sK4,sK4),X0) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_24496,c_26,c_27,c_28,c_29,c_30])).

cnf(c_28418,plain,
    ( sK1(sK3,k2_tarski(sK4,sK4),X0) = sK4
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,k1_orders_2(sK3,k2_tarski(sK4,sK4))) = iProver_top ),
    inference(renaming,[status(thm)],[c_28417])).

cnf(c_28427,plain,
    ( sK1(sK3,k2_tarski(sK4,sK4),sK5) = sK4
    | r2_orders_2(sK3,sK4,sK5) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_28418,c_22840])).

cnf(c_28451,plain,
    ( r2_orders_2(sK3,sK4,sK5) != iProver_top
    | sK1(sK3,k2_tarski(sK4,sK4),sK5) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_28427,c_32])).

cnf(c_28452,plain,
    ( sK1(sK3,k2_tarski(sK4,sK4),sK5) = sK4
    | r2_orders_2(sK3,sK4,sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_28451])).

cnf(c_28457,plain,
    ( sK2(sK5,sK3,k2_tarski(sK4,sK4)) = sK5
    | sK1(sK3,k2_tarski(sK4,sK4),sK5) = sK4 ),
    inference(superposition,[status(thm)],[c_22835,c_28452])).

cnf(c_11,plain,
    ( r2_orders_2(X0,X1,sK2(X2,X0,X3))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X2,a_2_0_orders_2(X0,X3))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_959,plain,
    ( r2_orders_2(X0,X1,sK2(X2,X0,X3)) = iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r2_hidden(X1,X3) != iProver_top
    | r2_hidden(X2,a_2_0_orders_2(X0,X3)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v3_orders_2(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_28588,plain,
    ( sK1(sK3,k2_tarski(sK4,sK4),sK5) = sK4
    | r2_orders_2(sK3,X0,sK5) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,k2_tarski(sK4,sK4)) != iProver_top
    | r2_hidden(sK5,a_2_0_orders_2(sK3,k2_tarski(sK4,sK4))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_28457,c_959])).

cnf(c_28627,plain,
    ( sK1(sK3,k2_tarski(sK4,sK4),sK5) = sK4
    | r2_orders_2(sK3,X0,sK5) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,k2_tarski(sK4,sK4)) != iProver_top
    | r2_hidden(sK5,k1_orders_2(sK3,k2_tarski(sK4,sK4))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_28588,c_22837])).

cnf(c_22839,plain,
    ( r2_orders_2(sK3,sK4,sK5) = iProver_top
    | r2_hidden(sK5,k1_orders_2(sK3,k2_tarski(sK4,sK4))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_22797,c_952])).

cnf(c_57517,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r2_orders_2(sK3,X0,sK5) = iProver_top
    | sK1(sK3,k2_tarski(sK4,sK4),sK5) = sK4
    | r2_hidden(X0,k2_tarski(sK4,sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_28627,c_26,c_27,c_28,c_29,c_30,c_31,c_22839,c_22960,c_28452])).

cnf(c_57518,plain,
    ( sK1(sK3,k2_tarski(sK4,sK4),sK5) = sK4
    | r2_orders_2(sK3,X0,sK5) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,k2_tarski(sK4,sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_57517])).

cnf(c_57528,plain,
    ( sK1(sK3,k2_tarski(sK4,sK4),sK5) = sK4
    | r2_orders_2(sK3,sK4,sK5) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_967,c_57518])).

cnf(c_28453,plain,
    ( ~ r2_orders_2(sK3,sK4,sK5)
    | sK1(sK3,k2_tarski(sK4,sK4),sK5) = sK4 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_28452])).

cnf(c_57576,plain,
    ( r2_orders_2(sK3,sK4,sK5)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | sK1(sK3,k2_tarski(sK4,sK4),sK5) = sK4 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_57528])).

cnf(c_58366,plain,
    ( sK1(sK3,k2_tarski(sK4,sK4),sK5) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_57528,c_20,c_28453,c_57576])).

cnf(c_8,plain,
    ( ~ r2_orders_2(X0,sK1(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | r2_hidden(X2,a_2_0_orders_2(X0,X1))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_962,plain,
    ( r2_orders_2(X0,sK1(X0,X1,X2),X2) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r2_hidden(X2,a_2_0_orders_2(X0,X1)) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v3_orders_2(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_58440,plain,
    ( r2_orders_2(sK3,sK4,sK5) != iProver_top
    | m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK5,a_2_0_orders_2(sK3,k2_tarski(sK4,sK4))) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_58366,c_962])).

cnf(c_58462,plain,
    ( r2_orders_2(sK3,sK4,sK5) != iProver_top
    | m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK5,k1_orders_2(sK3,k2_tarski(sK4,sK4))) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_58440,c_22837])).

cnf(c_58473,plain,
    ( sK2(sK5,sK3,k2_tarski(sK4,sK4)) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_48726,c_26,c_27,c_28,c_29,c_30,c_31,c_32,c_22835,c_22840,c_22960,c_58462])).

cnf(c_58486,plain,
    ( r2_orders_2(sK3,X0,sK5) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,k2_tarski(sK4,sK4)) != iProver_top
    | r2_hidden(sK5,a_2_0_orders_2(sK3,k2_tarski(sK4,sK4))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_58473,c_959])).

cnf(c_58522,plain,
    ( r2_orders_2(sK3,X0,sK5) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,k2_tarski(sK4,sK4)) != iProver_top
    | r2_hidden(sK5,k1_orders_2(sK3,k2_tarski(sK4,sK4))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_58486,c_22837])).

cnf(c_59147,plain,
    ( r2_hidden(sK5,k1_orders_2(sK3,k2_tarski(sK4,sK4))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_58462,c_26,c_27,c_28,c_29,c_30,c_31,c_32,c_22839,c_22840,c_22960])).

cnf(c_59269,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r2_orders_2(sK3,X0,sK5) = iProver_top
    | r2_hidden(X0,k2_tarski(sK4,sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_58522,c_26,c_27,c_28,c_29,c_30,c_31,c_32,c_22839,c_22840,c_22960,c_58462])).

cnf(c_59270,plain,
    ( r2_orders_2(sK3,X0,sK5) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,k2_tarski(sK4,sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_59269])).

cnf(c_59279,plain,
    ( r2_orders_2(sK3,sK4,sK5) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_967,c_59270])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_59279,c_59147,c_22840,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:33:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 19.68/2.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.68/2.99  
% 19.68/2.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.68/2.99  
% 19.68/2.99  ------  iProver source info
% 19.68/2.99  
% 19.68/2.99  git: date: 2020-06-30 10:37:57 +0100
% 19.68/2.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.68/2.99  git: non_committed_changes: false
% 19.68/2.99  git: last_make_outside_of_git: false
% 19.68/2.99  
% 19.68/2.99  ------ 
% 19.68/2.99  ------ Parsing...
% 19.68/2.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.68/2.99  
% 19.68/2.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 19.68/2.99  
% 19.68/2.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.68/2.99  
% 19.68/2.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.68/2.99  ------ Proving...
% 19.68/2.99  ------ Problem Properties 
% 19.68/2.99  
% 19.68/2.99  
% 19.68/2.99  clauses                                 26
% 19.68/2.99  conjectures                             9
% 19.68/2.99  EPR                                     5
% 19.68/2.99  Horn                                    14
% 19.68/2.99  unary                                   9
% 19.68/2.99  binary                                  2
% 19.68/2.99  lits                                    104
% 19.68/2.99  lits eq                                 12
% 19.68/2.99  fd_pure                                 0
% 19.68/2.99  fd_pseudo                               0
% 19.68/2.99  fd_cond                                 0
% 19.68/2.99  fd_pseudo_cond                          3
% 19.68/2.99  AC symbols                              0
% 19.68/2.99  
% 19.68/2.99  ------ Input Options Time Limit: Unbounded
% 19.68/2.99  
% 19.68/2.99  
% 19.68/2.99  ------ 
% 19.68/2.99  Current options:
% 19.68/2.99  ------ 
% 19.68/2.99  
% 19.68/2.99  
% 19.68/2.99  
% 19.68/2.99  
% 19.68/2.99  ------ Proving...
% 19.68/2.99  
% 19.68/2.99  
% 19.68/2.99  % SZS status Theorem for theBenchmark.p
% 19.68/2.99  
% 19.68/2.99  % SZS output start CNFRefutation for theBenchmark.p
% 19.68/2.99  
% 19.68/2.99  fof(f1,axiom,(
% 19.68/2.99    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 19.68/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.68/2.99  
% 19.68/2.99  fof(f25,plain,(
% 19.68/2.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 19.68/2.99    inference(nnf_transformation,[],[f1])).
% 19.68/2.99  
% 19.68/2.99  fof(f26,plain,(
% 19.68/2.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 19.68/2.99    inference(flattening,[],[f25])).
% 19.68/2.99  
% 19.68/2.99  fof(f27,plain,(
% 19.68/2.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 19.68/2.99    inference(rectify,[],[f26])).
% 19.68/2.99  
% 19.68/2.99  fof(f28,plain,(
% 19.68/2.99    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2))))),
% 19.68/2.99    introduced(choice_axiom,[])).
% 19.68/2.99  
% 19.68/2.99  fof(f29,plain,(
% 19.68/2.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 19.68/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 19.68/2.99  
% 19.68/2.99  fof(f43,plain,(
% 19.68/2.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 19.68/2.99    inference(cnf_transformation,[],[f29])).
% 19.68/2.99  
% 19.68/2.99  fof(f69,plain,(
% 19.68/2.99    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_tarski(X0,X4) != X2) )),
% 19.68/2.99    inference(equality_resolution,[],[f43])).
% 19.68/2.99  
% 19.68/2.99  fof(f70,plain,(
% 19.68/2.99    ( ! [X4,X0] : (r2_hidden(X4,k2_tarski(X0,X4))) )),
% 19.68/2.99    inference(equality_resolution,[],[f69])).
% 19.68/2.99  
% 19.68/2.99  fof(f44,plain,(
% 19.68/2.99    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) = X2 | sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 19.68/2.99    inference(cnf_transformation,[],[f29])).
% 19.68/2.99  
% 19.68/2.99  fof(f9,conjecture,(
% 19.68/2.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))))),
% 19.68/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.68/2.99  
% 19.68/2.99  fof(f10,negated_conjecture,(
% 19.68/2.99    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))))),
% 19.68/2.99    inference(negated_conjecture,[],[f9])).
% 19.68/2.99  
% 19.68/2.99  fof(f23,plain,(
% 19.68/2.99    ? [X0] : (? [X1] : (? [X2] : ((r2_orders_2(X0,X1,X2) <~> r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 19.68/2.99    inference(ennf_transformation,[],[f10])).
% 19.68/2.99  
% 19.68/2.99  fof(f24,plain,(
% 19.68/2.99    ? [X0] : (? [X1] : (? [X2] : ((r2_orders_2(X0,X1,X2) <~> r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 19.68/2.99    inference(flattening,[],[f23])).
% 19.68/2.99  
% 19.68/2.99  fof(f35,plain,(
% 19.68/2.99    ? [X0] : (? [X1] : (? [X2] : (((~r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | ~r2_orders_2(X0,X1,X2)) & (r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | r2_orders_2(X0,X1,X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 19.68/2.99    inference(nnf_transformation,[],[f24])).
% 19.68/2.99  
% 19.68/2.99  fof(f36,plain,(
% 19.68/2.99    ? [X0] : (? [X1] : (? [X2] : ((~r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | ~r2_orders_2(X0,X1,X2)) & (r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | r2_orders_2(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 19.68/2.99    inference(flattening,[],[f35])).
% 19.68/2.99  
% 19.68/2.99  fof(f39,plain,(
% 19.68/2.99    ( ! [X0,X1] : (? [X2] : ((~r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | ~r2_orders_2(X0,X1,X2)) & (r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | r2_orders_2(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) => ((~r2_hidden(sK5,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | ~r2_orders_2(X0,X1,sK5)) & (r2_hidden(sK5,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | r2_orders_2(X0,X1,sK5)) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 19.68/2.99    introduced(choice_axiom,[])).
% 19.68/2.99  
% 19.68/2.99  fof(f38,plain,(
% 19.68/2.99    ( ! [X0] : (? [X1] : (? [X2] : ((~r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | ~r2_orders_2(X0,X1,X2)) & (r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | r2_orders_2(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : ((~r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),sK4))) | ~r2_orders_2(X0,sK4,X2)) & (r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),sK4))) | r2_orders_2(X0,sK4,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 19.68/2.99    introduced(choice_axiom,[])).
% 19.68/2.99  
% 19.68/2.99  fof(f37,plain,(
% 19.68/2.99    ? [X0] : (? [X1] : (? [X2] : ((~r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | ~r2_orders_2(X0,X1,X2)) & (r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | r2_orders_2(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r2_hidden(X2,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X1))) | ~r2_orders_2(sK3,X1,X2)) & (r2_hidden(X2,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X1))) | r2_orders_2(sK3,X1,X2)) & m1_subset_1(X2,u1_struct_0(sK3))) & m1_subset_1(X1,u1_struct_0(sK3))) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3))),
% 19.68/2.99    introduced(choice_axiom,[])).
% 19.68/2.99  
% 19.68/2.99  fof(f40,plain,(
% 19.68/2.99    (((~r2_hidden(sK5,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) | ~r2_orders_2(sK3,sK4,sK5)) & (r2_hidden(sK5,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) | r2_orders_2(sK3,sK4,sK5)) & m1_subset_1(sK5,u1_struct_0(sK3))) & m1_subset_1(sK4,u1_struct_0(sK3))) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3)),
% 19.68/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f36,f39,f38,f37])).
% 19.68/2.99  
% 19.68/2.99  fof(f64,plain,(
% 19.68/2.99    m1_subset_1(sK4,u1_struct_0(sK3))),
% 19.68/2.99    inference(cnf_transformation,[],[f40])).
% 19.68/2.99  
% 19.68/2.99  fof(f6,axiom,(
% 19.68/2.99    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 19.68/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.68/2.99  
% 19.68/2.99  fof(f17,plain,(
% 19.68/2.99    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 19.68/2.99    inference(ennf_transformation,[],[f6])).
% 19.68/2.99  
% 19.68/2.99  fof(f18,plain,(
% 19.68/2.99    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 19.68/2.99    inference(flattening,[],[f17])).
% 19.68/2.99  
% 19.68/2.99  fof(f56,plain,(
% 19.68/2.99    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 19.68/2.99    inference(cnf_transformation,[],[f18])).
% 19.68/2.99  
% 19.68/2.99  fof(f2,axiom,(
% 19.68/2.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 19.68/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.68/2.99  
% 19.68/2.99  fof(f47,plain,(
% 19.68/2.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 19.68/2.99    inference(cnf_transformation,[],[f2])).
% 19.68/2.99  
% 19.68/2.99  fof(f68,plain,(
% 19.68/2.99    ( ! [X0,X1] : (k2_tarski(X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 19.68/2.99    inference(definition_unfolding,[],[f56,f47])).
% 19.68/2.99  
% 19.68/2.99  fof(f7,axiom,(
% 19.68/2.99    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0))))),
% 19.68/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.68/2.99  
% 19.68/2.99  fof(f11,plain,(
% 19.68/2.99    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 19.68/2.99    inference(pure_predicate_removal,[],[f7])).
% 19.68/2.99  
% 19.68/2.99  fof(f19,plain,(
% 19.68/2.99    ! [X0] : (! [X1] : (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 19.68/2.99    inference(ennf_transformation,[],[f11])).
% 19.68/2.99  
% 19.68/2.99  fof(f20,plain,(
% 19.68/2.99    ! [X0] : (! [X1] : (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 19.68/2.99    inference(flattening,[],[f19])).
% 19.68/2.99  
% 19.68/2.99  fof(f57,plain,(
% 19.68/2.99    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 19.68/2.99    inference(cnf_transformation,[],[f20])).
% 19.68/2.99  
% 19.68/2.99  fof(f4,axiom,(
% 19.68/2.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)))),
% 19.68/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.68/2.99  
% 19.68/2.99  fof(f13,plain,(
% 19.68/2.99    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 19.68/2.99    inference(ennf_transformation,[],[f4])).
% 19.68/2.99  
% 19.68/2.99  fof(f14,plain,(
% 19.68/2.99    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 19.68/2.99    inference(flattening,[],[f13])).
% 19.68/2.99  
% 19.68/2.99  fof(f49,plain,(
% 19.68/2.99    ( ! [X0,X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 19.68/2.99    inference(cnf_transformation,[],[f14])).
% 19.68/2.99  
% 19.68/2.99  fof(f59,plain,(
% 19.68/2.99    ~v2_struct_0(sK3)),
% 19.68/2.99    inference(cnf_transformation,[],[f40])).
% 19.68/2.99  
% 19.68/2.99  fof(f60,plain,(
% 19.68/2.99    v3_orders_2(sK3)),
% 19.68/2.99    inference(cnf_transformation,[],[f40])).
% 19.68/2.99  
% 19.68/2.99  fof(f61,plain,(
% 19.68/2.99    v4_orders_2(sK3)),
% 19.68/2.99    inference(cnf_transformation,[],[f40])).
% 19.68/2.99  
% 19.68/2.99  fof(f62,plain,(
% 19.68/2.99    v5_orders_2(sK3)),
% 19.68/2.99    inference(cnf_transformation,[],[f40])).
% 19.68/2.99  
% 19.68/2.99  fof(f63,plain,(
% 19.68/2.99    l1_orders_2(sK3)),
% 19.68/2.99    inference(cnf_transformation,[],[f40])).
% 19.68/2.99  
% 19.68/2.99  fof(f5,axiom,(
% 19.68/2.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X4,X3))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 19.68/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.68/2.99  
% 19.68/2.99  fof(f15,plain,(
% 19.68/2.99    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 19.68/2.99    inference(ennf_transformation,[],[f5])).
% 19.68/2.99  
% 19.68/2.99  fof(f16,plain,(
% 19.68/2.99    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 19.68/2.99    inference(flattening,[],[f15])).
% 19.68/2.99  
% 19.68/2.99  fof(f30,plain,(
% 19.68/2.99    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 19.68/2.99    inference(nnf_transformation,[],[f16])).
% 19.68/2.99  
% 19.68/2.99  fof(f31,plain,(
% 19.68/2.99    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (! [X6] : (r2_orders_2(X1,X6,X5) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 19.68/2.99    inference(rectify,[],[f30])).
% 19.68/2.99  
% 19.68/2.99  fof(f33,plain,(
% 19.68/2.99    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X1,X6,X5) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (! [X6] : (r2_orders_2(X1,X6,sK2(X0,X1,X2)) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))))),
% 19.68/2.99    introduced(choice_axiom,[])).
% 19.68/2.99  
% 19.68/2.99  fof(f32,plain,(
% 19.68/2.99    ! [X3,X2,X1] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) => (~r2_orders_2(X1,sK1(X1,X2,X3),X3) & r2_hidden(sK1(X1,X2,X3),X2) & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1))))),
% 19.68/2.99    introduced(choice_axiom,[])).
% 19.68/2.99  
% 19.68/2.99  fof(f34,plain,(
% 19.68/2.99    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : ((~r2_orders_2(X1,sK1(X1,X2,X3),X3) & r2_hidden(sK1(X1,X2,X3),X2) & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((! [X6] : (r2_orders_2(X1,X6,sK2(X0,X1,X2)) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 19.68/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f31,f33,f32])).
% 19.68/2.99  
% 19.68/2.99  fof(f54,plain,(
% 19.68/2.99    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_0_orders_2(X1,X2)) | r2_hidden(sK1(X1,X2,X3),X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 19.68/2.99    inference(cnf_transformation,[],[f34])).
% 19.68/2.99  
% 19.68/2.99  fof(f75,plain,(
% 19.68/2.99    ( ! [X2,X3,X1] : (r2_hidden(X3,a_2_0_orders_2(X1,X2)) | r2_hidden(sK1(X1,X2,X3),X2) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 19.68/2.99    inference(equality_resolution,[],[f54])).
% 19.68/2.99  
% 19.68/2.99  fof(f3,axiom,(
% 19.68/2.99    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 19.68/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.68/2.99  
% 19.68/2.99  fof(f12,plain,(
% 19.68/2.99    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 19.68/2.99    inference(ennf_transformation,[],[f3])).
% 19.68/2.99  
% 19.68/2.99  fof(f48,plain,(
% 19.68/2.99    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 19.68/2.99    inference(cnf_transformation,[],[f12])).
% 19.68/2.99  
% 19.68/2.99  fof(f65,plain,(
% 19.68/2.99    m1_subset_1(sK5,u1_struct_0(sK3))),
% 19.68/2.99    inference(cnf_transformation,[],[f40])).
% 19.68/2.99  
% 19.68/2.99  fof(f8,axiom,(
% 19.68/2.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))),
% 19.68/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.68/2.99  
% 19.68/2.99  fof(f21,plain,(
% 19.68/2.99    ! [X0] : (! [X1] : (~r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 19.68/2.99    inference(ennf_transformation,[],[f8])).
% 19.68/2.99  
% 19.68/2.99  fof(f22,plain,(
% 19.68/2.99    ! [X0] : (! [X1] : (~r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 19.68/2.99    inference(flattening,[],[f21])).
% 19.68/2.99  
% 19.68/2.99  fof(f58,plain,(
% 19.68/2.99    ( ! [X0,X1] : (~r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 19.68/2.99    inference(cnf_transformation,[],[f22])).
% 19.68/2.99  
% 19.68/2.99  fof(f66,plain,(
% 19.68/2.99    r2_hidden(sK5,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) | r2_orders_2(sK3,sK4,sK5)),
% 19.68/2.99    inference(cnf_transformation,[],[f40])).
% 19.68/2.99  
% 19.68/2.99  fof(f51,plain,(
% 19.68/2.99    ( ! [X2,X0,X1] : (sK2(X0,X1,X2) = X0 | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 19.68/2.99    inference(cnf_transformation,[],[f34])).
% 19.68/2.99  
% 19.68/2.99  fof(f53,plain,(
% 19.68/2.99    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_0_orders_2(X1,X2)) | m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1)) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 19.68/2.99    inference(cnf_transformation,[],[f34])).
% 19.68/2.99  
% 19.68/2.99  fof(f76,plain,(
% 19.68/2.99    ( ! [X2,X3,X1] : (r2_hidden(X3,a_2_0_orders_2(X1,X2)) | m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 19.68/2.99    inference(equality_resolution,[],[f53])).
% 19.68/2.99  
% 19.68/2.99  fof(f67,plain,(
% 19.68/2.99    ~r2_hidden(sK5,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) | ~r2_orders_2(sK3,sK4,sK5)),
% 19.68/2.99    inference(cnf_transformation,[],[f40])).
% 19.68/2.99  
% 19.68/2.99  fof(f41,plain,(
% 19.68/2.99    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 19.68/2.99    inference(cnf_transformation,[],[f29])).
% 19.68/2.99  
% 19.68/2.99  fof(f73,plain,(
% 19.68/2.99    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k2_tarski(X0,X1))) )),
% 19.68/2.99    inference(equality_resolution,[],[f41])).
% 19.68/2.99  
% 19.68/2.99  fof(f52,plain,(
% 19.68/2.99    ( ! [X6,X2,X0,X1] : (r2_orders_2(X1,X6,sK2(X0,X1,X2)) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 19.68/2.99    inference(cnf_transformation,[],[f34])).
% 19.68/2.99  
% 19.68/2.99  fof(f55,plain,(
% 19.68/2.99    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ~r2_orders_2(X1,sK1(X1,X2,X3),X3) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 19.68/2.99    inference(cnf_transformation,[],[f34])).
% 19.68/2.99  
% 19.68/2.99  fof(f74,plain,(
% 19.68/2.99    ( ! [X2,X3,X1] : (r2_hidden(X3,a_2_0_orders_2(X1,X2)) | ~r2_orders_2(X1,sK1(X1,X2,X3),X3) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 19.68/2.99    inference(equality_resolution,[],[f55])).
% 19.68/2.99  
% 19.68/2.99  cnf(c_3,plain,
% 19.68/2.99      ( r2_hidden(X0,k2_tarski(X1,X0)) ),
% 19.68/2.99      inference(cnf_transformation,[],[f70]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_967,plain,
% 19.68/2.99      ( r2_hidden(X0,k2_tarski(X1,X0)) = iProver_top ),
% 19.68/2.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_2,plain,
% 19.68/2.99      ( r2_hidden(sK0(X0,X1,X2),X2)
% 19.68/2.99      | sK0(X0,X1,X2) = X1
% 19.68/2.99      | sK0(X0,X1,X2) = X0
% 19.68/2.99      | k2_tarski(X0,X1) = X2 ),
% 19.68/2.99      inference(cnf_transformation,[],[f44]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_968,plain,
% 19.68/2.99      ( sK0(X0,X1,X2) = X1
% 19.68/2.99      | sK0(X0,X1,X2) = X0
% 19.68/2.99      | k2_tarski(X0,X1) = X2
% 19.68/2.99      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 19.68/2.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_20,negated_conjecture,
% 19.68/2.99      ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 19.68/2.99      inference(cnf_transformation,[],[f64]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_950,plain,
% 19.68/2.99      ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
% 19.68/2.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_14,plain,
% 19.68/2.99      ( ~ m1_subset_1(X0,X1)
% 19.68/2.99      | v1_xboole_0(X1)
% 19.68/2.99      | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
% 19.68/2.99      inference(cnf_transformation,[],[f68]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_956,plain,
% 19.68/2.99      ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
% 19.68/2.99      | m1_subset_1(X1,X0) != iProver_top
% 19.68/2.99      | v1_xboole_0(X0) = iProver_top ),
% 19.68/2.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_1689,plain,
% 19.68/2.99      ( k6_domain_1(u1_struct_0(sK3),sK4) = k2_tarski(sK4,sK4)
% 19.68/2.99      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 19.68/2.99      inference(superposition,[status(thm)],[c_950,c_956]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_15,plain,
% 19.68/2.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 19.68/2.99      | m1_subset_1(k6_domain_1(u1_struct_0(X1),X0),k1_zfmisc_1(u1_struct_0(X1)))
% 19.68/2.99      | v2_struct_0(X1)
% 19.68/2.99      | ~ v3_orders_2(X1)
% 19.68/2.99      | ~ l1_orders_2(X1) ),
% 19.68/2.99      inference(cnf_transformation,[],[f57]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_955,plain,
% 19.68/2.99      ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 19.68/2.99      | m1_subset_1(k6_domain_1(u1_struct_0(X1),X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 19.68/2.99      | v2_struct_0(X1) = iProver_top
% 19.68/2.99      | v3_orders_2(X1) != iProver_top
% 19.68/2.99      | l1_orders_2(X1) != iProver_top ),
% 19.68/2.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_7,plain,
% 19.68/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.68/2.99      | v2_struct_0(X1)
% 19.68/2.99      | ~ v3_orders_2(X1)
% 19.68/2.99      | ~ v4_orders_2(X1)
% 19.68/2.99      | ~ v5_orders_2(X1)
% 19.68/2.99      | ~ l1_orders_2(X1)
% 19.68/2.99      | a_2_0_orders_2(X1,X0) = k1_orders_2(X1,X0) ),
% 19.68/2.99      inference(cnf_transformation,[],[f49]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_963,plain,
% 19.68/2.99      ( a_2_0_orders_2(X0,X1) = k1_orders_2(X0,X1)
% 19.68/2.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 19.68/2.99      | v2_struct_0(X0) = iProver_top
% 19.68/2.99      | v3_orders_2(X0) != iProver_top
% 19.68/2.99      | v4_orders_2(X0) != iProver_top
% 19.68/2.99      | v5_orders_2(X0) != iProver_top
% 19.68/2.99      | l1_orders_2(X0) != iProver_top ),
% 19.68/2.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_2350,plain,
% 19.68/2.99      ( a_2_0_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)) = k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))
% 19.68/2.99      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 19.68/2.99      | v2_struct_0(X0) = iProver_top
% 19.68/2.99      | v3_orders_2(X0) != iProver_top
% 19.68/2.99      | v4_orders_2(X0) != iProver_top
% 19.68/2.99      | v5_orders_2(X0) != iProver_top
% 19.68/2.99      | l1_orders_2(X0) != iProver_top ),
% 19.68/2.99      inference(superposition,[status(thm)],[c_955,c_963]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_6486,plain,
% 19.68/2.99      ( a_2_0_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4)) = k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))
% 19.68/2.99      | v2_struct_0(sK3) = iProver_top
% 19.68/2.99      | v3_orders_2(sK3) != iProver_top
% 19.68/2.99      | v4_orders_2(sK3) != iProver_top
% 19.68/2.99      | v5_orders_2(sK3) != iProver_top
% 19.68/2.99      | l1_orders_2(sK3) != iProver_top ),
% 19.68/2.99      inference(superposition,[status(thm)],[c_950,c_2350]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_25,negated_conjecture,
% 19.68/2.99      ( ~ v2_struct_0(sK3) ),
% 19.68/2.99      inference(cnf_transformation,[],[f59]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_24,negated_conjecture,
% 19.68/2.99      ( v3_orders_2(sK3) ),
% 19.68/2.99      inference(cnf_transformation,[],[f60]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_23,negated_conjecture,
% 19.68/2.99      ( v4_orders_2(sK3) ),
% 19.68/2.99      inference(cnf_transformation,[],[f61]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_22,negated_conjecture,
% 19.68/2.99      ( v5_orders_2(sK3) ),
% 19.68/2.99      inference(cnf_transformation,[],[f62]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_21,negated_conjecture,
% 19.68/2.99      ( l1_orders_2(sK3) ),
% 19.68/2.99      inference(cnf_transformation,[],[f63]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_1296,plain,
% 19.68/2.99      ( m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 19.68/2.99      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 19.68/2.99      | v2_struct_0(sK3)
% 19.68/2.99      | ~ v3_orders_2(sK3)
% 19.68/2.99      | ~ l1_orders_2(sK3) ),
% 19.68/2.99      inference(instantiation,[status(thm)],[c_15]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_1429,plain,
% 19.68/2.99      ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 19.68/2.99      | v2_struct_0(sK3)
% 19.68/2.99      | ~ v3_orders_2(sK3)
% 19.68/2.99      | ~ v4_orders_2(sK3)
% 19.68/2.99      | ~ v5_orders_2(sK3)
% 19.68/2.99      | ~ l1_orders_2(sK3)
% 19.68/2.99      | a_2_0_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4)) = k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4)) ),
% 19.68/2.99      inference(instantiation,[status(thm)],[c_7]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_7321,plain,
% 19.68/2.99      ( a_2_0_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4)) = k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4)) ),
% 19.68/2.99      inference(global_propositional_subsumption,
% 19.68/2.99                [status(thm)],
% 19.68/2.99                [c_6486,c_25,c_24,c_23,c_22,c_21,c_20,c_1296,c_1429]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_9,plain,
% 19.68/2.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 19.68/2.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 19.68/2.99      | r2_hidden(X0,a_2_0_orders_2(X1,X2))
% 19.68/2.99      | r2_hidden(sK1(X1,X2,X0),X2)
% 19.68/2.99      | v2_struct_0(X1)
% 19.68/2.99      | ~ v3_orders_2(X1)
% 19.68/2.99      | ~ v4_orders_2(X1)
% 19.68/2.99      | ~ v5_orders_2(X1)
% 19.68/2.99      | ~ l1_orders_2(X1) ),
% 19.68/2.99      inference(cnf_transformation,[],[f75]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_961,plain,
% 19.68/2.99      ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 19.68/2.99      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 19.68/2.99      | r2_hidden(X0,a_2_0_orders_2(X1,X2)) = iProver_top
% 19.68/2.99      | r2_hidden(sK1(X1,X2,X0),X2) = iProver_top
% 19.68/2.99      | v2_struct_0(X1) = iProver_top
% 19.68/2.99      | v3_orders_2(X1) != iProver_top
% 19.68/2.99      | v4_orders_2(X1) != iProver_top
% 19.68/2.99      | v5_orders_2(X1) != iProver_top
% 19.68/2.99      | l1_orders_2(X1) != iProver_top ),
% 19.68/2.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_6,plain,
% 19.68/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.68/2.99      | ~ r2_hidden(X2,X0)
% 19.68/2.99      | ~ v1_xboole_0(X1) ),
% 19.68/2.99      inference(cnf_transformation,[],[f48]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_964,plain,
% 19.68/2.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 19.68/2.99      | r2_hidden(X2,X0) != iProver_top
% 19.68/2.99      | v1_xboole_0(X1) != iProver_top ),
% 19.68/2.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_2092,plain,
% 19.68/2.99      ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 19.68/2.99      | r2_hidden(X2,k6_domain_1(u1_struct_0(X1),X0)) != iProver_top
% 19.68/2.99      | v2_struct_0(X1) = iProver_top
% 19.68/2.99      | v3_orders_2(X1) != iProver_top
% 19.68/2.99      | l1_orders_2(X1) != iProver_top
% 19.68/2.99      | v1_xboole_0(u1_struct_0(X1)) != iProver_top ),
% 19.68/2.99      inference(superposition,[status(thm)],[c_955,c_964]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_4237,plain,
% 19.68/2.99      ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 19.68/2.99      | m1_subset_1(X2,u1_struct_0(X3)) != iProver_top
% 19.68/2.99      | m1_subset_1(k6_domain_1(u1_struct_0(X3),X2),k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 19.68/2.99      | r2_hidden(X0,a_2_0_orders_2(X1,k6_domain_1(u1_struct_0(X3),X2))) = iProver_top
% 19.68/2.99      | v2_struct_0(X1) = iProver_top
% 19.68/2.99      | v2_struct_0(X3) = iProver_top
% 19.68/2.99      | v3_orders_2(X1) != iProver_top
% 19.68/2.99      | v3_orders_2(X3) != iProver_top
% 19.68/2.99      | v4_orders_2(X1) != iProver_top
% 19.68/2.99      | v5_orders_2(X1) != iProver_top
% 19.68/2.99      | l1_orders_2(X1) != iProver_top
% 19.68/2.99      | l1_orders_2(X3) != iProver_top
% 19.68/2.99      | v1_xboole_0(u1_struct_0(X3)) != iProver_top ),
% 19.68/2.99      inference(superposition,[status(thm)],[c_961,c_2092]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_17712,plain,
% 19.68/2.99      ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 19.68/2.99      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 19.68/2.99      | r2_hidden(X2,a_2_0_orders_2(X1,k6_domain_1(u1_struct_0(X1),X0))) = iProver_top
% 19.68/2.99      | v2_struct_0(X1) = iProver_top
% 19.68/2.99      | v3_orders_2(X1) != iProver_top
% 19.68/2.99      | v4_orders_2(X1) != iProver_top
% 19.68/2.99      | v5_orders_2(X1) != iProver_top
% 19.68/2.99      | l1_orders_2(X1) != iProver_top
% 19.68/2.99      | v1_xboole_0(u1_struct_0(X1)) != iProver_top ),
% 19.68/2.99      inference(superposition,[status(thm)],[c_955,c_4237]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_21206,plain,
% 19.68/2.99      ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 19.68/2.99      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 19.68/2.99      | r2_hidden(X0,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) = iProver_top
% 19.68/2.99      | v2_struct_0(sK3) = iProver_top
% 19.68/2.99      | v3_orders_2(sK3) != iProver_top
% 19.68/2.99      | v4_orders_2(sK3) != iProver_top
% 19.68/2.99      | v5_orders_2(sK3) != iProver_top
% 19.68/2.99      | l1_orders_2(sK3) != iProver_top
% 19.68/2.99      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 19.68/2.99      inference(superposition,[status(thm)],[c_7321,c_17712]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_26,plain,
% 19.68/2.99      ( v2_struct_0(sK3) != iProver_top ),
% 19.68/2.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_27,plain,
% 19.68/2.99      ( v3_orders_2(sK3) = iProver_top ),
% 19.68/2.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_28,plain,
% 19.68/2.99      ( v4_orders_2(sK3) = iProver_top ),
% 19.68/2.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_29,plain,
% 19.68/2.99      ( v5_orders_2(sK3) = iProver_top ),
% 19.68/2.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_30,plain,
% 19.68/2.99      ( l1_orders_2(sK3) = iProver_top ),
% 19.68/2.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_19,negated_conjecture,
% 19.68/2.99      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 19.68/2.99      inference(cnf_transformation,[],[f65]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_32,plain,
% 19.68/2.99      ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
% 19.68/2.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_951,plain,
% 19.68/2.99      ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
% 19.68/2.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_6485,plain,
% 19.68/2.99      ( a_2_0_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)) = k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))
% 19.68/2.99      | v2_struct_0(sK3) = iProver_top
% 19.68/2.99      | v3_orders_2(sK3) != iProver_top
% 19.68/2.99      | v4_orders_2(sK3) != iProver_top
% 19.68/2.99      | v5_orders_2(sK3) != iProver_top
% 19.68/2.99      | l1_orders_2(sK3) != iProver_top ),
% 19.68/2.99      inference(superposition,[status(thm)],[c_951,c_2350]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_1293,plain,
% 19.68/2.99      ( m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK5),k1_zfmisc_1(u1_struct_0(sK3)))
% 19.68/2.99      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 19.68/2.99      | v2_struct_0(sK3)
% 19.68/2.99      | ~ v3_orders_2(sK3)
% 19.68/2.99      | ~ l1_orders_2(sK3) ),
% 19.68/2.99      inference(instantiation,[status(thm)],[c_15]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_1383,plain,
% 19.68/2.99      ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK5),k1_zfmisc_1(u1_struct_0(sK3)))
% 19.68/2.99      | v2_struct_0(sK3)
% 19.68/2.99      | ~ v3_orders_2(sK3)
% 19.68/2.99      | ~ v4_orders_2(sK3)
% 19.68/2.99      | ~ v5_orders_2(sK3)
% 19.68/2.99      | ~ l1_orders_2(sK3)
% 19.68/2.99      | a_2_0_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)) = k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)) ),
% 19.68/2.99      inference(instantiation,[status(thm)],[c_7]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_7317,plain,
% 19.68/2.99      ( a_2_0_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)) = k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)) ),
% 19.68/2.99      inference(global_propositional_subsumption,
% 19.68/2.99                [status(thm)],
% 19.68/2.99                [c_6485,c_25,c_24,c_23,c_22,c_21,c_19,c_1293,c_1383]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_21205,plain,
% 19.68/2.99      ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 19.68/2.99      | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
% 19.68/2.99      | r2_hidden(X0,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) = iProver_top
% 19.68/2.99      | v2_struct_0(sK3) = iProver_top
% 19.68/2.99      | v3_orders_2(sK3) != iProver_top
% 19.68/2.99      | v4_orders_2(sK3) != iProver_top
% 19.68/2.99      | v5_orders_2(sK3) != iProver_top
% 19.68/2.99      | l1_orders_2(sK3) != iProver_top
% 19.68/2.99      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 19.68/2.99      inference(superposition,[status(thm)],[c_7317,c_17712]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_22249,plain,
% 19.68/2.99      ( r2_hidden(X0,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) = iProver_top
% 19.68/2.99      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 19.68/2.99      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 19.68/2.99      inference(global_propositional_subsumption,
% 19.68/2.99                [status(thm)],
% 19.68/2.99                [c_21205,c_26,c_27,c_28,c_29,c_30,c_32]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_22250,plain,
% 19.68/2.99      ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 19.68/2.99      | r2_hidden(X0,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) = iProver_top
% 19.68/2.99      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 19.68/2.99      inference(renaming,[status(thm)],[c_22249]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_16,plain,
% 19.68/2.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 19.68/2.99      | ~ r2_hidden(X0,k1_orders_2(X1,k6_domain_1(u1_struct_0(X1),X0)))
% 19.68/2.99      | v2_struct_0(X1)
% 19.68/2.99      | ~ v3_orders_2(X1)
% 19.68/2.99      | ~ v4_orders_2(X1)
% 19.68/2.99      | ~ v5_orders_2(X1)
% 19.68/2.99      | ~ l1_orders_2(X1) ),
% 19.68/2.99      inference(cnf_transformation,[],[f58]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_954,plain,
% 19.68/2.99      ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 19.68/2.99      | r2_hidden(X0,k1_orders_2(X1,k6_domain_1(u1_struct_0(X1),X0))) != iProver_top
% 19.68/2.99      | v2_struct_0(X1) = iProver_top
% 19.68/2.99      | v3_orders_2(X1) != iProver_top
% 19.68/2.99      | v4_orders_2(X1) != iProver_top
% 19.68/2.99      | v5_orders_2(X1) != iProver_top
% 19.68/2.99      | l1_orders_2(X1) != iProver_top ),
% 19.68/2.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_22258,plain,
% 19.68/2.99      ( m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
% 19.68/2.99      | v2_struct_0(sK3) = iProver_top
% 19.68/2.99      | v3_orders_2(sK3) != iProver_top
% 19.68/2.99      | v4_orders_2(sK3) != iProver_top
% 19.68/2.99      | v5_orders_2(sK3) != iProver_top
% 19.68/2.99      | l1_orders_2(sK3) != iProver_top
% 19.68/2.99      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 19.68/2.99      inference(superposition,[status(thm)],[c_22250,c_954]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_22791,plain,
% 19.68/2.99      ( v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 19.68/2.99      inference(global_propositional_subsumption,
% 19.68/2.99                [status(thm)],
% 19.68/2.99                [c_21206,c_26,c_27,c_28,c_29,c_30,c_32,c_22258]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_22797,plain,
% 19.68/2.99      ( k6_domain_1(u1_struct_0(sK3),sK4) = k2_tarski(sK4,sK4) ),
% 19.68/2.99      inference(superposition,[status(thm)],[c_1689,c_22791]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_18,negated_conjecture,
% 19.68/2.99      ( r2_orders_2(sK3,sK4,sK5)
% 19.68/2.99      | r2_hidden(sK5,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) ),
% 19.68/2.99      inference(cnf_transformation,[],[f66]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_952,plain,
% 19.68/2.99      ( r2_orders_2(sK3,sK4,sK5) = iProver_top
% 19.68/2.99      | r2_hidden(sK5,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) = iProver_top ),
% 19.68/2.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_12,plain,
% 19.68/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.68/2.99      | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
% 19.68/2.99      | v2_struct_0(X1)
% 19.68/2.99      | ~ v3_orders_2(X1)
% 19.68/2.99      | ~ v4_orders_2(X1)
% 19.68/2.99      | ~ v5_orders_2(X1)
% 19.68/2.99      | ~ l1_orders_2(X1)
% 19.68/2.99      | sK2(X2,X1,X0) = X2 ),
% 19.68/2.99      inference(cnf_transformation,[],[f51]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_958,plain,
% 19.68/2.99      ( sK2(X0,X1,X2) = X0
% 19.68/2.99      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 19.68/2.99      | r2_hidden(X0,a_2_0_orders_2(X1,X2)) != iProver_top
% 19.68/2.99      | v2_struct_0(X1) = iProver_top
% 19.68/2.99      | v3_orders_2(X1) != iProver_top
% 19.68/2.99      | v4_orders_2(X1) != iProver_top
% 19.68/2.99      | v5_orders_2(X1) != iProver_top
% 19.68/2.99      | l1_orders_2(X1) != iProver_top ),
% 19.68/2.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_2470,plain,
% 19.68/2.99      ( sK2(X0,X1,k6_domain_1(u1_struct_0(X1),X2)) = X0
% 19.68/2.99      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 19.68/2.99      | r2_hidden(X0,a_2_0_orders_2(X1,k6_domain_1(u1_struct_0(X1),X2))) != iProver_top
% 19.68/2.99      | v2_struct_0(X1) = iProver_top
% 19.68/2.99      | v3_orders_2(X1) != iProver_top
% 19.68/2.99      | v4_orders_2(X1) != iProver_top
% 19.68/2.99      | v5_orders_2(X1) != iProver_top
% 19.68/2.99      | l1_orders_2(X1) != iProver_top ),
% 19.68/2.99      inference(superposition,[status(thm)],[c_955,c_958]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_8707,plain,
% 19.68/2.99      ( sK2(X0,sK3,k6_domain_1(u1_struct_0(sK3),sK4)) = X0
% 19.68/2.99      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 19.68/2.99      | r2_hidden(X0,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) != iProver_top
% 19.68/2.99      | v2_struct_0(sK3) = iProver_top
% 19.68/2.99      | v3_orders_2(sK3) != iProver_top
% 19.68/2.99      | v4_orders_2(sK3) != iProver_top
% 19.68/2.99      | v5_orders_2(sK3) != iProver_top
% 19.68/2.99      | l1_orders_2(sK3) != iProver_top ),
% 19.68/2.99      inference(superposition,[status(thm)],[c_7321,c_2470]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_31,plain,
% 19.68/2.99      ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
% 19.68/2.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_9596,plain,
% 19.68/2.99      ( r2_hidden(X0,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) != iProver_top
% 19.68/2.99      | sK2(X0,sK3,k6_domain_1(u1_struct_0(sK3),sK4)) = X0 ),
% 19.68/2.99      inference(global_propositional_subsumption,
% 19.68/2.99                [status(thm)],
% 19.68/2.99                [c_8707,c_26,c_27,c_28,c_29,c_30,c_31]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_9597,plain,
% 19.68/2.99      ( sK2(X0,sK3,k6_domain_1(u1_struct_0(sK3),sK4)) = X0
% 19.68/2.99      | r2_hidden(X0,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) != iProver_top ),
% 19.68/2.99      inference(renaming,[status(thm)],[c_9596]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_9606,plain,
% 19.68/2.99      ( sK2(sK5,sK3,k6_domain_1(u1_struct_0(sK3),sK4)) = sK5
% 19.68/2.99      | r2_orders_2(sK3,sK4,sK5) = iProver_top ),
% 19.68/2.99      inference(superposition,[status(thm)],[c_952,c_9597]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_22835,plain,
% 19.68/2.99      ( sK2(sK5,sK3,k2_tarski(sK4,sK4)) = sK5
% 19.68/2.99      | r2_orders_2(sK3,sK4,sK5) = iProver_top ),
% 19.68/2.99      inference(demodulation,[status(thm)],[c_22797,c_9606]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_22960,plain,
% 19.68/2.99      ( m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 19.68/2.99      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 19.68/2.99      | v2_struct_0(sK3) = iProver_top
% 19.68/2.99      | v3_orders_2(sK3) != iProver_top
% 19.68/2.99      | l1_orders_2(sK3) != iProver_top ),
% 19.68/2.99      inference(superposition,[status(thm)],[c_22797,c_955]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_24442,plain,
% 19.68/2.99      ( m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 19.68/2.99      inference(global_propositional_subsumption,
% 19.68/2.99                [status(thm)],
% 19.68/2.99                [c_22960,c_26,c_27,c_30,c_31]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_10,plain,
% 19.68/2.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 19.68/2.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 19.68/2.99      | m1_subset_1(sK1(X1,X2,X0),u1_struct_0(X1))
% 19.68/2.99      | r2_hidden(X0,a_2_0_orders_2(X1,X2))
% 19.68/2.99      | v2_struct_0(X1)
% 19.68/2.99      | ~ v3_orders_2(X1)
% 19.68/2.99      | ~ v4_orders_2(X1)
% 19.68/2.99      | ~ v5_orders_2(X1)
% 19.68/2.99      | ~ l1_orders_2(X1) ),
% 19.68/2.99      inference(cnf_transformation,[],[f76]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_960,plain,
% 19.68/2.99      ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 19.68/2.99      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 19.68/2.99      | m1_subset_1(sK1(X1,X2,X0),u1_struct_0(X1)) = iProver_top
% 19.68/2.99      | r2_hidden(X0,a_2_0_orders_2(X1,X2)) = iProver_top
% 19.68/2.99      | v2_struct_0(X1) = iProver_top
% 19.68/2.99      | v3_orders_2(X1) != iProver_top
% 19.68/2.99      | v4_orders_2(X1) != iProver_top
% 19.68/2.99      | v5_orders_2(X1) != iProver_top
% 19.68/2.99      | l1_orders_2(X1) != iProver_top ),
% 19.68/2.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_4300,plain,
% 19.68/2.99      ( k2_tarski(sK1(X0,X1,X2),sK1(X0,X1,X2)) = k6_domain_1(u1_struct_0(X0),sK1(X0,X1,X2))
% 19.68/2.99      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 19.68/2.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 19.68/2.99      | r2_hidden(X2,a_2_0_orders_2(X0,X1)) = iProver_top
% 19.68/2.99      | v2_struct_0(X0) = iProver_top
% 19.68/2.99      | v3_orders_2(X0) != iProver_top
% 19.68/2.99      | v4_orders_2(X0) != iProver_top
% 19.68/2.99      | v5_orders_2(X0) != iProver_top
% 19.68/2.99      | l1_orders_2(X0) != iProver_top
% 19.68/2.99      | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
% 19.68/2.99      inference(superposition,[status(thm)],[c_960,c_956]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_24448,plain,
% 19.68/2.99      ( k2_tarski(sK1(sK3,k2_tarski(sK4,sK4),X0),sK1(sK3,k2_tarski(sK4,sK4),X0)) = k6_domain_1(u1_struct_0(sK3),sK1(sK3,k2_tarski(sK4,sK4),X0))
% 19.68/2.99      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 19.68/2.99      | r2_hidden(X0,a_2_0_orders_2(sK3,k2_tarski(sK4,sK4))) = iProver_top
% 19.68/2.99      | v2_struct_0(sK3) = iProver_top
% 19.68/2.99      | v3_orders_2(sK3) != iProver_top
% 19.68/2.99      | v4_orders_2(sK3) != iProver_top
% 19.68/2.99      | v5_orders_2(sK3) != iProver_top
% 19.68/2.99      | l1_orders_2(sK3) != iProver_top
% 19.68/2.99      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 19.68/2.99      inference(superposition,[status(thm)],[c_24442,c_4300]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_22837,plain,
% 19.68/2.99      ( a_2_0_orders_2(sK3,k2_tarski(sK4,sK4)) = k1_orders_2(sK3,k2_tarski(sK4,sK4)) ),
% 19.68/2.99      inference(demodulation,[status(thm)],[c_22797,c_7321]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_24539,plain,
% 19.68/2.99      ( k2_tarski(sK1(sK3,k2_tarski(sK4,sK4),X0),sK1(sK3,k2_tarski(sK4,sK4),X0)) = k6_domain_1(u1_struct_0(sK3),sK1(sK3,k2_tarski(sK4,sK4),X0))
% 19.68/2.99      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 19.68/2.99      | r2_hidden(X0,k1_orders_2(sK3,k2_tarski(sK4,sK4))) = iProver_top
% 19.68/2.99      | v2_struct_0(sK3) = iProver_top
% 19.68/2.99      | v3_orders_2(sK3) != iProver_top
% 19.68/2.99      | v4_orders_2(sK3) != iProver_top
% 19.68/2.99      | v5_orders_2(sK3) != iProver_top
% 19.68/2.99      | l1_orders_2(sK3) != iProver_top
% 19.68/2.99      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 19.68/2.99      inference(light_normalisation,[status(thm)],[c_24448,c_22837]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_45926,plain,
% 19.68/2.99      ( k2_tarski(sK1(sK3,k2_tarski(sK4,sK4),X0),sK1(sK3,k2_tarski(sK4,sK4),X0)) = k6_domain_1(u1_struct_0(sK3),sK1(sK3,k2_tarski(sK4,sK4),X0))
% 19.68/2.99      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 19.68/2.99      | r2_hidden(X0,k1_orders_2(sK3,k2_tarski(sK4,sK4))) = iProver_top ),
% 19.68/2.99      inference(global_propositional_subsumption,
% 19.68/2.99                [status(thm)],
% 19.68/2.99                [c_24539,c_26,c_27,c_28,c_29,c_30,c_32,c_22258]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_17,negated_conjecture,
% 19.68/2.99      ( ~ r2_orders_2(sK3,sK4,sK5)
% 19.68/2.99      | ~ r2_hidden(sK5,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) ),
% 19.68/2.99      inference(cnf_transformation,[],[f67]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_953,plain,
% 19.68/2.99      ( r2_orders_2(sK3,sK4,sK5) != iProver_top
% 19.68/2.99      | r2_hidden(sK5,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) != iProver_top ),
% 19.68/2.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_22840,plain,
% 19.68/2.99      ( r2_orders_2(sK3,sK4,sK5) != iProver_top
% 19.68/2.99      | r2_hidden(sK5,k1_orders_2(sK3,k2_tarski(sK4,sK4))) != iProver_top ),
% 19.68/2.99      inference(demodulation,[status(thm)],[c_22797,c_953]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_45938,plain,
% 19.68/2.99      ( k2_tarski(sK1(sK3,k2_tarski(sK4,sK4),sK5),sK1(sK3,k2_tarski(sK4,sK4),sK5)) = k6_domain_1(u1_struct_0(sK3),sK1(sK3,k2_tarski(sK4,sK4),sK5))
% 19.68/2.99      | r2_orders_2(sK3,sK4,sK5) != iProver_top
% 19.68/2.99      | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top ),
% 19.68/2.99      inference(superposition,[status(thm)],[c_45926,c_22840]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_45980,plain,
% 19.68/2.99      ( r2_orders_2(sK3,sK4,sK5) != iProver_top
% 19.68/2.99      | k2_tarski(sK1(sK3,k2_tarski(sK4,sK4),sK5),sK1(sK3,k2_tarski(sK4,sK4),sK5)) = k6_domain_1(u1_struct_0(sK3),sK1(sK3,k2_tarski(sK4,sK4),sK5)) ),
% 19.68/2.99      inference(global_propositional_subsumption,
% 19.68/2.99                [status(thm)],
% 19.68/2.99                [c_45938,c_32]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_45981,plain,
% 19.68/2.99      ( k2_tarski(sK1(sK3,k2_tarski(sK4,sK4),sK5),sK1(sK3,k2_tarski(sK4,sK4),sK5)) = k6_domain_1(u1_struct_0(sK3),sK1(sK3,k2_tarski(sK4,sK4),sK5))
% 19.68/2.99      | r2_orders_2(sK3,sK4,sK5) != iProver_top ),
% 19.68/2.99      inference(renaming,[status(thm)],[c_45980]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_45988,plain,
% 19.68/2.99      ( sK2(sK5,sK3,k2_tarski(sK4,sK4)) = sK5
% 19.68/2.99      | k2_tarski(sK1(sK3,k2_tarski(sK4,sK4),sK5),sK1(sK3,k2_tarski(sK4,sK4),sK5)) = k6_domain_1(u1_struct_0(sK3),sK1(sK3,k2_tarski(sK4,sK4),sK5)) ),
% 19.68/2.99      inference(superposition,[status(thm)],[c_22835,c_45981]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_5,plain,
% 19.68/2.99      ( ~ r2_hidden(X0,k2_tarski(X1,X2)) | X0 = X1 | X0 = X2 ),
% 19.68/2.99      inference(cnf_transformation,[],[f73]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_965,plain,
% 19.68/2.99      ( X0 = X1
% 19.68/2.99      | X0 = X2
% 19.68/2.99      | r2_hidden(X0,k2_tarski(X1,X2)) != iProver_top ),
% 19.68/2.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_46673,plain,
% 19.68/2.99      ( sK2(sK5,sK3,k2_tarski(sK4,sK4)) = sK5
% 19.68/2.99      | sK1(sK3,k2_tarski(sK4,sK4),sK5) = X0
% 19.68/2.99      | r2_hidden(X0,k6_domain_1(u1_struct_0(sK3),sK1(sK3,k2_tarski(sK4,sK4),sK5))) != iProver_top ),
% 19.68/2.99      inference(superposition,[status(thm)],[c_45988,c_965]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_48726,plain,
% 19.68/2.99      ( sK2(sK5,sK3,k2_tarski(sK4,sK4)) = sK5
% 19.68/2.99      | sK0(X0,X1,k6_domain_1(u1_struct_0(sK3),sK1(sK3,k2_tarski(sK4,sK4),sK5))) = X0
% 19.68/2.99      | sK0(X0,X1,k6_domain_1(u1_struct_0(sK3),sK1(sK3,k2_tarski(sK4,sK4),sK5))) = X1
% 19.68/2.99      | sK0(X0,X1,k6_domain_1(u1_struct_0(sK3),sK1(sK3,k2_tarski(sK4,sK4),sK5))) = sK1(sK3,k2_tarski(sK4,sK4),sK5)
% 19.68/2.99      | k6_domain_1(u1_struct_0(sK3),sK1(sK3,k2_tarski(sK4,sK4),sK5)) = k2_tarski(X0,X1) ),
% 19.68/2.99      inference(superposition,[status(thm)],[c_968,c_46673]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_4236,plain,
% 19.68/2.99      ( sK1(X0,k2_tarski(X1,X2),X3) = X1
% 19.68/2.99      | sK1(X0,k2_tarski(X1,X2),X3) = X2
% 19.68/2.99      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 19.68/2.99      | m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 19.68/2.99      | r2_hidden(X3,a_2_0_orders_2(X0,k2_tarski(X1,X2))) = iProver_top
% 19.68/2.99      | v2_struct_0(X0) = iProver_top
% 19.68/2.99      | v3_orders_2(X0) != iProver_top
% 19.68/2.99      | v4_orders_2(X0) != iProver_top
% 19.68/2.99      | v5_orders_2(X0) != iProver_top
% 19.68/2.99      | l1_orders_2(X0) != iProver_top ),
% 19.68/2.99      inference(superposition,[status(thm)],[c_961,c_965]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_24453,plain,
% 19.68/2.99      ( sK1(sK3,k2_tarski(sK4,sK4),X0) = sK4
% 19.68/2.99      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 19.68/2.99      | r2_hidden(X0,a_2_0_orders_2(sK3,k2_tarski(sK4,sK4))) = iProver_top
% 19.68/2.99      | v2_struct_0(sK3) = iProver_top
% 19.68/2.99      | v3_orders_2(sK3) != iProver_top
% 19.68/2.99      | v4_orders_2(sK3) != iProver_top
% 19.68/2.99      | v5_orders_2(sK3) != iProver_top
% 19.68/2.99      | l1_orders_2(sK3) != iProver_top ),
% 19.68/2.99      inference(superposition,[status(thm)],[c_24442,c_4236]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_24496,plain,
% 19.68/2.99      ( sK1(sK3,k2_tarski(sK4,sK4),X0) = sK4
% 19.68/2.99      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 19.68/2.99      | r2_hidden(X0,k1_orders_2(sK3,k2_tarski(sK4,sK4))) = iProver_top
% 19.68/2.99      | v2_struct_0(sK3) = iProver_top
% 19.68/2.99      | v3_orders_2(sK3) != iProver_top
% 19.68/2.99      | v4_orders_2(sK3) != iProver_top
% 19.68/2.99      | v5_orders_2(sK3) != iProver_top
% 19.68/2.99      | l1_orders_2(sK3) != iProver_top ),
% 19.68/2.99      inference(light_normalisation,[status(thm)],[c_24453,c_22837]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_28417,plain,
% 19.68/2.99      ( r2_hidden(X0,k1_orders_2(sK3,k2_tarski(sK4,sK4))) = iProver_top
% 19.68/2.99      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 19.68/2.99      | sK1(sK3,k2_tarski(sK4,sK4),X0) = sK4 ),
% 19.68/2.99      inference(global_propositional_subsumption,
% 19.68/2.99                [status(thm)],
% 19.68/2.99                [c_24496,c_26,c_27,c_28,c_29,c_30]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_28418,plain,
% 19.68/2.99      ( sK1(sK3,k2_tarski(sK4,sK4),X0) = sK4
% 19.68/2.99      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 19.68/2.99      | r2_hidden(X0,k1_orders_2(sK3,k2_tarski(sK4,sK4))) = iProver_top ),
% 19.68/2.99      inference(renaming,[status(thm)],[c_28417]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_28427,plain,
% 19.68/2.99      ( sK1(sK3,k2_tarski(sK4,sK4),sK5) = sK4
% 19.68/2.99      | r2_orders_2(sK3,sK4,sK5) != iProver_top
% 19.68/2.99      | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top ),
% 19.68/2.99      inference(superposition,[status(thm)],[c_28418,c_22840]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_28451,plain,
% 19.68/2.99      ( r2_orders_2(sK3,sK4,sK5) != iProver_top
% 19.68/2.99      | sK1(sK3,k2_tarski(sK4,sK4),sK5) = sK4 ),
% 19.68/2.99      inference(global_propositional_subsumption,
% 19.68/2.99                [status(thm)],
% 19.68/2.99                [c_28427,c_32]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_28452,plain,
% 19.68/2.99      ( sK1(sK3,k2_tarski(sK4,sK4),sK5) = sK4
% 19.68/2.99      | r2_orders_2(sK3,sK4,sK5) != iProver_top ),
% 19.68/2.99      inference(renaming,[status(thm)],[c_28451]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_28457,plain,
% 19.68/2.99      ( sK2(sK5,sK3,k2_tarski(sK4,sK4)) = sK5
% 19.68/2.99      | sK1(sK3,k2_tarski(sK4,sK4),sK5) = sK4 ),
% 19.68/2.99      inference(superposition,[status(thm)],[c_22835,c_28452]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_11,plain,
% 19.68/2.99      ( r2_orders_2(X0,X1,sK2(X2,X0,X3))
% 19.68/2.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 19.68/2.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 19.68/2.99      | ~ r2_hidden(X1,X3)
% 19.68/2.99      | ~ r2_hidden(X2,a_2_0_orders_2(X0,X3))
% 19.68/2.99      | v2_struct_0(X0)
% 19.68/2.99      | ~ v3_orders_2(X0)
% 19.68/2.99      | ~ v4_orders_2(X0)
% 19.68/2.99      | ~ v5_orders_2(X0)
% 19.68/2.99      | ~ l1_orders_2(X0) ),
% 19.68/2.99      inference(cnf_transformation,[],[f52]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_959,plain,
% 19.68/2.99      ( r2_orders_2(X0,X1,sK2(X2,X0,X3)) = iProver_top
% 19.68/2.99      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 19.68/2.99      | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 19.68/2.99      | r2_hidden(X1,X3) != iProver_top
% 19.68/2.99      | r2_hidden(X2,a_2_0_orders_2(X0,X3)) != iProver_top
% 19.68/2.99      | v2_struct_0(X0) = iProver_top
% 19.68/2.99      | v3_orders_2(X0) != iProver_top
% 19.68/2.99      | v4_orders_2(X0) != iProver_top
% 19.68/2.99      | v5_orders_2(X0) != iProver_top
% 19.68/2.99      | l1_orders_2(X0) != iProver_top ),
% 19.68/2.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_28588,plain,
% 19.68/2.99      ( sK1(sK3,k2_tarski(sK4,sK4),sK5) = sK4
% 19.68/2.99      | r2_orders_2(sK3,X0,sK5) = iProver_top
% 19.68/2.99      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 19.68/2.99      | m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.68/2.99      | r2_hidden(X0,k2_tarski(sK4,sK4)) != iProver_top
% 19.68/2.99      | r2_hidden(sK5,a_2_0_orders_2(sK3,k2_tarski(sK4,sK4))) != iProver_top
% 19.68/2.99      | v2_struct_0(sK3) = iProver_top
% 19.68/2.99      | v3_orders_2(sK3) != iProver_top
% 19.68/2.99      | v4_orders_2(sK3) != iProver_top
% 19.68/2.99      | v5_orders_2(sK3) != iProver_top
% 19.68/2.99      | l1_orders_2(sK3) != iProver_top ),
% 19.68/2.99      inference(superposition,[status(thm)],[c_28457,c_959]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_28627,plain,
% 19.68/2.99      ( sK1(sK3,k2_tarski(sK4,sK4),sK5) = sK4
% 19.68/2.99      | r2_orders_2(sK3,X0,sK5) = iProver_top
% 19.68/2.99      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 19.68/2.99      | m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.68/2.99      | r2_hidden(X0,k2_tarski(sK4,sK4)) != iProver_top
% 19.68/2.99      | r2_hidden(sK5,k1_orders_2(sK3,k2_tarski(sK4,sK4))) != iProver_top
% 19.68/2.99      | v2_struct_0(sK3) = iProver_top
% 19.68/2.99      | v3_orders_2(sK3) != iProver_top
% 19.68/2.99      | v4_orders_2(sK3) != iProver_top
% 19.68/2.99      | v5_orders_2(sK3) != iProver_top
% 19.68/2.99      | l1_orders_2(sK3) != iProver_top ),
% 19.68/2.99      inference(light_normalisation,[status(thm)],[c_28588,c_22837]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_22839,plain,
% 19.68/2.99      ( r2_orders_2(sK3,sK4,sK5) = iProver_top
% 19.68/2.99      | r2_hidden(sK5,k1_orders_2(sK3,k2_tarski(sK4,sK4))) = iProver_top ),
% 19.68/2.99      inference(demodulation,[status(thm)],[c_22797,c_952]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_57517,plain,
% 19.68/2.99      ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 19.68/2.99      | r2_orders_2(sK3,X0,sK5) = iProver_top
% 19.68/2.99      | sK1(sK3,k2_tarski(sK4,sK4),sK5) = sK4
% 19.68/2.99      | r2_hidden(X0,k2_tarski(sK4,sK4)) != iProver_top ),
% 19.68/2.99      inference(global_propositional_subsumption,
% 19.68/2.99                [status(thm)],
% 19.68/2.99                [c_28627,c_26,c_27,c_28,c_29,c_30,c_31,c_22839,c_22960,
% 19.68/2.99                 c_28452]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_57518,plain,
% 19.68/2.99      ( sK1(sK3,k2_tarski(sK4,sK4),sK5) = sK4
% 19.68/2.99      | r2_orders_2(sK3,X0,sK5) = iProver_top
% 19.68/2.99      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 19.68/2.99      | r2_hidden(X0,k2_tarski(sK4,sK4)) != iProver_top ),
% 19.68/2.99      inference(renaming,[status(thm)],[c_57517]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_57528,plain,
% 19.68/2.99      ( sK1(sK3,k2_tarski(sK4,sK4),sK5) = sK4
% 19.68/2.99      | r2_orders_2(sK3,sK4,sK5) = iProver_top
% 19.68/2.99      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 19.68/2.99      inference(superposition,[status(thm)],[c_967,c_57518]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_28453,plain,
% 19.68/2.99      ( ~ r2_orders_2(sK3,sK4,sK5)
% 19.68/2.99      | sK1(sK3,k2_tarski(sK4,sK4),sK5) = sK4 ),
% 19.68/2.99      inference(predicate_to_equality_rev,[status(thm)],[c_28452]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_57576,plain,
% 19.68/2.99      ( r2_orders_2(sK3,sK4,sK5)
% 19.68/2.99      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 19.68/2.99      | sK1(sK3,k2_tarski(sK4,sK4),sK5) = sK4 ),
% 19.68/2.99      inference(predicate_to_equality_rev,[status(thm)],[c_57528]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_58366,plain,
% 19.68/2.99      ( sK1(sK3,k2_tarski(sK4,sK4),sK5) = sK4 ),
% 19.68/2.99      inference(global_propositional_subsumption,
% 19.68/2.99                [status(thm)],
% 19.68/2.99                [c_57528,c_20,c_28453,c_57576]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_8,plain,
% 19.68/2.99      ( ~ r2_orders_2(X0,sK1(X0,X1,X2),X2)
% 19.68/2.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 19.68/2.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 19.68/2.99      | r2_hidden(X2,a_2_0_orders_2(X0,X1))
% 19.68/2.99      | v2_struct_0(X0)
% 19.68/2.99      | ~ v3_orders_2(X0)
% 19.68/2.99      | ~ v4_orders_2(X0)
% 19.68/2.99      | ~ v5_orders_2(X0)
% 19.68/2.99      | ~ l1_orders_2(X0) ),
% 19.68/2.99      inference(cnf_transformation,[],[f74]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_962,plain,
% 19.68/2.99      ( r2_orders_2(X0,sK1(X0,X1,X2),X2) != iProver_top
% 19.68/2.99      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 19.68/2.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 19.68/2.99      | r2_hidden(X2,a_2_0_orders_2(X0,X1)) = iProver_top
% 19.68/2.99      | v2_struct_0(X0) = iProver_top
% 19.68/2.99      | v3_orders_2(X0) != iProver_top
% 19.68/2.99      | v4_orders_2(X0) != iProver_top
% 19.68/2.99      | v5_orders_2(X0) != iProver_top
% 19.68/2.99      | l1_orders_2(X0) != iProver_top ),
% 19.68/2.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_58440,plain,
% 19.68/2.99      ( r2_orders_2(sK3,sK4,sK5) != iProver_top
% 19.68/2.99      | m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.68/2.99      | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
% 19.68/2.99      | r2_hidden(sK5,a_2_0_orders_2(sK3,k2_tarski(sK4,sK4))) = iProver_top
% 19.68/2.99      | v2_struct_0(sK3) = iProver_top
% 19.68/2.99      | v3_orders_2(sK3) != iProver_top
% 19.68/2.99      | v4_orders_2(sK3) != iProver_top
% 19.68/2.99      | v5_orders_2(sK3) != iProver_top
% 19.68/2.99      | l1_orders_2(sK3) != iProver_top ),
% 19.68/2.99      inference(superposition,[status(thm)],[c_58366,c_962]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_58462,plain,
% 19.68/2.99      ( r2_orders_2(sK3,sK4,sK5) != iProver_top
% 19.68/2.99      | m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.68/2.99      | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
% 19.68/2.99      | r2_hidden(sK5,k1_orders_2(sK3,k2_tarski(sK4,sK4))) = iProver_top
% 19.68/2.99      | v2_struct_0(sK3) = iProver_top
% 19.68/2.99      | v3_orders_2(sK3) != iProver_top
% 19.68/2.99      | v4_orders_2(sK3) != iProver_top
% 19.68/2.99      | v5_orders_2(sK3) != iProver_top
% 19.68/2.99      | l1_orders_2(sK3) != iProver_top ),
% 19.68/2.99      inference(light_normalisation,[status(thm)],[c_58440,c_22837]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_58473,plain,
% 19.68/2.99      ( sK2(sK5,sK3,k2_tarski(sK4,sK4)) = sK5 ),
% 19.68/2.99      inference(global_propositional_subsumption,
% 19.68/2.99                [status(thm)],
% 19.68/2.99                [c_48726,c_26,c_27,c_28,c_29,c_30,c_31,c_32,c_22835,
% 19.68/2.99                 c_22840,c_22960,c_58462]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_58486,plain,
% 19.68/2.99      ( r2_orders_2(sK3,X0,sK5) = iProver_top
% 19.68/2.99      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 19.68/2.99      | m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.68/2.99      | r2_hidden(X0,k2_tarski(sK4,sK4)) != iProver_top
% 19.68/2.99      | r2_hidden(sK5,a_2_0_orders_2(sK3,k2_tarski(sK4,sK4))) != iProver_top
% 19.68/2.99      | v2_struct_0(sK3) = iProver_top
% 19.68/2.99      | v3_orders_2(sK3) != iProver_top
% 19.68/2.99      | v4_orders_2(sK3) != iProver_top
% 19.68/2.99      | v5_orders_2(sK3) != iProver_top
% 19.68/2.99      | l1_orders_2(sK3) != iProver_top ),
% 19.68/2.99      inference(superposition,[status(thm)],[c_58473,c_959]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_58522,plain,
% 19.68/2.99      ( r2_orders_2(sK3,X0,sK5) = iProver_top
% 19.68/2.99      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 19.68/2.99      | m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.68/2.99      | r2_hidden(X0,k2_tarski(sK4,sK4)) != iProver_top
% 19.68/2.99      | r2_hidden(sK5,k1_orders_2(sK3,k2_tarski(sK4,sK4))) != iProver_top
% 19.68/2.99      | v2_struct_0(sK3) = iProver_top
% 19.68/2.99      | v3_orders_2(sK3) != iProver_top
% 19.68/2.99      | v4_orders_2(sK3) != iProver_top
% 19.68/2.99      | v5_orders_2(sK3) != iProver_top
% 19.68/2.99      | l1_orders_2(sK3) != iProver_top ),
% 19.68/2.99      inference(light_normalisation,[status(thm)],[c_58486,c_22837]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_59147,plain,
% 19.68/2.99      ( r2_hidden(sK5,k1_orders_2(sK3,k2_tarski(sK4,sK4))) = iProver_top ),
% 19.68/2.99      inference(global_propositional_subsumption,
% 19.68/2.99                [status(thm)],
% 19.68/2.99                [c_58462,c_26,c_27,c_28,c_29,c_30,c_31,c_32,c_22839,
% 19.68/2.99                 c_22840,c_22960]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_59269,plain,
% 19.68/2.99      ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 19.68/2.99      | r2_orders_2(sK3,X0,sK5) = iProver_top
% 19.68/2.99      | r2_hidden(X0,k2_tarski(sK4,sK4)) != iProver_top ),
% 19.68/2.99      inference(global_propositional_subsumption,
% 19.68/2.99                [status(thm)],
% 19.68/2.99                [c_58522,c_26,c_27,c_28,c_29,c_30,c_31,c_32,c_22839,
% 19.68/2.99                 c_22840,c_22960,c_58462]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_59270,plain,
% 19.68/2.99      ( r2_orders_2(sK3,X0,sK5) = iProver_top
% 19.68/2.99      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 19.68/2.99      | r2_hidden(X0,k2_tarski(sK4,sK4)) != iProver_top ),
% 19.68/2.99      inference(renaming,[status(thm)],[c_59269]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_59279,plain,
% 19.68/2.99      ( r2_orders_2(sK3,sK4,sK5) = iProver_top
% 19.68/2.99      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 19.68/2.99      inference(superposition,[status(thm)],[c_967,c_59270]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(contradiction,plain,
% 19.68/2.99      ( $false ),
% 19.68/2.99      inference(minisat,[status(thm)],[c_59279,c_59147,c_22840,c_31]) ).
% 19.68/2.99  
% 19.68/2.99  
% 19.68/2.99  % SZS output end CNFRefutation for theBenchmark.p
% 19.68/2.99  
% 19.68/2.99  ------                               Statistics
% 19.68/2.99  
% 19.68/2.99  ------ Selected
% 19.68/2.99  
% 19.68/2.99  total_time:                             2.178
% 19.68/2.99  
%------------------------------------------------------------------------------
