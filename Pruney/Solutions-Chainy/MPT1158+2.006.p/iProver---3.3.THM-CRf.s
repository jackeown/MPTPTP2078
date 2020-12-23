%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:12:30 EST 2020

% Result     : Theorem 11.32s
% Output     : CNFRefutation 11.32s
% Verified   : 
% Statistics : Number of formulae       :  166 (7477 expanded)
%              Number of clauses        :   92 (1834 expanded)
%              Number of leaves         :   17 (1941 expanded)
%              Depth                    :   34
%              Number of atoms          :  824 (55026 expanded)
%              Number of equality atoms :  346 (4106 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   22 (   4 average)
%              Maximal term depth       :    5 (   1 average)

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

fof(f29,plain,(
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

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f32,plain,(
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

fof(f33,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f76,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f47])).

fof(f77,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f76])).

fof(f11,conjecture,(
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
              <=> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
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
                <=> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <~> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <~> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))
                | ~ r2_orders_2(X0,X1,X2) )
              & ( r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))
                | r2_orders_2(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))
                | ~ r2_orders_2(X0,X1,X2) )
              & ( r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))
                | r2_orders_2(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))
            | ~ r2_orders_2(X0,X1,X2) )
          & ( r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))
            | r2_orders_2(X0,X1,X2) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),sK5)))
          | ~ r2_orders_2(X0,X1,sK5) )
        & ( r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),sK5)))
          | r2_orders_2(X0,X1,sK5) )
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))
                | ~ r2_orders_2(X0,X1,X2) )
              & ( r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))
                | r2_orders_2(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ( ~ r2_hidden(sK4,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))
              | ~ r2_orders_2(X0,sK4,X2) )
            & ( r2_hidden(sK4,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))
              | r2_orders_2(X0,sK4,X2) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))
                  | ~ r2_orders_2(X0,X1,X2) )
                & ( r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))
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
              ( ( ~ r2_hidden(X1,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X2)))
                | ~ r2_orders_2(sK3,X1,X2) )
              & ( r2_hidden(X1,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X2)))
                | r2_orders_2(sK3,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(sK3)) )
          & m1_subset_1(X1,u1_struct_0(sK3)) )
      & l1_orders_2(sK3)
      & v5_orders_2(sK3)
      & v4_orders_2(sK3)
      & v3_orders_2(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ( ~ r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)))
      | ~ r2_orders_2(sK3,sK4,sK5) )
    & ( r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)))
      | r2_orders_2(sK3,sK4,sK5) )
    & m1_subset_1(sK5,u1_struct_0(sK3))
    & m1_subset_1(sK4,u1_struct_0(sK3))
    & l1_orders_2(sK3)
    & v5_orders_2(sK3)
    & v4_orders_2(sK3)
    & v3_orders_2(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f40,f43,f42,f41])).

fof(f71,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f44])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k2_tarski(X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f64,f51])).

fof(f65,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f69,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f57,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f72,plain,
    ( r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)))
    | r2_orders_2(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f44])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f52,f51])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f66,plain,(
    v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f67,plain,(
    v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f68,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & l1_orders_2(X1)
        & v5_orders_2(X1)
        & v4_orders_2(X1)
        & v3_orders_2(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r2_orders_2(X1,X3,X4) ) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X3,X4)
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
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X3,X4)
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
    inference(flattening,[],[f23])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
          | ! [X3] :
              ( ? [X4] :
                  ( ~ r2_orders_2(X1,X3,X4)
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( ! [X4] :
                  ( r2_orders_2(X1,X3,X4)
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
          | ! [X3] :
              ( ? [X4] :
                  ( ~ r2_orders_2(X1,X3,X4)
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X5] :
              ( ! [X6] :
                  ( r2_orders_2(X1,X5,X6)
                  | ~ r2_hidden(X6,X2)
                  | ~ m1_subset_1(X6,u1_struct_0(X1)) )
              & X0 = X5
              & m1_subset_1(X5,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f34])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_orders_2(X1,X5,X6)
              | ~ r2_hidden(X6,X2)
              | ~ m1_subset_1(X6,u1_struct_0(X1)) )
          & X0 = X5
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ! [X6] :
            ( r2_orders_2(X1,sK2(X0,X1,X2),X6)
            | ~ r2_hidden(X6,X2)
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        & sK2(X0,X1,X2) = X0
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ~ r2_orders_2(X1,X3,X4)
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_orders_2(X1,X3,sK1(X1,X2,X3))
        & r2_hidden(sK1(X1,X2,X3),X2)
        & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
          | ! [X3] :
              ( ( ~ r2_orders_2(X1,X3,sK1(X1,X2,X3))
                & r2_hidden(sK1(X1,X2,X3),X2)
                & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( ! [X6] :
                ( r2_orders_2(X1,sK2(X0,X1,X2),X6)
                | ~ r2_hidden(X6,X2)
                | ~ m1_subset_1(X6,u1_struct_0(X1)) )
            & sK2(X0,X1,X2) = X0
            & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f35,f37,f36])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( sK2(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | r2_hidden(sK1(X1,X2,X3),X2)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f82,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,a_2_1_orders_2(X1,X2))
      | r2_hidden(sK1(X1,X2,X3),X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f62])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f80,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_tarski(X0,X1)) ) ),
    inference(equality_resolution,[],[f45])).

fof(f73,plain,
    ( ~ r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)))
    | ~ r2_orders_2(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f44])).

fof(f70,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f44])).

fof(f60,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_orders_2(X1,sK2(X0,X1,X2),X6)
      | ~ r2_hidden(X6,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | ~ r2_orders_2(X1,X3,sK1(X1,X2,X3))
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f81,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,a_2_1_orders_2(X1,X2))
      | ~ r2_orders_2(X1,X3,sK1(X1,X2,X3))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f63])).

cnf(c_3,plain,
    ( r2_hidden(X0,k2_tarski(X1,X0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_28954,plain,
    ( r2_hidden(X0,k2_tarski(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_28939,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_28942,plain,
    ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_30453,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK5) = k2_tarski(sK5,sK5)
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_28939,c_28942])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_28,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_23,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_32,plain,
    ( l1_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_11,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_58,plain,
    ( l1_orders_2(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_60,plain,
    ( l1_orders_2(sK3) != iProver_top
    | l1_struct_0(sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_58])).

cnf(c_9,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_64,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_66,plain,
    ( v2_struct_0(sK3) = iProver_top
    | l1_struct_0(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_64])).

cnf(c_30771,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK5) = k2_tarski(sK5,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_30453,c_28,c_32,c_60,c_66])).

cnf(c_20,negated_conjecture,
    ( r2_orders_2(sK3,sK4,sK5)
    | r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_28940,plain,
    ( r2_orders_2(sK3,sK4,sK5) = iProver_top
    | r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_30775,plain,
    ( r2_orders_2(sK3,sK4,sK5) = iProver_top
    | r2_hidden(sK4,k2_orders_2(sK3,k2_tarski(sK5,sK5))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_30771,c_28940])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_28950,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_30428,plain,
    ( r2_hidden(sK5,u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_28939,c_28950])).

cnf(c_34,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_6953,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | r2_hidden(X0,u1_struct_0(X1))
    | v1_xboole_0(u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_7050,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | r2_hidden(sK5,u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_6953])).

cnf(c_7051,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK5,u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7050])).

cnf(c_30617,plain,
    ( r2_hidden(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_30428,c_28,c_32,c_34,c_60,c_66,c_7051])).

cnf(c_6,plain,
    ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_28951,plain,
    ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1)) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1)
    | a_2_1_orders_2(X1,X0) = k2_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_28947,plain,
    ( a_2_1_orders_2(X0,X1) = k2_orders_2(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v3_orders_2(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_31747,plain,
    ( a_2_1_orders_2(X0,k2_tarski(X1,X1)) = k2_orders_2(X0,k2_tarski(X1,X1))
    | r2_hidden(X1,u1_struct_0(X0)) != iProver_top
    | v3_orders_2(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_28951,c_28947])).

cnf(c_32894,plain,
    ( a_2_1_orders_2(sK3,k2_tarski(sK5,sK5)) = k2_orders_2(sK3,k2_tarski(sK5,sK5))
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_30617,c_31747])).

cnf(c_26,negated_conjecture,
    ( v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_29,plain,
    ( v3_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,negated_conjecture,
    ( v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_30,plain,
    ( v4_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_31,plain,
    ( v5_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_33459,plain,
    ( a_2_1_orders_2(sK3,k2_tarski(sK5,sK5)) = k2_orders_2(sK3,k2_tarski(sK5,sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_32894,c_28,c_29,c_30,c_31,c_32])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,a_2_1_orders_2(X1,X0))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1)
    | sK2(X2,X1,X0) = X2 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_28943,plain,
    ( sK2(X0,X1,X2) = X0
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r2_hidden(X0,a_2_1_orders_2(X1,X2)) != iProver_top
    | v3_orders_2(X1) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v5_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top
    | v2_struct_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_30278,plain,
    ( sK2(X0,X1,k2_tarski(X2,X2)) = X0
    | r2_hidden(X0,a_2_1_orders_2(X1,k2_tarski(X2,X2))) != iProver_top
    | r2_hidden(X2,u1_struct_0(X1)) != iProver_top
    | v3_orders_2(X1) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v5_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top
    | v2_struct_0(X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_28951,c_28943])).

cnf(c_33462,plain,
    ( sK2(X0,sK3,k2_tarski(sK5,sK5)) = X0
    | r2_hidden(X0,k2_orders_2(sK3,k2_tarski(sK5,sK5))) != iProver_top
    | r2_hidden(sK5,u1_struct_0(sK3)) != iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_33459,c_30278])).

cnf(c_33686,plain,
    ( sK2(X0,sK3,k2_tarski(sK5,sK5)) = X0
    | r2_hidden(X0,k2_orders_2(sK3,k2_tarski(sK5,sK5))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_33462,c_28,c_29,c_30,c_31,c_32,c_34,c_60,c_66,c_7051])).

cnf(c_33695,plain,
    ( sK2(sK4,sK3,k2_tarski(sK5,sK5)) = sK4
    | r2_orders_2(sK3,sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_30775,c_33686])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,a_2_1_orders_2(X1,X2))
    | r2_hidden(sK1(X1,X2,X0),X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_28944,plain,
    ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r2_hidden(X0,a_2_1_orders_2(X1,X2)) = iProver_top
    | r2_hidden(sK1(X1,X2,X0),X2) = iProver_top
    | v3_orders_2(X1) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v5_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top
    | v2_struct_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k2_tarski(X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_28952,plain,
    ( X0 = X1
    | X0 = X2
    | r2_hidden(X0,k2_tarski(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_31435,plain,
    ( sK1(X0,k2_tarski(X1,X2),X3) = X1
    | sK1(X0,k2_tarski(X1,X2),X3) = X2
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r2_hidden(X3,a_2_1_orders_2(X0,k2_tarski(X1,X2))) = iProver_top
    | v3_orders_2(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_28944,c_28952])).

cnf(c_34083,plain,
    ( sK1(X0,k2_tarski(X1,X1),X2) = X1
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | r2_hidden(X2,a_2_1_orders_2(X0,k2_tarski(X1,X1))) = iProver_top
    | r2_hidden(X1,u1_struct_0(X0)) != iProver_top
    | v3_orders_2(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_28951,c_31435])).

cnf(c_34301,plain,
    ( sK1(sK3,k2_tarski(sK5,sK5),X0) = sK5
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,k2_orders_2(sK3,k2_tarski(sK5,sK5))) = iProver_top
    | r2_hidden(sK5,u1_struct_0(sK3)) != iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_33459,c_34083])).

cnf(c_35207,plain,
    ( sK1(sK3,k2_tarski(sK5,sK5),X0) = sK5
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,k2_orders_2(sK3,k2_tarski(sK5,sK5))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_34301,c_28,c_29,c_30,c_31,c_32,c_34,c_60,c_66,c_7051])).

cnf(c_19,negated_conjecture,
    ( ~ r2_orders_2(sK3,sK4,sK5)
    | ~ r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_28941,plain,
    ( r2_orders_2(sK3,sK4,sK5) != iProver_top
    | r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_30776,plain,
    ( r2_orders_2(sK3,sK4,sK5) != iProver_top
    | r2_hidden(sK4,k2_orders_2(sK3,k2_tarski(sK5,sK5))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_30771,c_28941])).

cnf(c_35218,plain,
    ( sK1(sK3,k2_tarski(sK5,sK5),sK4) = sK5
    | r2_orders_2(sK3,sK4,sK5) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_35207,c_30776])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_33,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_35257,plain,
    ( r2_orders_2(sK3,sK4,sK5) != iProver_top
    | sK1(sK3,k2_tarski(sK5,sK5),sK4) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_35218,c_33])).

cnf(c_35258,plain,
    ( sK1(sK3,k2_tarski(sK5,sK5),sK4) = sK5
    | r2_orders_2(sK3,sK4,sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_35257])).

cnf(c_35263,plain,
    ( sK2(sK4,sK3,k2_tarski(sK5,sK5)) = sK4
    | sK1(sK3,k2_tarski(sK5,sK5),sK4) = sK5 ),
    inference(superposition,[status(thm)],[c_33695,c_35258])).

cnf(c_15,plain,
    ( r2_orders_2(X0,sK2(X1,X0,X2),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,a_2_1_orders_2(X0,X2))
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_4818,plain,
    ( r2_orders_2(X0,sK2(X1,X0,X2),X3) = iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r2_hidden(X3,X2) != iProver_top
    | r2_hidden(X1,a_2_1_orders_2(X0,X2)) != iProver_top
    | v3_orders_2(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_8,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_4821,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4906,plain,
    ( r2_orders_2(X0,sK2(X1,X0,X2),X3) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r2_hidden(X3,X2) != iProver_top
    | r2_hidden(X1,a_2_1_orders_2(X0,X2)) != iProver_top
    | v3_orders_2(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4818,c_4821])).

cnf(c_4917,plain,
    ( r2_orders_2(X0,sK2(X1,X0,X2),X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,a_2_1_orders_2(X0,X2))
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4906])).

cnf(c_28839,plain,
    ( r2_orders_2(X0,sK2(X1,X0,X2),X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,a_2_1_orders_2(X0,X2))
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15,c_4917])).

cnf(c_28929,plain,
    ( r2_orders_2(X0,sK2(X1,X0,X2),X3) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r2_hidden(X3,X2) != iProver_top
    | r2_hidden(X1,a_2_1_orders_2(X0,X2)) != iProver_top
    | v3_orders_2(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28839])).

cnf(c_35551,plain,
    ( sK1(sK3,k2_tarski(sK5,sK5),sK4) = sK5
    | r2_orders_2(sK3,sK4,X0) = iProver_top
    | m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,k2_tarski(sK5,sK5)) != iProver_top
    | r2_hidden(sK4,a_2_1_orders_2(sK3,k2_tarski(sK5,sK5))) != iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_35263,c_28929])).

cnf(c_35552,plain,
    ( sK1(sK3,k2_tarski(sK5,sK5),sK4) = sK5
    | r2_orders_2(sK3,sK4,X0) = iProver_top
    | m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,k2_tarski(sK5,sK5)) != iProver_top
    | r2_hidden(sK4,k2_orders_2(sK3,k2_tarski(sK5,sK5))) != iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_35551,c_33459])).

cnf(c_7069,plain,
    ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(sK5,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_7075,plain,
    ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | r2_hidden(sK5,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7069])).

cnf(c_36016,plain,
    ( r2_orders_2(sK3,sK4,X0) = iProver_top
    | sK1(sK3,k2_tarski(sK5,sK5),sK4) = sK5
    | r2_hidden(X0,k2_tarski(sK5,sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_35552,c_28,c_29,c_30,c_31,c_32,c_34,c_60,c_66,c_7051,c_7075,c_30775,c_35258])).

cnf(c_36017,plain,
    ( sK1(sK3,k2_tarski(sK5,sK5),sK4) = sK5
    | r2_orders_2(sK3,sK4,X0) = iProver_top
    | r2_hidden(X0,k2_tarski(sK5,sK5)) != iProver_top ),
    inference(renaming,[status(thm)],[c_36016])).

cnf(c_36025,plain,
    ( sK1(sK3,k2_tarski(sK5,sK5),sK4) = sK5
    | r2_orders_2(sK3,sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_28954,c_36017])).

cnf(c_36057,plain,
    ( sK1(sK3,k2_tarski(sK5,sK5),sK4) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_36025,c_35258])).

cnf(c_12,plain,
    ( ~ r2_orders_2(X0,X1,sK1(X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | r2_hidden(X1,a_2_1_orders_2(X0,X2))
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_28945,plain,
    ( r2_orders_2(X0,X1,sK1(X0,X2,X1)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r2_hidden(X1,a_2_1_orders_2(X0,X2)) = iProver_top
    | v3_orders_2(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_36060,plain,
    ( r2_orders_2(sK3,sK4,sK5) != iProver_top
    | m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK4,a_2_1_orders_2(sK3,k2_tarski(sK5,sK5))) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_36057,c_28945])).

cnf(c_36104,plain,
    ( r2_orders_2(sK3,sK4,sK5) != iProver_top
    | m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK4,k2_orders_2(sK3,k2_tarski(sK5,sK5))) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_36060,c_33459])).

cnf(c_36367,plain,
    ( r2_hidden(sK4,k2_orders_2(sK3,k2_tarski(sK5,sK5))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_36104,c_28,c_29,c_30,c_31,c_32,c_33,c_34,c_60,c_66,c_7051,c_7075,c_30775])).

cnf(c_36375,plain,
    ( sK2(sK4,sK3,k2_tarski(sK5,sK5)) = sK4 ),
    inference(superposition,[status(thm)],[c_36367,c_33686])).

cnf(c_37840,plain,
    ( r2_orders_2(sK3,sK4,X0) = iProver_top
    | m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,k2_tarski(sK5,sK5)) != iProver_top
    | r2_hidden(sK4,a_2_1_orders_2(sK3,k2_tarski(sK5,sK5))) != iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_36375,c_28929])).

cnf(c_37876,plain,
    ( r2_orders_2(sK3,sK4,X0) = iProver_top
    | m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,k2_tarski(sK5,sK5)) != iProver_top
    | r2_hidden(sK4,k2_orders_2(sK3,k2_tarski(sK5,sK5))) != iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_37840,c_33459])).

cnf(c_37893,plain,
    ( r2_orders_2(sK3,sK4,X0) = iProver_top
    | r2_hidden(X0,k2_tarski(sK5,sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_37876,c_28,c_29,c_30,c_31,c_32,c_33,c_34,c_60,c_66,c_7051,c_7075,c_30775,c_36104])).

cnf(c_37901,plain,
    ( r2_orders_2(sK3,sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_28954,c_37893])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_37901,c_36367,c_30776])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:53:34 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.32/1.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.32/1.99  
% 11.32/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.32/1.99  
% 11.32/1.99  ------  iProver source info
% 11.32/1.99  
% 11.32/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.32/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.32/1.99  git: non_committed_changes: false
% 11.32/1.99  git: last_make_outside_of_git: false
% 11.32/1.99  
% 11.32/1.99  ------ 
% 11.32/1.99  ------ Parsing...
% 11.32/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.32/1.99  
% 11.32/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 11.32/1.99  
% 11.32/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.32/1.99  
% 11.32/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.32/1.99  ------ Proving...
% 11.32/1.99  ------ Problem Properties 
% 11.32/1.99  
% 11.32/1.99  
% 11.32/1.99  clauses                                 28
% 11.32/1.99  conjectures                             9
% 11.32/1.99  EPR                                     7
% 11.32/1.99  Horn                                    16
% 11.32/1.99  unary                                   9
% 11.32/1.99  binary                                  4
% 11.32/1.99  lits                                    102
% 11.32/1.99  lits eq                                 12
% 11.32/1.99  fd_pure                                 0
% 11.32/1.99  fd_pseudo                               0
% 11.32/1.99  fd_cond                                 0
% 11.32/1.99  fd_pseudo_cond                          3
% 11.32/1.99  AC symbols                              0
% 11.32/1.99  
% 11.32/1.99  ------ Input Options Time Limit: Unbounded
% 11.32/1.99  
% 11.32/1.99  
% 11.32/1.99  
% 11.32/1.99  
% 11.32/1.99  ------ Preprocessing...
% 11.32/1.99  
% 11.32/1.99  ------ Preprocessing... sf_s  rm: 10 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 11.32/1.99  Current options:
% 11.32/1.99  ------ 
% 11.32/1.99  
% 11.32/1.99  
% 11.32/1.99  
% 11.32/1.99  
% 11.32/1.99  ------ Proving...
% 11.32/1.99  
% 11.32/1.99  
% 11.32/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.32/1.99  
% 11.32/1.99  ------ Proving...
% 11.32/1.99  
% 11.32/1.99  
% 11.32/1.99  ------ Preprocessing... sf_s  rm: 10 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.32/1.99  
% 11.32/1.99  ------ Proving...
% 11.32/1.99  
% 11.32/1.99  
% 11.32/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.32/1.99  
% 11.32/1.99  ------ Proving...
% 11.32/1.99  
% 11.32/1.99  
% 11.32/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.32/1.99  
% 11.32/1.99  ------ Proving...
% 11.32/1.99  
% 11.32/1.99  
% 11.32/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.32/1.99  
% 11.32/1.99  ------ Proving...
% 11.32/1.99  
% 11.32/1.99  
% 11.32/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.32/1.99  
% 11.32/1.99  ------ Proving...
% 11.32/1.99  
% 11.32/1.99  
% 11.32/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.32/1.99  
% 11.32/1.99  ------ Proving...
% 11.32/1.99  
% 11.32/1.99  
% 11.32/1.99  % SZS status Theorem for theBenchmark.p
% 11.32/1.99  
% 11.32/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.32/1.99  
% 11.32/1.99  fof(f1,axiom,(
% 11.32/1.99    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 11.32/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.32/1.99  
% 11.32/1.99  fof(f29,plain,(
% 11.32/1.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 11.32/1.99    inference(nnf_transformation,[],[f1])).
% 11.32/1.99  
% 11.32/1.99  fof(f30,plain,(
% 11.32/1.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 11.32/1.99    inference(flattening,[],[f29])).
% 11.32/1.99  
% 11.32/1.99  fof(f31,plain,(
% 11.32/1.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 11.32/1.99    inference(rectify,[],[f30])).
% 11.32/1.99  
% 11.32/1.99  fof(f32,plain,(
% 11.32/1.99    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2))))),
% 11.32/1.99    introduced(choice_axiom,[])).
% 11.32/1.99  
% 11.32/1.99  fof(f33,plain,(
% 11.32/1.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 11.32/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).
% 11.32/1.99  
% 11.32/1.99  fof(f47,plain,(
% 11.32/1.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 11.32/1.99    inference(cnf_transformation,[],[f33])).
% 11.32/1.99  
% 11.32/1.99  fof(f76,plain,(
% 11.32/1.99    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_tarski(X0,X4) != X2) )),
% 11.32/1.99    inference(equality_resolution,[],[f47])).
% 11.32/1.99  
% 11.32/1.99  fof(f77,plain,(
% 11.32/1.99    ( ! [X4,X0] : (r2_hidden(X4,k2_tarski(X0,X4))) )),
% 11.32/1.99    inference(equality_resolution,[],[f76])).
% 11.32/1.99  
% 11.32/1.99  fof(f11,conjecture,(
% 11.32/1.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))))))),
% 11.32/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.32/1.99  
% 11.32/1.99  fof(f12,negated_conjecture,(
% 11.32/1.99    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))))))),
% 11.32/1.99    inference(negated_conjecture,[],[f11])).
% 11.32/1.99  
% 11.32/1.99  fof(f27,plain,(
% 11.32/1.99    ? [X0] : (? [X1] : (? [X2] : ((r2_orders_2(X0,X1,X2) <~> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 11.32/1.99    inference(ennf_transformation,[],[f12])).
% 11.32/1.99  
% 11.32/1.99  fof(f28,plain,(
% 11.32/1.99    ? [X0] : (? [X1] : (? [X2] : ((r2_orders_2(X0,X1,X2) <~> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 11.32/1.99    inference(flattening,[],[f27])).
% 11.32/1.99  
% 11.32/1.99  fof(f39,plain,(
% 11.32/1.99    ? [X0] : (? [X1] : (? [X2] : (((~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~r2_orders_2(X0,X1,X2)) & (r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | r2_orders_2(X0,X1,X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 11.32/1.99    inference(nnf_transformation,[],[f28])).
% 11.32/1.99  
% 11.32/1.99  fof(f40,plain,(
% 11.32/1.99    ? [X0] : (? [X1] : (? [X2] : ((~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~r2_orders_2(X0,X1,X2)) & (r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | r2_orders_2(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 11.32/1.99    inference(flattening,[],[f39])).
% 11.32/1.99  
% 11.32/1.99  fof(f43,plain,(
% 11.32/1.99    ( ! [X0,X1] : (? [X2] : ((~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~r2_orders_2(X0,X1,X2)) & (r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | r2_orders_2(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) => ((~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),sK5))) | ~r2_orders_2(X0,X1,sK5)) & (r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),sK5))) | r2_orders_2(X0,X1,sK5)) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 11.32/1.99    introduced(choice_axiom,[])).
% 11.32/1.99  
% 11.32/1.99  fof(f42,plain,(
% 11.32/1.99    ( ! [X0] : (? [X1] : (? [X2] : ((~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~r2_orders_2(X0,X1,X2)) & (r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | r2_orders_2(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : ((~r2_hidden(sK4,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~r2_orders_2(X0,sK4,X2)) & (r2_hidden(sK4,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | r2_orders_2(X0,sK4,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 11.32/1.99    introduced(choice_axiom,[])).
% 11.32/1.99  
% 11.32/1.99  fof(f41,plain,(
% 11.32/1.99    ? [X0] : (? [X1] : (? [X2] : ((~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~r2_orders_2(X0,X1,X2)) & (r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | r2_orders_2(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r2_hidden(X1,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X2))) | ~r2_orders_2(sK3,X1,X2)) & (r2_hidden(X1,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X2))) | r2_orders_2(sK3,X1,X2)) & m1_subset_1(X2,u1_struct_0(sK3))) & m1_subset_1(X1,u1_struct_0(sK3))) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3))),
% 11.32/1.99    introduced(choice_axiom,[])).
% 11.32/1.99  
% 11.32/1.99  fof(f44,plain,(
% 11.32/1.99    (((~r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) | ~r2_orders_2(sK3,sK4,sK5)) & (r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) | r2_orders_2(sK3,sK4,sK5)) & m1_subset_1(sK5,u1_struct_0(sK3))) & m1_subset_1(sK4,u1_struct_0(sK3))) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3)),
% 11.32/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f40,f43,f42,f41])).
% 11.32/1.99  
% 11.32/1.99  fof(f71,plain,(
% 11.32/1.99    m1_subset_1(sK5,u1_struct_0(sK3))),
% 11.32/1.99    inference(cnf_transformation,[],[f44])).
% 11.32/1.99  
% 11.32/1.99  fof(f10,axiom,(
% 11.32/1.99    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 11.32/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.32/1.99  
% 11.32/1.99  fof(f25,plain,(
% 11.32/1.99    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 11.32/1.99    inference(ennf_transformation,[],[f10])).
% 11.32/1.99  
% 11.32/1.99  fof(f26,plain,(
% 11.32/1.99    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 11.32/1.99    inference(flattening,[],[f25])).
% 11.32/1.99  
% 11.32/1.99  fof(f64,plain,(
% 11.32/1.99    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 11.32/1.99    inference(cnf_transformation,[],[f26])).
% 11.32/1.99  
% 11.32/1.99  fof(f2,axiom,(
% 11.32/1.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 11.32/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.32/1.99  
% 11.32/1.99  fof(f51,plain,(
% 11.32/1.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 11.32/1.99    inference(cnf_transformation,[],[f2])).
% 11.32/1.99  
% 11.32/1.99  fof(f75,plain,(
% 11.32/1.99    ( ! [X0,X1] : (k2_tarski(X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 11.32/1.99    inference(definition_unfolding,[],[f64,f51])).
% 11.32/1.99  
% 11.32/1.99  fof(f65,plain,(
% 11.32/1.99    ~v2_struct_0(sK3)),
% 11.32/1.99    inference(cnf_transformation,[],[f44])).
% 11.32/1.99  
% 11.32/1.99  fof(f69,plain,(
% 11.32/1.99    l1_orders_2(sK3)),
% 11.32/1.99    inference(cnf_transformation,[],[f44])).
% 11.32/1.99  
% 11.32/1.99  fof(f8,axiom,(
% 11.32/1.99    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 11.32/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.32/1.99  
% 11.32/1.99  fof(f22,plain,(
% 11.32/1.99    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 11.32/1.99    inference(ennf_transformation,[],[f8])).
% 11.32/1.99  
% 11.32/1.99  fof(f57,plain,(
% 11.32/1.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 11.32/1.99    inference(cnf_transformation,[],[f22])).
% 11.32/1.99  
% 11.32/1.99  fof(f6,axiom,(
% 11.32/1.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 11.32/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.32/1.99  
% 11.32/1.99  fof(f18,plain,(
% 11.32/1.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 11.32/1.99    inference(ennf_transformation,[],[f6])).
% 11.32/1.99  
% 11.32/1.99  fof(f19,plain,(
% 11.32/1.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 11.32/1.99    inference(flattening,[],[f18])).
% 11.32/1.99  
% 11.32/1.99  fof(f55,plain,(
% 11.32/1.99    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 11.32/1.99    inference(cnf_transformation,[],[f19])).
% 11.32/1.99  
% 11.32/1.99  fof(f72,plain,(
% 11.32/1.99    r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) | r2_orders_2(sK3,sK4,sK5)),
% 11.32/1.99    inference(cnf_transformation,[],[f44])).
% 11.32/1.99  
% 11.32/1.99  fof(f4,axiom,(
% 11.32/1.99    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 11.32/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.32/1.99  
% 11.32/1.99  fof(f14,plain,(
% 11.32/1.99    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 11.32/1.99    inference(ennf_transformation,[],[f4])).
% 11.32/1.99  
% 11.32/1.99  fof(f15,plain,(
% 11.32/1.99    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 11.32/1.99    inference(flattening,[],[f14])).
% 11.32/1.99  
% 11.32/1.99  fof(f53,plain,(
% 11.32/1.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 11.32/1.99    inference(cnf_transformation,[],[f15])).
% 11.32/1.99  
% 11.32/1.99  fof(f3,axiom,(
% 11.32/1.99    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 11.32/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.32/1.99  
% 11.32/1.99  fof(f13,plain,(
% 11.32/1.99    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 11.32/1.99    inference(ennf_transformation,[],[f3])).
% 11.32/1.99  
% 11.32/1.99  fof(f52,plain,(
% 11.32/1.99    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 11.32/1.99    inference(cnf_transformation,[],[f13])).
% 11.32/1.99  
% 11.32/1.99  fof(f74,plain,(
% 11.32/1.99    ( ! [X0,X1] : (m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 11.32/1.99    inference(definition_unfolding,[],[f52,f51])).
% 11.32/1.99  
% 11.32/1.99  fof(f7,axiom,(
% 11.32/1.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)))),
% 11.32/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.32/1.99  
% 11.32/1.99  fof(f20,plain,(
% 11.32/1.99    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 11.32/1.99    inference(ennf_transformation,[],[f7])).
% 11.32/1.99  
% 11.32/1.99  fof(f21,plain,(
% 11.32/1.99    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 11.32/1.99    inference(flattening,[],[f20])).
% 11.32/1.99  
% 11.32/1.99  fof(f56,plain,(
% 11.32/1.99    ( ! [X0,X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 11.32/1.99    inference(cnf_transformation,[],[f21])).
% 11.32/1.99  
% 11.32/1.99  fof(f66,plain,(
% 11.32/1.99    v3_orders_2(sK3)),
% 11.32/1.99    inference(cnf_transformation,[],[f44])).
% 11.32/1.99  
% 11.32/1.99  fof(f67,plain,(
% 11.32/1.99    v4_orders_2(sK3)),
% 11.32/1.99    inference(cnf_transformation,[],[f44])).
% 11.32/1.99  
% 11.32/1.99  fof(f68,plain,(
% 11.32/1.99    v5_orders_2(sK3)),
% 11.32/1.99    inference(cnf_transformation,[],[f44])).
% 11.32/1.99  
% 11.32/1.99  fof(f9,axiom,(
% 11.32/1.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X3,X4))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 11.32/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.32/1.99  
% 11.32/1.99  fof(f23,plain,(
% 11.32/1.99    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 11.32/1.99    inference(ennf_transformation,[],[f9])).
% 11.32/1.99  
% 11.32/1.99  fof(f24,plain,(
% 11.32/1.99    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 11.32/1.99    inference(flattening,[],[f23])).
% 11.32/1.99  
% 11.32/1.99  fof(f34,plain,(
% 11.32/1.99    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 11.32/1.99    inference(nnf_transformation,[],[f24])).
% 11.32/1.99  
% 11.32/1.99  fof(f35,plain,(
% 11.32/1.99    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (! [X6] : (r2_orders_2(X1,X5,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 11.32/1.99    inference(rectify,[],[f34])).
% 11.32/1.99  
% 11.32/1.99  fof(f37,plain,(
% 11.32/1.99    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X1,X5,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (! [X6] : (r2_orders_2(X1,sK2(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))))),
% 11.32/1.99    introduced(choice_axiom,[])).
% 11.32/1.99  
% 11.32/1.99  fof(f36,plain,(
% 11.32/1.99    ! [X3,X2,X1] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) => (~r2_orders_2(X1,X3,sK1(X1,X2,X3)) & r2_hidden(sK1(X1,X2,X3),X2) & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1))))),
% 11.32/1.99    introduced(choice_axiom,[])).
% 11.32/1.99  
% 11.32/1.99  fof(f38,plain,(
% 11.32/1.99    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : ((~r2_orders_2(X1,X3,sK1(X1,X2,X3)) & r2_hidden(sK1(X1,X2,X3),X2) & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((! [X6] : (r2_orders_2(X1,sK2(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 11.32/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f35,f37,f36])).
% 11.32/1.99  
% 11.32/1.99  fof(f59,plain,(
% 11.32/1.99    ( ! [X2,X0,X1] : (sK2(X0,X1,X2) = X0 | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 11.32/1.99    inference(cnf_transformation,[],[f38])).
% 11.32/1.99  
% 11.32/1.99  fof(f62,plain,(
% 11.32/1.99    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_1_orders_2(X1,X2)) | r2_hidden(sK1(X1,X2,X3),X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 11.32/1.99    inference(cnf_transformation,[],[f38])).
% 11.32/1.99  
% 11.32/1.99  fof(f82,plain,(
% 11.32/1.99    ( ! [X2,X3,X1] : (r2_hidden(X3,a_2_1_orders_2(X1,X2)) | r2_hidden(sK1(X1,X2,X3),X2) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 11.32/1.99    inference(equality_resolution,[],[f62])).
% 11.32/1.99  
% 11.32/1.99  fof(f45,plain,(
% 11.32/1.99    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 11.32/1.99    inference(cnf_transformation,[],[f33])).
% 11.32/1.99  
% 11.32/1.99  fof(f80,plain,(
% 11.32/1.99    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k2_tarski(X0,X1))) )),
% 11.32/1.99    inference(equality_resolution,[],[f45])).
% 11.32/1.99  
% 11.32/1.99  fof(f73,plain,(
% 11.32/1.99    ~r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) | ~r2_orders_2(sK3,sK4,sK5)),
% 11.32/1.99    inference(cnf_transformation,[],[f44])).
% 11.32/1.99  
% 11.32/1.99  fof(f70,plain,(
% 11.32/1.99    m1_subset_1(sK4,u1_struct_0(sK3))),
% 11.32/1.99    inference(cnf_transformation,[],[f44])).
% 11.32/1.99  
% 11.32/1.99  fof(f60,plain,(
% 11.32/1.99    ( ! [X6,X2,X0,X1] : (r2_orders_2(X1,sK2(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 11.32/1.99    inference(cnf_transformation,[],[f38])).
% 11.32/1.99  
% 11.32/1.99  fof(f5,axiom,(
% 11.32/1.99    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 11.32/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.32/1.99  
% 11.32/1.99  fof(f16,plain,(
% 11.32/1.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 11.32/1.99    inference(ennf_transformation,[],[f5])).
% 11.32/1.99  
% 11.32/1.99  fof(f17,plain,(
% 11.32/1.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 11.32/1.99    inference(flattening,[],[f16])).
% 11.32/1.99  
% 11.32/1.99  fof(f54,plain,(
% 11.32/1.99    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 11.32/1.99    inference(cnf_transformation,[],[f17])).
% 11.32/1.99  
% 11.32/1.99  fof(f63,plain,(
% 11.32/1.99    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~r2_orders_2(X1,X3,sK1(X1,X2,X3)) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 11.32/1.99    inference(cnf_transformation,[],[f38])).
% 11.32/1.99  
% 11.32/1.99  fof(f81,plain,(
% 11.32/1.99    ( ! [X2,X3,X1] : (r2_hidden(X3,a_2_1_orders_2(X1,X2)) | ~r2_orders_2(X1,X3,sK1(X1,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 11.32/1.99    inference(equality_resolution,[],[f63])).
% 11.32/1.99  
% 11.32/1.99  cnf(c_3,plain,
% 11.32/1.99      ( r2_hidden(X0,k2_tarski(X1,X0)) ),
% 11.32/1.99      inference(cnf_transformation,[],[f77]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_28954,plain,
% 11.32/1.99      ( r2_hidden(X0,k2_tarski(X1,X0)) = iProver_top ),
% 11.32/1.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_21,negated_conjecture,
% 11.32/1.99      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 11.32/1.99      inference(cnf_transformation,[],[f71]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_28939,plain,
% 11.32/1.99      ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
% 11.32/1.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_18,plain,
% 11.32/1.99      ( ~ m1_subset_1(X0,X1)
% 11.32/1.99      | v1_xboole_0(X1)
% 11.32/1.99      | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
% 11.32/1.99      inference(cnf_transformation,[],[f75]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_28942,plain,
% 11.32/1.99      ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
% 11.32/1.99      | m1_subset_1(X1,X0) != iProver_top
% 11.32/1.99      | v1_xboole_0(X0) = iProver_top ),
% 11.32/1.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_30453,plain,
% 11.32/1.99      ( k6_domain_1(u1_struct_0(sK3),sK5) = k2_tarski(sK5,sK5)
% 11.32/1.99      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 11.32/1.99      inference(superposition,[status(thm)],[c_28939,c_28942]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_27,negated_conjecture,
% 11.32/1.99      ( ~ v2_struct_0(sK3) ),
% 11.32/1.99      inference(cnf_transformation,[],[f65]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_28,plain,
% 11.32/1.99      ( v2_struct_0(sK3) != iProver_top ),
% 11.32/1.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_23,negated_conjecture,
% 11.32/1.99      ( l1_orders_2(sK3) ),
% 11.32/1.99      inference(cnf_transformation,[],[f69]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_32,plain,
% 11.32/1.99      ( l1_orders_2(sK3) = iProver_top ),
% 11.32/1.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_11,plain,
% 11.32/1.99      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 11.32/1.99      inference(cnf_transformation,[],[f57]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_58,plain,
% 11.32/1.99      ( l1_orders_2(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 11.32/1.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_60,plain,
% 11.32/1.99      ( l1_orders_2(sK3) != iProver_top
% 11.32/1.99      | l1_struct_0(sK3) = iProver_top ),
% 11.32/1.99      inference(instantiation,[status(thm)],[c_58]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_9,plain,
% 11.32/1.99      ( v2_struct_0(X0)
% 11.32/1.99      | ~ l1_struct_0(X0)
% 11.32/1.99      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 11.32/1.99      inference(cnf_transformation,[],[f55]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_64,plain,
% 11.32/1.99      ( v2_struct_0(X0) = iProver_top
% 11.32/1.99      | l1_struct_0(X0) != iProver_top
% 11.32/1.99      | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
% 11.32/1.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_66,plain,
% 11.32/1.99      ( v2_struct_0(sK3) = iProver_top
% 11.32/1.99      | l1_struct_0(sK3) != iProver_top
% 11.32/1.99      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 11.32/1.99      inference(instantiation,[status(thm)],[c_64]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_30771,plain,
% 11.32/1.99      ( k6_domain_1(u1_struct_0(sK3),sK5) = k2_tarski(sK5,sK5) ),
% 11.32/1.99      inference(global_propositional_subsumption,
% 11.32/1.99                [status(thm)],
% 11.32/1.99                [c_30453,c_28,c_32,c_60,c_66]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_20,negated_conjecture,
% 11.32/1.99      ( r2_orders_2(sK3,sK4,sK5)
% 11.32/1.99      | r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) ),
% 11.32/1.99      inference(cnf_transformation,[],[f72]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_28940,plain,
% 11.32/1.99      ( r2_orders_2(sK3,sK4,sK5) = iProver_top
% 11.32/1.99      | r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) = iProver_top ),
% 11.32/1.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_30775,plain,
% 11.32/1.99      ( r2_orders_2(sK3,sK4,sK5) = iProver_top
% 11.32/1.99      | r2_hidden(sK4,k2_orders_2(sK3,k2_tarski(sK5,sK5))) = iProver_top ),
% 11.32/1.99      inference(demodulation,[status(thm)],[c_30771,c_28940]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_7,plain,
% 11.32/1.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 11.32/1.99      inference(cnf_transformation,[],[f53]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_28950,plain,
% 11.32/1.99      ( m1_subset_1(X0,X1) != iProver_top
% 11.32/1.99      | r2_hidden(X0,X1) = iProver_top
% 11.32/1.99      | v1_xboole_0(X1) = iProver_top ),
% 11.32/1.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_30428,plain,
% 11.32/1.99      ( r2_hidden(sK5,u1_struct_0(sK3)) = iProver_top
% 11.32/1.99      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 11.32/1.99      inference(superposition,[status(thm)],[c_28939,c_28950]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_34,plain,
% 11.32/1.99      ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
% 11.32/1.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_6953,plain,
% 11.32/1.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.32/1.99      | r2_hidden(X0,u1_struct_0(X1))
% 11.32/1.99      | v1_xboole_0(u1_struct_0(X1)) ),
% 11.32/1.99      inference(instantiation,[status(thm)],[c_7]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_7050,plain,
% 11.32/1.99      ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 11.32/1.99      | r2_hidden(sK5,u1_struct_0(sK3))
% 11.32/1.99      | v1_xboole_0(u1_struct_0(sK3)) ),
% 11.32/1.99      inference(instantiation,[status(thm)],[c_6953]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_7051,plain,
% 11.32/1.99      ( m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
% 11.32/1.99      | r2_hidden(sK5,u1_struct_0(sK3)) = iProver_top
% 11.32/1.99      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 11.32/1.99      inference(predicate_to_equality,[status(thm)],[c_7050]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_30617,plain,
% 11.32/1.99      ( r2_hidden(sK5,u1_struct_0(sK3)) = iProver_top ),
% 11.32/1.99      inference(global_propositional_subsumption,
% 11.32/1.99                [status(thm)],
% 11.32/1.99                [c_30428,c_28,c_32,c_34,c_60,c_66,c_7051]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_6,plain,
% 11.32/1.99      ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
% 11.32/1.99      | ~ r2_hidden(X0,X1) ),
% 11.32/1.99      inference(cnf_transformation,[],[f74]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_28951,plain,
% 11.32/1.99      ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1)) = iProver_top
% 11.32/1.99      | r2_hidden(X0,X1) != iProver_top ),
% 11.32/1.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_10,plain,
% 11.32/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.32/1.99      | ~ v3_orders_2(X1)
% 11.32/1.99      | ~ v4_orders_2(X1)
% 11.32/1.99      | ~ v5_orders_2(X1)
% 11.32/1.99      | ~ l1_orders_2(X1)
% 11.32/1.99      | v2_struct_0(X1)
% 11.32/1.99      | a_2_1_orders_2(X1,X0) = k2_orders_2(X1,X0) ),
% 11.32/1.99      inference(cnf_transformation,[],[f56]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_28947,plain,
% 11.32/1.99      ( a_2_1_orders_2(X0,X1) = k2_orders_2(X0,X1)
% 11.32/1.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.32/1.99      | v3_orders_2(X0) != iProver_top
% 11.32/1.99      | v4_orders_2(X0) != iProver_top
% 11.32/1.99      | v5_orders_2(X0) != iProver_top
% 11.32/1.99      | l1_orders_2(X0) != iProver_top
% 11.32/1.99      | v2_struct_0(X0) = iProver_top ),
% 11.32/1.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_31747,plain,
% 11.32/1.99      ( a_2_1_orders_2(X0,k2_tarski(X1,X1)) = k2_orders_2(X0,k2_tarski(X1,X1))
% 11.32/1.99      | r2_hidden(X1,u1_struct_0(X0)) != iProver_top
% 11.32/1.99      | v3_orders_2(X0) != iProver_top
% 11.32/1.99      | v4_orders_2(X0) != iProver_top
% 11.32/1.99      | v5_orders_2(X0) != iProver_top
% 11.32/1.99      | l1_orders_2(X0) != iProver_top
% 11.32/1.99      | v2_struct_0(X0) = iProver_top ),
% 11.32/1.99      inference(superposition,[status(thm)],[c_28951,c_28947]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_32894,plain,
% 11.32/1.99      ( a_2_1_orders_2(sK3,k2_tarski(sK5,sK5)) = k2_orders_2(sK3,k2_tarski(sK5,sK5))
% 11.32/1.99      | v3_orders_2(sK3) != iProver_top
% 11.32/1.99      | v4_orders_2(sK3) != iProver_top
% 11.32/1.99      | v5_orders_2(sK3) != iProver_top
% 11.32/1.99      | l1_orders_2(sK3) != iProver_top
% 11.32/1.99      | v2_struct_0(sK3) = iProver_top ),
% 11.32/1.99      inference(superposition,[status(thm)],[c_30617,c_31747]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_26,negated_conjecture,
% 11.32/1.99      ( v3_orders_2(sK3) ),
% 11.32/1.99      inference(cnf_transformation,[],[f66]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_29,plain,
% 11.32/1.99      ( v3_orders_2(sK3) = iProver_top ),
% 11.32/1.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_25,negated_conjecture,
% 11.32/1.99      ( v4_orders_2(sK3) ),
% 11.32/1.99      inference(cnf_transformation,[],[f67]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_30,plain,
% 11.32/1.99      ( v4_orders_2(sK3) = iProver_top ),
% 11.32/1.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_24,negated_conjecture,
% 11.32/1.99      ( v5_orders_2(sK3) ),
% 11.32/1.99      inference(cnf_transformation,[],[f68]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_31,plain,
% 11.32/1.99      ( v5_orders_2(sK3) = iProver_top ),
% 11.32/1.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_33459,plain,
% 11.32/1.99      ( a_2_1_orders_2(sK3,k2_tarski(sK5,sK5)) = k2_orders_2(sK3,k2_tarski(sK5,sK5)) ),
% 11.32/1.99      inference(global_propositional_subsumption,
% 11.32/1.99                [status(thm)],
% 11.32/1.99                [c_32894,c_28,c_29,c_30,c_31,c_32]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_16,plain,
% 11.32/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.32/1.99      | ~ r2_hidden(X2,a_2_1_orders_2(X1,X0))
% 11.32/1.99      | ~ v3_orders_2(X1)
% 11.32/1.99      | ~ v4_orders_2(X1)
% 11.32/1.99      | ~ v5_orders_2(X1)
% 11.32/1.99      | ~ l1_orders_2(X1)
% 11.32/1.99      | v2_struct_0(X1)
% 11.32/1.99      | sK2(X2,X1,X0) = X2 ),
% 11.32/1.99      inference(cnf_transformation,[],[f59]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_28943,plain,
% 11.32/1.99      ( sK2(X0,X1,X2) = X0
% 11.32/1.99      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 11.32/1.99      | r2_hidden(X0,a_2_1_orders_2(X1,X2)) != iProver_top
% 11.32/1.99      | v3_orders_2(X1) != iProver_top
% 11.32/1.99      | v4_orders_2(X1) != iProver_top
% 11.32/1.99      | v5_orders_2(X1) != iProver_top
% 11.32/1.99      | l1_orders_2(X1) != iProver_top
% 11.32/1.99      | v2_struct_0(X1) = iProver_top ),
% 11.32/1.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_30278,plain,
% 11.32/1.99      ( sK2(X0,X1,k2_tarski(X2,X2)) = X0
% 11.32/1.99      | r2_hidden(X0,a_2_1_orders_2(X1,k2_tarski(X2,X2))) != iProver_top
% 11.32/1.99      | r2_hidden(X2,u1_struct_0(X1)) != iProver_top
% 11.32/1.99      | v3_orders_2(X1) != iProver_top
% 11.32/1.99      | v4_orders_2(X1) != iProver_top
% 11.32/1.99      | v5_orders_2(X1) != iProver_top
% 11.32/1.99      | l1_orders_2(X1) != iProver_top
% 11.32/1.99      | v2_struct_0(X1) = iProver_top ),
% 11.32/1.99      inference(superposition,[status(thm)],[c_28951,c_28943]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_33462,plain,
% 11.32/1.99      ( sK2(X0,sK3,k2_tarski(sK5,sK5)) = X0
% 11.32/1.99      | r2_hidden(X0,k2_orders_2(sK3,k2_tarski(sK5,sK5))) != iProver_top
% 11.32/1.99      | r2_hidden(sK5,u1_struct_0(sK3)) != iProver_top
% 11.32/1.99      | v3_orders_2(sK3) != iProver_top
% 11.32/1.99      | v4_orders_2(sK3) != iProver_top
% 11.32/1.99      | v5_orders_2(sK3) != iProver_top
% 11.32/1.99      | l1_orders_2(sK3) != iProver_top
% 11.32/1.99      | v2_struct_0(sK3) = iProver_top ),
% 11.32/1.99      inference(superposition,[status(thm)],[c_33459,c_30278]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_33686,plain,
% 11.32/1.99      ( sK2(X0,sK3,k2_tarski(sK5,sK5)) = X0
% 11.32/1.99      | r2_hidden(X0,k2_orders_2(sK3,k2_tarski(sK5,sK5))) != iProver_top ),
% 11.32/1.99      inference(global_propositional_subsumption,
% 11.32/1.99                [status(thm)],
% 11.32/1.99                [c_33462,c_28,c_29,c_30,c_31,c_32,c_34,c_60,c_66,c_7051]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_33695,plain,
% 11.32/1.99      ( sK2(sK4,sK3,k2_tarski(sK5,sK5)) = sK4
% 11.32/1.99      | r2_orders_2(sK3,sK4,sK5) = iProver_top ),
% 11.32/1.99      inference(superposition,[status(thm)],[c_30775,c_33686]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_13,plain,
% 11.32/1.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.32/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 11.32/1.99      | r2_hidden(X0,a_2_1_orders_2(X1,X2))
% 11.32/1.99      | r2_hidden(sK1(X1,X2,X0),X2)
% 11.32/1.99      | ~ v3_orders_2(X1)
% 11.32/1.99      | ~ v4_orders_2(X1)
% 11.32/1.99      | ~ v5_orders_2(X1)
% 11.32/1.99      | ~ l1_orders_2(X1)
% 11.32/1.99      | v2_struct_0(X1) ),
% 11.32/1.99      inference(cnf_transformation,[],[f82]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_28944,plain,
% 11.32/1.99      ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 11.32/1.99      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 11.32/1.99      | r2_hidden(X0,a_2_1_orders_2(X1,X2)) = iProver_top
% 11.32/1.99      | r2_hidden(sK1(X1,X2,X0),X2) = iProver_top
% 11.32/1.99      | v3_orders_2(X1) != iProver_top
% 11.32/1.99      | v4_orders_2(X1) != iProver_top
% 11.32/1.99      | v5_orders_2(X1) != iProver_top
% 11.32/1.99      | l1_orders_2(X1) != iProver_top
% 11.32/1.99      | v2_struct_0(X1) = iProver_top ),
% 11.32/1.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_5,plain,
% 11.32/1.99      ( ~ r2_hidden(X0,k2_tarski(X1,X2)) | X0 = X1 | X0 = X2 ),
% 11.32/1.99      inference(cnf_transformation,[],[f80]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_28952,plain,
% 11.32/1.99      ( X0 = X1
% 11.32/1.99      | X0 = X2
% 11.32/1.99      | r2_hidden(X0,k2_tarski(X1,X2)) != iProver_top ),
% 11.32/1.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_31435,plain,
% 11.32/1.99      ( sK1(X0,k2_tarski(X1,X2),X3) = X1
% 11.32/1.99      | sK1(X0,k2_tarski(X1,X2),X3) = X2
% 11.32/1.99      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 11.32/1.99      | m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.32/1.99      | r2_hidden(X3,a_2_1_orders_2(X0,k2_tarski(X1,X2))) = iProver_top
% 11.32/1.99      | v3_orders_2(X0) != iProver_top
% 11.32/1.99      | v4_orders_2(X0) != iProver_top
% 11.32/1.99      | v5_orders_2(X0) != iProver_top
% 11.32/1.99      | l1_orders_2(X0) != iProver_top
% 11.32/1.99      | v2_struct_0(X0) = iProver_top ),
% 11.32/1.99      inference(superposition,[status(thm)],[c_28944,c_28952]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_34083,plain,
% 11.32/1.99      ( sK1(X0,k2_tarski(X1,X1),X2) = X1
% 11.32/1.99      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 11.32/1.99      | r2_hidden(X2,a_2_1_orders_2(X0,k2_tarski(X1,X1))) = iProver_top
% 11.32/1.99      | r2_hidden(X1,u1_struct_0(X0)) != iProver_top
% 11.32/1.99      | v3_orders_2(X0) != iProver_top
% 11.32/1.99      | v4_orders_2(X0) != iProver_top
% 11.32/1.99      | v5_orders_2(X0) != iProver_top
% 11.32/1.99      | l1_orders_2(X0) != iProver_top
% 11.32/1.99      | v2_struct_0(X0) = iProver_top ),
% 11.32/1.99      inference(superposition,[status(thm)],[c_28951,c_31435]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_34301,plain,
% 11.32/1.99      ( sK1(sK3,k2_tarski(sK5,sK5),X0) = sK5
% 11.32/1.99      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 11.32/1.99      | r2_hidden(X0,k2_orders_2(sK3,k2_tarski(sK5,sK5))) = iProver_top
% 11.32/1.99      | r2_hidden(sK5,u1_struct_0(sK3)) != iProver_top
% 11.32/1.99      | v3_orders_2(sK3) != iProver_top
% 11.32/1.99      | v4_orders_2(sK3) != iProver_top
% 11.32/1.99      | v5_orders_2(sK3) != iProver_top
% 11.32/1.99      | l1_orders_2(sK3) != iProver_top
% 11.32/1.99      | v2_struct_0(sK3) = iProver_top ),
% 11.32/1.99      inference(superposition,[status(thm)],[c_33459,c_34083]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_35207,plain,
% 11.32/1.99      ( sK1(sK3,k2_tarski(sK5,sK5),X0) = sK5
% 11.32/1.99      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 11.32/1.99      | r2_hidden(X0,k2_orders_2(sK3,k2_tarski(sK5,sK5))) = iProver_top ),
% 11.32/1.99      inference(global_propositional_subsumption,
% 11.32/1.99                [status(thm)],
% 11.32/1.99                [c_34301,c_28,c_29,c_30,c_31,c_32,c_34,c_60,c_66,c_7051]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_19,negated_conjecture,
% 11.32/1.99      ( ~ r2_orders_2(sK3,sK4,sK5)
% 11.32/1.99      | ~ r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) ),
% 11.32/1.99      inference(cnf_transformation,[],[f73]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_28941,plain,
% 11.32/1.99      ( r2_orders_2(sK3,sK4,sK5) != iProver_top
% 11.32/1.99      | r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) != iProver_top ),
% 11.32/1.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_30776,plain,
% 11.32/1.99      ( r2_orders_2(sK3,sK4,sK5) != iProver_top
% 11.32/1.99      | r2_hidden(sK4,k2_orders_2(sK3,k2_tarski(sK5,sK5))) != iProver_top ),
% 11.32/1.99      inference(demodulation,[status(thm)],[c_30771,c_28941]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_35218,plain,
% 11.32/1.99      ( sK1(sK3,k2_tarski(sK5,sK5),sK4) = sK5
% 11.32/1.99      | r2_orders_2(sK3,sK4,sK5) != iProver_top
% 11.32/1.99      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 11.32/1.99      inference(superposition,[status(thm)],[c_35207,c_30776]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_22,negated_conjecture,
% 11.32/1.99      ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 11.32/1.99      inference(cnf_transformation,[],[f70]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_33,plain,
% 11.32/1.99      ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
% 11.32/1.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_35257,plain,
% 11.32/1.99      ( r2_orders_2(sK3,sK4,sK5) != iProver_top
% 11.32/1.99      | sK1(sK3,k2_tarski(sK5,sK5),sK4) = sK5 ),
% 11.32/1.99      inference(global_propositional_subsumption,
% 11.32/1.99                [status(thm)],
% 11.32/1.99                [c_35218,c_33]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_35258,plain,
% 11.32/1.99      ( sK1(sK3,k2_tarski(sK5,sK5),sK4) = sK5
% 11.32/1.99      | r2_orders_2(sK3,sK4,sK5) != iProver_top ),
% 11.32/1.99      inference(renaming,[status(thm)],[c_35257]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_35263,plain,
% 11.32/1.99      ( sK2(sK4,sK3,k2_tarski(sK5,sK5)) = sK4
% 11.32/1.99      | sK1(sK3,k2_tarski(sK5,sK5),sK4) = sK5 ),
% 11.32/1.99      inference(superposition,[status(thm)],[c_33695,c_35258]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_15,plain,
% 11.32/1.99      ( r2_orders_2(X0,sK2(X1,X0,X2),X3)
% 11.32/1.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 11.32/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 11.32/1.99      | ~ r2_hidden(X3,X2)
% 11.32/1.99      | ~ r2_hidden(X1,a_2_1_orders_2(X0,X2))
% 11.32/1.99      | ~ v3_orders_2(X0)
% 11.32/1.99      | ~ v4_orders_2(X0)
% 11.32/1.99      | ~ v5_orders_2(X0)
% 11.32/1.99      | ~ l1_orders_2(X0)
% 11.32/1.99      | v2_struct_0(X0) ),
% 11.32/1.99      inference(cnf_transformation,[],[f60]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_4818,plain,
% 11.32/1.99      ( r2_orders_2(X0,sK2(X1,X0,X2),X3) = iProver_top
% 11.32/1.99      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 11.32/1.99      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.32/1.99      | r2_hidden(X3,X2) != iProver_top
% 11.32/1.99      | r2_hidden(X1,a_2_1_orders_2(X0,X2)) != iProver_top
% 11.32/1.99      | v3_orders_2(X0) != iProver_top
% 11.32/1.99      | v4_orders_2(X0) != iProver_top
% 11.32/1.99      | v5_orders_2(X0) != iProver_top
% 11.32/1.99      | l1_orders_2(X0) != iProver_top
% 11.32/1.99      | v2_struct_0(X0) = iProver_top ),
% 11.32/1.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_8,plain,
% 11.32/1.99      ( m1_subset_1(X0,X1)
% 11.32/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 11.32/1.99      | ~ r2_hidden(X0,X2) ),
% 11.32/1.99      inference(cnf_transformation,[],[f54]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_4821,plain,
% 11.32/1.99      ( m1_subset_1(X0,X1) = iProver_top
% 11.32/1.99      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 11.32/1.99      | r2_hidden(X0,X2) != iProver_top ),
% 11.32/1.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_4906,plain,
% 11.32/1.99      ( r2_orders_2(X0,sK2(X1,X0,X2),X3) = iProver_top
% 11.32/1.99      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.32/1.99      | r2_hidden(X3,X2) != iProver_top
% 11.32/1.99      | r2_hidden(X1,a_2_1_orders_2(X0,X2)) != iProver_top
% 11.32/1.99      | v3_orders_2(X0) != iProver_top
% 11.32/1.99      | v4_orders_2(X0) != iProver_top
% 11.32/1.99      | v5_orders_2(X0) != iProver_top
% 11.32/1.99      | l1_orders_2(X0) != iProver_top
% 11.32/1.99      | v2_struct_0(X0) = iProver_top ),
% 11.32/1.99      inference(forward_subsumption_resolution,
% 11.32/1.99                [status(thm)],
% 11.32/1.99                [c_4818,c_4821]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_4917,plain,
% 11.32/1.99      ( r2_orders_2(X0,sK2(X1,X0,X2),X3)
% 11.32/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 11.32/1.99      | ~ r2_hidden(X3,X2)
% 11.32/1.99      | ~ r2_hidden(X1,a_2_1_orders_2(X0,X2))
% 11.32/1.99      | ~ v3_orders_2(X0)
% 11.32/1.99      | ~ v4_orders_2(X0)
% 11.32/1.99      | ~ v5_orders_2(X0)
% 11.32/1.99      | ~ l1_orders_2(X0)
% 11.32/1.99      | v2_struct_0(X0) ),
% 11.32/1.99      inference(predicate_to_equality_rev,[status(thm)],[c_4906]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_28839,plain,
% 11.32/1.99      ( r2_orders_2(X0,sK2(X1,X0,X2),X3)
% 11.32/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 11.32/1.99      | ~ r2_hidden(X3,X2)
% 11.32/1.99      | ~ r2_hidden(X1,a_2_1_orders_2(X0,X2))
% 11.32/1.99      | ~ v3_orders_2(X0)
% 11.32/1.99      | ~ v4_orders_2(X0)
% 11.32/1.99      | ~ v5_orders_2(X0)
% 11.32/1.99      | ~ l1_orders_2(X0)
% 11.32/1.99      | v2_struct_0(X0) ),
% 11.32/1.99      inference(global_propositional_subsumption,
% 11.32/1.99                [status(thm)],
% 11.32/1.99                [c_15,c_4917]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_28929,plain,
% 11.32/1.99      ( r2_orders_2(X0,sK2(X1,X0,X2),X3) = iProver_top
% 11.32/1.99      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.32/1.99      | r2_hidden(X3,X2) != iProver_top
% 11.32/1.99      | r2_hidden(X1,a_2_1_orders_2(X0,X2)) != iProver_top
% 11.32/1.99      | v3_orders_2(X0) != iProver_top
% 11.32/1.99      | v4_orders_2(X0) != iProver_top
% 11.32/1.99      | v5_orders_2(X0) != iProver_top
% 11.32/1.99      | l1_orders_2(X0) != iProver_top
% 11.32/1.99      | v2_struct_0(X0) = iProver_top ),
% 11.32/1.99      inference(predicate_to_equality,[status(thm)],[c_28839]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_35551,plain,
% 11.32/1.99      ( sK1(sK3,k2_tarski(sK5,sK5),sK4) = sK5
% 11.32/1.99      | r2_orders_2(sK3,sK4,X0) = iProver_top
% 11.32/1.99      | m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 11.32/1.99      | r2_hidden(X0,k2_tarski(sK5,sK5)) != iProver_top
% 11.32/1.99      | r2_hidden(sK4,a_2_1_orders_2(sK3,k2_tarski(sK5,sK5))) != iProver_top
% 11.32/1.99      | v3_orders_2(sK3) != iProver_top
% 11.32/1.99      | v4_orders_2(sK3) != iProver_top
% 11.32/1.99      | v5_orders_2(sK3) != iProver_top
% 11.32/1.99      | l1_orders_2(sK3) != iProver_top
% 11.32/1.99      | v2_struct_0(sK3) = iProver_top ),
% 11.32/1.99      inference(superposition,[status(thm)],[c_35263,c_28929]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_35552,plain,
% 11.32/1.99      ( sK1(sK3,k2_tarski(sK5,sK5),sK4) = sK5
% 11.32/1.99      | r2_orders_2(sK3,sK4,X0) = iProver_top
% 11.32/1.99      | m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 11.32/1.99      | r2_hidden(X0,k2_tarski(sK5,sK5)) != iProver_top
% 11.32/1.99      | r2_hidden(sK4,k2_orders_2(sK3,k2_tarski(sK5,sK5))) != iProver_top
% 11.32/1.99      | v3_orders_2(sK3) != iProver_top
% 11.32/1.99      | v4_orders_2(sK3) != iProver_top
% 11.32/1.99      | v5_orders_2(sK3) != iProver_top
% 11.32/1.99      | l1_orders_2(sK3) != iProver_top
% 11.32/1.99      | v2_struct_0(sK3) = iProver_top ),
% 11.32/1.99      inference(light_normalisation,[status(thm)],[c_35551,c_33459]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_7069,plain,
% 11.32/1.99      ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
% 11.32/1.99      | ~ r2_hidden(sK5,u1_struct_0(sK3)) ),
% 11.32/1.99      inference(instantiation,[status(thm)],[c_6]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_7075,plain,
% 11.32/1.99      ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 11.32/1.99      | r2_hidden(sK5,u1_struct_0(sK3)) != iProver_top ),
% 11.32/1.99      inference(predicate_to_equality,[status(thm)],[c_7069]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_36016,plain,
% 11.32/1.99      ( r2_orders_2(sK3,sK4,X0) = iProver_top
% 11.32/1.99      | sK1(sK3,k2_tarski(sK5,sK5),sK4) = sK5
% 11.32/1.99      | r2_hidden(X0,k2_tarski(sK5,sK5)) != iProver_top ),
% 11.32/1.99      inference(global_propositional_subsumption,
% 11.32/1.99                [status(thm)],
% 11.32/1.99                [c_35552,c_28,c_29,c_30,c_31,c_32,c_34,c_60,c_66,c_7051,
% 11.32/1.99                 c_7075,c_30775,c_35258]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_36017,plain,
% 11.32/1.99      ( sK1(sK3,k2_tarski(sK5,sK5),sK4) = sK5
% 11.32/1.99      | r2_orders_2(sK3,sK4,X0) = iProver_top
% 11.32/1.99      | r2_hidden(X0,k2_tarski(sK5,sK5)) != iProver_top ),
% 11.32/1.99      inference(renaming,[status(thm)],[c_36016]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_36025,plain,
% 11.32/1.99      ( sK1(sK3,k2_tarski(sK5,sK5),sK4) = sK5
% 11.32/1.99      | r2_orders_2(sK3,sK4,sK5) = iProver_top ),
% 11.32/1.99      inference(superposition,[status(thm)],[c_28954,c_36017]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_36057,plain,
% 11.32/1.99      ( sK1(sK3,k2_tarski(sK5,sK5),sK4) = sK5 ),
% 11.32/1.99      inference(global_propositional_subsumption,
% 11.32/1.99                [status(thm)],
% 11.32/1.99                [c_36025,c_35258]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_12,plain,
% 11.32/1.99      ( ~ r2_orders_2(X0,X1,sK1(X0,X2,X1))
% 11.32/1.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.32/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 11.32/1.99      | r2_hidden(X1,a_2_1_orders_2(X0,X2))
% 11.32/1.99      | ~ v3_orders_2(X0)
% 11.32/1.99      | ~ v4_orders_2(X0)
% 11.32/1.99      | ~ v5_orders_2(X0)
% 11.32/1.99      | ~ l1_orders_2(X0)
% 11.32/1.99      | v2_struct_0(X0) ),
% 11.32/1.99      inference(cnf_transformation,[],[f81]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_28945,plain,
% 11.32/1.99      ( r2_orders_2(X0,X1,sK1(X0,X2,X1)) != iProver_top
% 11.32/1.99      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 11.32/1.99      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.32/1.99      | r2_hidden(X1,a_2_1_orders_2(X0,X2)) = iProver_top
% 11.32/1.99      | v3_orders_2(X0) != iProver_top
% 11.32/1.99      | v4_orders_2(X0) != iProver_top
% 11.32/1.99      | v5_orders_2(X0) != iProver_top
% 11.32/1.99      | l1_orders_2(X0) != iProver_top
% 11.32/1.99      | v2_struct_0(X0) = iProver_top ),
% 11.32/1.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_36060,plain,
% 11.32/1.99      ( r2_orders_2(sK3,sK4,sK5) != iProver_top
% 11.32/1.99      | m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 11.32/1.99      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 11.32/1.99      | r2_hidden(sK4,a_2_1_orders_2(sK3,k2_tarski(sK5,sK5))) = iProver_top
% 11.32/1.99      | v3_orders_2(sK3) != iProver_top
% 11.32/1.99      | v4_orders_2(sK3) != iProver_top
% 11.32/1.99      | v5_orders_2(sK3) != iProver_top
% 11.32/1.99      | l1_orders_2(sK3) != iProver_top
% 11.32/1.99      | v2_struct_0(sK3) = iProver_top ),
% 11.32/1.99      inference(superposition,[status(thm)],[c_36057,c_28945]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_36104,plain,
% 11.32/1.99      ( r2_orders_2(sK3,sK4,sK5) != iProver_top
% 11.32/1.99      | m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 11.32/1.99      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 11.32/1.99      | r2_hidden(sK4,k2_orders_2(sK3,k2_tarski(sK5,sK5))) = iProver_top
% 11.32/1.99      | v3_orders_2(sK3) != iProver_top
% 11.32/1.99      | v4_orders_2(sK3) != iProver_top
% 11.32/1.99      | v5_orders_2(sK3) != iProver_top
% 11.32/1.99      | l1_orders_2(sK3) != iProver_top
% 11.32/1.99      | v2_struct_0(sK3) = iProver_top ),
% 11.32/1.99      inference(light_normalisation,[status(thm)],[c_36060,c_33459]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_36367,plain,
% 11.32/1.99      ( r2_hidden(sK4,k2_orders_2(sK3,k2_tarski(sK5,sK5))) = iProver_top ),
% 11.32/1.99      inference(global_propositional_subsumption,
% 11.32/1.99                [status(thm)],
% 11.32/1.99                [c_36104,c_28,c_29,c_30,c_31,c_32,c_33,c_34,c_60,c_66,
% 11.32/1.99                 c_7051,c_7075,c_30775]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_36375,plain,
% 11.32/1.99      ( sK2(sK4,sK3,k2_tarski(sK5,sK5)) = sK4 ),
% 11.32/1.99      inference(superposition,[status(thm)],[c_36367,c_33686]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_37840,plain,
% 11.32/1.99      ( r2_orders_2(sK3,sK4,X0) = iProver_top
% 11.32/1.99      | m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 11.32/1.99      | r2_hidden(X0,k2_tarski(sK5,sK5)) != iProver_top
% 11.32/1.99      | r2_hidden(sK4,a_2_1_orders_2(sK3,k2_tarski(sK5,sK5))) != iProver_top
% 11.32/1.99      | v3_orders_2(sK3) != iProver_top
% 11.32/1.99      | v4_orders_2(sK3) != iProver_top
% 11.32/1.99      | v5_orders_2(sK3) != iProver_top
% 11.32/1.99      | l1_orders_2(sK3) != iProver_top
% 11.32/1.99      | v2_struct_0(sK3) = iProver_top ),
% 11.32/1.99      inference(superposition,[status(thm)],[c_36375,c_28929]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_37876,plain,
% 11.32/1.99      ( r2_orders_2(sK3,sK4,X0) = iProver_top
% 11.32/1.99      | m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 11.32/1.99      | r2_hidden(X0,k2_tarski(sK5,sK5)) != iProver_top
% 11.32/1.99      | r2_hidden(sK4,k2_orders_2(sK3,k2_tarski(sK5,sK5))) != iProver_top
% 11.32/1.99      | v3_orders_2(sK3) != iProver_top
% 11.32/1.99      | v4_orders_2(sK3) != iProver_top
% 11.32/1.99      | v5_orders_2(sK3) != iProver_top
% 11.32/1.99      | l1_orders_2(sK3) != iProver_top
% 11.32/1.99      | v2_struct_0(sK3) = iProver_top ),
% 11.32/1.99      inference(light_normalisation,[status(thm)],[c_37840,c_33459]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_37893,plain,
% 11.32/1.99      ( r2_orders_2(sK3,sK4,X0) = iProver_top
% 11.32/1.99      | r2_hidden(X0,k2_tarski(sK5,sK5)) != iProver_top ),
% 11.32/1.99      inference(global_propositional_subsumption,
% 11.32/1.99                [status(thm)],
% 11.32/1.99                [c_37876,c_28,c_29,c_30,c_31,c_32,c_33,c_34,c_60,c_66,
% 11.32/1.99                 c_7051,c_7075,c_30775,c_36104]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(c_37901,plain,
% 11.32/1.99      ( r2_orders_2(sK3,sK4,sK5) = iProver_top ),
% 11.32/1.99      inference(superposition,[status(thm)],[c_28954,c_37893]) ).
% 11.32/1.99  
% 11.32/1.99  cnf(contradiction,plain,
% 11.32/1.99      ( $false ),
% 11.32/1.99      inference(minisat,[status(thm)],[c_37901,c_36367,c_30776]) ).
% 11.32/1.99  
% 11.32/1.99  
% 11.32/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.32/1.99  
% 11.32/1.99  ------                               Statistics
% 11.32/1.99  
% 11.32/1.99  ------ Selected
% 11.32/1.99  
% 11.32/1.99  total_time:                             1.107
% 11.32/1.99  
%------------------------------------------------------------------------------
