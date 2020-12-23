%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:12:29 EST 2020

% Result     : Theorem 31.39s
% Output     : CNFRefutation 31.39s
% Verified   : 
% Statistics : Number of formulae       :  198 (22530 expanded)
%              Number of clauses        :  132 (5528 expanded)
%              Number of leaves         :   16 (5791 expanded)
%              Depth                    :   40
%              Number of atoms          :  890 (155801 expanded)
%              Number of equality atoms :  430 (11781 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   22 (   3 average)
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

fof(f24,plain,(
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
    inference(flattening,[],[f24])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
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

fof(f28,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f68,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f42])).

fof(f69,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f68])).

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

fof(f22,plain,(
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
    inference(flattening,[],[f22])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f23])).

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
    inference(flattening,[],[f34])).

fof(f38,plain,(
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

fof(f37,plain,(
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

fof(f36,plain,
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

fof(f39,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f35,f38,f37,f36])).

fof(f63,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f39])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k2_tarski(X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f57,f46])).

fof(f58,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f62,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f50,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f65,plain,
    ( r2_hidden(sK5,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4)))
    | r2_orders_2(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f39])).

fof(f59,plain,(
    v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f60,plain,(
    v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f61,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f64,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f39])).

fof(f66,plain,
    ( ~ r2_hidden(sK5,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4)))
    | ~ r2_orders_2(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f39])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f7,axiom,(
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

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f19])).

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
    inference(rectify,[],[f29])).

fof(f32,plain,(
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

fof(f31,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ~ r2_orders_2(X1,X4,X3)
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_orders_2(X1,sK1(X1,X2,X3),X3)
        & r2_hidden(sK1(X1,X2,X3),X2)
        & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f30,f32,f31])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( sK2(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f33])).

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

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f55,plain,(
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
    inference(cnf_transformation,[],[f33])).

fof(f74,plain,(
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
    inference(equality_resolution,[],[f55])).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f72,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_tarski(X0,X1)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f53,plain,(
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
    inference(cnf_transformation,[],[f33])).

fof(f56,plain,(
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
    inference(cnf_transformation,[],[f33])).

fof(f73,plain,(
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
    inference(equality_resolution,[],[f56])).

cnf(c_3,plain,
    ( r2_hidden(X0,k2_tarski(X1,X0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_101956,plain,
    ( r2_hidden(X0,k2_tarski(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_101945,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_101947,plain,
    ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_102978,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK4) = k2_tarski(sK4,sK4)
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_101945,c_101947])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_26,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_21,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_30,plain,
    ( l1_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_9,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_56,plain,
    ( l1_orders_2(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_58,plain,
    ( l1_orders_2(sK3) != iProver_top
    | l1_struct_0(sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_56])).

cnf(c_6,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_65,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_67,plain,
    ( v2_struct_0(sK3) = iProver_top
    | l1_struct_0(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_65])).

cnf(c_17706,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_17710,plain,
    ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_18522,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK4) = k2_tarski(sK4,sK4)
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_17706,c_17710])).

cnf(c_103087,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK4) = k2_tarski(sK4,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_102978,c_26,c_30,c_58,c_67,c_18522])).

cnf(c_18,negated_conjecture,
    ( r2_orders_2(sK3,sK4,sK5)
    | r2_hidden(sK5,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_24,negated_conjecture,
    ( v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_23,negated_conjecture,
    ( v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_22,negated_conjecture,
    ( v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_57,plain,
    ( ~ l1_orders_2(sK3)
    | l1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_66,plain,
    ( v2_struct_0(sK3)
    | ~ l1_struct_0(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_18675,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK4) = k2_tarski(sK4,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18522,c_26,c_30,c_58,c_67])).

cnf(c_17,negated_conjecture,
    ( ~ r2_orders_2(sK3,sK4,sK5)
    | ~ r2_hidden(sK5,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_17709,plain,
    ( r2_orders_2(sK3,sK4,sK5) != iProver_top
    | r2_hidden(sK5,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_18679,plain,
    ( r2_orders_2(sK3,sK4,sK5) != iProver_top
    | r2_hidden(sK5,k1_orders_2(sK3,k2_tarski(sK4,sK4))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_18675,c_17709])).

cnf(c_18689,plain,
    ( ~ r2_orders_2(sK3,sK4,sK5)
    | ~ r2_hidden(sK5,k1_orders_2(sK3,k2_tarski(sK4,sK4))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_18679])).

cnf(c_21117,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_21121,plain,
    ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_22507,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK4) = k2_tarski(sK4,sK4)
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_21117,c_21121])).

cnf(c_22945,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK4) = k2_tarski(sK4,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_22507,c_26,c_30,c_58,c_67,c_18522])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_21123,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_22960,plain,
    ( m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_22945,c_21123])).

cnf(c_22961,plain,
    ( m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_22960])).

cnf(c_60528,plain,
    ( r2_hidden(X0,k2_tarski(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_60513,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_60517,plain,
    ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_61489,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK4) = k2_tarski(sK4,sK4)
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_60513,c_60517])).

cnf(c_61595,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK4) = k2_tarski(sK4,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_61489,c_26,c_30,c_58,c_67,c_18522])).

cnf(c_60515,plain,
    ( r2_orders_2(sK3,sK4,sK5) = iProver_top
    | r2_hidden(sK5,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_61598,plain,
    ( r2_orders_2(sK3,sK4,sK5) = iProver_top
    | r2_hidden(sK5,k1_orders_2(sK3,k2_tarski(sK4,sK4))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_61595,c_60515])).

cnf(c_60523,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_61752,plain,
    ( m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_61595,c_60523])).

cnf(c_31,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_62303,plain,
    ( m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_61752,c_26,c_30,c_31,c_58,c_67,c_22960])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1)
    | sK2(X2,X1,X0) = X2 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_60518,plain,
    ( sK2(X0,X1,X2) = X0
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r2_hidden(X0,a_2_0_orders_2(X1,X2)) != iProver_top
    | v3_orders_2(X1) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v5_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top
    | v2_struct_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_62310,plain,
    ( sK2(X0,sK3,k2_tarski(sK4,sK4)) = X0
    | r2_hidden(X0,a_2_0_orders_2(sK3,k2_tarski(sK4,sK4))) != iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_62303,c_60518])).

cnf(c_27,plain,
    ( v3_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_28,plain,
    ( v4_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_29,plain,
    ( v5_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_63106,plain,
    ( r2_hidden(X0,a_2_0_orders_2(sK3,k2_tarski(sK4,sK4))) != iProver_top
    | sK2(X0,sK3,k2_tarski(sK4,sK4)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_62310,c_26,c_27,c_28,c_29,c_30])).

cnf(c_63107,plain,
    ( sK2(X0,sK3,k2_tarski(sK4,sK4)) = X0
    | r2_hidden(X0,a_2_0_orders_2(sK3,k2_tarski(sK4,sK4))) != iProver_top ),
    inference(renaming,[status(thm)],[c_63106])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1)
    | a_2_0_orders_2(X1,X0) = k1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_60524,plain,
    ( a_2_0_orders_2(X0,X1) = k1_orders_2(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v3_orders_2(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_62308,plain,
    ( a_2_0_orders_2(sK3,k2_tarski(sK4,sK4)) = k1_orders_2(sK3,k2_tarski(sK4,sK4))
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_62303,c_60524])).

cnf(c_23367,plain,
    ( m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_22960,c_26,c_30,c_31,c_58,c_67])).

cnf(c_21124,plain,
    ( a_2_0_orders_2(X0,X1) = k1_orders_2(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v3_orders_2(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_23372,plain,
    ( a_2_0_orders_2(sK3,k2_tarski(sK4,sK4)) = k1_orders_2(sK3,k2_tarski(sK4,sK4))
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_23367,c_21124])).

cnf(c_62733,plain,
    ( a_2_0_orders_2(sK3,k2_tarski(sK4,sK4)) = k1_orders_2(sK3,k2_tarski(sK4,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_62308,c_26,c_27,c_28,c_29,c_30,c_23372])).

cnf(c_63112,plain,
    ( sK2(X0,sK3,k2_tarski(sK4,sK4)) = X0
    | r2_hidden(X0,k1_orders_2(sK3,k2_tarski(sK4,sK4))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_63107,c_62733])).

cnf(c_63119,plain,
    ( sK2(sK5,sK3,k2_tarski(sK4,sK4)) = sK5
    | r2_orders_2(sK3,sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_61598,c_63112])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,a_2_0_orders_2(X1,X0))
    | r2_hidden(sK1(X1,X0,X2),X0)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_60520,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | r2_hidden(X2,a_2_0_orders_2(X1,X0)) = iProver_top
    | r2_hidden(sK1(X1,X0,X2),X0) = iProver_top
    | v3_orders_2(X1) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v5_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top
    | v2_struct_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k2_tarski(X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_60526,plain,
    ( X0 = X1
    | X0 = X2
    | r2_hidden(X0,k2_tarski(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_61943,plain,
    ( sK1(X0,k2_tarski(X1,X2),X3) = X1
    | sK1(X0,k2_tarski(X1,X2),X3) = X2
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r2_hidden(X3,a_2_0_orders_2(X0,k2_tarski(X1,X2))) = iProver_top
    | v3_orders_2(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_60520,c_60526])).

cnf(c_64594,plain,
    ( sK1(sK3,k2_tarski(sK4,sK4),X0) = sK4
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,a_2_0_orders_2(sK3,k2_tarski(sK4,sK4))) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_62303,c_61943])).

cnf(c_64603,plain,
    ( sK1(sK3,k2_tarski(sK4,sK4),X0) = sK4
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,k1_orders_2(sK3,k2_tarski(sK4,sK4))) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_64594,c_62733])).

cnf(c_66089,plain,
    ( r2_hidden(X0,k1_orders_2(sK3,k2_tarski(sK4,sK4))) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | sK1(sK3,k2_tarski(sK4,sK4),X0) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_64603,c_26,c_27,c_28,c_29,c_30])).

cnf(c_66090,plain,
    ( sK1(sK3,k2_tarski(sK4,sK4),X0) = sK4
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,k1_orders_2(sK3,k2_tarski(sK4,sK4))) = iProver_top ),
    inference(renaming,[status(thm)],[c_66089])).

cnf(c_60516,plain,
    ( r2_orders_2(sK3,sK4,sK5) != iProver_top
    | r2_hidden(sK5,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_61599,plain,
    ( r2_orders_2(sK3,sK4,sK5) != iProver_top
    | r2_hidden(sK5,k1_orders_2(sK3,k2_tarski(sK4,sK4))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_61595,c_60516])).

cnf(c_66098,plain,
    ( sK1(sK3,k2_tarski(sK4,sK4),sK5) = sK4
    | r2_orders_2(sK3,sK4,sK5) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_66090,c_61599])).

cnf(c_32,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_66117,plain,
    ( r2_orders_2(sK3,sK4,sK5) != iProver_top
    | sK1(sK3,k2_tarski(sK4,sK4),sK5) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_66098,c_32])).

cnf(c_66118,plain,
    ( sK1(sK3,k2_tarski(sK4,sK4),sK5) = sK4
    | r2_orders_2(sK3,sK4,sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_66117])).

cnf(c_66123,plain,
    ( sK2(sK5,sK3,k2_tarski(sK4,sK4)) = sK5
    | sK1(sK3,k2_tarski(sK4,sK4),sK5) = sK4 ),
    inference(superposition,[status(thm)],[c_63119,c_66118])).

cnf(c_13,plain,
    ( r2_orders_2(X0,X1,sK2(X2,X0,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X2,a_2_0_orders_2(X0,X3))
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_60519,plain,
    ( r2_orders_2(X0,X1,sK2(X2,X0,X3)) = iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | r2_hidden(X1,X3) != iProver_top
    | r2_hidden(X2,a_2_0_orders_2(X0,X3)) != iProver_top
    | v3_orders_2(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_66382,plain,
    ( sK1(sK3,k2_tarski(sK4,sK4),sK5) = sK4
    | r2_orders_2(sK3,X0,sK5) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,k2_tarski(sK4,sK4)) != iProver_top
    | r2_hidden(sK5,a_2_0_orders_2(sK3,k2_tarski(sK4,sK4))) != iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_66123,c_60519])).

cnf(c_66422,plain,
    ( sK1(sK3,k2_tarski(sK4,sK4),sK5) = sK4
    | r2_orders_2(sK3,X0,sK5) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,k2_tarski(sK4,sK4)) != iProver_top
    | r2_hidden(sK5,k1_orders_2(sK3,k2_tarski(sK4,sK4))) != iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_66382,c_62733])).

cnf(c_304,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_7762,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | X1 != u1_struct_0(sK3)
    | X0 != sK4 ),
    inference(instantiation,[status(thm)],[c_304])).

cnf(c_7932,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | X0 != sK4
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_7762])).

cnf(c_7933,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | X0 != sK4 ),
    inference(equality_resolution_simp,[status(thm)],[c_7932])).

cnf(c_7934,plain,
    ( X0 != sK4
    | m1_subset_1(X0,u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7933])).

cnf(c_17708,plain,
    ( r2_orders_2(sK3,sK4,sK5) = iProver_top
    | r2_hidden(sK5,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_18678,plain,
    ( r2_orders_2(sK3,sK4,sK5) = iProver_top
    | r2_hidden(sK5,k1_orders_2(sK3,k2_tarski(sK4,sK4))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_18675,c_17708])).

cnf(c_32144,plain,
    ( ~ r2_hidden(X0,k2_tarski(X1,sK4))
    | X0 = X1
    | X0 = sK4 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_38629,plain,
    ( ~ r2_hidden(X0,k2_tarski(sK4,sK4))
    | X0 = sK4 ),
    inference(instantiation,[status(thm)],[c_32144])).

cnf(c_38630,plain,
    ( X0 = sK4
    | r2_hidden(X0,k2_tarski(sK4,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38629])).

cnf(c_73425,plain,
    ( sK1(sK3,k2_tarski(sK4,sK4),sK5) = sK4
    | r2_orders_2(sK3,X0,sK5) = iProver_top
    | r2_hidden(X0,k2_tarski(sK4,sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_66422,c_26,c_27,c_28,c_29,c_30,c_31,c_58,c_67,c_7934,c_18678,c_22960,c_38630,c_66118])).

cnf(c_73434,plain,
    ( sK1(sK3,k2_tarski(sK4,sK4),sK5) = sK4
    | r2_orders_2(sK3,sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_60528,c_73425])).

cnf(c_73739,plain,
    ( sK1(sK3,k2_tarski(sK4,sK4),sK5) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_73434,c_66118])).

cnf(c_10,plain,
    ( ~ r2_orders_2(X0,sK1(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(X2,a_2_0_orders_2(X0,X1))
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_60521,plain,
    ( r2_orders_2(X0,sK1(X0,X1,X2),X2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | r2_hidden(X2,a_2_0_orders_2(X0,X1)) = iProver_top
    | v3_orders_2(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_73742,plain,
    ( r2_orders_2(sK3,sK4,sK5) != iProver_top
    | m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK5,a_2_0_orders_2(sK3,k2_tarski(sK4,sK4))) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_73739,c_60521])).

cnf(c_73763,plain,
    ( r2_orders_2(sK3,sK4,sK5) != iProver_top
    | m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK5,k1_orders_2(sK3,k2_tarski(sK4,sK4))) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_73742,c_62733])).

cnf(c_73773,plain,
    ( ~ r2_orders_2(sK3,sK4,sK5)
    | ~ m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | r2_hidden(sK5,k1_orders_2(sK3,k2_tarski(sK4,sK4)))
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ v5_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | v2_struct_0(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_73763])).

cnf(c_74794,negated_conjecture,
    ( r2_hidden(sK5,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18,c_25,c_24,c_23,c_22,c_21,c_20,c_19,c_57,c_66,c_18689,c_22961,c_73773])).

cnf(c_101724,plain,
    ( r2_orders_2(sK3,sK4,sK5)
    | r2_hidden(sK5,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) ),
    inference(prop_impl,[status(thm)],[c_25,c_24,c_23,c_22,c_21,c_20,c_19,c_18,c_57,c_66,c_18689,c_22961,c_73773])).

cnf(c_101820,plain,
    ( r2_hidden(sK5,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_101724,c_25,c_24,c_23,c_22,c_21,c_20,c_19,c_18,c_57,c_66,c_18689,c_22961,c_73773])).

cnf(c_101936,plain,
    ( r2_hidden(sK5,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_101820])).

cnf(c_103090,plain,
    ( r2_hidden(sK5,k1_orders_2(sK3,k2_tarski(sK4,sK4))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_103087,c_101936])).

cnf(c_101951,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_103188,plain,
    ( m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_103087,c_101951])).

cnf(c_103793,plain,
    ( m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_103188,c_26,c_30,c_31,c_58,c_67,c_22960])).

cnf(c_101948,plain,
    ( sK2(X0,X1,X2) = X0
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r2_hidden(X0,a_2_0_orders_2(X1,X2)) != iProver_top
    | v3_orders_2(X1) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v5_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top
    | v2_struct_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_103801,plain,
    ( sK2(X0,sK3,k2_tarski(sK4,sK4)) = X0
    | r2_hidden(X0,a_2_0_orders_2(sK3,k2_tarski(sK4,sK4))) != iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_103793,c_101948])).

cnf(c_104650,plain,
    ( r2_hidden(X0,a_2_0_orders_2(sK3,k2_tarski(sK4,sK4))) != iProver_top
    | sK2(X0,sK3,k2_tarski(sK4,sK4)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_103801,c_26,c_27,c_28,c_29,c_30,c_62310])).

cnf(c_104651,plain,
    ( sK2(X0,sK3,k2_tarski(sK4,sK4)) = X0
    | r2_hidden(X0,a_2_0_orders_2(sK3,k2_tarski(sK4,sK4))) != iProver_top ),
    inference(renaming,[status(thm)],[c_104650])).

cnf(c_101952,plain,
    ( a_2_0_orders_2(X0,X1) = k1_orders_2(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v3_orders_2(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_103798,plain,
    ( a_2_0_orders_2(sK3,k2_tarski(sK4,sK4)) = k1_orders_2(sK3,k2_tarski(sK4,sK4))
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_103793,c_101952])).

cnf(c_104507,plain,
    ( a_2_0_orders_2(sK3,k2_tarski(sK4,sK4)) = k1_orders_2(sK3,k2_tarski(sK4,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_103798,c_26,c_27,c_28,c_29,c_30,c_23372])).

cnf(c_104654,plain,
    ( sK2(X0,sK3,k2_tarski(sK4,sK4)) = X0
    | r2_hidden(X0,k1_orders_2(sK3,k2_tarski(sK4,sK4))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_104651,c_104507])).

cnf(c_104658,plain,
    ( sK2(sK5,sK3,k2_tarski(sK4,sK4)) = sK5 ),
    inference(superposition,[status(thm)],[c_103090,c_104654])).

cnf(c_101949,plain,
    ( r2_orders_2(X0,X1,sK2(X2,X0,X3)) = iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | r2_hidden(X1,X3) != iProver_top
    | r2_hidden(X2,a_2_0_orders_2(X0,X3)) != iProver_top
    | v3_orders_2(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_105655,plain,
    ( r2_orders_2(sK3,X0,sK5) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,k2_tarski(sK4,sK4)) != iProver_top
    | r2_hidden(sK5,a_2_0_orders_2(sK3,k2_tarski(sK4,sK4))) != iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_104658,c_101949])).

cnf(c_105656,plain,
    ( r2_orders_2(sK3,X0,sK5) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,k2_tarski(sK4,sK4)) != iProver_top
    | r2_hidden(sK5,k1_orders_2(sK3,k2_tarski(sK4,sK4))) != iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_105655,c_104507])).

cnf(c_34,plain,
    ( r2_orders_2(sK3,sK4,sK5) != iProver_top
    | r2_hidden(sK5,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_74796,plain,
    ( r2_hidden(sK5,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_74794])).

cnf(c_109007,plain,
    ( r2_orders_2(sK3,X0,sK5) = iProver_top
    | r2_hidden(X0,k2_tarski(sK4,sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_105656,c_26,c_27,c_28,c_29,c_30,c_31,c_34,c_58,c_67,c_7934,c_18678,c_22960,c_38630,c_74796])).

cnf(c_109015,plain,
    ( r2_orders_2(sK3,sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_101956,c_109007])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_109015,c_74796,c_34])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:26:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 31.39/4.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 31.39/4.50  
% 31.39/4.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 31.39/4.50  
% 31.39/4.50  ------  iProver source info
% 31.39/4.50  
% 31.39/4.50  git: date: 2020-06-30 10:37:57 +0100
% 31.39/4.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 31.39/4.50  git: non_committed_changes: false
% 31.39/4.50  git: last_make_outside_of_git: false
% 31.39/4.50  
% 31.39/4.50  ------ 
% 31.39/4.50  ------ Parsing...
% 31.39/4.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 31.39/4.50  
% 31.39/4.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 31.39/4.50  
% 31.39/4.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 31.39/4.50  
% 31.39/4.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.39/4.50  ------ Proving...
% 31.39/4.50  ------ Problem Properties 
% 31.39/4.50  
% 31.39/4.50  
% 31.39/4.50  clauses                                 26
% 31.39/4.50  conjectures                             9
% 31.39/4.50  EPR                                     6
% 31.39/4.50  Horn                                    14
% 31.39/4.50  unary                                   9
% 31.39/4.50  binary                                  3
% 31.39/4.50  lits                                    97
% 31.39/4.50  lits eq                                 12
% 31.39/4.50  fd_pure                                 0
% 31.39/4.50  fd_pseudo                               0
% 31.39/4.50  fd_cond                                 0
% 31.39/4.50  fd_pseudo_cond                          3
% 31.39/4.50  AC symbols                              0
% 31.39/4.50  
% 31.39/4.50  ------ Input Options Time Limit: Unbounded
% 31.39/4.50  
% 31.39/4.50  
% 31.39/4.50  
% 31.39/4.50  
% 31.39/4.50  ------ Preprocessing...
% 31.39/4.50  
% 31.39/4.50  ------ Preprocessing... sf_s  rm: 11 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 31.39/4.50  Current options:
% 31.39/4.50  ------ 
% 31.39/4.50  
% 31.39/4.50  
% 31.39/4.50  
% 31.39/4.50  
% 31.39/4.50  ------ Proving...
% 31.39/4.50  
% 31.39/4.50  
% 31.39/4.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.39/4.50  
% 31.39/4.50  ------ Proving...
% 31.39/4.50  
% 31.39/4.50  
% 31.39/4.50  ------ Preprocessing... sf_s  rm: 10 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.39/4.50  
% 31.39/4.50  ------ Proving...
% 31.39/4.50  
% 31.39/4.50  
% 31.39/4.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.39/4.50  
% 31.39/4.50  ------ Proving...
% 31.39/4.50  
% 31.39/4.50  
% 31.39/4.50  ------ Preprocessing... sf_s  rm: 17 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.39/4.50  
% 31.39/4.50  ------ Proving...
% 31.39/4.50  
% 31.39/4.50  
% 31.39/4.50  ------ Preprocessing... sf_s  rm: 17 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.39/4.50  
% 31.39/4.50  ------ Proving...
% 31.39/4.50  
% 31.39/4.50  
% 31.39/4.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.39/4.50  
% 31.39/4.50  ------ Proving...
% 31.39/4.50  
% 31.39/4.50  
% 31.39/4.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.39/4.50  
% 31.39/4.50  ------ Proving...
% 31.39/4.50  
% 31.39/4.50  
% 31.39/4.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.39/4.50  
% 31.39/4.50  ------ Proving...
% 31.39/4.50  
% 31.39/4.50  
% 31.39/4.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.39/4.50  
% 31.39/4.50  ------ Proving...
% 31.39/4.50  
% 31.39/4.50  
% 31.39/4.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.39/4.50  
% 31.39/4.50  ------ Proving...
% 31.39/4.50  
% 31.39/4.50  
% 31.39/4.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.39/4.50  
% 31.39/4.50  ------ Proving...
% 31.39/4.50  
% 31.39/4.50  
% 31.39/4.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.39/4.50  
% 31.39/4.50  ------ Proving...
% 31.39/4.50  
% 31.39/4.50  
% 31.39/4.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.39/4.50  
% 31.39/4.50  ------ Proving...
% 31.39/4.50  
% 31.39/4.50  
% 31.39/4.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.39/4.50  
% 31.39/4.50  ------ Proving...
% 31.39/4.50  
% 31.39/4.50  
% 31.39/4.50  % SZS status Theorem for theBenchmark.p
% 31.39/4.50  
% 31.39/4.50  % SZS output start CNFRefutation for theBenchmark.p
% 31.39/4.50  
% 31.39/4.50  fof(f1,axiom,(
% 31.39/4.50    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 31.39/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.39/4.50  
% 31.39/4.50  fof(f24,plain,(
% 31.39/4.50    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 31.39/4.50    inference(nnf_transformation,[],[f1])).
% 31.39/4.50  
% 31.39/4.50  fof(f25,plain,(
% 31.39/4.50    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 31.39/4.50    inference(flattening,[],[f24])).
% 31.39/4.50  
% 31.39/4.50  fof(f26,plain,(
% 31.39/4.50    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 31.39/4.50    inference(rectify,[],[f25])).
% 31.39/4.50  
% 31.39/4.50  fof(f27,plain,(
% 31.39/4.50    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2))))),
% 31.39/4.50    introduced(choice_axiom,[])).
% 31.39/4.50  
% 31.39/4.50  fof(f28,plain,(
% 31.39/4.50    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 31.39/4.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 31.39/4.50  
% 31.39/4.50  fof(f42,plain,(
% 31.39/4.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 31.39/4.50    inference(cnf_transformation,[],[f28])).
% 31.39/4.50  
% 31.39/4.50  fof(f68,plain,(
% 31.39/4.50    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_tarski(X0,X4) != X2) )),
% 31.39/4.50    inference(equality_resolution,[],[f42])).
% 31.39/4.50  
% 31.39/4.50  fof(f69,plain,(
% 31.39/4.50    ( ! [X4,X0] : (r2_hidden(X4,k2_tarski(X0,X4))) )),
% 31.39/4.50    inference(equality_resolution,[],[f68])).
% 31.39/4.50  
% 31.39/4.50  fof(f9,conjecture,(
% 31.39/4.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))))),
% 31.39/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.39/4.50  
% 31.39/4.50  fof(f10,negated_conjecture,(
% 31.39/4.50    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))))),
% 31.39/4.50    inference(negated_conjecture,[],[f9])).
% 31.39/4.50  
% 31.39/4.50  fof(f22,plain,(
% 31.39/4.50    ? [X0] : (? [X1] : (? [X2] : ((r2_orders_2(X0,X1,X2) <~> r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 31.39/4.50    inference(ennf_transformation,[],[f10])).
% 31.39/4.50  
% 31.39/4.50  fof(f23,plain,(
% 31.39/4.50    ? [X0] : (? [X1] : (? [X2] : ((r2_orders_2(X0,X1,X2) <~> r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 31.39/4.50    inference(flattening,[],[f22])).
% 31.39/4.50  
% 31.39/4.50  fof(f34,plain,(
% 31.39/4.50    ? [X0] : (? [X1] : (? [X2] : (((~r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | ~r2_orders_2(X0,X1,X2)) & (r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | r2_orders_2(X0,X1,X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 31.39/4.50    inference(nnf_transformation,[],[f23])).
% 31.39/4.50  
% 31.39/4.50  fof(f35,plain,(
% 31.39/4.50    ? [X0] : (? [X1] : (? [X2] : ((~r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | ~r2_orders_2(X0,X1,X2)) & (r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | r2_orders_2(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 31.39/4.50    inference(flattening,[],[f34])).
% 31.39/4.50  
% 31.39/4.50  fof(f38,plain,(
% 31.39/4.50    ( ! [X0,X1] : (? [X2] : ((~r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | ~r2_orders_2(X0,X1,X2)) & (r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | r2_orders_2(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) => ((~r2_hidden(sK5,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | ~r2_orders_2(X0,X1,sK5)) & (r2_hidden(sK5,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | r2_orders_2(X0,X1,sK5)) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 31.39/4.50    introduced(choice_axiom,[])).
% 31.39/4.50  
% 31.39/4.50  fof(f37,plain,(
% 31.39/4.50    ( ! [X0] : (? [X1] : (? [X2] : ((~r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | ~r2_orders_2(X0,X1,X2)) & (r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | r2_orders_2(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : ((~r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),sK4))) | ~r2_orders_2(X0,sK4,X2)) & (r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),sK4))) | r2_orders_2(X0,sK4,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 31.39/4.50    introduced(choice_axiom,[])).
% 31.39/4.50  
% 31.39/4.50  fof(f36,plain,(
% 31.39/4.50    ? [X0] : (? [X1] : (? [X2] : ((~r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | ~r2_orders_2(X0,X1,X2)) & (r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | r2_orders_2(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r2_hidden(X2,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X1))) | ~r2_orders_2(sK3,X1,X2)) & (r2_hidden(X2,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X1))) | r2_orders_2(sK3,X1,X2)) & m1_subset_1(X2,u1_struct_0(sK3))) & m1_subset_1(X1,u1_struct_0(sK3))) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3))),
% 31.39/4.50    introduced(choice_axiom,[])).
% 31.39/4.50  
% 31.39/4.50  fof(f39,plain,(
% 31.39/4.50    (((~r2_hidden(sK5,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) | ~r2_orders_2(sK3,sK4,sK5)) & (r2_hidden(sK5,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) | r2_orders_2(sK3,sK4,sK5)) & m1_subset_1(sK5,u1_struct_0(sK3))) & m1_subset_1(sK4,u1_struct_0(sK3))) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3)),
% 31.39/4.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f35,f38,f37,f36])).
% 31.39/4.50  
% 31.39/4.50  fof(f63,plain,(
% 31.39/4.50    m1_subset_1(sK4,u1_struct_0(sK3))),
% 31.39/4.50    inference(cnf_transformation,[],[f39])).
% 31.39/4.50  
% 31.39/4.50  fof(f8,axiom,(
% 31.39/4.50    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 31.39/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.39/4.50  
% 31.39/4.50  fof(f20,plain,(
% 31.39/4.50    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 31.39/4.50    inference(ennf_transformation,[],[f8])).
% 31.39/4.50  
% 31.39/4.50  fof(f21,plain,(
% 31.39/4.50    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 31.39/4.50    inference(flattening,[],[f20])).
% 31.39/4.50  
% 31.39/4.50  fof(f57,plain,(
% 31.39/4.50    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 31.39/4.50    inference(cnf_transformation,[],[f21])).
% 31.39/4.50  
% 31.39/4.50  fof(f2,axiom,(
% 31.39/4.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 31.39/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.39/4.50  
% 31.39/4.50  fof(f46,plain,(
% 31.39/4.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 31.39/4.50    inference(cnf_transformation,[],[f2])).
% 31.39/4.50  
% 31.39/4.50  fof(f67,plain,(
% 31.39/4.50    ( ! [X0,X1] : (k2_tarski(X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 31.39/4.50    inference(definition_unfolding,[],[f57,f46])).
% 31.39/4.50  
% 31.39/4.50  fof(f58,plain,(
% 31.39/4.50    ~v2_struct_0(sK3)),
% 31.39/4.50    inference(cnf_transformation,[],[f39])).
% 31.39/4.50  
% 31.39/4.50  fof(f62,plain,(
% 31.39/4.50    l1_orders_2(sK3)),
% 31.39/4.50    inference(cnf_transformation,[],[f39])).
% 31.39/4.50  
% 31.39/4.50  fof(f6,axiom,(
% 31.39/4.50    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 31.39/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.39/4.50  
% 31.39/4.50  fof(f17,plain,(
% 31.39/4.50    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 31.39/4.50    inference(ennf_transformation,[],[f6])).
% 31.39/4.50  
% 31.39/4.50  fof(f50,plain,(
% 31.39/4.50    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 31.39/4.50    inference(cnf_transformation,[],[f17])).
% 31.39/4.50  
% 31.39/4.50  fof(f3,axiom,(
% 31.39/4.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 31.39/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.39/4.50  
% 31.39/4.50  fof(f11,plain,(
% 31.39/4.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 31.39/4.50    inference(ennf_transformation,[],[f3])).
% 31.39/4.50  
% 31.39/4.50  fof(f12,plain,(
% 31.39/4.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 31.39/4.50    inference(flattening,[],[f11])).
% 31.39/4.50  
% 31.39/4.50  fof(f47,plain,(
% 31.39/4.50    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 31.39/4.50    inference(cnf_transformation,[],[f12])).
% 31.39/4.50  
% 31.39/4.50  fof(f65,plain,(
% 31.39/4.50    r2_hidden(sK5,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) | r2_orders_2(sK3,sK4,sK5)),
% 31.39/4.50    inference(cnf_transformation,[],[f39])).
% 31.39/4.50  
% 31.39/4.50  fof(f59,plain,(
% 31.39/4.50    v3_orders_2(sK3)),
% 31.39/4.50    inference(cnf_transformation,[],[f39])).
% 31.39/4.50  
% 31.39/4.50  fof(f60,plain,(
% 31.39/4.50    v4_orders_2(sK3)),
% 31.39/4.50    inference(cnf_transformation,[],[f39])).
% 31.39/4.50  
% 31.39/4.50  fof(f61,plain,(
% 31.39/4.50    v5_orders_2(sK3)),
% 31.39/4.50    inference(cnf_transformation,[],[f39])).
% 31.39/4.50  
% 31.39/4.50  fof(f64,plain,(
% 31.39/4.50    m1_subset_1(sK5,u1_struct_0(sK3))),
% 31.39/4.50    inference(cnf_transformation,[],[f39])).
% 31.39/4.50  
% 31.39/4.50  fof(f66,plain,(
% 31.39/4.50    ~r2_hidden(sK5,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) | ~r2_orders_2(sK3,sK4,sK5)),
% 31.39/4.50    inference(cnf_transformation,[],[f39])).
% 31.39/4.50  
% 31.39/4.50  fof(f5,axiom,(
% 31.39/4.50    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 31.39/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.39/4.50  
% 31.39/4.50  fof(f15,plain,(
% 31.39/4.50    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 31.39/4.50    inference(ennf_transformation,[],[f5])).
% 31.39/4.50  
% 31.39/4.50  fof(f16,plain,(
% 31.39/4.50    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 31.39/4.50    inference(flattening,[],[f15])).
% 31.39/4.50  
% 31.39/4.50  fof(f49,plain,(
% 31.39/4.50    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 31.39/4.50    inference(cnf_transformation,[],[f16])).
% 31.39/4.50  
% 31.39/4.50  fof(f7,axiom,(
% 31.39/4.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X4,X3))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 31.39/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.39/4.50  
% 31.39/4.50  fof(f18,plain,(
% 31.39/4.50    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 31.39/4.50    inference(ennf_transformation,[],[f7])).
% 31.39/4.50  
% 31.39/4.50  fof(f19,plain,(
% 31.39/4.50    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 31.39/4.50    inference(flattening,[],[f18])).
% 31.39/4.50  
% 31.39/4.50  fof(f29,plain,(
% 31.39/4.50    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 31.39/4.50    inference(nnf_transformation,[],[f19])).
% 31.39/4.50  
% 31.39/4.50  fof(f30,plain,(
% 31.39/4.50    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (! [X6] : (r2_orders_2(X1,X6,X5) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 31.39/4.50    inference(rectify,[],[f29])).
% 31.39/4.50  
% 31.39/4.50  fof(f32,plain,(
% 31.39/4.50    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X1,X6,X5) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (! [X6] : (r2_orders_2(X1,X6,sK2(X0,X1,X2)) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))))),
% 31.39/4.50    introduced(choice_axiom,[])).
% 31.39/4.50  
% 31.39/4.50  fof(f31,plain,(
% 31.39/4.50    ! [X3,X2,X1] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) => (~r2_orders_2(X1,sK1(X1,X2,X3),X3) & r2_hidden(sK1(X1,X2,X3),X2) & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1))))),
% 31.39/4.50    introduced(choice_axiom,[])).
% 31.39/4.50  
% 31.39/4.50  fof(f33,plain,(
% 31.39/4.50    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : ((~r2_orders_2(X1,sK1(X1,X2,X3),X3) & r2_hidden(sK1(X1,X2,X3),X2) & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((! [X6] : (r2_orders_2(X1,X6,sK2(X0,X1,X2)) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 31.39/4.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f30,f32,f31])).
% 31.39/4.50  
% 31.39/4.50  fof(f52,plain,(
% 31.39/4.50    ( ! [X2,X0,X1] : (sK2(X0,X1,X2) = X0 | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 31.39/4.50    inference(cnf_transformation,[],[f33])).
% 31.39/4.50  
% 31.39/4.50  fof(f4,axiom,(
% 31.39/4.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)))),
% 31.39/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.39/4.50  
% 31.39/4.50  fof(f13,plain,(
% 31.39/4.50    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 31.39/4.50    inference(ennf_transformation,[],[f4])).
% 31.39/4.50  
% 31.39/4.50  fof(f14,plain,(
% 31.39/4.50    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 31.39/4.50    inference(flattening,[],[f13])).
% 31.39/4.50  
% 31.39/4.50  fof(f48,plain,(
% 31.39/4.50    ( ! [X0,X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 31.39/4.50    inference(cnf_transformation,[],[f14])).
% 31.39/4.50  
% 31.39/4.50  fof(f55,plain,(
% 31.39/4.50    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_0_orders_2(X1,X2)) | r2_hidden(sK1(X1,X2,X3),X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 31.39/4.50    inference(cnf_transformation,[],[f33])).
% 31.39/4.50  
% 31.39/4.50  fof(f74,plain,(
% 31.39/4.50    ( ! [X2,X3,X1] : (r2_hidden(X3,a_2_0_orders_2(X1,X2)) | r2_hidden(sK1(X1,X2,X3),X2) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 31.39/4.50    inference(equality_resolution,[],[f55])).
% 31.39/4.50  
% 31.39/4.50  fof(f40,plain,(
% 31.39/4.50    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 31.39/4.50    inference(cnf_transformation,[],[f28])).
% 31.39/4.50  
% 31.39/4.50  fof(f72,plain,(
% 31.39/4.50    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k2_tarski(X0,X1))) )),
% 31.39/4.50    inference(equality_resolution,[],[f40])).
% 31.39/4.50  
% 31.39/4.50  fof(f53,plain,(
% 31.39/4.50    ( ! [X6,X2,X0,X1] : (r2_orders_2(X1,X6,sK2(X0,X1,X2)) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 31.39/4.50    inference(cnf_transformation,[],[f33])).
% 31.39/4.50  
% 31.39/4.50  fof(f56,plain,(
% 31.39/4.50    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ~r2_orders_2(X1,sK1(X1,X2,X3),X3) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 31.39/4.50    inference(cnf_transformation,[],[f33])).
% 31.39/4.50  
% 31.39/4.50  fof(f73,plain,(
% 31.39/4.50    ( ! [X2,X3,X1] : (r2_hidden(X3,a_2_0_orders_2(X1,X2)) | ~r2_orders_2(X1,sK1(X1,X2,X3),X3) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 31.39/4.50    inference(equality_resolution,[],[f56])).
% 31.39/4.50  
% 31.39/4.50  cnf(c_3,plain,
% 31.39/4.50      ( r2_hidden(X0,k2_tarski(X1,X0)) ),
% 31.39/4.50      inference(cnf_transformation,[],[f69]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_101956,plain,
% 31.39/4.50      ( r2_hidden(X0,k2_tarski(X1,X0)) = iProver_top ),
% 31.39/4.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_20,negated_conjecture,
% 31.39/4.50      ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 31.39/4.50      inference(cnf_transformation,[],[f63]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_101945,plain,
% 31.39/4.50      ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
% 31.39/4.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_16,plain,
% 31.39/4.50      ( ~ m1_subset_1(X0,X1)
% 31.39/4.50      | v1_xboole_0(X1)
% 31.39/4.50      | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
% 31.39/4.50      inference(cnf_transformation,[],[f67]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_101947,plain,
% 31.39/4.50      ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
% 31.39/4.50      | m1_subset_1(X1,X0) != iProver_top
% 31.39/4.50      | v1_xboole_0(X0) = iProver_top ),
% 31.39/4.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_102978,plain,
% 31.39/4.50      ( k6_domain_1(u1_struct_0(sK3),sK4) = k2_tarski(sK4,sK4)
% 31.39/4.50      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 31.39/4.50      inference(superposition,[status(thm)],[c_101945,c_101947]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_25,negated_conjecture,
% 31.39/4.50      ( ~ v2_struct_0(sK3) ),
% 31.39/4.50      inference(cnf_transformation,[],[f58]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_26,plain,
% 31.39/4.50      ( v2_struct_0(sK3) != iProver_top ),
% 31.39/4.50      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_21,negated_conjecture,
% 31.39/4.50      ( l1_orders_2(sK3) ),
% 31.39/4.50      inference(cnf_transformation,[],[f62]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_30,plain,
% 31.39/4.50      ( l1_orders_2(sK3) = iProver_top ),
% 31.39/4.50      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_9,plain,
% 31.39/4.50      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 31.39/4.50      inference(cnf_transformation,[],[f50]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_56,plain,
% 31.39/4.50      ( l1_orders_2(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 31.39/4.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_58,plain,
% 31.39/4.50      ( l1_orders_2(sK3) != iProver_top
% 31.39/4.50      | l1_struct_0(sK3) = iProver_top ),
% 31.39/4.50      inference(instantiation,[status(thm)],[c_56]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_6,plain,
% 31.39/4.50      ( v2_struct_0(X0)
% 31.39/4.50      | ~ l1_struct_0(X0)
% 31.39/4.50      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 31.39/4.50      inference(cnf_transformation,[],[f47]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_65,plain,
% 31.39/4.50      ( v2_struct_0(X0) = iProver_top
% 31.39/4.50      | l1_struct_0(X0) != iProver_top
% 31.39/4.50      | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
% 31.39/4.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_67,plain,
% 31.39/4.50      ( v2_struct_0(sK3) = iProver_top
% 31.39/4.50      | l1_struct_0(sK3) != iProver_top
% 31.39/4.50      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 31.39/4.50      inference(instantiation,[status(thm)],[c_65]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_17706,plain,
% 31.39/4.50      ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
% 31.39/4.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_17710,plain,
% 31.39/4.50      ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
% 31.39/4.50      | m1_subset_1(X1,X0) != iProver_top
% 31.39/4.50      | v1_xboole_0(X0) = iProver_top ),
% 31.39/4.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_18522,plain,
% 31.39/4.50      ( k6_domain_1(u1_struct_0(sK3),sK4) = k2_tarski(sK4,sK4)
% 31.39/4.50      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 31.39/4.50      inference(superposition,[status(thm)],[c_17706,c_17710]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_103087,plain,
% 31.39/4.50      ( k6_domain_1(u1_struct_0(sK3),sK4) = k2_tarski(sK4,sK4) ),
% 31.39/4.50      inference(global_propositional_subsumption,
% 31.39/4.50                [status(thm)],
% 31.39/4.50                [c_102978,c_26,c_30,c_58,c_67,c_18522]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_18,negated_conjecture,
% 31.39/4.50      ( r2_orders_2(sK3,sK4,sK5)
% 31.39/4.50      | r2_hidden(sK5,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) ),
% 31.39/4.50      inference(cnf_transformation,[],[f65]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_24,negated_conjecture,
% 31.39/4.50      ( v3_orders_2(sK3) ),
% 31.39/4.50      inference(cnf_transformation,[],[f59]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_23,negated_conjecture,
% 31.39/4.50      ( v4_orders_2(sK3) ),
% 31.39/4.50      inference(cnf_transformation,[],[f60]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_22,negated_conjecture,
% 31.39/4.50      ( v5_orders_2(sK3) ),
% 31.39/4.50      inference(cnf_transformation,[],[f61]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_19,negated_conjecture,
% 31.39/4.50      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 31.39/4.50      inference(cnf_transformation,[],[f64]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_57,plain,
% 31.39/4.50      ( ~ l1_orders_2(sK3) | l1_struct_0(sK3) ),
% 31.39/4.50      inference(instantiation,[status(thm)],[c_9]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_66,plain,
% 31.39/4.50      ( v2_struct_0(sK3)
% 31.39/4.50      | ~ l1_struct_0(sK3)
% 31.39/4.50      | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 31.39/4.50      inference(instantiation,[status(thm)],[c_6]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_18675,plain,
% 31.39/4.50      ( k6_domain_1(u1_struct_0(sK3),sK4) = k2_tarski(sK4,sK4) ),
% 31.39/4.50      inference(global_propositional_subsumption,
% 31.39/4.50                [status(thm)],
% 31.39/4.50                [c_18522,c_26,c_30,c_58,c_67]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_17,negated_conjecture,
% 31.39/4.50      ( ~ r2_orders_2(sK3,sK4,sK5)
% 31.39/4.50      | ~ r2_hidden(sK5,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) ),
% 31.39/4.50      inference(cnf_transformation,[],[f66]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_17709,plain,
% 31.39/4.50      ( r2_orders_2(sK3,sK4,sK5) != iProver_top
% 31.39/4.50      | r2_hidden(sK5,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) != iProver_top ),
% 31.39/4.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_18679,plain,
% 31.39/4.50      ( r2_orders_2(sK3,sK4,sK5) != iProver_top
% 31.39/4.50      | r2_hidden(sK5,k1_orders_2(sK3,k2_tarski(sK4,sK4))) != iProver_top ),
% 31.39/4.50      inference(demodulation,[status(thm)],[c_18675,c_17709]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_18689,plain,
% 31.39/4.50      ( ~ r2_orders_2(sK3,sK4,sK5)
% 31.39/4.50      | ~ r2_hidden(sK5,k1_orders_2(sK3,k2_tarski(sK4,sK4))) ),
% 31.39/4.50      inference(predicate_to_equality_rev,[status(thm)],[c_18679]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_21117,plain,
% 31.39/4.50      ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
% 31.39/4.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_21121,plain,
% 31.39/4.50      ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
% 31.39/4.50      | m1_subset_1(X1,X0) != iProver_top
% 31.39/4.50      | v1_xboole_0(X0) = iProver_top ),
% 31.39/4.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_22507,plain,
% 31.39/4.50      ( k6_domain_1(u1_struct_0(sK3),sK4) = k2_tarski(sK4,sK4)
% 31.39/4.50      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 31.39/4.50      inference(superposition,[status(thm)],[c_21117,c_21121]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_22945,plain,
% 31.39/4.50      ( k6_domain_1(u1_struct_0(sK3),sK4) = k2_tarski(sK4,sK4) ),
% 31.39/4.50      inference(global_propositional_subsumption,
% 31.39/4.50                [status(thm)],
% 31.39/4.50                [c_22507,c_26,c_30,c_58,c_67,c_18522]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_8,plain,
% 31.39/4.50      ( ~ m1_subset_1(X0,X1)
% 31.39/4.50      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 31.39/4.50      | v1_xboole_0(X1) ),
% 31.39/4.50      inference(cnf_transformation,[],[f49]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_21123,plain,
% 31.39/4.50      ( m1_subset_1(X0,X1) != iProver_top
% 31.39/4.50      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
% 31.39/4.50      | v1_xboole_0(X1) = iProver_top ),
% 31.39/4.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_22960,plain,
% 31.39/4.50      ( m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 31.39/4.50      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 31.39/4.50      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 31.39/4.50      inference(superposition,[status(thm)],[c_22945,c_21123]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_22961,plain,
% 31.39/4.50      ( m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 31.39/4.50      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 31.39/4.50      | v1_xboole_0(u1_struct_0(sK3)) ),
% 31.39/4.50      inference(predicate_to_equality_rev,[status(thm)],[c_22960]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_60528,plain,
% 31.39/4.50      ( r2_hidden(X0,k2_tarski(X1,X0)) = iProver_top ),
% 31.39/4.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_60513,plain,
% 31.39/4.50      ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
% 31.39/4.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_60517,plain,
% 31.39/4.50      ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
% 31.39/4.50      | m1_subset_1(X1,X0) != iProver_top
% 31.39/4.50      | v1_xboole_0(X0) = iProver_top ),
% 31.39/4.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_61489,plain,
% 31.39/4.50      ( k6_domain_1(u1_struct_0(sK3),sK4) = k2_tarski(sK4,sK4)
% 31.39/4.50      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 31.39/4.50      inference(superposition,[status(thm)],[c_60513,c_60517]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_61595,plain,
% 31.39/4.50      ( k6_domain_1(u1_struct_0(sK3),sK4) = k2_tarski(sK4,sK4) ),
% 31.39/4.50      inference(global_propositional_subsumption,
% 31.39/4.50                [status(thm)],
% 31.39/4.50                [c_61489,c_26,c_30,c_58,c_67,c_18522]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_60515,plain,
% 31.39/4.50      ( r2_orders_2(sK3,sK4,sK5) = iProver_top
% 31.39/4.50      | r2_hidden(sK5,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) = iProver_top ),
% 31.39/4.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_61598,plain,
% 31.39/4.50      ( r2_orders_2(sK3,sK4,sK5) = iProver_top
% 31.39/4.50      | r2_hidden(sK5,k1_orders_2(sK3,k2_tarski(sK4,sK4))) = iProver_top ),
% 31.39/4.50      inference(demodulation,[status(thm)],[c_61595,c_60515]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_60523,plain,
% 31.39/4.50      ( m1_subset_1(X0,X1) != iProver_top
% 31.39/4.50      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
% 31.39/4.50      | v1_xboole_0(X1) = iProver_top ),
% 31.39/4.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_61752,plain,
% 31.39/4.50      ( m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 31.39/4.50      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 31.39/4.50      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 31.39/4.50      inference(superposition,[status(thm)],[c_61595,c_60523]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_31,plain,
% 31.39/4.50      ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
% 31.39/4.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_62303,plain,
% 31.39/4.50      ( m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 31.39/4.50      inference(global_propositional_subsumption,
% 31.39/4.50                [status(thm)],
% 31.39/4.50                [c_61752,c_26,c_30,c_31,c_58,c_67,c_22960]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_14,plain,
% 31.39/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.39/4.50      | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
% 31.39/4.50      | ~ v3_orders_2(X1)
% 31.39/4.50      | ~ v4_orders_2(X1)
% 31.39/4.50      | ~ v5_orders_2(X1)
% 31.39/4.50      | ~ l1_orders_2(X1)
% 31.39/4.50      | v2_struct_0(X1)
% 31.39/4.50      | sK2(X2,X1,X0) = X2 ),
% 31.39/4.50      inference(cnf_transformation,[],[f52]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_60518,plain,
% 31.39/4.50      ( sK2(X0,X1,X2) = X0
% 31.39/4.50      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 31.39/4.50      | r2_hidden(X0,a_2_0_orders_2(X1,X2)) != iProver_top
% 31.39/4.50      | v3_orders_2(X1) != iProver_top
% 31.39/4.50      | v4_orders_2(X1) != iProver_top
% 31.39/4.50      | v5_orders_2(X1) != iProver_top
% 31.39/4.50      | l1_orders_2(X1) != iProver_top
% 31.39/4.50      | v2_struct_0(X1) = iProver_top ),
% 31.39/4.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_62310,plain,
% 31.39/4.50      ( sK2(X0,sK3,k2_tarski(sK4,sK4)) = X0
% 31.39/4.50      | r2_hidden(X0,a_2_0_orders_2(sK3,k2_tarski(sK4,sK4))) != iProver_top
% 31.39/4.50      | v3_orders_2(sK3) != iProver_top
% 31.39/4.50      | v4_orders_2(sK3) != iProver_top
% 31.39/4.50      | v5_orders_2(sK3) != iProver_top
% 31.39/4.50      | l1_orders_2(sK3) != iProver_top
% 31.39/4.50      | v2_struct_0(sK3) = iProver_top ),
% 31.39/4.50      inference(superposition,[status(thm)],[c_62303,c_60518]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_27,plain,
% 31.39/4.50      ( v3_orders_2(sK3) = iProver_top ),
% 31.39/4.50      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_28,plain,
% 31.39/4.50      ( v4_orders_2(sK3) = iProver_top ),
% 31.39/4.50      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_29,plain,
% 31.39/4.50      ( v5_orders_2(sK3) = iProver_top ),
% 31.39/4.50      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_63106,plain,
% 31.39/4.50      ( r2_hidden(X0,a_2_0_orders_2(sK3,k2_tarski(sK4,sK4))) != iProver_top
% 31.39/4.50      | sK2(X0,sK3,k2_tarski(sK4,sK4)) = X0 ),
% 31.39/4.50      inference(global_propositional_subsumption,
% 31.39/4.50                [status(thm)],
% 31.39/4.50                [c_62310,c_26,c_27,c_28,c_29,c_30]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_63107,plain,
% 31.39/4.50      ( sK2(X0,sK3,k2_tarski(sK4,sK4)) = X0
% 31.39/4.50      | r2_hidden(X0,a_2_0_orders_2(sK3,k2_tarski(sK4,sK4))) != iProver_top ),
% 31.39/4.50      inference(renaming,[status(thm)],[c_63106]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_7,plain,
% 31.39/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.39/4.50      | ~ v3_orders_2(X1)
% 31.39/4.50      | ~ v4_orders_2(X1)
% 31.39/4.50      | ~ v5_orders_2(X1)
% 31.39/4.50      | ~ l1_orders_2(X1)
% 31.39/4.50      | v2_struct_0(X1)
% 31.39/4.50      | a_2_0_orders_2(X1,X0) = k1_orders_2(X1,X0) ),
% 31.39/4.50      inference(cnf_transformation,[],[f48]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_60524,plain,
% 31.39/4.50      ( a_2_0_orders_2(X0,X1) = k1_orders_2(X0,X1)
% 31.39/4.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 31.39/4.50      | v3_orders_2(X0) != iProver_top
% 31.39/4.50      | v4_orders_2(X0) != iProver_top
% 31.39/4.50      | v5_orders_2(X0) != iProver_top
% 31.39/4.50      | l1_orders_2(X0) != iProver_top
% 31.39/4.50      | v2_struct_0(X0) = iProver_top ),
% 31.39/4.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_62308,plain,
% 31.39/4.50      ( a_2_0_orders_2(sK3,k2_tarski(sK4,sK4)) = k1_orders_2(sK3,k2_tarski(sK4,sK4))
% 31.39/4.50      | v3_orders_2(sK3) != iProver_top
% 31.39/4.50      | v4_orders_2(sK3) != iProver_top
% 31.39/4.50      | v5_orders_2(sK3) != iProver_top
% 31.39/4.50      | l1_orders_2(sK3) != iProver_top
% 31.39/4.50      | v2_struct_0(sK3) = iProver_top ),
% 31.39/4.50      inference(superposition,[status(thm)],[c_62303,c_60524]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_23367,plain,
% 31.39/4.50      ( m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 31.39/4.50      inference(global_propositional_subsumption,
% 31.39/4.50                [status(thm)],
% 31.39/4.50                [c_22960,c_26,c_30,c_31,c_58,c_67]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_21124,plain,
% 31.39/4.50      ( a_2_0_orders_2(X0,X1) = k1_orders_2(X0,X1)
% 31.39/4.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 31.39/4.50      | v3_orders_2(X0) != iProver_top
% 31.39/4.50      | v4_orders_2(X0) != iProver_top
% 31.39/4.50      | v5_orders_2(X0) != iProver_top
% 31.39/4.50      | l1_orders_2(X0) != iProver_top
% 31.39/4.50      | v2_struct_0(X0) = iProver_top ),
% 31.39/4.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_23372,plain,
% 31.39/4.50      ( a_2_0_orders_2(sK3,k2_tarski(sK4,sK4)) = k1_orders_2(sK3,k2_tarski(sK4,sK4))
% 31.39/4.50      | v3_orders_2(sK3) != iProver_top
% 31.39/4.50      | v4_orders_2(sK3) != iProver_top
% 31.39/4.50      | v5_orders_2(sK3) != iProver_top
% 31.39/4.50      | l1_orders_2(sK3) != iProver_top
% 31.39/4.50      | v2_struct_0(sK3) = iProver_top ),
% 31.39/4.50      inference(superposition,[status(thm)],[c_23367,c_21124]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_62733,plain,
% 31.39/4.50      ( a_2_0_orders_2(sK3,k2_tarski(sK4,sK4)) = k1_orders_2(sK3,k2_tarski(sK4,sK4)) ),
% 31.39/4.50      inference(global_propositional_subsumption,
% 31.39/4.50                [status(thm)],
% 31.39/4.50                [c_62308,c_26,c_27,c_28,c_29,c_30,c_23372]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_63112,plain,
% 31.39/4.50      ( sK2(X0,sK3,k2_tarski(sK4,sK4)) = X0
% 31.39/4.50      | r2_hidden(X0,k1_orders_2(sK3,k2_tarski(sK4,sK4))) != iProver_top ),
% 31.39/4.50      inference(light_normalisation,[status(thm)],[c_63107,c_62733]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_63119,plain,
% 31.39/4.50      ( sK2(sK5,sK3,k2_tarski(sK4,sK4)) = sK5
% 31.39/4.50      | r2_orders_2(sK3,sK4,sK5) = iProver_top ),
% 31.39/4.50      inference(superposition,[status(thm)],[c_61598,c_63112]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_11,plain,
% 31.39/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.39/4.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 31.39/4.50      | r2_hidden(X2,a_2_0_orders_2(X1,X0))
% 31.39/4.50      | r2_hidden(sK1(X1,X0,X2),X0)
% 31.39/4.50      | ~ v3_orders_2(X1)
% 31.39/4.50      | ~ v4_orders_2(X1)
% 31.39/4.50      | ~ v5_orders_2(X1)
% 31.39/4.50      | ~ l1_orders_2(X1)
% 31.39/4.50      | v2_struct_0(X1) ),
% 31.39/4.50      inference(cnf_transformation,[],[f74]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_60520,plain,
% 31.39/4.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 31.39/4.50      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 31.39/4.50      | r2_hidden(X2,a_2_0_orders_2(X1,X0)) = iProver_top
% 31.39/4.50      | r2_hidden(sK1(X1,X0,X2),X0) = iProver_top
% 31.39/4.50      | v3_orders_2(X1) != iProver_top
% 31.39/4.50      | v4_orders_2(X1) != iProver_top
% 31.39/4.50      | v5_orders_2(X1) != iProver_top
% 31.39/4.50      | l1_orders_2(X1) != iProver_top
% 31.39/4.50      | v2_struct_0(X1) = iProver_top ),
% 31.39/4.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_5,plain,
% 31.39/4.50      ( ~ r2_hidden(X0,k2_tarski(X1,X2)) | X0 = X1 | X0 = X2 ),
% 31.39/4.50      inference(cnf_transformation,[],[f72]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_60526,plain,
% 31.39/4.50      ( X0 = X1
% 31.39/4.50      | X0 = X2
% 31.39/4.50      | r2_hidden(X0,k2_tarski(X1,X2)) != iProver_top ),
% 31.39/4.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_61943,plain,
% 31.39/4.50      ( sK1(X0,k2_tarski(X1,X2),X3) = X1
% 31.39/4.50      | sK1(X0,k2_tarski(X1,X2),X3) = X2
% 31.39/4.50      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 31.39/4.50      | m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 31.39/4.50      | r2_hidden(X3,a_2_0_orders_2(X0,k2_tarski(X1,X2))) = iProver_top
% 31.39/4.50      | v3_orders_2(X0) != iProver_top
% 31.39/4.50      | v4_orders_2(X0) != iProver_top
% 31.39/4.50      | v5_orders_2(X0) != iProver_top
% 31.39/4.50      | l1_orders_2(X0) != iProver_top
% 31.39/4.50      | v2_struct_0(X0) = iProver_top ),
% 31.39/4.50      inference(superposition,[status(thm)],[c_60520,c_60526]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_64594,plain,
% 31.39/4.50      ( sK1(sK3,k2_tarski(sK4,sK4),X0) = sK4
% 31.39/4.50      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 31.39/4.50      | r2_hidden(X0,a_2_0_orders_2(sK3,k2_tarski(sK4,sK4))) = iProver_top
% 31.39/4.50      | v3_orders_2(sK3) != iProver_top
% 31.39/4.50      | v4_orders_2(sK3) != iProver_top
% 31.39/4.50      | v5_orders_2(sK3) != iProver_top
% 31.39/4.50      | l1_orders_2(sK3) != iProver_top
% 31.39/4.50      | v2_struct_0(sK3) = iProver_top ),
% 31.39/4.50      inference(superposition,[status(thm)],[c_62303,c_61943]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_64603,plain,
% 31.39/4.50      ( sK1(sK3,k2_tarski(sK4,sK4),X0) = sK4
% 31.39/4.50      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 31.39/4.50      | r2_hidden(X0,k1_orders_2(sK3,k2_tarski(sK4,sK4))) = iProver_top
% 31.39/4.50      | v3_orders_2(sK3) != iProver_top
% 31.39/4.50      | v4_orders_2(sK3) != iProver_top
% 31.39/4.50      | v5_orders_2(sK3) != iProver_top
% 31.39/4.50      | l1_orders_2(sK3) != iProver_top
% 31.39/4.50      | v2_struct_0(sK3) = iProver_top ),
% 31.39/4.50      inference(light_normalisation,[status(thm)],[c_64594,c_62733]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_66089,plain,
% 31.39/4.50      ( r2_hidden(X0,k1_orders_2(sK3,k2_tarski(sK4,sK4))) = iProver_top
% 31.39/4.50      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 31.39/4.50      | sK1(sK3,k2_tarski(sK4,sK4),X0) = sK4 ),
% 31.39/4.50      inference(global_propositional_subsumption,
% 31.39/4.50                [status(thm)],
% 31.39/4.50                [c_64603,c_26,c_27,c_28,c_29,c_30]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_66090,plain,
% 31.39/4.50      ( sK1(sK3,k2_tarski(sK4,sK4),X0) = sK4
% 31.39/4.50      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 31.39/4.50      | r2_hidden(X0,k1_orders_2(sK3,k2_tarski(sK4,sK4))) = iProver_top ),
% 31.39/4.50      inference(renaming,[status(thm)],[c_66089]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_60516,plain,
% 31.39/4.50      ( r2_orders_2(sK3,sK4,sK5) != iProver_top
% 31.39/4.50      | r2_hidden(sK5,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) != iProver_top ),
% 31.39/4.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_61599,plain,
% 31.39/4.50      ( r2_orders_2(sK3,sK4,sK5) != iProver_top
% 31.39/4.50      | r2_hidden(sK5,k1_orders_2(sK3,k2_tarski(sK4,sK4))) != iProver_top ),
% 31.39/4.50      inference(demodulation,[status(thm)],[c_61595,c_60516]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_66098,plain,
% 31.39/4.50      ( sK1(sK3,k2_tarski(sK4,sK4),sK5) = sK4
% 31.39/4.50      | r2_orders_2(sK3,sK4,sK5) != iProver_top
% 31.39/4.50      | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top ),
% 31.39/4.50      inference(superposition,[status(thm)],[c_66090,c_61599]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_32,plain,
% 31.39/4.50      ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
% 31.39/4.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_66117,plain,
% 31.39/4.50      ( r2_orders_2(sK3,sK4,sK5) != iProver_top
% 31.39/4.50      | sK1(sK3,k2_tarski(sK4,sK4),sK5) = sK4 ),
% 31.39/4.50      inference(global_propositional_subsumption,
% 31.39/4.50                [status(thm)],
% 31.39/4.50                [c_66098,c_32]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_66118,plain,
% 31.39/4.50      ( sK1(sK3,k2_tarski(sK4,sK4),sK5) = sK4
% 31.39/4.50      | r2_orders_2(sK3,sK4,sK5) != iProver_top ),
% 31.39/4.50      inference(renaming,[status(thm)],[c_66117]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_66123,plain,
% 31.39/4.50      ( sK2(sK5,sK3,k2_tarski(sK4,sK4)) = sK5
% 31.39/4.50      | sK1(sK3,k2_tarski(sK4,sK4),sK5) = sK4 ),
% 31.39/4.50      inference(superposition,[status(thm)],[c_63119,c_66118]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_13,plain,
% 31.39/4.50      ( r2_orders_2(X0,X1,sK2(X2,X0,X3))
% 31.39/4.50      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 31.39/4.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.39/4.50      | ~ r2_hidden(X1,X3)
% 31.39/4.50      | ~ r2_hidden(X2,a_2_0_orders_2(X0,X3))
% 31.39/4.50      | ~ v3_orders_2(X0)
% 31.39/4.50      | ~ v4_orders_2(X0)
% 31.39/4.50      | ~ v5_orders_2(X0)
% 31.39/4.50      | ~ l1_orders_2(X0)
% 31.39/4.50      | v2_struct_0(X0) ),
% 31.39/4.50      inference(cnf_transformation,[],[f53]) ).
% 31.39/4.50  
% 31.39/4.50  cnf(c_60519,plain,
% 31.39/4.50      ( r2_orders_2(X0,X1,sK2(X2,X0,X3)) = iProver_top
% 31.39/4.50      | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 31.39/4.50      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 31.39/4.50      | r2_hidden(X1,X3) != iProver_top
% 31.39/4.50      | r2_hidden(X2,a_2_0_orders_2(X0,X3)) != iProver_top
% 31.39/4.51      | v3_orders_2(X0) != iProver_top
% 31.39/4.51      | v4_orders_2(X0) != iProver_top
% 31.39/4.51      | v5_orders_2(X0) != iProver_top
% 31.39/4.51      | l1_orders_2(X0) != iProver_top
% 31.39/4.51      | v2_struct_0(X0) = iProver_top ),
% 31.39/4.51      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 31.39/4.51  
% 31.39/4.51  cnf(c_66382,plain,
% 31.39/4.51      ( sK1(sK3,k2_tarski(sK4,sK4),sK5) = sK4
% 31.39/4.51      | r2_orders_2(sK3,X0,sK5) = iProver_top
% 31.39/4.51      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 31.39/4.51      | m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 31.39/4.51      | r2_hidden(X0,k2_tarski(sK4,sK4)) != iProver_top
% 31.39/4.51      | r2_hidden(sK5,a_2_0_orders_2(sK3,k2_tarski(sK4,sK4))) != iProver_top
% 31.39/4.51      | v3_orders_2(sK3) != iProver_top
% 31.39/4.51      | v4_orders_2(sK3) != iProver_top
% 31.39/4.51      | v5_orders_2(sK3) != iProver_top
% 31.39/4.51      | l1_orders_2(sK3) != iProver_top
% 31.39/4.51      | v2_struct_0(sK3) = iProver_top ),
% 31.39/4.51      inference(superposition,[status(thm)],[c_66123,c_60519]) ).
% 31.39/4.51  
% 31.39/4.51  cnf(c_66422,plain,
% 31.39/4.51      ( sK1(sK3,k2_tarski(sK4,sK4),sK5) = sK4
% 31.39/4.51      | r2_orders_2(sK3,X0,sK5) = iProver_top
% 31.39/4.51      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 31.39/4.51      | m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 31.39/4.51      | r2_hidden(X0,k2_tarski(sK4,sK4)) != iProver_top
% 31.39/4.51      | r2_hidden(sK5,k1_orders_2(sK3,k2_tarski(sK4,sK4))) != iProver_top
% 31.39/4.51      | v3_orders_2(sK3) != iProver_top
% 31.39/4.51      | v4_orders_2(sK3) != iProver_top
% 31.39/4.51      | v5_orders_2(sK3) != iProver_top
% 31.39/4.51      | l1_orders_2(sK3) != iProver_top
% 31.39/4.51      | v2_struct_0(sK3) = iProver_top ),
% 31.39/4.51      inference(light_normalisation,[status(thm)],[c_66382,c_62733]) ).
% 31.39/4.51  
% 31.39/4.51  cnf(c_304,plain,
% 31.39/4.51      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 31.39/4.51      theory(equality) ).
% 31.39/4.51  
% 31.39/4.51  cnf(c_7762,plain,
% 31.39/4.51      ( m1_subset_1(X0,X1)
% 31.39/4.51      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 31.39/4.51      | X1 != u1_struct_0(sK3)
% 31.39/4.51      | X0 != sK4 ),
% 31.39/4.51      inference(instantiation,[status(thm)],[c_304]) ).
% 31.39/4.51  
% 31.39/4.51  cnf(c_7932,plain,
% 31.39/4.51      ( m1_subset_1(X0,u1_struct_0(sK3))
% 31.39/4.51      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 31.39/4.51      | X0 != sK4
% 31.39/4.51      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 31.39/4.51      inference(instantiation,[status(thm)],[c_7762]) ).
% 31.39/4.51  
% 31.39/4.51  cnf(c_7933,plain,
% 31.39/4.51      ( m1_subset_1(X0,u1_struct_0(sK3))
% 31.39/4.51      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 31.39/4.51      | X0 != sK4 ),
% 31.39/4.51      inference(equality_resolution_simp,[status(thm)],[c_7932]) ).
% 31.39/4.51  
% 31.39/4.51  cnf(c_7934,plain,
% 31.39/4.51      ( X0 != sK4
% 31.39/4.51      | m1_subset_1(X0,u1_struct_0(sK3)) = iProver_top
% 31.39/4.51      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 31.39/4.51      inference(predicate_to_equality,[status(thm)],[c_7933]) ).
% 31.39/4.51  
% 31.39/4.51  cnf(c_17708,plain,
% 31.39/4.51      ( r2_orders_2(sK3,sK4,sK5) = iProver_top
% 31.39/4.51      | r2_hidden(sK5,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) = iProver_top ),
% 31.39/4.51      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 31.39/4.51  
% 31.39/4.51  cnf(c_18678,plain,
% 31.39/4.51      ( r2_orders_2(sK3,sK4,sK5) = iProver_top
% 31.39/4.51      | r2_hidden(sK5,k1_orders_2(sK3,k2_tarski(sK4,sK4))) = iProver_top ),
% 31.39/4.51      inference(demodulation,[status(thm)],[c_18675,c_17708]) ).
% 31.39/4.51  
% 31.39/4.51  cnf(c_32144,plain,
% 31.39/4.51      ( ~ r2_hidden(X0,k2_tarski(X1,sK4)) | X0 = X1 | X0 = sK4 ),
% 31.39/4.51      inference(instantiation,[status(thm)],[c_5]) ).
% 31.39/4.51  
% 31.39/4.51  cnf(c_38629,plain,
% 31.39/4.51      ( ~ r2_hidden(X0,k2_tarski(sK4,sK4)) | X0 = sK4 ),
% 31.39/4.51      inference(instantiation,[status(thm)],[c_32144]) ).
% 31.39/4.51  
% 31.39/4.51  cnf(c_38630,plain,
% 31.39/4.51      ( X0 = sK4 | r2_hidden(X0,k2_tarski(sK4,sK4)) != iProver_top ),
% 31.39/4.51      inference(predicate_to_equality,[status(thm)],[c_38629]) ).
% 31.39/4.51  
% 31.39/4.51  cnf(c_73425,plain,
% 31.39/4.51      ( sK1(sK3,k2_tarski(sK4,sK4),sK5) = sK4
% 31.39/4.51      | r2_orders_2(sK3,X0,sK5) = iProver_top
% 31.39/4.51      | r2_hidden(X0,k2_tarski(sK4,sK4)) != iProver_top ),
% 31.39/4.51      inference(global_propositional_subsumption,
% 31.39/4.51                [status(thm)],
% 31.39/4.51                [c_66422,c_26,c_27,c_28,c_29,c_30,c_31,c_58,c_67,c_7934,
% 31.39/4.51                 c_18678,c_22960,c_38630,c_66118]) ).
% 31.39/4.51  
% 31.39/4.51  cnf(c_73434,plain,
% 31.39/4.51      ( sK1(sK3,k2_tarski(sK4,sK4),sK5) = sK4
% 31.39/4.51      | r2_orders_2(sK3,sK4,sK5) = iProver_top ),
% 31.39/4.51      inference(superposition,[status(thm)],[c_60528,c_73425]) ).
% 31.39/4.51  
% 31.39/4.51  cnf(c_73739,plain,
% 31.39/4.51      ( sK1(sK3,k2_tarski(sK4,sK4),sK5) = sK4 ),
% 31.39/4.51      inference(global_propositional_subsumption,
% 31.39/4.51                [status(thm)],
% 31.39/4.51                [c_73434,c_66118]) ).
% 31.39/4.51  
% 31.39/4.51  cnf(c_10,plain,
% 31.39/4.51      ( ~ r2_orders_2(X0,sK1(X0,X1,X2),X2)
% 31.39/4.51      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 31.39/4.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 31.39/4.51      | r2_hidden(X2,a_2_0_orders_2(X0,X1))
% 31.39/4.51      | ~ v3_orders_2(X0)
% 31.39/4.51      | ~ v4_orders_2(X0)
% 31.39/4.51      | ~ v5_orders_2(X0)
% 31.39/4.51      | ~ l1_orders_2(X0)
% 31.39/4.51      | v2_struct_0(X0) ),
% 31.39/4.51      inference(cnf_transformation,[],[f73]) ).
% 31.39/4.51  
% 31.39/4.51  cnf(c_60521,plain,
% 31.39/4.51      ( r2_orders_2(X0,sK1(X0,X1,X2),X2) != iProver_top
% 31.39/4.51      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 31.39/4.51      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 31.39/4.51      | r2_hidden(X2,a_2_0_orders_2(X0,X1)) = iProver_top
% 31.39/4.51      | v3_orders_2(X0) != iProver_top
% 31.39/4.51      | v4_orders_2(X0) != iProver_top
% 31.39/4.51      | v5_orders_2(X0) != iProver_top
% 31.39/4.51      | l1_orders_2(X0) != iProver_top
% 31.39/4.51      | v2_struct_0(X0) = iProver_top ),
% 31.39/4.51      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 31.39/4.51  
% 31.39/4.51  cnf(c_73742,plain,
% 31.39/4.51      ( r2_orders_2(sK3,sK4,sK5) != iProver_top
% 31.39/4.51      | m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 31.39/4.51      | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
% 31.39/4.51      | r2_hidden(sK5,a_2_0_orders_2(sK3,k2_tarski(sK4,sK4))) = iProver_top
% 31.39/4.51      | v3_orders_2(sK3) != iProver_top
% 31.39/4.51      | v4_orders_2(sK3) != iProver_top
% 31.39/4.51      | v5_orders_2(sK3) != iProver_top
% 31.39/4.51      | l1_orders_2(sK3) != iProver_top
% 31.39/4.51      | v2_struct_0(sK3) = iProver_top ),
% 31.39/4.51      inference(superposition,[status(thm)],[c_73739,c_60521]) ).
% 31.39/4.51  
% 31.39/4.51  cnf(c_73763,plain,
% 31.39/4.51      ( r2_orders_2(sK3,sK4,sK5) != iProver_top
% 31.39/4.51      | m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 31.39/4.51      | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
% 31.39/4.51      | r2_hidden(sK5,k1_orders_2(sK3,k2_tarski(sK4,sK4))) = iProver_top
% 31.39/4.51      | v3_orders_2(sK3) != iProver_top
% 31.39/4.51      | v4_orders_2(sK3) != iProver_top
% 31.39/4.51      | v5_orders_2(sK3) != iProver_top
% 31.39/4.51      | l1_orders_2(sK3) != iProver_top
% 31.39/4.51      | v2_struct_0(sK3) = iProver_top ),
% 31.39/4.51      inference(light_normalisation,[status(thm)],[c_73742,c_62733]) ).
% 31.39/4.51  
% 31.39/4.51  cnf(c_73773,plain,
% 31.39/4.51      ( ~ r2_orders_2(sK3,sK4,sK5)
% 31.39/4.51      | ~ m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 31.39/4.51      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 31.39/4.51      | r2_hidden(sK5,k1_orders_2(sK3,k2_tarski(sK4,sK4)))
% 31.39/4.51      | ~ v3_orders_2(sK3)
% 31.39/4.51      | ~ v4_orders_2(sK3)
% 31.39/4.51      | ~ v5_orders_2(sK3)
% 31.39/4.51      | ~ l1_orders_2(sK3)
% 31.39/4.51      | v2_struct_0(sK3) ),
% 31.39/4.51      inference(predicate_to_equality_rev,[status(thm)],[c_73763]) ).
% 31.39/4.51  
% 31.39/4.51  cnf(c_74794,negated_conjecture,
% 31.39/4.51      ( r2_hidden(sK5,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) ),
% 31.39/4.51      inference(global_propositional_subsumption,
% 31.39/4.51                [status(thm)],
% 31.39/4.51                [c_18,c_25,c_24,c_23,c_22,c_21,c_20,c_19,c_57,c_66,
% 31.39/4.51                 c_18689,c_22961,c_73773]) ).
% 31.39/4.51  
% 31.39/4.51  cnf(c_101724,plain,
% 31.39/4.51      ( r2_orders_2(sK3,sK4,sK5)
% 31.39/4.51      | r2_hidden(sK5,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) ),
% 31.39/4.51      inference(prop_impl,
% 31.39/4.51                [status(thm)],
% 31.39/4.51                [c_25,c_24,c_23,c_22,c_21,c_20,c_19,c_18,c_57,c_66,
% 31.39/4.51                 c_18689,c_22961,c_73773]) ).
% 31.39/4.51  
% 31.39/4.51  cnf(c_101820,plain,
% 31.39/4.51      ( r2_hidden(sK5,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) ),
% 31.39/4.51      inference(global_propositional_subsumption,
% 31.39/4.51                [status(thm)],
% 31.39/4.51                [c_101724,c_25,c_24,c_23,c_22,c_21,c_20,c_19,c_18,c_57,
% 31.39/4.51                 c_66,c_18689,c_22961,c_73773]) ).
% 31.39/4.51  
% 31.39/4.51  cnf(c_101936,plain,
% 31.39/4.51      ( r2_hidden(sK5,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) = iProver_top ),
% 31.39/4.51      inference(predicate_to_equality,[status(thm)],[c_101820]) ).
% 31.39/4.51  
% 31.39/4.51  cnf(c_103090,plain,
% 31.39/4.51      ( r2_hidden(sK5,k1_orders_2(sK3,k2_tarski(sK4,sK4))) = iProver_top ),
% 31.39/4.51      inference(demodulation,[status(thm)],[c_103087,c_101936]) ).
% 31.39/4.51  
% 31.39/4.51  cnf(c_101951,plain,
% 31.39/4.51      ( m1_subset_1(X0,X1) != iProver_top
% 31.39/4.51      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
% 31.39/4.51      | v1_xboole_0(X1) = iProver_top ),
% 31.39/4.51      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 31.39/4.51  
% 31.39/4.51  cnf(c_103188,plain,
% 31.39/4.51      ( m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 31.39/4.51      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 31.39/4.51      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 31.39/4.51      inference(superposition,[status(thm)],[c_103087,c_101951]) ).
% 31.39/4.51  
% 31.39/4.51  cnf(c_103793,plain,
% 31.39/4.51      ( m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 31.39/4.51      inference(global_propositional_subsumption,
% 31.39/4.51                [status(thm)],
% 31.39/4.51                [c_103188,c_26,c_30,c_31,c_58,c_67,c_22960]) ).
% 31.39/4.51  
% 31.39/4.51  cnf(c_101948,plain,
% 31.39/4.51      ( sK2(X0,X1,X2) = X0
% 31.39/4.51      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 31.39/4.51      | r2_hidden(X0,a_2_0_orders_2(X1,X2)) != iProver_top
% 31.39/4.51      | v3_orders_2(X1) != iProver_top
% 31.39/4.51      | v4_orders_2(X1) != iProver_top
% 31.39/4.51      | v5_orders_2(X1) != iProver_top
% 31.39/4.51      | l1_orders_2(X1) != iProver_top
% 31.39/4.51      | v2_struct_0(X1) = iProver_top ),
% 31.39/4.51      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 31.39/4.51  
% 31.39/4.51  cnf(c_103801,plain,
% 31.39/4.51      ( sK2(X0,sK3,k2_tarski(sK4,sK4)) = X0
% 31.39/4.51      | r2_hidden(X0,a_2_0_orders_2(sK3,k2_tarski(sK4,sK4))) != iProver_top
% 31.39/4.51      | v3_orders_2(sK3) != iProver_top
% 31.39/4.51      | v4_orders_2(sK3) != iProver_top
% 31.39/4.51      | v5_orders_2(sK3) != iProver_top
% 31.39/4.51      | l1_orders_2(sK3) != iProver_top
% 31.39/4.51      | v2_struct_0(sK3) = iProver_top ),
% 31.39/4.51      inference(superposition,[status(thm)],[c_103793,c_101948]) ).
% 31.39/4.51  
% 31.39/4.51  cnf(c_104650,plain,
% 31.39/4.51      ( r2_hidden(X0,a_2_0_orders_2(sK3,k2_tarski(sK4,sK4))) != iProver_top
% 31.39/4.51      | sK2(X0,sK3,k2_tarski(sK4,sK4)) = X0 ),
% 31.39/4.51      inference(global_propositional_subsumption,
% 31.39/4.51                [status(thm)],
% 31.39/4.51                [c_103801,c_26,c_27,c_28,c_29,c_30,c_62310]) ).
% 31.39/4.51  
% 31.39/4.51  cnf(c_104651,plain,
% 31.39/4.51      ( sK2(X0,sK3,k2_tarski(sK4,sK4)) = X0
% 31.39/4.51      | r2_hidden(X0,a_2_0_orders_2(sK3,k2_tarski(sK4,sK4))) != iProver_top ),
% 31.39/4.51      inference(renaming,[status(thm)],[c_104650]) ).
% 31.39/4.51  
% 31.39/4.51  cnf(c_101952,plain,
% 31.39/4.51      ( a_2_0_orders_2(X0,X1) = k1_orders_2(X0,X1)
% 31.39/4.51      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 31.39/4.51      | v3_orders_2(X0) != iProver_top
% 31.39/4.51      | v4_orders_2(X0) != iProver_top
% 31.39/4.51      | v5_orders_2(X0) != iProver_top
% 31.39/4.51      | l1_orders_2(X0) != iProver_top
% 31.39/4.51      | v2_struct_0(X0) = iProver_top ),
% 31.39/4.51      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 31.39/4.51  
% 31.39/4.51  cnf(c_103798,plain,
% 31.39/4.51      ( a_2_0_orders_2(sK3,k2_tarski(sK4,sK4)) = k1_orders_2(sK3,k2_tarski(sK4,sK4))
% 31.39/4.51      | v3_orders_2(sK3) != iProver_top
% 31.39/4.51      | v4_orders_2(sK3) != iProver_top
% 31.39/4.51      | v5_orders_2(sK3) != iProver_top
% 31.39/4.51      | l1_orders_2(sK3) != iProver_top
% 31.39/4.51      | v2_struct_0(sK3) = iProver_top ),
% 31.39/4.51      inference(superposition,[status(thm)],[c_103793,c_101952]) ).
% 31.39/4.51  
% 31.39/4.51  cnf(c_104507,plain,
% 31.39/4.51      ( a_2_0_orders_2(sK3,k2_tarski(sK4,sK4)) = k1_orders_2(sK3,k2_tarski(sK4,sK4)) ),
% 31.39/4.51      inference(global_propositional_subsumption,
% 31.39/4.51                [status(thm)],
% 31.39/4.51                [c_103798,c_26,c_27,c_28,c_29,c_30,c_23372]) ).
% 31.39/4.51  
% 31.39/4.51  cnf(c_104654,plain,
% 31.39/4.51      ( sK2(X0,sK3,k2_tarski(sK4,sK4)) = X0
% 31.39/4.51      | r2_hidden(X0,k1_orders_2(sK3,k2_tarski(sK4,sK4))) != iProver_top ),
% 31.39/4.51      inference(light_normalisation,[status(thm)],[c_104651,c_104507]) ).
% 31.39/4.51  
% 31.39/4.51  cnf(c_104658,plain,
% 31.39/4.51      ( sK2(sK5,sK3,k2_tarski(sK4,sK4)) = sK5 ),
% 31.39/4.51      inference(superposition,[status(thm)],[c_103090,c_104654]) ).
% 31.39/4.51  
% 31.39/4.51  cnf(c_101949,plain,
% 31.39/4.51      ( r2_orders_2(X0,X1,sK2(X2,X0,X3)) = iProver_top
% 31.39/4.51      | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 31.39/4.51      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 31.39/4.51      | r2_hidden(X1,X3) != iProver_top
% 31.39/4.51      | r2_hidden(X2,a_2_0_orders_2(X0,X3)) != iProver_top
% 31.39/4.51      | v3_orders_2(X0) != iProver_top
% 31.39/4.51      | v4_orders_2(X0) != iProver_top
% 31.39/4.51      | v5_orders_2(X0) != iProver_top
% 31.39/4.51      | l1_orders_2(X0) != iProver_top
% 31.39/4.51      | v2_struct_0(X0) = iProver_top ),
% 31.39/4.51      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 31.39/4.51  
% 31.39/4.51  cnf(c_105655,plain,
% 31.39/4.51      ( r2_orders_2(sK3,X0,sK5) = iProver_top
% 31.39/4.51      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 31.39/4.51      | m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 31.39/4.51      | r2_hidden(X0,k2_tarski(sK4,sK4)) != iProver_top
% 31.39/4.51      | r2_hidden(sK5,a_2_0_orders_2(sK3,k2_tarski(sK4,sK4))) != iProver_top
% 31.39/4.51      | v3_orders_2(sK3) != iProver_top
% 31.39/4.51      | v4_orders_2(sK3) != iProver_top
% 31.39/4.51      | v5_orders_2(sK3) != iProver_top
% 31.39/4.51      | l1_orders_2(sK3) != iProver_top
% 31.39/4.51      | v2_struct_0(sK3) = iProver_top ),
% 31.39/4.51      inference(superposition,[status(thm)],[c_104658,c_101949]) ).
% 31.39/4.51  
% 31.39/4.51  cnf(c_105656,plain,
% 31.39/4.51      ( r2_orders_2(sK3,X0,sK5) = iProver_top
% 31.39/4.51      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 31.39/4.51      | m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 31.39/4.51      | r2_hidden(X0,k2_tarski(sK4,sK4)) != iProver_top
% 31.39/4.51      | r2_hidden(sK5,k1_orders_2(sK3,k2_tarski(sK4,sK4))) != iProver_top
% 31.39/4.51      | v3_orders_2(sK3) != iProver_top
% 31.39/4.51      | v4_orders_2(sK3) != iProver_top
% 31.39/4.51      | v5_orders_2(sK3) != iProver_top
% 31.39/4.51      | l1_orders_2(sK3) != iProver_top
% 31.39/4.51      | v2_struct_0(sK3) = iProver_top ),
% 31.39/4.51      inference(light_normalisation,[status(thm)],[c_105655,c_104507]) ).
% 31.39/4.51  
% 31.39/4.51  cnf(c_34,plain,
% 31.39/4.51      ( r2_orders_2(sK3,sK4,sK5) != iProver_top
% 31.39/4.51      | r2_hidden(sK5,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) != iProver_top ),
% 31.39/4.51      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 31.39/4.51  
% 31.39/4.51  cnf(c_74796,plain,
% 31.39/4.51      ( r2_hidden(sK5,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) = iProver_top ),
% 31.39/4.51      inference(predicate_to_equality,[status(thm)],[c_74794]) ).
% 31.39/4.51  
% 31.39/4.51  cnf(c_109007,plain,
% 31.39/4.51      ( r2_orders_2(sK3,X0,sK5) = iProver_top
% 31.39/4.51      | r2_hidden(X0,k2_tarski(sK4,sK4)) != iProver_top ),
% 31.39/4.51      inference(global_propositional_subsumption,
% 31.39/4.51                [status(thm)],
% 31.39/4.51                [c_105656,c_26,c_27,c_28,c_29,c_30,c_31,c_34,c_58,c_67,
% 31.39/4.51                 c_7934,c_18678,c_22960,c_38630,c_74796]) ).
% 31.39/4.51  
% 31.39/4.51  cnf(c_109015,plain,
% 31.39/4.51      ( r2_orders_2(sK3,sK4,sK5) = iProver_top ),
% 31.39/4.51      inference(superposition,[status(thm)],[c_101956,c_109007]) ).
% 31.39/4.51  
% 31.39/4.51  cnf(contradiction,plain,
% 31.39/4.51      ( $false ),
% 31.39/4.51      inference(minisat,[status(thm)],[c_109015,c_74796,c_34]) ).
% 31.39/4.51  
% 31.39/4.51  
% 31.39/4.51  % SZS output end CNFRefutation for theBenchmark.p
% 31.39/4.51  
% 31.39/4.51  ------                               Statistics
% 31.39/4.51  
% 31.39/4.51  ------ Selected
% 31.39/4.51  
% 31.39/4.51  total_time:                             3.65
% 31.39/4.51  
%------------------------------------------------------------------------------
