%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:12:30 EST 2020

% Result     : Theorem 27.73s
% Output     : CNFRefutation 27.73s
% Verified   : 
% Statistics : Number of formulae       :  163 (55603 expanded)
%              Number of clauses        :   96 (10968 expanded)
%              Number of leaves         :   15 (15210 expanded)
%              Depth                    :   44
%              Number of atoms          :  881 (469828 expanded)
%              Number of equality atoms :  400 (27843 expanded)
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
              <=> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ),
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
                <=> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f39,plain,(
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

fof(f38,plain,(
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

fof(f37,plain,
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

fof(f40,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f36,f39,f38,f37])).

fof(f65,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
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
         => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
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
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
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
     => ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r2_orders_2(X1,X3,X4) ) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f33,plain,(
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

fof(f32,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ~ r2_orders_2(X1,X3,X4)
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_orders_2(X1,X3,sK1(X1,X2,X3))
        & r2_hidden(sK1(X1,X2,X3),X2)
        & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f31,f33,f32])).

fof(f54,plain,(
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
    inference(cnf_transformation,[],[f34])).

fof(f75,plain,(
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

fof(f67,plain,
    ( ~ r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)))
    | ~ r2_orders_2(sK3,sK4,sK5) ),
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
         => ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
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
          ( ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f66,plain,
    ( r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)))
    | r2_orders_2(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f40])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( sK2(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f34])).

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

fof(f64,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f40])).

fof(f52,plain,(
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
    inference(cnf_transformation,[],[f34])).

fof(f55,plain,(
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
    inference(cnf_transformation,[],[f34])).

fof(f74,plain,(
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
    inference(equality_resolution,[],[f55])).

cnf(c_3,plain,
    ( r2_hidden(X0,k2_tarski(X1,X0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_964,plain,
    ( r2_hidden(X0,k2_tarski(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_948,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_953,plain,
    ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1685,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK5) = k2_tarski(sK5,sK5)
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_948,c_953])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k6_domain_1(u1_struct_0(X1),X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_952,plain,
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
    | a_2_1_orders_2(X1,X0) = k2_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_960,plain,
    ( a_2_1_orders_2(X0,X1) = k2_orders_2(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v3_orders_2(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2348,plain,
    ( a_2_1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v3_orders_2(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_952,c_960])).

cnf(c_6487,plain,
    ( a_2_1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)) = k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_948,c_2348])).

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

cnf(c_1290,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1375,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ v5_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | a_2_1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)) = k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_7320,plain,
    ( a_2_1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)) = k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6487,c_25,c_24,c_23,c_22,c_21,c_19,c_1290,c_1375])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,a_2_1_orders_2(X1,X2))
    | r2_hidden(sK1(X1,X2,X0),X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_958,plain,
    ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r2_hidden(X0,a_2_1_orders_2(X1,X2)) = iProver_top
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

cnf(c_961,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2089,plain,
    ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | r2_hidden(X2,k6_domain_1(u1_struct_0(X1),X0)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v3_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top
    | v1_xboole_0(u1_struct_0(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_952,c_961])).

cnf(c_4243,plain,
    ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X3)) != iProver_top
    | m1_subset_1(k6_domain_1(u1_struct_0(X3),X2),k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r2_hidden(X0,a_2_1_orders_2(X1,k6_domain_1(u1_struct_0(X3),X2))) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X3) = iProver_top
    | v3_orders_2(X1) != iProver_top
    | v3_orders_2(X3) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v5_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top
    | l1_orders_2(X3) != iProver_top
    | v1_xboole_0(u1_struct_0(X3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_958,c_2089])).

cnf(c_17717,plain,
    ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | r2_hidden(X2,a_2_1_orders_2(X1,k6_domain_1(u1_struct_0(X1),X0))) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v3_orders_2(X1) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v5_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top
    | v1_xboole_0(u1_struct_0(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_952,c_4243])).

cnf(c_20698,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7320,c_17717])).

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

cnf(c_32,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_21118,plain,
    ( r2_hidden(X0,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20698,c_26,c_27,c_28,c_29,c_30,c_32])).

cnf(c_21119,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_21118])).

cnf(c_17,negated_conjecture,
    ( ~ r2_orders_2(sK3,sK4,sK5)
    | ~ r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_950,plain,
    ( r2_orders_2(sK3,sK4,sK5) != iProver_top
    | r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_21128,plain,
    ( r2_orders_2(sK3,sK4,sK5) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_21119,c_950])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ r2_hidden(X0,k2_orders_2(X1,k6_domain_1(u1_struct_0(X1),X0)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_951,plain,
    ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | r2_hidden(X0,k2_orders_2(X1,k6_domain_1(u1_struct_0(X1),X0))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v3_orders_2(X1) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v5_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_21127,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_21119,c_951])).

cnf(c_21510,plain,
    ( v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_21128,c_26,c_27,c_28,c_29,c_30,c_32,c_21127])).

cnf(c_21517,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK5) = k2_tarski(sK5,sK5) ),
    inference(superposition,[status(thm)],[c_1685,c_21510])).

cnf(c_18,negated_conjecture,
    ( r2_orders_2(sK3,sK4,sK5)
    | r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_949,plain,
    ( r2_orders_2(sK3,sK4,sK5) = iProver_top
    | r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,a_2_1_orders_2(X1,X0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK2(X2,X1,X0) = X2 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_955,plain,
    ( sK2(X0,X1,X2) = X0
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r2_hidden(X0,a_2_1_orders_2(X1,X2)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v3_orders_2(X1) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v5_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2468,plain,
    ( sK2(X0,X1,k6_domain_1(u1_struct_0(X1),X2)) = X0
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | r2_hidden(X0,a_2_1_orders_2(X1,k6_domain_1(u1_struct_0(X1),X2))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v3_orders_2(X1) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v5_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_952,c_955])).

cnf(c_8711,plain,
    ( sK2(X0,sK3,k6_domain_1(u1_struct_0(sK3),sK5)) = X0
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7320,c_2468])).

cnf(c_9560,plain,
    ( r2_hidden(X0,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) != iProver_top
    | sK2(X0,sK3,k6_domain_1(u1_struct_0(sK3),sK5)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8711,c_26,c_27,c_28,c_29,c_30,c_32])).

cnf(c_9561,plain,
    ( sK2(X0,sK3,k6_domain_1(u1_struct_0(sK3),sK5)) = X0
    | r2_hidden(X0,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) != iProver_top ),
    inference(renaming,[status(thm)],[c_9560])).

cnf(c_9570,plain,
    ( sK2(sK4,sK3,k6_domain_1(u1_struct_0(sK3),sK5)) = sK4
    | r2_orders_2(sK3,sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_949,c_9561])).

cnf(c_23033,plain,
    ( sK2(sK4,sK3,k2_tarski(sK5,sK5)) = sK4
    | r2_orders_2(sK3,sK4,sK5) = iProver_top ),
    inference(demodulation,[status(thm)],[c_21517,c_9570])).

cnf(c_23157,plain,
    ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_21517,c_952])).

cnf(c_24819,plain,
    ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_23157,c_26,c_27,c_30,c_32])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k2_tarski(X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_962,plain,
    ( X0 = X1
    | X0 = X2
    | r2_hidden(X0,k2_tarski(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4242,plain,
    ( sK1(X0,k2_tarski(X1,X2),X3) = X1
    | sK1(X0,k2_tarski(X1,X2),X3) = X2
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r2_hidden(X3,a_2_1_orders_2(X0,k2_tarski(X1,X2))) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v3_orders_2(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_958,c_962])).

cnf(c_24831,plain,
    ( sK1(sK3,k2_tarski(sK5,sK5),X0) = sK5
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,a_2_1_orders_2(sK3,k2_tarski(sK5,sK5))) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_24819,c_4242])).

cnf(c_23035,plain,
    ( a_2_1_orders_2(sK3,k2_tarski(sK5,sK5)) = k2_orders_2(sK3,k2_tarski(sK5,sK5)) ),
    inference(demodulation,[status(thm)],[c_21517,c_7320])).

cnf(c_24858,plain,
    ( sK1(sK3,k2_tarski(sK5,sK5),X0) = sK5
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,k2_orders_2(sK3,k2_tarski(sK5,sK5))) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_24831,c_23035])).

cnf(c_28628,plain,
    ( r2_hidden(X0,k2_orders_2(sK3,k2_tarski(sK5,sK5))) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | sK1(sK3,k2_tarski(sK5,sK5),X0) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_24858,c_26,c_27,c_28,c_29,c_30])).

cnf(c_28629,plain,
    ( sK1(sK3,k2_tarski(sK5,sK5),X0) = sK5
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,k2_orders_2(sK3,k2_tarski(sK5,sK5))) = iProver_top ),
    inference(renaming,[status(thm)],[c_28628])).

cnf(c_23038,plain,
    ( r2_orders_2(sK3,sK4,sK5) != iProver_top
    | r2_hidden(sK4,k2_orders_2(sK3,k2_tarski(sK5,sK5))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_21517,c_950])).

cnf(c_28638,plain,
    ( sK1(sK3,k2_tarski(sK5,sK5),sK4) = sK5
    | r2_orders_2(sK3,sK4,sK5) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_28629,c_23038])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_31,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_29748,plain,
    ( r2_orders_2(sK3,sK4,sK5) != iProver_top
    | sK1(sK3,k2_tarski(sK5,sK5),sK4) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_28638,c_31])).

cnf(c_29749,plain,
    ( sK1(sK3,k2_tarski(sK5,sK5),sK4) = sK5
    | r2_orders_2(sK3,sK4,sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_29748])).

cnf(c_29754,plain,
    ( sK2(sK4,sK3,k2_tarski(sK5,sK5)) = sK4
    | sK1(sK3,k2_tarski(sK5,sK5),sK4) = sK5 ),
    inference(superposition,[status(thm)],[c_23033,c_29749])).

cnf(c_11,plain,
    ( r2_orders_2(X0,sK2(X1,X0,X2),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,a_2_1_orders_2(X0,X2))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_956,plain,
    ( r2_orders_2(X0,sK2(X1,X0,X2),X3) = iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r2_hidden(X3,X2) != iProver_top
    | r2_hidden(X1,a_2_1_orders_2(X0,X2)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v3_orders_2(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_29757,plain,
    ( sK1(sK3,k2_tarski(sK5,sK5),sK4) = sK5
    | r2_orders_2(sK3,sK4,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,k2_tarski(sK5,sK5)) != iProver_top
    | r2_hidden(sK4,a_2_1_orders_2(sK3,k2_tarski(sK5,sK5))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_29754,c_956])).

cnf(c_29796,plain,
    ( sK1(sK3,k2_tarski(sK5,sK5),sK4) = sK5
    | r2_orders_2(sK3,sK4,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,k2_tarski(sK5,sK5)) != iProver_top
    | r2_hidden(sK4,k2_orders_2(sK3,k2_tarski(sK5,sK5))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_29757,c_23035])).

cnf(c_23037,plain,
    ( r2_orders_2(sK3,sK4,sK5) = iProver_top
    | r2_hidden(sK4,k2_orders_2(sK3,k2_tarski(sK5,sK5))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_21517,c_949])).

cnf(c_54506,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r2_orders_2(sK3,sK4,X0) = iProver_top
    | sK1(sK3,k2_tarski(sK5,sK5),sK4) = sK5
    | r2_hidden(X0,k2_tarski(sK5,sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_29796,c_26,c_27,c_28,c_29,c_30,c_32,c_23037,c_23157,c_29749])).

cnf(c_54507,plain,
    ( sK1(sK3,k2_tarski(sK5,sK5),sK4) = sK5
    | r2_orders_2(sK3,sK4,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,k2_tarski(sK5,sK5)) != iProver_top ),
    inference(renaming,[status(thm)],[c_54506])).

cnf(c_54517,plain,
    ( sK1(sK3,k2_tarski(sK5,sK5),sK4) = sK5
    | r2_orders_2(sK3,sK4,sK5) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_964,c_54507])).

cnf(c_29750,plain,
    ( ~ r2_orders_2(sK3,sK4,sK5)
    | sK1(sK3,k2_tarski(sK5,sK5),sK4) = sK5 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_29749])).

cnf(c_54565,plain,
    ( r2_orders_2(sK3,sK4,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | sK1(sK3,k2_tarski(sK5,sK5),sK4) = sK5 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_54517])).

cnf(c_54998,plain,
    ( sK1(sK3,k2_tarski(sK5,sK5),sK4) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_54517,c_19,c_29750,c_54565])).

cnf(c_8,plain,
    ( ~ r2_orders_2(X0,X1,sK1(X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | r2_hidden(X1,a_2_1_orders_2(X0,X2))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_959,plain,
    ( r2_orders_2(X0,X1,sK1(X0,X2,X1)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r2_hidden(X1,a_2_1_orders_2(X0,X2)) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v3_orders_2(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_55066,plain,
    ( r2_orders_2(sK3,sK4,sK5) != iProver_top
    | m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK4,a_2_1_orders_2(sK3,k2_tarski(sK5,sK5))) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_54998,c_959])).

cnf(c_55088,plain,
    ( r2_orders_2(sK3,sK4,sK5) != iProver_top
    | m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK4,k2_orders_2(sK3,k2_tarski(sK5,sK5))) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_55066,c_23035])).

cnf(c_55221,plain,
    ( r2_hidden(sK4,k2_orders_2(sK3,k2_tarski(sK5,sK5))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_55088,c_26,c_27,c_28,c_29,c_30,c_31,c_32,c_23037,c_23157])).

cnf(c_23034,plain,
    ( sK2(X0,sK3,k2_tarski(sK5,sK5)) = X0
    | r2_hidden(X0,k2_orders_2(sK3,k2_tarski(sK5,sK5))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_21517,c_9561])).

cnf(c_55229,plain,
    ( sK2(sK4,sK3,k2_tarski(sK5,sK5)) = sK4 ),
    inference(superposition,[status(thm)],[c_55221,c_23034])).

cnf(c_81260,plain,
    ( r2_orders_2(sK3,sK4,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,k2_tarski(sK5,sK5)) != iProver_top
    | r2_hidden(sK4,a_2_1_orders_2(sK3,k2_tarski(sK5,sK5))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_55229,c_956])).

cnf(c_81320,plain,
    ( r2_orders_2(sK3,sK4,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,k2_tarski(sK5,sK5)) != iProver_top
    | r2_hidden(sK4,k2_orders_2(sK3,k2_tarski(sK5,sK5))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_81260,c_23035])).

cnf(c_83090,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r2_orders_2(sK3,sK4,X0) = iProver_top
    | r2_hidden(X0,k2_tarski(sK5,sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_81320,c_26,c_27,c_28,c_29,c_30,c_31,c_32,c_23037,c_23157,c_55088])).

cnf(c_83091,plain,
    ( r2_orders_2(sK3,sK4,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,k2_tarski(sK5,sK5)) != iProver_top ),
    inference(renaming,[status(thm)],[c_83090])).

cnf(c_83100,plain,
    ( r2_orders_2(sK3,sK4,sK5) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_964,c_83091])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_83100,c_55221,c_23038,c_32])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n023.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 10:45:21 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 27.73/3.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.73/3.97  
% 27.73/3.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.73/3.97  
% 27.73/3.97  ------  iProver source info
% 27.73/3.97  
% 27.73/3.97  git: date: 2020-06-30 10:37:57 +0100
% 27.73/3.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.73/3.97  git: non_committed_changes: false
% 27.73/3.97  git: last_make_outside_of_git: false
% 27.73/3.97  
% 27.73/3.97  ------ 
% 27.73/3.97  ------ Parsing...
% 27.73/3.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.73/3.97  
% 27.73/3.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 27.73/3.97  
% 27.73/3.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.73/3.97  
% 27.73/3.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.73/3.97  ------ Proving...
% 27.73/3.97  ------ Problem Properties 
% 27.73/3.97  
% 27.73/3.97  
% 27.73/3.97  clauses                                 26
% 27.73/3.97  conjectures                             9
% 27.73/3.97  EPR                                     5
% 27.73/3.97  Horn                                    14
% 27.73/3.97  unary                                   9
% 27.73/3.97  binary                                  2
% 27.73/3.97  lits                                    104
% 27.73/3.97  lits eq                                 12
% 27.73/3.97  fd_pure                                 0
% 27.73/3.97  fd_pseudo                               0
% 27.73/3.97  fd_cond                                 0
% 27.73/3.97  fd_pseudo_cond                          3
% 27.73/3.97  AC symbols                              0
% 27.73/3.97  
% 27.73/3.97  ------ Input Options Time Limit: Unbounded
% 27.73/3.97  
% 27.73/3.97  
% 27.73/3.97  ------ 
% 27.73/3.97  Current options:
% 27.73/3.97  ------ 
% 27.73/3.97  
% 27.73/3.97  
% 27.73/3.97  
% 27.73/3.97  
% 27.73/3.97  ------ Proving...
% 27.73/3.97  
% 27.73/3.97  
% 27.73/3.97  % SZS status Theorem for theBenchmark.p
% 27.73/3.97  
% 27.73/3.97  % SZS output start CNFRefutation for theBenchmark.p
% 27.73/3.97  
% 27.73/3.97  fof(f1,axiom,(
% 27.73/3.97    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 27.73/3.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.73/3.97  
% 27.73/3.97  fof(f25,plain,(
% 27.73/3.97    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 27.73/3.97    inference(nnf_transformation,[],[f1])).
% 27.73/3.97  
% 27.73/3.97  fof(f26,plain,(
% 27.73/3.97    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 27.73/3.97    inference(flattening,[],[f25])).
% 27.73/3.97  
% 27.73/3.97  fof(f27,plain,(
% 27.73/3.97    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 27.73/3.97    inference(rectify,[],[f26])).
% 27.73/3.97  
% 27.73/3.97  fof(f28,plain,(
% 27.73/3.97    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2))))),
% 27.73/3.97    introduced(choice_axiom,[])).
% 27.73/3.97  
% 27.73/3.97  fof(f29,plain,(
% 27.73/3.97    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 27.73/3.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 27.73/3.97  
% 27.73/3.97  fof(f43,plain,(
% 27.73/3.97    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 27.73/3.97    inference(cnf_transformation,[],[f29])).
% 27.73/3.97  
% 27.73/3.97  fof(f69,plain,(
% 27.73/3.97    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_tarski(X0,X4) != X2) )),
% 27.73/3.97    inference(equality_resolution,[],[f43])).
% 27.73/3.97  
% 27.73/3.97  fof(f70,plain,(
% 27.73/3.97    ( ! [X4,X0] : (r2_hidden(X4,k2_tarski(X0,X4))) )),
% 27.73/3.97    inference(equality_resolution,[],[f69])).
% 27.73/3.97  
% 27.73/3.97  fof(f9,conjecture,(
% 27.73/3.97    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))))))),
% 27.73/3.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.73/3.97  
% 27.73/3.97  fof(f10,negated_conjecture,(
% 27.73/3.97    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))))))),
% 27.73/3.97    inference(negated_conjecture,[],[f9])).
% 27.73/3.97  
% 27.73/3.97  fof(f23,plain,(
% 27.73/3.97    ? [X0] : (? [X1] : (? [X2] : ((r2_orders_2(X0,X1,X2) <~> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 27.73/3.97    inference(ennf_transformation,[],[f10])).
% 27.73/3.97  
% 27.73/3.97  fof(f24,plain,(
% 27.73/3.97    ? [X0] : (? [X1] : (? [X2] : ((r2_orders_2(X0,X1,X2) <~> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 27.73/3.97    inference(flattening,[],[f23])).
% 27.73/3.97  
% 27.73/3.97  fof(f35,plain,(
% 27.73/3.97    ? [X0] : (? [X1] : (? [X2] : (((~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~r2_orders_2(X0,X1,X2)) & (r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | r2_orders_2(X0,X1,X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 27.73/3.97    inference(nnf_transformation,[],[f24])).
% 27.73/3.97  
% 27.73/3.97  fof(f36,plain,(
% 27.73/3.97    ? [X0] : (? [X1] : (? [X2] : ((~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~r2_orders_2(X0,X1,X2)) & (r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | r2_orders_2(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 27.73/3.97    inference(flattening,[],[f35])).
% 27.73/3.97  
% 27.73/3.97  fof(f39,plain,(
% 27.73/3.97    ( ! [X0,X1] : (? [X2] : ((~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~r2_orders_2(X0,X1,X2)) & (r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | r2_orders_2(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) => ((~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),sK5))) | ~r2_orders_2(X0,X1,sK5)) & (r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),sK5))) | r2_orders_2(X0,X1,sK5)) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 27.73/3.97    introduced(choice_axiom,[])).
% 27.73/3.97  
% 27.73/3.97  fof(f38,plain,(
% 27.73/3.97    ( ! [X0] : (? [X1] : (? [X2] : ((~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~r2_orders_2(X0,X1,X2)) & (r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | r2_orders_2(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : ((~r2_hidden(sK4,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~r2_orders_2(X0,sK4,X2)) & (r2_hidden(sK4,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | r2_orders_2(X0,sK4,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 27.73/3.97    introduced(choice_axiom,[])).
% 27.73/3.97  
% 27.73/3.97  fof(f37,plain,(
% 27.73/3.97    ? [X0] : (? [X1] : (? [X2] : ((~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~r2_orders_2(X0,X1,X2)) & (r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | r2_orders_2(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r2_hidden(X1,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X2))) | ~r2_orders_2(sK3,X1,X2)) & (r2_hidden(X1,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X2))) | r2_orders_2(sK3,X1,X2)) & m1_subset_1(X2,u1_struct_0(sK3))) & m1_subset_1(X1,u1_struct_0(sK3))) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3))),
% 27.73/3.97    introduced(choice_axiom,[])).
% 27.73/3.97  
% 27.73/3.97  fof(f40,plain,(
% 27.73/3.97    (((~r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) | ~r2_orders_2(sK3,sK4,sK5)) & (r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) | r2_orders_2(sK3,sK4,sK5)) & m1_subset_1(sK5,u1_struct_0(sK3))) & m1_subset_1(sK4,u1_struct_0(sK3))) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3)),
% 27.73/3.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f36,f39,f38,f37])).
% 27.73/3.97  
% 27.73/3.97  fof(f65,plain,(
% 27.73/3.97    m1_subset_1(sK5,u1_struct_0(sK3))),
% 27.73/3.97    inference(cnf_transformation,[],[f40])).
% 27.73/3.97  
% 27.73/3.97  fof(f6,axiom,(
% 27.73/3.97    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 27.73/3.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.73/3.97  
% 27.73/3.97  fof(f17,plain,(
% 27.73/3.97    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 27.73/3.97    inference(ennf_transformation,[],[f6])).
% 27.73/3.97  
% 27.73/3.97  fof(f18,plain,(
% 27.73/3.97    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 27.73/3.97    inference(flattening,[],[f17])).
% 27.73/3.97  
% 27.73/3.97  fof(f56,plain,(
% 27.73/3.97    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 27.73/3.97    inference(cnf_transformation,[],[f18])).
% 27.73/3.97  
% 27.73/3.97  fof(f2,axiom,(
% 27.73/3.97    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 27.73/3.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.73/3.97  
% 27.73/3.97  fof(f47,plain,(
% 27.73/3.97    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 27.73/3.97    inference(cnf_transformation,[],[f2])).
% 27.73/3.97  
% 27.73/3.97  fof(f68,plain,(
% 27.73/3.97    ( ! [X0,X1] : (k2_tarski(X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 27.73/3.97    inference(definition_unfolding,[],[f56,f47])).
% 27.73/3.97  
% 27.73/3.97  fof(f7,axiom,(
% 27.73/3.97    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0))))),
% 27.73/3.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.73/3.97  
% 27.73/3.97  fof(f11,plain,(
% 27.73/3.97    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 27.73/3.97    inference(pure_predicate_removal,[],[f7])).
% 27.73/3.97  
% 27.73/3.97  fof(f19,plain,(
% 27.73/3.97    ! [X0] : (! [X1] : (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 27.73/3.97    inference(ennf_transformation,[],[f11])).
% 27.73/3.97  
% 27.73/3.97  fof(f20,plain,(
% 27.73/3.97    ! [X0] : (! [X1] : (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 27.73/3.97    inference(flattening,[],[f19])).
% 27.73/3.97  
% 27.73/3.97  fof(f57,plain,(
% 27.73/3.97    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 27.73/3.97    inference(cnf_transformation,[],[f20])).
% 27.73/3.97  
% 27.73/3.97  fof(f4,axiom,(
% 27.73/3.97    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)))),
% 27.73/3.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.73/3.97  
% 27.73/3.97  fof(f13,plain,(
% 27.73/3.97    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 27.73/3.97    inference(ennf_transformation,[],[f4])).
% 27.73/3.97  
% 27.73/3.97  fof(f14,plain,(
% 27.73/3.97    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 27.73/3.97    inference(flattening,[],[f13])).
% 27.73/3.97  
% 27.73/3.97  fof(f49,plain,(
% 27.73/3.97    ( ! [X0,X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 27.73/3.97    inference(cnf_transformation,[],[f14])).
% 27.73/3.97  
% 27.73/3.97  fof(f59,plain,(
% 27.73/3.97    ~v2_struct_0(sK3)),
% 27.73/3.97    inference(cnf_transformation,[],[f40])).
% 27.73/3.97  
% 27.73/3.97  fof(f60,plain,(
% 27.73/3.97    v3_orders_2(sK3)),
% 27.73/3.97    inference(cnf_transformation,[],[f40])).
% 27.73/3.97  
% 27.73/3.97  fof(f61,plain,(
% 27.73/3.97    v4_orders_2(sK3)),
% 27.73/3.97    inference(cnf_transformation,[],[f40])).
% 27.73/3.97  
% 27.73/3.97  fof(f62,plain,(
% 27.73/3.97    v5_orders_2(sK3)),
% 27.73/3.97    inference(cnf_transformation,[],[f40])).
% 27.73/3.97  
% 27.73/3.97  fof(f63,plain,(
% 27.73/3.97    l1_orders_2(sK3)),
% 27.73/3.97    inference(cnf_transformation,[],[f40])).
% 27.73/3.97  
% 27.73/3.97  fof(f5,axiom,(
% 27.73/3.97    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X3,X4))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 27.73/3.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.73/3.97  
% 27.73/3.97  fof(f15,plain,(
% 27.73/3.97    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 27.73/3.97    inference(ennf_transformation,[],[f5])).
% 27.73/3.97  
% 27.73/3.97  fof(f16,plain,(
% 27.73/3.97    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 27.73/3.97    inference(flattening,[],[f15])).
% 27.73/3.97  
% 27.73/3.97  fof(f30,plain,(
% 27.73/3.97    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 27.73/3.97    inference(nnf_transformation,[],[f16])).
% 27.73/3.97  
% 27.73/3.97  fof(f31,plain,(
% 27.73/3.97    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (! [X6] : (r2_orders_2(X1,X5,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 27.73/3.97    inference(rectify,[],[f30])).
% 27.73/3.97  
% 27.73/3.97  fof(f33,plain,(
% 27.73/3.97    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X1,X5,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (! [X6] : (r2_orders_2(X1,sK2(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))))),
% 27.73/3.97    introduced(choice_axiom,[])).
% 27.73/3.97  
% 27.73/3.97  fof(f32,plain,(
% 27.73/3.97    ! [X3,X2,X1] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) => (~r2_orders_2(X1,X3,sK1(X1,X2,X3)) & r2_hidden(sK1(X1,X2,X3),X2) & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1))))),
% 27.73/3.97    introduced(choice_axiom,[])).
% 27.73/3.97  
% 27.73/3.97  fof(f34,plain,(
% 27.73/3.97    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : ((~r2_orders_2(X1,X3,sK1(X1,X2,X3)) & r2_hidden(sK1(X1,X2,X3),X2) & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((! [X6] : (r2_orders_2(X1,sK2(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 27.73/3.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f31,f33,f32])).
% 27.73/3.97  
% 27.73/3.97  fof(f54,plain,(
% 27.73/3.97    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_1_orders_2(X1,X2)) | r2_hidden(sK1(X1,X2,X3),X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 27.73/3.97    inference(cnf_transformation,[],[f34])).
% 27.73/3.97  
% 27.73/3.97  fof(f75,plain,(
% 27.73/3.97    ( ! [X2,X3,X1] : (r2_hidden(X3,a_2_1_orders_2(X1,X2)) | r2_hidden(sK1(X1,X2,X3),X2) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 27.73/3.97    inference(equality_resolution,[],[f54])).
% 27.73/3.97  
% 27.73/3.97  fof(f3,axiom,(
% 27.73/3.97    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 27.73/3.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.73/3.97  
% 27.73/3.97  fof(f12,plain,(
% 27.73/3.97    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 27.73/3.97    inference(ennf_transformation,[],[f3])).
% 27.73/3.97  
% 27.73/3.97  fof(f48,plain,(
% 27.73/3.97    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 27.73/3.97    inference(cnf_transformation,[],[f12])).
% 27.73/3.97  
% 27.73/3.97  fof(f67,plain,(
% 27.73/3.97    ~r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) | ~r2_orders_2(sK3,sK4,sK5)),
% 27.73/3.97    inference(cnf_transformation,[],[f40])).
% 27.73/3.97  
% 27.73/3.97  fof(f8,axiom,(
% 27.73/3.97    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))),
% 27.73/3.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.73/3.97  
% 27.73/3.97  fof(f21,plain,(
% 27.73/3.97    ! [X0] : (! [X1] : (~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 27.73/3.97    inference(ennf_transformation,[],[f8])).
% 27.73/3.97  
% 27.73/3.97  fof(f22,plain,(
% 27.73/3.97    ! [X0] : (! [X1] : (~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 27.73/3.97    inference(flattening,[],[f21])).
% 27.73/3.97  
% 27.73/3.97  fof(f58,plain,(
% 27.73/3.97    ( ! [X0,X1] : (~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 27.73/3.97    inference(cnf_transformation,[],[f22])).
% 27.73/3.97  
% 27.73/3.97  fof(f66,plain,(
% 27.73/3.97    r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) | r2_orders_2(sK3,sK4,sK5)),
% 27.73/3.97    inference(cnf_transformation,[],[f40])).
% 27.73/3.97  
% 27.73/3.97  fof(f51,plain,(
% 27.73/3.97    ( ! [X2,X0,X1] : (sK2(X0,X1,X2) = X0 | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 27.73/3.97    inference(cnf_transformation,[],[f34])).
% 27.73/3.97  
% 27.73/3.97  fof(f41,plain,(
% 27.73/3.97    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 27.73/3.97    inference(cnf_transformation,[],[f29])).
% 27.73/3.97  
% 27.73/3.97  fof(f73,plain,(
% 27.73/3.97    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k2_tarski(X0,X1))) )),
% 27.73/3.97    inference(equality_resolution,[],[f41])).
% 27.73/3.97  
% 27.73/3.97  fof(f64,plain,(
% 27.73/3.97    m1_subset_1(sK4,u1_struct_0(sK3))),
% 27.73/3.97    inference(cnf_transformation,[],[f40])).
% 27.73/3.97  
% 27.73/3.97  fof(f52,plain,(
% 27.73/3.97    ( ! [X6,X2,X0,X1] : (r2_orders_2(X1,sK2(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 27.73/3.97    inference(cnf_transformation,[],[f34])).
% 27.73/3.97  
% 27.73/3.97  fof(f55,plain,(
% 27.73/3.97    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~r2_orders_2(X1,X3,sK1(X1,X2,X3)) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 27.73/3.97    inference(cnf_transformation,[],[f34])).
% 27.73/3.97  
% 27.73/3.97  fof(f74,plain,(
% 27.73/3.97    ( ! [X2,X3,X1] : (r2_hidden(X3,a_2_1_orders_2(X1,X2)) | ~r2_orders_2(X1,X3,sK1(X1,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 27.73/3.97    inference(equality_resolution,[],[f55])).
% 27.73/3.97  
% 27.73/3.97  cnf(c_3,plain,
% 27.73/3.97      ( r2_hidden(X0,k2_tarski(X1,X0)) ),
% 27.73/3.97      inference(cnf_transformation,[],[f70]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_964,plain,
% 27.73/3.97      ( r2_hidden(X0,k2_tarski(X1,X0)) = iProver_top ),
% 27.73/3.97      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_19,negated_conjecture,
% 27.73/3.97      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 27.73/3.97      inference(cnf_transformation,[],[f65]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_948,plain,
% 27.73/3.97      ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
% 27.73/3.97      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_14,plain,
% 27.73/3.97      ( ~ m1_subset_1(X0,X1)
% 27.73/3.97      | v1_xboole_0(X1)
% 27.73/3.97      | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
% 27.73/3.97      inference(cnf_transformation,[],[f68]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_953,plain,
% 27.73/3.97      ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
% 27.73/3.97      | m1_subset_1(X1,X0) != iProver_top
% 27.73/3.97      | v1_xboole_0(X0) = iProver_top ),
% 27.73/3.97      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_1685,plain,
% 27.73/3.97      ( k6_domain_1(u1_struct_0(sK3),sK5) = k2_tarski(sK5,sK5)
% 27.73/3.97      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 27.73/3.97      inference(superposition,[status(thm)],[c_948,c_953]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_15,plain,
% 27.73/3.97      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 27.73/3.97      | m1_subset_1(k6_domain_1(u1_struct_0(X1),X0),k1_zfmisc_1(u1_struct_0(X1)))
% 27.73/3.97      | v2_struct_0(X1)
% 27.73/3.97      | ~ v3_orders_2(X1)
% 27.73/3.97      | ~ l1_orders_2(X1) ),
% 27.73/3.97      inference(cnf_transformation,[],[f57]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_952,plain,
% 27.73/3.97      ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 27.73/3.97      | m1_subset_1(k6_domain_1(u1_struct_0(X1),X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 27.73/3.97      | v2_struct_0(X1) = iProver_top
% 27.73/3.97      | v3_orders_2(X1) != iProver_top
% 27.73/3.97      | l1_orders_2(X1) != iProver_top ),
% 27.73/3.97      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_7,plain,
% 27.73/3.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.73/3.97      | v2_struct_0(X1)
% 27.73/3.97      | ~ v3_orders_2(X1)
% 27.73/3.97      | ~ v4_orders_2(X1)
% 27.73/3.97      | ~ v5_orders_2(X1)
% 27.73/3.97      | ~ l1_orders_2(X1)
% 27.73/3.97      | a_2_1_orders_2(X1,X0) = k2_orders_2(X1,X0) ),
% 27.73/3.97      inference(cnf_transformation,[],[f49]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_960,plain,
% 27.73/3.97      ( a_2_1_orders_2(X0,X1) = k2_orders_2(X0,X1)
% 27.73/3.97      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 27.73/3.97      | v2_struct_0(X0) = iProver_top
% 27.73/3.97      | v3_orders_2(X0) != iProver_top
% 27.73/3.97      | v4_orders_2(X0) != iProver_top
% 27.73/3.97      | v5_orders_2(X0) != iProver_top
% 27.73/3.97      | l1_orders_2(X0) != iProver_top ),
% 27.73/3.97      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_2348,plain,
% 27.73/3.97      ( a_2_1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))
% 27.73/3.97      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 27.73/3.97      | v2_struct_0(X0) = iProver_top
% 27.73/3.97      | v3_orders_2(X0) != iProver_top
% 27.73/3.97      | v4_orders_2(X0) != iProver_top
% 27.73/3.97      | v5_orders_2(X0) != iProver_top
% 27.73/3.97      | l1_orders_2(X0) != iProver_top ),
% 27.73/3.97      inference(superposition,[status(thm)],[c_952,c_960]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_6487,plain,
% 27.73/3.97      ( a_2_1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)) = k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))
% 27.73/3.97      | v2_struct_0(sK3) = iProver_top
% 27.73/3.97      | v3_orders_2(sK3) != iProver_top
% 27.73/3.97      | v4_orders_2(sK3) != iProver_top
% 27.73/3.97      | v5_orders_2(sK3) != iProver_top
% 27.73/3.97      | l1_orders_2(sK3) != iProver_top ),
% 27.73/3.97      inference(superposition,[status(thm)],[c_948,c_2348]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_25,negated_conjecture,
% 27.73/3.97      ( ~ v2_struct_0(sK3) ),
% 27.73/3.97      inference(cnf_transformation,[],[f59]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_24,negated_conjecture,
% 27.73/3.97      ( v3_orders_2(sK3) ),
% 27.73/3.97      inference(cnf_transformation,[],[f60]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_23,negated_conjecture,
% 27.73/3.97      ( v4_orders_2(sK3) ),
% 27.73/3.97      inference(cnf_transformation,[],[f61]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_22,negated_conjecture,
% 27.73/3.97      ( v5_orders_2(sK3) ),
% 27.73/3.97      inference(cnf_transformation,[],[f62]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_21,negated_conjecture,
% 27.73/3.97      ( l1_orders_2(sK3) ),
% 27.73/3.97      inference(cnf_transformation,[],[f63]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_1290,plain,
% 27.73/3.97      ( m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK5),k1_zfmisc_1(u1_struct_0(sK3)))
% 27.73/3.97      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 27.73/3.97      | v2_struct_0(sK3)
% 27.73/3.97      | ~ v3_orders_2(sK3)
% 27.73/3.97      | ~ l1_orders_2(sK3) ),
% 27.73/3.97      inference(instantiation,[status(thm)],[c_15]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_1375,plain,
% 27.73/3.97      ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK5),k1_zfmisc_1(u1_struct_0(sK3)))
% 27.73/3.97      | v2_struct_0(sK3)
% 27.73/3.97      | ~ v3_orders_2(sK3)
% 27.73/3.97      | ~ v4_orders_2(sK3)
% 27.73/3.97      | ~ v5_orders_2(sK3)
% 27.73/3.97      | ~ l1_orders_2(sK3)
% 27.73/3.97      | a_2_1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)) = k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)) ),
% 27.73/3.97      inference(instantiation,[status(thm)],[c_7]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_7320,plain,
% 27.73/3.97      ( a_2_1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)) = k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)) ),
% 27.73/3.97      inference(global_propositional_subsumption,
% 27.73/3.97                [status(thm)],
% 27.73/3.97                [c_6487,c_25,c_24,c_23,c_22,c_21,c_19,c_1290,c_1375]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_9,plain,
% 27.73/3.97      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 27.73/3.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 27.73/3.97      | r2_hidden(X0,a_2_1_orders_2(X1,X2))
% 27.73/3.97      | r2_hidden(sK1(X1,X2,X0),X2)
% 27.73/3.97      | v2_struct_0(X1)
% 27.73/3.97      | ~ v3_orders_2(X1)
% 27.73/3.97      | ~ v4_orders_2(X1)
% 27.73/3.97      | ~ v5_orders_2(X1)
% 27.73/3.97      | ~ l1_orders_2(X1) ),
% 27.73/3.97      inference(cnf_transformation,[],[f75]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_958,plain,
% 27.73/3.97      ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 27.73/3.97      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 27.73/3.97      | r2_hidden(X0,a_2_1_orders_2(X1,X2)) = iProver_top
% 27.73/3.97      | r2_hidden(sK1(X1,X2,X0),X2) = iProver_top
% 27.73/3.97      | v2_struct_0(X1) = iProver_top
% 27.73/3.97      | v3_orders_2(X1) != iProver_top
% 27.73/3.97      | v4_orders_2(X1) != iProver_top
% 27.73/3.97      | v5_orders_2(X1) != iProver_top
% 27.73/3.97      | l1_orders_2(X1) != iProver_top ),
% 27.73/3.97      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_6,plain,
% 27.73/3.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 27.73/3.97      | ~ r2_hidden(X2,X0)
% 27.73/3.97      | ~ v1_xboole_0(X1) ),
% 27.73/3.97      inference(cnf_transformation,[],[f48]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_961,plain,
% 27.73/3.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 27.73/3.97      | r2_hidden(X2,X0) != iProver_top
% 27.73/3.97      | v1_xboole_0(X1) != iProver_top ),
% 27.73/3.97      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_2089,plain,
% 27.73/3.97      ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 27.73/3.97      | r2_hidden(X2,k6_domain_1(u1_struct_0(X1),X0)) != iProver_top
% 27.73/3.97      | v2_struct_0(X1) = iProver_top
% 27.73/3.97      | v3_orders_2(X1) != iProver_top
% 27.73/3.97      | l1_orders_2(X1) != iProver_top
% 27.73/3.97      | v1_xboole_0(u1_struct_0(X1)) != iProver_top ),
% 27.73/3.97      inference(superposition,[status(thm)],[c_952,c_961]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_4243,plain,
% 27.73/3.97      ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 27.73/3.97      | m1_subset_1(X2,u1_struct_0(X3)) != iProver_top
% 27.73/3.97      | m1_subset_1(k6_domain_1(u1_struct_0(X3),X2),k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 27.73/3.97      | r2_hidden(X0,a_2_1_orders_2(X1,k6_domain_1(u1_struct_0(X3),X2))) = iProver_top
% 27.73/3.97      | v2_struct_0(X1) = iProver_top
% 27.73/3.97      | v2_struct_0(X3) = iProver_top
% 27.73/3.97      | v3_orders_2(X1) != iProver_top
% 27.73/3.97      | v3_orders_2(X3) != iProver_top
% 27.73/3.97      | v4_orders_2(X1) != iProver_top
% 27.73/3.97      | v5_orders_2(X1) != iProver_top
% 27.73/3.97      | l1_orders_2(X1) != iProver_top
% 27.73/3.97      | l1_orders_2(X3) != iProver_top
% 27.73/3.97      | v1_xboole_0(u1_struct_0(X3)) != iProver_top ),
% 27.73/3.97      inference(superposition,[status(thm)],[c_958,c_2089]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_17717,plain,
% 27.73/3.97      ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 27.73/3.97      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 27.73/3.97      | r2_hidden(X2,a_2_1_orders_2(X1,k6_domain_1(u1_struct_0(X1),X0))) = iProver_top
% 27.73/3.97      | v2_struct_0(X1) = iProver_top
% 27.73/3.97      | v3_orders_2(X1) != iProver_top
% 27.73/3.97      | v4_orders_2(X1) != iProver_top
% 27.73/3.97      | v5_orders_2(X1) != iProver_top
% 27.73/3.97      | l1_orders_2(X1) != iProver_top
% 27.73/3.97      | v1_xboole_0(u1_struct_0(X1)) != iProver_top ),
% 27.73/3.97      inference(superposition,[status(thm)],[c_952,c_4243]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_20698,plain,
% 27.73/3.97      ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 27.73/3.97      | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
% 27.73/3.97      | r2_hidden(X0,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) = iProver_top
% 27.73/3.97      | v2_struct_0(sK3) = iProver_top
% 27.73/3.97      | v3_orders_2(sK3) != iProver_top
% 27.73/3.97      | v4_orders_2(sK3) != iProver_top
% 27.73/3.97      | v5_orders_2(sK3) != iProver_top
% 27.73/3.97      | l1_orders_2(sK3) != iProver_top
% 27.73/3.97      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 27.73/3.97      inference(superposition,[status(thm)],[c_7320,c_17717]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_26,plain,
% 27.73/3.97      ( v2_struct_0(sK3) != iProver_top ),
% 27.73/3.97      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_27,plain,
% 27.73/3.97      ( v3_orders_2(sK3) = iProver_top ),
% 27.73/3.97      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_28,plain,
% 27.73/3.97      ( v4_orders_2(sK3) = iProver_top ),
% 27.73/3.97      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_29,plain,
% 27.73/3.97      ( v5_orders_2(sK3) = iProver_top ),
% 27.73/3.97      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_30,plain,
% 27.73/3.97      ( l1_orders_2(sK3) = iProver_top ),
% 27.73/3.97      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_32,plain,
% 27.73/3.97      ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
% 27.73/3.97      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_21118,plain,
% 27.73/3.97      ( r2_hidden(X0,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) = iProver_top
% 27.73/3.97      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 27.73/3.97      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 27.73/3.97      inference(global_propositional_subsumption,
% 27.73/3.97                [status(thm)],
% 27.73/3.97                [c_20698,c_26,c_27,c_28,c_29,c_30,c_32]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_21119,plain,
% 27.73/3.97      ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 27.73/3.97      | r2_hidden(X0,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) = iProver_top
% 27.73/3.97      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 27.73/3.97      inference(renaming,[status(thm)],[c_21118]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_17,negated_conjecture,
% 27.73/3.97      ( ~ r2_orders_2(sK3,sK4,sK5)
% 27.73/3.97      | ~ r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) ),
% 27.73/3.97      inference(cnf_transformation,[],[f67]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_950,plain,
% 27.73/3.97      ( r2_orders_2(sK3,sK4,sK5) != iProver_top
% 27.73/3.97      | r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) != iProver_top ),
% 27.73/3.97      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_21128,plain,
% 27.73/3.97      ( r2_orders_2(sK3,sK4,sK5) != iProver_top
% 27.73/3.97      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 27.73/3.97      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 27.73/3.97      inference(superposition,[status(thm)],[c_21119,c_950]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_16,plain,
% 27.73/3.97      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 27.73/3.97      | ~ r2_hidden(X0,k2_orders_2(X1,k6_domain_1(u1_struct_0(X1),X0)))
% 27.73/3.97      | v2_struct_0(X1)
% 27.73/3.97      | ~ v3_orders_2(X1)
% 27.73/3.97      | ~ v4_orders_2(X1)
% 27.73/3.97      | ~ v5_orders_2(X1)
% 27.73/3.97      | ~ l1_orders_2(X1) ),
% 27.73/3.97      inference(cnf_transformation,[],[f58]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_951,plain,
% 27.73/3.97      ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 27.73/3.97      | r2_hidden(X0,k2_orders_2(X1,k6_domain_1(u1_struct_0(X1),X0))) != iProver_top
% 27.73/3.97      | v2_struct_0(X1) = iProver_top
% 27.73/3.97      | v3_orders_2(X1) != iProver_top
% 27.73/3.97      | v4_orders_2(X1) != iProver_top
% 27.73/3.97      | v5_orders_2(X1) != iProver_top
% 27.73/3.97      | l1_orders_2(X1) != iProver_top ),
% 27.73/3.97      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_21127,plain,
% 27.73/3.97      ( m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
% 27.73/3.97      | v2_struct_0(sK3) = iProver_top
% 27.73/3.97      | v3_orders_2(sK3) != iProver_top
% 27.73/3.97      | v4_orders_2(sK3) != iProver_top
% 27.73/3.97      | v5_orders_2(sK3) != iProver_top
% 27.73/3.97      | l1_orders_2(sK3) != iProver_top
% 27.73/3.97      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 27.73/3.97      inference(superposition,[status(thm)],[c_21119,c_951]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_21510,plain,
% 27.73/3.97      ( v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 27.73/3.97      inference(global_propositional_subsumption,
% 27.73/3.97                [status(thm)],
% 27.73/3.97                [c_21128,c_26,c_27,c_28,c_29,c_30,c_32,c_21127]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_21517,plain,
% 27.73/3.97      ( k6_domain_1(u1_struct_0(sK3),sK5) = k2_tarski(sK5,sK5) ),
% 27.73/3.97      inference(superposition,[status(thm)],[c_1685,c_21510]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_18,negated_conjecture,
% 27.73/3.97      ( r2_orders_2(sK3,sK4,sK5)
% 27.73/3.97      | r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) ),
% 27.73/3.97      inference(cnf_transformation,[],[f66]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_949,plain,
% 27.73/3.97      ( r2_orders_2(sK3,sK4,sK5) = iProver_top
% 27.73/3.97      | r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) = iProver_top ),
% 27.73/3.97      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_12,plain,
% 27.73/3.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.73/3.97      | ~ r2_hidden(X2,a_2_1_orders_2(X1,X0))
% 27.73/3.97      | v2_struct_0(X1)
% 27.73/3.97      | ~ v3_orders_2(X1)
% 27.73/3.97      | ~ v4_orders_2(X1)
% 27.73/3.97      | ~ v5_orders_2(X1)
% 27.73/3.97      | ~ l1_orders_2(X1)
% 27.73/3.97      | sK2(X2,X1,X0) = X2 ),
% 27.73/3.97      inference(cnf_transformation,[],[f51]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_955,plain,
% 27.73/3.97      ( sK2(X0,X1,X2) = X0
% 27.73/3.97      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 27.73/3.97      | r2_hidden(X0,a_2_1_orders_2(X1,X2)) != iProver_top
% 27.73/3.97      | v2_struct_0(X1) = iProver_top
% 27.73/3.97      | v3_orders_2(X1) != iProver_top
% 27.73/3.97      | v4_orders_2(X1) != iProver_top
% 27.73/3.97      | v5_orders_2(X1) != iProver_top
% 27.73/3.97      | l1_orders_2(X1) != iProver_top ),
% 27.73/3.97      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_2468,plain,
% 27.73/3.97      ( sK2(X0,X1,k6_domain_1(u1_struct_0(X1),X2)) = X0
% 27.73/3.97      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 27.73/3.97      | r2_hidden(X0,a_2_1_orders_2(X1,k6_domain_1(u1_struct_0(X1),X2))) != iProver_top
% 27.73/3.97      | v2_struct_0(X1) = iProver_top
% 27.73/3.97      | v3_orders_2(X1) != iProver_top
% 27.73/3.97      | v4_orders_2(X1) != iProver_top
% 27.73/3.97      | v5_orders_2(X1) != iProver_top
% 27.73/3.97      | l1_orders_2(X1) != iProver_top ),
% 27.73/3.97      inference(superposition,[status(thm)],[c_952,c_955]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_8711,plain,
% 27.73/3.97      ( sK2(X0,sK3,k6_domain_1(u1_struct_0(sK3),sK5)) = X0
% 27.73/3.97      | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
% 27.73/3.97      | r2_hidden(X0,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) != iProver_top
% 27.73/3.97      | v2_struct_0(sK3) = iProver_top
% 27.73/3.97      | v3_orders_2(sK3) != iProver_top
% 27.73/3.97      | v4_orders_2(sK3) != iProver_top
% 27.73/3.97      | v5_orders_2(sK3) != iProver_top
% 27.73/3.97      | l1_orders_2(sK3) != iProver_top ),
% 27.73/3.97      inference(superposition,[status(thm)],[c_7320,c_2468]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_9560,plain,
% 27.73/3.97      ( r2_hidden(X0,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) != iProver_top
% 27.73/3.97      | sK2(X0,sK3,k6_domain_1(u1_struct_0(sK3),sK5)) = X0 ),
% 27.73/3.97      inference(global_propositional_subsumption,
% 27.73/3.97                [status(thm)],
% 27.73/3.97                [c_8711,c_26,c_27,c_28,c_29,c_30,c_32]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_9561,plain,
% 27.73/3.97      ( sK2(X0,sK3,k6_domain_1(u1_struct_0(sK3),sK5)) = X0
% 27.73/3.97      | r2_hidden(X0,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) != iProver_top ),
% 27.73/3.97      inference(renaming,[status(thm)],[c_9560]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_9570,plain,
% 27.73/3.97      ( sK2(sK4,sK3,k6_domain_1(u1_struct_0(sK3),sK5)) = sK4
% 27.73/3.97      | r2_orders_2(sK3,sK4,sK5) = iProver_top ),
% 27.73/3.97      inference(superposition,[status(thm)],[c_949,c_9561]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_23033,plain,
% 27.73/3.97      ( sK2(sK4,sK3,k2_tarski(sK5,sK5)) = sK4
% 27.73/3.97      | r2_orders_2(sK3,sK4,sK5) = iProver_top ),
% 27.73/3.97      inference(demodulation,[status(thm)],[c_21517,c_9570]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_23157,plain,
% 27.73/3.97      ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 27.73/3.97      | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
% 27.73/3.97      | v2_struct_0(sK3) = iProver_top
% 27.73/3.97      | v3_orders_2(sK3) != iProver_top
% 27.73/3.97      | l1_orders_2(sK3) != iProver_top ),
% 27.73/3.97      inference(superposition,[status(thm)],[c_21517,c_952]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_24819,plain,
% 27.73/3.97      ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 27.73/3.97      inference(global_propositional_subsumption,
% 27.73/3.97                [status(thm)],
% 27.73/3.97                [c_23157,c_26,c_27,c_30,c_32]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_5,plain,
% 27.73/3.97      ( ~ r2_hidden(X0,k2_tarski(X1,X2)) | X0 = X1 | X0 = X2 ),
% 27.73/3.97      inference(cnf_transformation,[],[f73]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_962,plain,
% 27.73/3.97      ( X0 = X1
% 27.73/3.97      | X0 = X2
% 27.73/3.97      | r2_hidden(X0,k2_tarski(X1,X2)) != iProver_top ),
% 27.73/3.97      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_4242,plain,
% 27.73/3.97      ( sK1(X0,k2_tarski(X1,X2),X3) = X1
% 27.73/3.97      | sK1(X0,k2_tarski(X1,X2),X3) = X2
% 27.73/3.97      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 27.73/3.97      | m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 27.73/3.97      | r2_hidden(X3,a_2_1_orders_2(X0,k2_tarski(X1,X2))) = iProver_top
% 27.73/3.97      | v2_struct_0(X0) = iProver_top
% 27.73/3.97      | v3_orders_2(X0) != iProver_top
% 27.73/3.97      | v4_orders_2(X0) != iProver_top
% 27.73/3.97      | v5_orders_2(X0) != iProver_top
% 27.73/3.97      | l1_orders_2(X0) != iProver_top ),
% 27.73/3.97      inference(superposition,[status(thm)],[c_958,c_962]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_24831,plain,
% 27.73/3.97      ( sK1(sK3,k2_tarski(sK5,sK5),X0) = sK5
% 27.73/3.97      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 27.73/3.97      | r2_hidden(X0,a_2_1_orders_2(sK3,k2_tarski(sK5,sK5))) = iProver_top
% 27.73/3.97      | v2_struct_0(sK3) = iProver_top
% 27.73/3.97      | v3_orders_2(sK3) != iProver_top
% 27.73/3.97      | v4_orders_2(sK3) != iProver_top
% 27.73/3.97      | v5_orders_2(sK3) != iProver_top
% 27.73/3.97      | l1_orders_2(sK3) != iProver_top ),
% 27.73/3.97      inference(superposition,[status(thm)],[c_24819,c_4242]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_23035,plain,
% 27.73/3.97      ( a_2_1_orders_2(sK3,k2_tarski(sK5,sK5)) = k2_orders_2(sK3,k2_tarski(sK5,sK5)) ),
% 27.73/3.97      inference(demodulation,[status(thm)],[c_21517,c_7320]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_24858,plain,
% 27.73/3.97      ( sK1(sK3,k2_tarski(sK5,sK5),X0) = sK5
% 27.73/3.97      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 27.73/3.97      | r2_hidden(X0,k2_orders_2(sK3,k2_tarski(sK5,sK5))) = iProver_top
% 27.73/3.97      | v2_struct_0(sK3) = iProver_top
% 27.73/3.97      | v3_orders_2(sK3) != iProver_top
% 27.73/3.97      | v4_orders_2(sK3) != iProver_top
% 27.73/3.97      | v5_orders_2(sK3) != iProver_top
% 27.73/3.97      | l1_orders_2(sK3) != iProver_top ),
% 27.73/3.97      inference(light_normalisation,[status(thm)],[c_24831,c_23035]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_28628,plain,
% 27.73/3.97      ( r2_hidden(X0,k2_orders_2(sK3,k2_tarski(sK5,sK5))) = iProver_top
% 27.73/3.97      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 27.73/3.97      | sK1(sK3,k2_tarski(sK5,sK5),X0) = sK5 ),
% 27.73/3.97      inference(global_propositional_subsumption,
% 27.73/3.97                [status(thm)],
% 27.73/3.97                [c_24858,c_26,c_27,c_28,c_29,c_30]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_28629,plain,
% 27.73/3.97      ( sK1(sK3,k2_tarski(sK5,sK5),X0) = sK5
% 27.73/3.97      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 27.73/3.97      | r2_hidden(X0,k2_orders_2(sK3,k2_tarski(sK5,sK5))) = iProver_top ),
% 27.73/3.97      inference(renaming,[status(thm)],[c_28628]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_23038,plain,
% 27.73/3.97      ( r2_orders_2(sK3,sK4,sK5) != iProver_top
% 27.73/3.97      | r2_hidden(sK4,k2_orders_2(sK3,k2_tarski(sK5,sK5))) != iProver_top ),
% 27.73/3.97      inference(demodulation,[status(thm)],[c_21517,c_950]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_28638,plain,
% 27.73/3.97      ( sK1(sK3,k2_tarski(sK5,sK5),sK4) = sK5
% 27.73/3.97      | r2_orders_2(sK3,sK4,sK5) != iProver_top
% 27.73/3.97      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 27.73/3.97      inference(superposition,[status(thm)],[c_28629,c_23038]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_20,negated_conjecture,
% 27.73/3.97      ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 27.73/3.97      inference(cnf_transformation,[],[f64]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_31,plain,
% 27.73/3.97      ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
% 27.73/3.97      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_29748,plain,
% 27.73/3.97      ( r2_orders_2(sK3,sK4,sK5) != iProver_top
% 27.73/3.97      | sK1(sK3,k2_tarski(sK5,sK5),sK4) = sK5 ),
% 27.73/3.97      inference(global_propositional_subsumption,
% 27.73/3.97                [status(thm)],
% 27.73/3.97                [c_28638,c_31]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_29749,plain,
% 27.73/3.97      ( sK1(sK3,k2_tarski(sK5,sK5),sK4) = sK5
% 27.73/3.97      | r2_orders_2(sK3,sK4,sK5) != iProver_top ),
% 27.73/3.97      inference(renaming,[status(thm)],[c_29748]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_29754,plain,
% 27.73/3.97      ( sK2(sK4,sK3,k2_tarski(sK5,sK5)) = sK4
% 27.73/3.97      | sK1(sK3,k2_tarski(sK5,sK5),sK4) = sK5 ),
% 27.73/3.97      inference(superposition,[status(thm)],[c_23033,c_29749]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_11,plain,
% 27.73/3.97      ( r2_orders_2(X0,sK2(X1,X0,X2),X3)
% 27.73/3.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 27.73/3.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 27.73/3.97      | ~ r2_hidden(X3,X2)
% 27.73/3.97      | ~ r2_hidden(X1,a_2_1_orders_2(X0,X2))
% 27.73/3.97      | v2_struct_0(X0)
% 27.73/3.97      | ~ v3_orders_2(X0)
% 27.73/3.97      | ~ v4_orders_2(X0)
% 27.73/3.97      | ~ v5_orders_2(X0)
% 27.73/3.97      | ~ l1_orders_2(X0) ),
% 27.73/3.97      inference(cnf_transformation,[],[f52]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_956,plain,
% 27.73/3.97      ( r2_orders_2(X0,sK2(X1,X0,X2),X3) = iProver_top
% 27.73/3.97      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 27.73/3.97      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 27.73/3.97      | r2_hidden(X3,X2) != iProver_top
% 27.73/3.97      | r2_hidden(X1,a_2_1_orders_2(X0,X2)) != iProver_top
% 27.73/3.97      | v2_struct_0(X0) = iProver_top
% 27.73/3.97      | v3_orders_2(X0) != iProver_top
% 27.73/3.97      | v4_orders_2(X0) != iProver_top
% 27.73/3.97      | v5_orders_2(X0) != iProver_top
% 27.73/3.97      | l1_orders_2(X0) != iProver_top ),
% 27.73/3.97      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_29757,plain,
% 27.73/3.97      ( sK1(sK3,k2_tarski(sK5,sK5),sK4) = sK5
% 27.73/3.97      | r2_orders_2(sK3,sK4,X0) = iProver_top
% 27.73/3.97      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 27.73/3.97      | m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 27.73/3.97      | r2_hidden(X0,k2_tarski(sK5,sK5)) != iProver_top
% 27.73/3.97      | r2_hidden(sK4,a_2_1_orders_2(sK3,k2_tarski(sK5,sK5))) != iProver_top
% 27.73/3.97      | v2_struct_0(sK3) = iProver_top
% 27.73/3.97      | v3_orders_2(sK3) != iProver_top
% 27.73/3.97      | v4_orders_2(sK3) != iProver_top
% 27.73/3.97      | v5_orders_2(sK3) != iProver_top
% 27.73/3.97      | l1_orders_2(sK3) != iProver_top ),
% 27.73/3.97      inference(superposition,[status(thm)],[c_29754,c_956]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_29796,plain,
% 27.73/3.97      ( sK1(sK3,k2_tarski(sK5,sK5),sK4) = sK5
% 27.73/3.97      | r2_orders_2(sK3,sK4,X0) = iProver_top
% 27.73/3.97      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 27.73/3.97      | m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 27.73/3.97      | r2_hidden(X0,k2_tarski(sK5,sK5)) != iProver_top
% 27.73/3.97      | r2_hidden(sK4,k2_orders_2(sK3,k2_tarski(sK5,sK5))) != iProver_top
% 27.73/3.97      | v2_struct_0(sK3) = iProver_top
% 27.73/3.97      | v3_orders_2(sK3) != iProver_top
% 27.73/3.97      | v4_orders_2(sK3) != iProver_top
% 27.73/3.97      | v5_orders_2(sK3) != iProver_top
% 27.73/3.97      | l1_orders_2(sK3) != iProver_top ),
% 27.73/3.97      inference(light_normalisation,[status(thm)],[c_29757,c_23035]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_23037,plain,
% 27.73/3.97      ( r2_orders_2(sK3,sK4,sK5) = iProver_top
% 27.73/3.97      | r2_hidden(sK4,k2_orders_2(sK3,k2_tarski(sK5,sK5))) = iProver_top ),
% 27.73/3.97      inference(demodulation,[status(thm)],[c_21517,c_949]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_54506,plain,
% 27.73/3.97      ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 27.73/3.97      | r2_orders_2(sK3,sK4,X0) = iProver_top
% 27.73/3.97      | sK1(sK3,k2_tarski(sK5,sK5),sK4) = sK5
% 27.73/3.97      | r2_hidden(X0,k2_tarski(sK5,sK5)) != iProver_top ),
% 27.73/3.97      inference(global_propositional_subsumption,
% 27.73/3.97                [status(thm)],
% 27.73/3.97                [c_29796,c_26,c_27,c_28,c_29,c_30,c_32,c_23037,c_23157,
% 27.73/3.97                 c_29749]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_54507,plain,
% 27.73/3.97      ( sK1(sK3,k2_tarski(sK5,sK5),sK4) = sK5
% 27.73/3.97      | r2_orders_2(sK3,sK4,X0) = iProver_top
% 27.73/3.97      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 27.73/3.97      | r2_hidden(X0,k2_tarski(sK5,sK5)) != iProver_top ),
% 27.73/3.97      inference(renaming,[status(thm)],[c_54506]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_54517,plain,
% 27.73/3.97      ( sK1(sK3,k2_tarski(sK5,sK5),sK4) = sK5
% 27.73/3.97      | r2_orders_2(sK3,sK4,sK5) = iProver_top
% 27.73/3.97      | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top ),
% 27.73/3.97      inference(superposition,[status(thm)],[c_964,c_54507]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_29750,plain,
% 27.73/3.97      ( ~ r2_orders_2(sK3,sK4,sK5)
% 27.73/3.97      | sK1(sK3,k2_tarski(sK5,sK5),sK4) = sK5 ),
% 27.73/3.97      inference(predicate_to_equality_rev,[status(thm)],[c_29749]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_54565,plain,
% 27.73/3.97      ( r2_orders_2(sK3,sK4,sK5)
% 27.73/3.97      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 27.73/3.97      | sK1(sK3,k2_tarski(sK5,sK5),sK4) = sK5 ),
% 27.73/3.97      inference(predicate_to_equality_rev,[status(thm)],[c_54517]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_54998,plain,
% 27.73/3.97      ( sK1(sK3,k2_tarski(sK5,sK5),sK4) = sK5 ),
% 27.73/3.97      inference(global_propositional_subsumption,
% 27.73/3.97                [status(thm)],
% 27.73/3.97                [c_54517,c_19,c_29750,c_54565]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_8,plain,
% 27.73/3.97      ( ~ r2_orders_2(X0,X1,sK1(X0,X2,X1))
% 27.73/3.97      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 27.73/3.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 27.73/3.97      | r2_hidden(X1,a_2_1_orders_2(X0,X2))
% 27.73/3.97      | v2_struct_0(X0)
% 27.73/3.97      | ~ v3_orders_2(X0)
% 27.73/3.97      | ~ v4_orders_2(X0)
% 27.73/3.97      | ~ v5_orders_2(X0)
% 27.73/3.97      | ~ l1_orders_2(X0) ),
% 27.73/3.97      inference(cnf_transformation,[],[f74]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_959,plain,
% 27.73/3.97      ( r2_orders_2(X0,X1,sK1(X0,X2,X1)) != iProver_top
% 27.73/3.97      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 27.73/3.97      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 27.73/3.97      | r2_hidden(X1,a_2_1_orders_2(X0,X2)) = iProver_top
% 27.73/3.97      | v2_struct_0(X0) = iProver_top
% 27.73/3.97      | v3_orders_2(X0) != iProver_top
% 27.73/3.97      | v4_orders_2(X0) != iProver_top
% 27.73/3.97      | v5_orders_2(X0) != iProver_top
% 27.73/3.97      | l1_orders_2(X0) != iProver_top ),
% 27.73/3.97      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_55066,plain,
% 27.73/3.97      ( r2_orders_2(sK3,sK4,sK5) != iProver_top
% 27.73/3.97      | m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 27.73/3.97      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 27.73/3.97      | r2_hidden(sK4,a_2_1_orders_2(sK3,k2_tarski(sK5,sK5))) = iProver_top
% 27.73/3.97      | v2_struct_0(sK3) = iProver_top
% 27.73/3.97      | v3_orders_2(sK3) != iProver_top
% 27.73/3.97      | v4_orders_2(sK3) != iProver_top
% 27.73/3.97      | v5_orders_2(sK3) != iProver_top
% 27.73/3.97      | l1_orders_2(sK3) != iProver_top ),
% 27.73/3.97      inference(superposition,[status(thm)],[c_54998,c_959]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_55088,plain,
% 27.73/3.97      ( r2_orders_2(sK3,sK4,sK5) != iProver_top
% 27.73/3.97      | m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 27.73/3.97      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 27.73/3.97      | r2_hidden(sK4,k2_orders_2(sK3,k2_tarski(sK5,sK5))) = iProver_top
% 27.73/3.97      | v2_struct_0(sK3) = iProver_top
% 27.73/3.97      | v3_orders_2(sK3) != iProver_top
% 27.73/3.97      | v4_orders_2(sK3) != iProver_top
% 27.73/3.97      | v5_orders_2(sK3) != iProver_top
% 27.73/3.97      | l1_orders_2(sK3) != iProver_top ),
% 27.73/3.97      inference(light_normalisation,[status(thm)],[c_55066,c_23035]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_55221,plain,
% 27.73/3.97      ( r2_hidden(sK4,k2_orders_2(sK3,k2_tarski(sK5,sK5))) = iProver_top ),
% 27.73/3.97      inference(global_propositional_subsumption,
% 27.73/3.97                [status(thm)],
% 27.73/3.97                [c_55088,c_26,c_27,c_28,c_29,c_30,c_31,c_32,c_23037,
% 27.73/3.97                 c_23157]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_23034,plain,
% 27.73/3.97      ( sK2(X0,sK3,k2_tarski(sK5,sK5)) = X0
% 27.73/3.97      | r2_hidden(X0,k2_orders_2(sK3,k2_tarski(sK5,sK5))) != iProver_top ),
% 27.73/3.97      inference(demodulation,[status(thm)],[c_21517,c_9561]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_55229,plain,
% 27.73/3.97      ( sK2(sK4,sK3,k2_tarski(sK5,sK5)) = sK4 ),
% 27.73/3.97      inference(superposition,[status(thm)],[c_55221,c_23034]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_81260,plain,
% 27.73/3.97      ( r2_orders_2(sK3,sK4,X0) = iProver_top
% 27.73/3.97      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 27.73/3.97      | m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 27.73/3.97      | r2_hidden(X0,k2_tarski(sK5,sK5)) != iProver_top
% 27.73/3.97      | r2_hidden(sK4,a_2_1_orders_2(sK3,k2_tarski(sK5,sK5))) != iProver_top
% 27.73/3.97      | v2_struct_0(sK3) = iProver_top
% 27.73/3.97      | v3_orders_2(sK3) != iProver_top
% 27.73/3.97      | v4_orders_2(sK3) != iProver_top
% 27.73/3.97      | v5_orders_2(sK3) != iProver_top
% 27.73/3.97      | l1_orders_2(sK3) != iProver_top ),
% 27.73/3.97      inference(superposition,[status(thm)],[c_55229,c_956]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_81320,plain,
% 27.73/3.97      ( r2_orders_2(sK3,sK4,X0) = iProver_top
% 27.73/3.97      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 27.73/3.97      | m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 27.73/3.97      | r2_hidden(X0,k2_tarski(sK5,sK5)) != iProver_top
% 27.73/3.97      | r2_hidden(sK4,k2_orders_2(sK3,k2_tarski(sK5,sK5))) != iProver_top
% 27.73/3.97      | v2_struct_0(sK3) = iProver_top
% 27.73/3.97      | v3_orders_2(sK3) != iProver_top
% 27.73/3.97      | v4_orders_2(sK3) != iProver_top
% 27.73/3.97      | v5_orders_2(sK3) != iProver_top
% 27.73/3.97      | l1_orders_2(sK3) != iProver_top ),
% 27.73/3.97      inference(light_normalisation,[status(thm)],[c_81260,c_23035]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_83090,plain,
% 27.73/3.97      ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 27.73/3.97      | r2_orders_2(sK3,sK4,X0) = iProver_top
% 27.73/3.97      | r2_hidden(X0,k2_tarski(sK5,sK5)) != iProver_top ),
% 27.73/3.97      inference(global_propositional_subsumption,
% 27.73/3.97                [status(thm)],
% 27.73/3.97                [c_81320,c_26,c_27,c_28,c_29,c_30,c_31,c_32,c_23037,
% 27.73/3.97                 c_23157,c_55088]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_83091,plain,
% 27.73/3.97      ( r2_orders_2(sK3,sK4,X0) = iProver_top
% 27.73/3.97      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 27.73/3.97      | r2_hidden(X0,k2_tarski(sK5,sK5)) != iProver_top ),
% 27.73/3.97      inference(renaming,[status(thm)],[c_83090]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(c_83100,plain,
% 27.73/3.97      ( r2_orders_2(sK3,sK4,sK5) = iProver_top
% 27.73/3.97      | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top ),
% 27.73/3.97      inference(superposition,[status(thm)],[c_964,c_83091]) ).
% 27.73/3.97  
% 27.73/3.97  cnf(contradiction,plain,
% 27.73/3.97      ( $false ),
% 27.73/3.97      inference(minisat,[status(thm)],[c_83100,c_55221,c_23038,c_32]) ).
% 27.73/3.97  
% 27.73/3.97  
% 27.73/3.97  % SZS output end CNFRefutation for theBenchmark.p
% 27.73/3.97  
% 27.73/3.97  ------                               Statistics
% 27.73/3.97  
% 27.73/3.97  ------ Selected
% 27.73/3.97  
% 27.73/3.97  total_time:                             3.353
% 27.73/3.97  
%------------------------------------------------------------------------------
