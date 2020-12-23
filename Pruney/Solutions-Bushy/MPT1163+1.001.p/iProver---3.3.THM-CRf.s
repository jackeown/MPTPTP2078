%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1163+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:04 EST 2020

% Result     : Theorem 15.50s
% Output     : CNFRefutation 15.50s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 677 expanded)
%              Number of clauses        :   57 ( 161 expanded)
%              Number of leaves         :   11 ( 236 expanded)
%              Depth                    :   19
%              Number of atoms          :  392 (5005 expanded)
%              Number of equality atoms :  110 ( 326 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f14])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,conjecture,(
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
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( r1_tarski(X2,X3)
                   => r1_tarski(k3_orders_2(X0,X2,X1),k3_orders_2(X0,X3,X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( r1_tarski(X2,X3)
                     => r1_tarski(k3_orders_2(X0,X2,X1),k3_orders_2(X0,X3,X1)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k3_orders_2(X0,X2,X1),k3_orders_2(X0,X3,X1))
                  & r1_tarski(X2,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k3_orders_2(X0,X2,X1),k3_orders_2(X0,X3,X1))
                  & r1_tarski(X2,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_tarski(k3_orders_2(X0,X2,X1),k3_orders_2(X0,X3,X1))
          & r1_tarski(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k3_orders_2(X0,X2,X1),k3_orders_2(X0,sK5,X1))
        & r1_tarski(X2,sK5)
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k3_orders_2(X0,X2,X1),k3_orders_2(X0,X3,X1))
              & r1_tarski(X2,X3)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X3] :
            ( ~ r1_tarski(k3_orders_2(X0,sK4,X1),k3_orders_2(X0,X3,X1))
            & r1_tarski(sK4,X3)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k3_orders_2(X0,X2,X1),k3_orders_2(X0,X3,X1))
                  & r1_tarski(X2,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_tarski(k3_orders_2(X0,X2,sK3),k3_orders_2(X0,X3,sK3))
                & r1_tarski(X2,X3)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r1_tarski(k3_orders_2(X0,X2,X1),k3_orders_2(X0,X3,X1))
                    & r1_tarski(X2,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k3_orders_2(sK2,X2,X1),k3_orders_2(sK2,X3,X1))
                  & r1_tarski(X2,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l1_orders_2(sK2)
      & v5_orders_2(sK2)
      & v4_orders_2(sK2)
      & v3_orders_2(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ~ r1_tarski(k3_orders_2(sK2,sK4,sK3),k3_orders_2(sK2,sK5,sK3))
    & r1_tarski(sK4,sK5)
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_orders_2(sK2)
    & v5_orders_2(sK2)
    & v4_orders_2(sK2)
    & v3_orders_2(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f13,f26,f25,f24,f23])).

fof(f45,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f27])).

fof(f46,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k3_orders_2(X0,X1,X2) = k9_subset_1(u1_struct_0(X0),k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k3_orders_2(X0,X1,X2) = k9_subset_1(u1_struct_0(X0),k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)),X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k3_orders_2(X0,X1,X2) = k9_subset_1(u1_struct_0(X0),k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)),X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k3_orders_2(X0,X1,X2) = k9_subset_1(u1_struct_0(X0),k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f40,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f41,plain,(
    v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f42,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f43,plain,(
    v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f44,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f18])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f19])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f21])).

fof(f33,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f52,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f47,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f27])).

fof(f35,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f50,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f35])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f48,plain,(
    r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f27])).

fof(f34,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f51,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f49,plain,(
    ~ r1_tarski(k3_orders_2(sK2,sK4,sK3),k3_orders_2(sK2,sK5,sK3)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_617,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_604,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_605,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k9_subset_1(u1_struct_0(X1),k2_orders_2(X1,k6_domain_1(u1_struct_0(X1),X2)),X0) = k3_orders_2(X1,X0,X2) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_619,plain,
    ( k9_subset_1(u1_struct_0(X0),k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)),X2) = k3_orders_2(X0,X2,X1)
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v3_orders_2(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1717,plain,
    ( k9_subset_1(u1_struct_0(sK2),k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),X0)),sK4) = k3_orders_2(sK2,sK4,X0)
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v3_orders_2(sK2) != iProver_top
    | v4_orders_2(sK2) != iProver_top
    | v5_orders_2(sK2) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_605,c_619])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_609,plain,
    ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1424,plain,
    ( k9_subset_1(u1_struct_0(sK2),X0,sK4) = k3_xboole_0(X0,sK4) ),
    inference(superposition,[status(thm)],[c_605,c_609])).

cnf(c_1725,plain,
    ( k3_xboole_0(k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),X0)),sK4) = k3_orders_2(sK2,sK4,X0)
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v3_orders_2(sK2) != iProver_top
    | v4_orders_2(sK2) != iProver_top
    | v5_orders_2(sK2) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1717,c_1424])).

cnf(c_21,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_22,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,negated_conjecture,
    ( v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_23,plain,
    ( v3_orders_2(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_19,negated_conjecture,
    ( v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_24,plain,
    ( v4_orders_2(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_18,negated_conjecture,
    ( v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_25,plain,
    ( v5_orders_2(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_17,negated_conjecture,
    ( l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_26,plain,
    ( l1_orders_2(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2399,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | k3_xboole_0(k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),X0)),sK4) = k3_orders_2(sK2,sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1725,c_22,c_23,c_24,c_25,c_26])).

cnf(c_2400,plain,
    ( k3_xboole_0(k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),X0)),sK4) = k3_orders_2(sK2,sK4,X0)
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2399])).

cnf(c_2407,plain,
    ( k3_xboole_0(k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK3)),sK4) = k3_orders_2(sK2,sK4,sK3) ),
    inference(superposition,[status(thm)],[c_604,c_2400])).

cnf(c_10,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_610,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2416,plain,
    ( r2_hidden(X0,k3_orders_2(sK2,sK4,sK3)) != iProver_top
    | r2_hidden(X0,k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2407,c_610])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_606,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1716,plain,
    ( k9_subset_1(u1_struct_0(sK2),k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),X0)),sK5) = k3_orders_2(sK2,sK5,X0)
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v3_orders_2(sK2) != iProver_top
    | v4_orders_2(sK2) != iProver_top
    | v5_orders_2(sK2) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_606,c_619])).

cnf(c_1423,plain,
    ( k9_subset_1(u1_struct_0(sK2),X0,sK5) = k3_xboole_0(X0,sK5) ),
    inference(superposition,[status(thm)],[c_606,c_609])).

cnf(c_1740,plain,
    ( k3_xboole_0(k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),X0)),sK5) = k3_orders_2(sK2,sK5,X0)
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v3_orders_2(sK2) != iProver_top
    | v4_orders_2(sK2) != iProver_top
    | v5_orders_2(sK2) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1716,c_1423])).

cnf(c_2888,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | k3_xboole_0(k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),X0)),sK5) = k3_orders_2(sK2,sK5,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1740,c_22,c_23,c_24,c_25,c_26])).

cnf(c_2889,plain,
    ( k3_xboole_0(k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),X0)),sK5) = k3_orders_2(sK2,sK5,X0)
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2888])).

cnf(c_2896,plain,
    ( k3_xboole_0(k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK3)),sK5) = k3_orders_2(sK2,sK5,sK3) ),
    inference(superposition,[status(thm)],[c_604,c_2889])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_612,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X0,k3_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3606,plain,
    ( r2_hidden(X0,k3_orders_2(sK2,sK5,sK3)) = iProver_top
    | r2_hidden(X0,k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK3))) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2896,c_612])).

cnf(c_4656,plain,
    ( r2_hidden(X0,k3_orders_2(sK2,sK5,sK3)) = iProver_top
    | r2_hidden(X0,k3_orders_2(sK2,sK4,sK3)) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2416,c_3606])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_13,negated_conjecture,
    ( r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1448,plain,
    ( r2_hidden(X0,sK5)
    | ~ r2_hidden(X0,sK4) ),
    inference(resolution,[status(thm)],[c_4,c_13])).

cnf(c_1449,plain,
    ( r2_hidden(X0,sK5) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1448])).

cnf(c_9,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_611,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2415,plain,
    ( r2_hidden(X0,k3_orders_2(sK2,sK4,sK3)) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2407,c_611])).

cnf(c_5949,plain,
    ( r2_hidden(X0,k3_orders_2(sK2,sK4,sK3)) != iProver_top
    | r2_hidden(X0,k3_orders_2(sK2,sK5,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4656,c_1449,c_2415,c_2416,c_3606])).

cnf(c_5950,plain,
    ( r2_hidden(X0,k3_orders_2(sK2,sK5,sK3)) = iProver_top
    | r2_hidden(X0,k3_orders_2(sK2,sK4,sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5949])).

cnf(c_5957,plain,
    ( r2_hidden(sK0(k3_orders_2(sK2,sK4,sK3),X0),k3_orders_2(sK2,sK5,sK3)) = iProver_top
    | r1_tarski(k3_orders_2(sK2,sK4,sK3),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_617,c_5950])).

cnf(c_2,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_618,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_58124,plain,
    ( r1_tarski(k3_orders_2(sK2,sK4,sK3),k3_orders_2(sK2,sK5,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5957,c_618])).

cnf(c_12,negated_conjecture,
    ( ~ r1_tarski(k3_orders_2(sK2,sK4,sK3),k3_orders_2(sK2,sK5,sK3)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_31,plain,
    ( r1_tarski(k3_orders_2(sK2,sK4,sK3),k3_orders_2(sK2,sK5,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_58124,c_31])).


%------------------------------------------------------------------------------
