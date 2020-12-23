%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1638+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:03 EST 2020

% Result     : Theorem 51.88s
% Output     : CNFRefutation 51.88s
% Verified   : 
% Statistics : Number of formulae       :  185 (10562 expanded)
%              Number of clauses        :  113 (2602 expanded)
%              Number of leaves         :   18 (2708 expanded)
%              Depth                    :   31
%              Number of atoms          :  799 (58755 expanded)
%              Number of equality atoms :  230 (2316 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k6_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(X2,k6_waybel_0(X0,X1))
                <=> r1_orders_2(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k6_waybel_0(X0,X1))
              <~> r1_orders_2(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k6_waybel_0(X0,X1))
              <~> r1_orders_2(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_orders_2(X0,X1,X2)
                | ~ r2_hidden(X2,k6_waybel_0(X0,X1)) )
              & ( r1_orders_2(X0,X1,X2)
                | r2_hidden(X2,k6_waybel_0(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_orders_2(X0,X1,X2)
                | ~ r2_hidden(X2,k6_waybel_0(X0,X1)) )
              & ( r1_orders_2(X0,X1,X2)
                | r2_hidden(X2,k6_waybel_0(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_orders_2(X0,X1,X2)
            | ~ r2_hidden(X2,k6_waybel_0(X0,X1)) )
          & ( r1_orders_2(X0,X1,X2)
            | r2_hidden(X2,k6_waybel_0(X0,X1)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( ~ r1_orders_2(X0,X1,sK7)
          | ~ r2_hidden(sK7,k6_waybel_0(X0,X1)) )
        & ( r1_orders_2(X0,X1,sK7)
          | r2_hidden(sK7,k6_waybel_0(X0,X1)) )
        & m1_subset_1(sK7,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_orders_2(X0,X1,X2)
                | ~ r2_hidden(X2,k6_waybel_0(X0,X1)) )
              & ( r1_orders_2(X0,X1,X2)
                | r2_hidden(X2,k6_waybel_0(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ( ~ r1_orders_2(X0,sK6,X2)
              | ~ r2_hidden(X2,k6_waybel_0(X0,sK6)) )
            & ( r1_orders_2(X0,sK6,X2)
              | r2_hidden(X2,k6_waybel_0(X0,sK6)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK6,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r1_orders_2(X0,X1,X2)
                  | ~ r2_hidden(X2,k6_waybel_0(X0,X1)) )
                & ( r1_orders_2(X0,X1,X2)
                  | r2_hidden(X2,k6_waybel_0(X0,X1)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_orders_2(sK5,X1,X2)
                | ~ r2_hidden(X2,k6_waybel_0(sK5,X1)) )
              & ( r1_orders_2(sK5,X1,X2)
                | r2_hidden(X2,k6_waybel_0(sK5,X1)) )
              & m1_subset_1(X2,u1_struct_0(sK5)) )
          & m1_subset_1(X1,u1_struct_0(sK5)) )
      & l1_orders_2(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ( ~ r1_orders_2(sK5,sK6,sK7)
      | ~ r2_hidden(sK7,k6_waybel_0(sK5,sK6)) )
    & ( r1_orders_2(sK5,sK6,sK7)
      | r2_hidden(sK7,k6_waybel_0(sK5,sK6)) )
    & m1_subset_1(sK7,u1_struct_0(sK5))
    & m1_subset_1(sK6,u1_struct_0(sK5))
    & l1_orders_2(sK5)
    & ~ v2_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f44,f47,f46,f45])).

fof(f75,plain,
    ( r1_orders_2(sK5,sK6,sK7)
    | r2_hidden(sK7,k6_waybel_0(sK5,sK6)) ),
    inference(cnf_transformation,[],[f48])).

fof(f73,plain,(
    m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f48])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f55,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f72,plain,(
    l1_orders_2(sK5) ),
    inference(cnf_transformation,[],[f48])).

fof(f71,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f48])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_waybel_0(X0,X1) = a_2_1_waybel_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_waybel_0(X0,X1) = a_2_1_waybel_0(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_waybel_0(X0,X1) = a_2_1_waybel_0(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k4_waybel_0(X0,X1) = a_2_1_waybel_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k6_waybel_0(X0,X1) = k4_waybel_0(X0,k6_domain_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_waybel_0(X0,X1) = k4_waybel_0(X0,k6_domain_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_waybel_0(X0,X1) = k4_waybel_0(X0,k6_domain_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k6_waybel_0(X0,X1) = k4_waybel_0(X0,k6_domain_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & l1_orders_2(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_1_waybel_0(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r1_orders_2(X1,X4,X3)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_waybel_0(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r1_orders_2(X1,X4,X3)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_waybel_0(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r1_orders_2(X1,X4,X3)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f19])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_waybel_0(X1,X2))
          | ! [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,X2)
                  | ~ r1_orders_2(X1,X4,X3)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( ? [X4] :
                  ( r2_hidden(X4,X2)
                  & r1_orders_2(X1,X4,X3)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_waybel_0(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_waybel_0(X1,X2))
          | ! [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,X2)
                  | ~ r1_orders_2(X1,X4,X3)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X5] :
              ( ? [X6] :
                  ( r2_hidden(X6,X2)
                  & r1_orders_2(X1,X6,X5)
                  & m1_subset_1(X6,u1_struct_0(X1)) )
              & X0 = X5
              & m1_subset_1(X5,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_waybel_0(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f33])).

fof(f36,plain,(
    ! [X5,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(X6,X2)
          & r1_orders_2(X1,X6,X5)
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( r2_hidden(sK2(X0,X1,X2),X2)
        & r1_orders_2(X1,sK2(X0,X1,X2),X5)
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ? [X6] :
              ( r2_hidden(X6,X2)
              & r1_orders_2(X1,X6,X5)
              & m1_subset_1(X6,u1_struct_0(X1)) )
          & X0 = X5
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ? [X6] :
            ( r2_hidden(X6,X2)
            & r1_orders_2(X1,X6,sK1(X0,X1,X2))
            & m1_subset_1(X6,u1_struct_0(X1)) )
        & sK1(X0,X1,X2) = X0
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_waybel_0(X1,X2))
          | ! [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,X2)
                  | ~ r1_orders_2(X1,X4,X3)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( r2_hidden(sK2(X0,X1,X2),X2)
            & r1_orders_2(X1,sK2(X0,X1,X2),sK1(X0,X1,X2))
            & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
            & sK1(X0,X1,X2) = X0
            & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_waybel_0(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f34,f36,f35])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X2)
      | ~ r2_hidden(X0,a_2_1_waybel_0(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f31,plain,(
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

fof(f32,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f79,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f50])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_orders_2(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_6_waybel_0(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,k6_domain_1(u1_struct_0(X1),X2))
                & r1_orders_2(X1,X4,X3)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_6_waybel_0(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,k6_domain_1(u1_struct_0(X1),X2))
                & r1_orders_2(X1,X4,X3)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_6_waybel_0(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,k6_domain_1(u1_struct_0(X1),X2))
                & r1_orders_2(X1,X4,X3)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f21])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_6_waybel_0(X1,X2))
          | ! [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,k6_domain_1(u1_struct_0(X1),X2))
                  | ~ r1_orders_2(X1,X4,X3)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( ? [X4] :
                  ( r2_hidden(X4,k6_domain_1(u1_struct_0(X1),X2))
                  & r1_orders_2(X1,X4,X3)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_6_waybel_0(X1,X2)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_6_waybel_0(X1,X2))
          | ! [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,k6_domain_1(u1_struct_0(X1),X2))
                  | ~ r1_orders_2(X1,X4,X3)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X5] :
              ( ? [X6] :
                  ( r2_hidden(X6,k6_domain_1(u1_struct_0(X1),X2))
                  & r1_orders_2(X1,X6,X5)
                  & m1_subset_1(X6,u1_struct_0(X1)) )
              & X0 = X5
              & m1_subset_1(X5,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_6_waybel_0(X1,X2)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f38])).

fof(f41,plain,(
    ! [X5,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(X6,k6_domain_1(u1_struct_0(X1),X2))
          & r1_orders_2(X1,X6,X5)
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( r2_hidden(sK4(X0,X1,X2),k6_domain_1(u1_struct_0(X1),X2))
        & r1_orders_2(X1,sK4(X0,X1,X2),X5)
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ? [X6] :
              ( r2_hidden(X6,k6_domain_1(u1_struct_0(X1),X2))
              & r1_orders_2(X1,X6,X5)
              & m1_subset_1(X6,u1_struct_0(X1)) )
          & X0 = X5
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ? [X6] :
            ( r2_hidden(X6,k6_domain_1(u1_struct_0(X1),X2))
            & r1_orders_2(X1,X6,sK3(X0,X1,X2))
            & m1_subset_1(X6,u1_struct_0(X1)) )
        & sK3(X0,X1,X2) = X0
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_6_waybel_0(X1,X2))
          | ! [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,k6_domain_1(u1_struct_0(X1),X2))
                  | ~ r1_orders_2(X1,X4,X3)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( r2_hidden(sK4(X0,X1,X2),k6_domain_1(u1_struct_0(X1),X2))
            & r1_orders_2(X1,sK4(X0,X1,X2),sK3(X0,X1,X2))
            & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1))
            & sK3(X0,X1,X2) = X0
            & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_6_waybel_0(X1,X2)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f39,f41,f40])).

fof(f68,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_6_waybel_0(X1,X2))
      | ~ r2_hidden(X4,k6_domain_1(u1_struct_0(X1),X2))
      | ~ r1_orders_2(X1,X4,X3)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f81,plain,(
    ! [X4,X2,X3,X1] :
      ( r2_hidden(X3,a_2_6_waybel_0(X1,X2))
      | ~ r2_hidden(X4,k6_domain_1(u1_struct_0(X1),X2))
      | ~ r1_orders_2(X1,X4,X3)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f68])).

fof(f74,plain,(
    m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f48])).

fof(f76,plain,
    ( ~ r1_orders_2(sK5,sK6,sK7)
    | ~ r2_hidden(sK7,k6_waybel_0(sK5,sK6)) ),
    inference(cnf_transformation,[],[f48])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f77,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f51])).

fof(f78,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f77])).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_1_waybel_0(X1,X2))
      | ~ r2_hidden(X4,X2)
      | ~ r1_orders_2(X1,X4,X3)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f80,plain,(
    ! [X4,X2,X3,X1] :
      ( r2_hidden(X3,a_2_1_waybel_0(X1,X2))
      | ~ r2_hidden(X4,X2)
      | ~ r1_orders_2(X1,X4,X3)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f62])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X1,sK2(X0,X1,X2),sK1(X0,X1,X2))
      | ~ r2_hidden(X0,a_2_1_waybel_0(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( sK1(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_1_waybel_0(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_23,negated_conjecture,
    ( r1_orders_2(sK5,sK6,sK7)
    | r2_hidden(sK7,k6_waybel_0(sK5,sK6)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_285108,plain,
    ( r1_orders_2(sK5,sK6,sK7) = iProver_top
    | r2_hidden(sK7,k6_waybel_0(sK5,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_285106,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_6,plain,
    ( l1_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_7,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_377,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(resolution,[status(thm)],[c_6,c_7])).

cnf(c_26,negated_conjecture,
    ( l1_orders_2(sK5) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_439,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_377,c_26])).

cnf(c_440,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK5))
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_439])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_77,plain,
    ( ~ l1_struct_0(sK5)
    | ~ v1_xboole_0(u1_struct_0(sK5))
    | v2_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_80,plain,
    ( l1_struct_0(sK5)
    | ~ l1_orders_2(sK5) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_442,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_440,c_27,c_26,c_77,c_80])).

cnf(c_818,plain,
    ( ~ m1_subset_1(X0,X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0)
    | u1_struct_0(sK5) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_442])).

cnf(c_819,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | k6_domain_1(u1_struct_0(sK5),X0) = k1_tarski(X0) ),
    inference(unflattening,[status(thm)],[c_818])).

cnf(c_285093,plain,
    ( k6_domain_1(u1_struct_0(sK5),X0) = k1_tarski(X0)
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_819])).

cnf(c_285451,plain,
    ( k6_domain_1(u1_struct_0(sK5),sK6) = k1_tarski(sK6) ),
    inference(superposition,[status(thm)],[c_285106,c_285093])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_830,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | u1_struct_0(sK5) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_442])).

cnf(c_831,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | m1_subset_1(k6_domain_1(u1_struct_0(sK5),X0),k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(unflattening,[status(thm)],[c_830])).

cnf(c_285092,plain,
    ( m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(k6_domain_1(u1_struct_0(sK5),X0),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_831])).

cnf(c_285696,plain,
    ( m1_subset_1(k1_tarski(sK6),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_285451,c_285092])).

cnf(c_30,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_108523,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_108516,plain,
    ( k6_domain_1(u1_struct_0(sK5),X0) = k1_tarski(X0)
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_819])).

cnf(c_108900,plain,
    ( k6_domain_1(u1_struct_0(sK5),sK6) = k1_tarski(sK6) ),
    inference(superposition,[status(thm)],[c_108523,c_108516])).

cnf(c_108515,plain,
    ( m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(k6_domain_1(u1_struct_0(sK5),X0),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_831])).

cnf(c_109230,plain,
    ( m1_subset_1(k1_tarski(sK6),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_108900,c_108515])).

cnf(c_285757,plain,
    ( m1_subset_1(k1_tarski(sK6),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_285696,c_30,c_109230])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | a_2_1_waybel_0(X1,X0) = k4_waybel_0(X1,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_552,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | a_2_1_waybel_0(X1,X0) = k4_waybel_0(X1,X0)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_26])).

cnf(c_553,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | v2_struct_0(sK5)
    | a_2_1_waybel_0(sK5,X0) = k4_waybel_0(sK5,X0) ),
    inference(unflattening,[status(thm)],[c_552])).

cnf(c_557,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | a_2_1_waybel_0(sK5,X0) = k4_waybel_0(sK5,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_553,c_27])).

cnf(c_285099,plain,
    ( a_2_1_waybel_0(sK5,X0) = k4_waybel_0(sK5,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_557])).

cnf(c_285763,plain,
    ( a_2_1_waybel_0(sK5,k1_tarski(sK6)) = k4_waybel_0(sK5,k1_tarski(sK6)) ),
    inference(superposition,[status(thm)],[c_285757,c_285099])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | k4_waybel_0(X1,k6_domain_1(u1_struct_0(X1),X0)) = k6_waybel_0(X1,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_738,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | k4_waybel_0(X1,k6_domain_1(u1_struct_0(X1),X0)) = k6_waybel_0(X1,X0)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_26])).

cnf(c_739,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | v2_struct_0(sK5)
    | k4_waybel_0(sK5,k6_domain_1(u1_struct_0(sK5),X0)) = k6_waybel_0(sK5,X0) ),
    inference(unflattening,[status(thm)],[c_738])).

cnf(c_743,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | k4_waybel_0(sK5,k6_domain_1(u1_struct_0(sK5),X0)) = k6_waybel_0(sK5,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_739,c_27])).

cnf(c_285094,plain,
    ( k4_waybel_0(sK5,k6_domain_1(u1_struct_0(sK5),X0)) = k6_waybel_0(sK5,X0)
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_743])).

cnf(c_285304,plain,
    ( k4_waybel_0(sK5,k6_domain_1(u1_struct_0(sK5),sK6)) = k6_waybel_0(sK5,sK6) ),
    inference(superposition,[status(thm)],[c_285106,c_285094])).

cnf(c_285486,plain,
    ( k4_waybel_0(sK5,k1_tarski(sK6)) = k6_waybel_0(sK5,sK6) ),
    inference(demodulation,[status(thm)],[c_285451,c_285304])).

cnf(c_285765,plain,
    ( a_2_1_waybel_0(sK5,k1_tarski(sK6)) = k6_waybel_0(sK5,sK6) ),
    inference(light_normalisation,[status(thm)],[c_285763,c_285486])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,a_2_1_waybel_0(X1,X2))
    | r2_hidden(sK2(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_717,plain,
    ( ~ r2_hidden(X0,a_2_1_waybel_0(X1,X2))
    | r2_hidden(sK2(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_26])).

cnf(c_718,plain,
    ( ~ r2_hidden(X0,a_2_1_waybel_0(sK5,X1))
    | r2_hidden(sK2(X0,sK5,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_717])).

cnf(c_722,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))
    | r2_hidden(sK2(X0,sK5,X1),X1)
    | ~ r2_hidden(X0,a_2_1_waybel_0(sK5,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_718,c_27])).

cnf(c_723,plain,
    ( ~ r2_hidden(X0,a_2_1_waybel_0(sK5,X1))
    | r2_hidden(sK2(X0,sK5,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(renaming,[status(thm)],[c_722])).

cnf(c_285095,plain,
    ( r2_hidden(X0,a_2_1_waybel_0(sK5,X1)) != iProver_top
    | r2_hidden(sK2(X0,sK5,X1),X1) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_723])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_285110,plain,
    ( X0 = X1
    | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_285344,plain,
    ( sK2(X0,sK5,k1_tarski(X1)) = X1
    | r2_hidden(X0,a_2_1_waybel_0(sK5,k1_tarski(X1))) != iProver_top
    | m1_subset_1(k1_tarski(X1),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_285095,c_285110])).

cnf(c_287207,plain,
    ( sK2(X0,sK5,k1_tarski(sK6)) = sK6
    | r2_hidden(X0,k6_waybel_0(sK5,sK6)) != iProver_top
    | m1_subset_1(k1_tarski(sK6),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_285765,c_285344])).

cnf(c_288011,plain,
    ( r2_hidden(X0,k6_waybel_0(sK5,sK6)) != iProver_top
    | sK2(X0,sK5,k1_tarski(sK6)) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_287207,c_30,c_109230])).

cnf(c_288012,plain,
    ( sK2(X0,sK5,k1_tarski(sK6)) = sK6
    | r2_hidden(X0,k6_waybel_0(sK5,sK6)) != iProver_top ),
    inference(renaming,[status(thm)],[c_288011])).

cnf(c_288019,plain,
    ( sK2(sK7,sK5,k1_tarski(sK6)) = sK6
    | r1_orders_2(sK5,sK6,sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_285108,c_288012])).

cnf(c_14,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r2_hidden(X2,a_2_6_waybel_0(X0,X3))
    | ~ r2_hidden(X1,k6_domain_1(u1_struct_0(X0),X3))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_471,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r2_hidden(X2,a_2_6_waybel_0(X0,X3))
    | ~ r2_hidden(X1,k6_domain_1(u1_struct_0(X0),X3))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_26])).

cnf(c_472,plain,
    ( ~ r1_orders_2(sK5,X0,X1)
    | r2_hidden(X1,a_2_6_waybel_0(sK5,X2))
    | ~ r2_hidden(X0,k6_domain_1(u1_struct_0(sK5),X2))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X2,u1_struct_0(sK5))
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_471])).

cnf(c_476,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ r2_hidden(X0,k6_domain_1(u1_struct_0(sK5),X2))
    | r2_hidden(X1,a_2_6_waybel_0(sK5,X2))
    | ~ r1_orders_2(sK5,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_472,c_27])).

cnf(c_477,plain,
    ( ~ r1_orders_2(sK5,X0,X1)
    | r2_hidden(X1,a_2_6_waybel_0(sK5,X2))
    | ~ r2_hidden(X0,k6_domain_1(u1_struct_0(sK5),X2))
    | ~ m1_subset_1(X2,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_476])).

cnf(c_285102,plain,
    ( r1_orders_2(sK5,X0,X1) != iProver_top
    | r2_hidden(X1,a_2_6_waybel_0(sK5,X2)) = iProver_top
    | r2_hidden(X0,k6_domain_1(u1_struct_0(sK5),X2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_477])).

cnf(c_285540,plain,
    ( r1_orders_2(sK5,X0,X1) != iProver_top
    | r2_hidden(X1,a_2_6_waybel_0(sK5,sK6)) = iProver_top
    | r2_hidden(X0,k1_tarski(sK6)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_285451,c_285102])).

cnf(c_286382,plain,
    ( m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X0,k1_tarski(sK6)) != iProver_top
    | r2_hidden(X1,a_2_6_waybel_0(sK5,sK6)) = iProver_top
    | r1_orders_2(sK5,X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_285540,c_30])).

cnf(c_286383,plain,
    ( r1_orders_2(sK5,X0,X1) != iProver_top
    | r2_hidden(X1,a_2_6_waybel_0(sK5,sK6)) = iProver_top
    | r2_hidden(X0,k1_tarski(sK6)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(renaming,[status(thm)],[c_286382])).

cnf(c_288038,plain,
    ( sK2(sK7,sK5,k1_tarski(sK6)) = sK6
    | r2_hidden(sK7,a_2_6_waybel_0(sK5,sK6)) = iProver_top
    | r2_hidden(sK6,k1_tarski(sK6)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_288019,c_286383])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_31,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_22,negated_conjecture,
    ( ~ r1_orders_2(sK5,sK6,sK7)
    | ~ r2_hidden(sK7,k6_waybel_0(sK5,sK6)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_33,plain,
    ( r1_orders_2(sK5,sK6,sK7) != iProver_top
    | r2_hidden(sK7,k6_waybel_0(sK5,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3,plain,
    ( r2_hidden(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_109270,plain,
    ( r2_hidden(sK6,k1_tarski(sK6)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_109271,plain,
    ( r2_hidden(sK6,k1_tarski(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_109270])).

cnf(c_8,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r2_hidden(X1,X3)
    | r2_hidden(X2,a_2_1_waybel_0(X0,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_522,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r2_hidden(X1,X3)
    | r2_hidden(X2,a_2_1_waybel_0(X0,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_26])).

cnf(c_523,plain,
    ( ~ r1_orders_2(sK5,X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,a_2_1_waybel_0(sK5,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_522])).

cnf(c_527,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
    | r2_hidden(X1,a_2_1_waybel_0(sK5,X2))
    | ~ r2_hidden(X0,X2)
    | ~ r1_orders_2(sK5,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_523,c_27])).

cnf(c_528,plain,
    ( ~ r1_orders_2(sK5,X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,a_2_1_waybel_0(sK5,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_527])).

cnf(c_285100,plain,
    ( r1_orders_2(sK5,X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X1,a_2_1_waybel_0(sK5,X2)) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_528])).

cnf(c_285762,plain,
    ( r1_orders_2(sK5,X0,X1) != iProver_top
    | r2_hidden(X1,a_2_1_waybel_0(sK5,k1_tarski(sK6))) = iProver_top
    | r2_hidden(X0,k1_tarski(sK6)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_285757,c_285100])).

cnf(c_285767,plain,
    ( r1_orders_2(sK5,X0,X1) != iProver_top
    | r2_hidden(X1,k6_waybel_0(sK5,sK6)) = iProver_top
    | r2_hidden(X0,k1_tarski(sK6)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_285762,c_285765])).

cnf(c_289336,plain,
    ( sK2(sK7,sK5,k1_tarski(sK6)) = sK6
    | r2_hidden(sK7,k6_waybel_0(sK5,sK6)) = iProver_top
    | r2_hidden(sK6,k1_tarski(sK6)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_288019,c_285767])).

cnf(c_289776,plain,
    ( sK2(sK7,sK5,k1_tarski(sK6)) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_288038,c_30,c_31,c_33,c_109271,c_288019,c_289336])).

cnf(c_10,plain,
    ( r1_orders_2(X0,sK2(X1,X0,X2),sK1(X1,X0,X2))
    | ~ r2_hidden(X1,a_2_1_waybel_0(X0,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_501,plain,
    ( r1_orders_2(X0,sK2(X1,X0,X2),sK1(X1,X0,X2))
    | ~ r2_hidden(X1,a_2_1_waybel_0(X0,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_26])).

cnf(c_502,plain,
    ( r1_orders_2(sK5,sK2(X0,sK5,X1),sK1(X0,sK5,X1))
    | ~ r2_hidden(X0,a_2_1_waybel_0(sK5,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_501])).

cnf(c_506,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X0,a_2_1_waybel_0(sK5,X1))
    | r1_orders_2(sK5,sK2(X0,sK5,X1),sK1(X0,sK5,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_502,c_27])).

cnf(c_507,plain,
    ( r1_orders_2(sK5,sK2(X0,sK5,X1),sK1(X0,sK5,X1))
    | ~ r2_hidden(X0,a_2_1_waybel_0(sK5,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(renaming,[status(thm)],[c_506])).

cnf(c_285101,plain,
    ( r1_orders_2(sK5,sK2(X0,sK5,X1),sK1(X0,sK5,X1)) = iProver_top
    | r2_hidden(X0,a_2_1_waybel_0(sK5,X1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_507])).

cnf(c_289779,plain,
    ( r1_orders_2(sK5,sK6,sK1(sK7,sK5,k1_tarski(sK6))) = iProver_top
    | r2_hidden(sK7,a_2_1_waybel_0(sK5,k1_tarski(sK6))) != iProver_top
    | m1_subset_1(k1_tarski(sK6),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_289776,c_285101])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,a_2_1_waybel_0(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | sK1(X0,X1,X2) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_675,plain,
    ( ~ r2_hidden(X0,a_2_1_waybel_0(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | sK1(X0,X1,X2) = X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_26])).

cnf(c_676,plain,
    ( ~ r2_hidden(X0,a_2_1_waybel_0(sK5,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))
    | v2_struct_0(sK5)
    | sK1(X0,sK5,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_675])).

cnf(c_680,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X0,a_2_1_waybel_0(sK5,X1))
    | sK1(X0,sK5,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_676,c_27])).

cnf(c_681,plain,
    ( ~ r2_hidden(X0,a_2_1_waybel_0(sK5,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))
    | sK1(X0,sK5,X1) = X0 ),
    inference(renaming,[status(thm)],[c_680])).

cnf(c_285097,plain,
    ( sK1(X0,sK5,X1) = X0
    | r2_hidden(X0,a_2_1_waybel_0(sK5,X1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_681])).

cnf(c_287205,plain,
    ( sK1(X0,sK5,k1_tarski(sK6)) = X0
    | r2_hidden(X0,k6_waybel_0(sK5,sK6)) != iProver_top
    | m1_subset_1(k1_tarski(sK6),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_285765,c_285097])).

cnf(c_287346,plain,
    ( r2_hidden(X0,k6_waybel_0(sK5,sK6)) != iProver_top
    | sK1(X0,sK5,k1_tarski(sK6)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_287205,c_30,c_109230])).

cnf(c_287347,plain,
    ( sK1(X0,sK5,k1_tarski(sK6)) = X0
    | r2_hidden(X0,k6_waybel_0(sK5,sK6)) != iProver_top ),
    inference(renaming,[status(thm)],[c_287346])).

cnf(c_287354,plain,
    ( sK1(sK7,sK5,k1_tarski(sK6)) = sK7
    | r1_orders_2(sK5,sK6,sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_285108,c_287347])).

cnf(c_108723,plain,
    ( ~ r1_orders_2(sK5,sK6,sK7)
    | r2_hidden(sK7,a_2_1_waybel_0(sK5,X0))
    | ~ r2_hidden(sK6,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_528])).

cnf(c_108920,plain,
    ( ~ r1_orders_2(sK5,sK6,sK7)
    | r2_hidden(sK7,a_2_1_waybel_0(sK5,k1_tarski(sK6)))
    | ~ r2_hidden(sK6,k1_tarski(sK6))
    | ~ m1_subset_1(k1_tarski(sK6),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_108723])).

cnf(c_108921,plain,
    ( r1_orders_2(sK5,sK6,sK7) != iProver_top
    | r2_hidden(sK7,a_2_1_waybel_0(sK5,k1_tarski(sK6))) = iProver_top
    | r2_hidden(sK6,k1_tarski(sK6)) != iProver_top
    | m1_subset_1(k1_tarski(sK6),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_108920])).

cnf(c_285823,plain,
    ( ~ r2_hidden(sK7,a_2_1_waybel_0(sK5,k1_tarski(sK6)))
    | ~ m1_subset_1(k1_tarski(sK6),k1_zfmisc_1(u1_struct_0(sK5)))
    | sK1(sK7,sK5,k1_tarski(sK6)) = sK7 ),
    inference(instantiation,[status(thm)],[c_681])).

cnf(c_285830,plain,
    ( sK1(sK7,sK5,k1_tarski(sK6)) = sK7
    | r2_hidden(sK7,a_2_1_waybel_0(sK5,k1_tarski(sK6))) != iProver_top
    | m1_subset_1(k1_tarski(sK6),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_285823])).

cnf(c_287400,plain,
    ( sK1(sK7,sK5,k1_tarski(sK6)) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_287354,c_30,c_31,c_108921,c_109230,c_109271,c_285830])).

cnf(c_289789,plain,
    ( r1_orders_2(sK5,sK6,sK7) = iProver_top
    | r2_hidden(sK7,k6_waybel_0(sK5,sK6)) != iProver_top
    | m1_subset_1(k1_tarski(sK6),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_289779,c_285765,c_287400])).

cnf(c_289809,plain,
    ( r2_hidden(sK7,k6_waybel_0(sK5,sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_289789,c_30,c_33,c_109230])).

cnf(c_289814,plain,
    ( r1_orders_2(sK5,sK6,sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_285108,c_289809])).

cnf(c_289853,plain,
    ( r2_hidden(sK7,k6_waybel_0(sK5,sK6)) = iProver_top
    | r2_hidden(sK6,k1_tarski(sK6)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_289814,c_285767])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_289853,c_289809,c_109271,c_31,c_30])).


%------------------------------------------------------------------------------
