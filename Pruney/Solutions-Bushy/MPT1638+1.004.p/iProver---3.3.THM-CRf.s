%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1638+1.004 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:03 EST 2020

% Result     : Theorem 7.59s
% Output     : CNFRefutation 7.59s
% Verified   : 
% Statistics : Number of formulae       :  165 (9301 expanded)
%              Number of clauses        :   99 (2100 expanded)
%              Number of leaves         :   16 (2453 expanded)
%              Depth                    :   31
%              Number of atoms          :  631 (54231 expanded)
%              Number of equality atoms :  266 (3616 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
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

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(X2,k6_waybel_0(X0,X1))
                <=> r1_orders_2(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k6_waybel_0(X0,X1))
              <~> r1_orders_2(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k6_waybel_0(X0,X1))
              <~> r1_orders_2(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

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
    inference(nnf_transformation,[],[f33])).

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
     => ( ( ~ r1_orders_2(X0,X1,sK5)
          | ~ r2_hidden(sK5,k6_waybel_0(X0,X1)) )
        & ( r1_orders_2(X0,X1,sK5)
          | r2_hidden(sK5,k6_waybel_0(X0,X1)) )
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
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
            ( ( ~ r1_orders_2(X0,sK4,X2)
              | ~ r2_hidden(X2,k6_waybel_0(X0,sK4)) )
            & ( r1_orders_2(X0,sK4,X2)
              | r2_hidden(X2,k6_waybel_0(X0,sK4)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
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
              ( ( ~ r1_orders_2(sK3,X1,X2)
                | ~ r2_hidden(X2,k6_waybel_0(sK3,X1)) )
              & ( r1_orders_2(sK3,X1,X2)
                | r2_hidden(X2,k6_waybel_0(sK3,X1)) )
              & m1_subset_1(X2,u1_struct_0(sK3)) )
          & m1_subset_1(X1,u1_struct_0(sK3)) )
      & l1_orders_2(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ( ~ r1_orders_2(sK3,sK4,sK5)
      | ~ r2_hidden(sK5,k6_waybel_0(sK3,sK4)) )
    & ( r1_orders_2(sK3,sK4,sK5)
      | r2_hidden(sK5,k6_waybel_0(sK3,sK4)) )
    & m1_subset_1(sK5,u1_struct_0(sK3))
    & m1_subset_1(sK4,u1_struct_0(sK3))
    & l1_orders_2(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f44,f47,f46,f45])).

fof(f72,plain,
    ( r1_orders_2(sK3,sK4,sK5)
    | r2_hidden(sK5,k6_waybel_0(sK3,sK4)) ),
    inference(cnf_transformation,[],[f48])).

fof(f70,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f48])).

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f68,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f69,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f55,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_waybel_0(X0,X1) = a_2_1_waybel_0(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f64,plain,(
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

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_waybel_0(X0,X1) = k4_waybel_0(X0,k6_domain_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_waybel_0(X0,X1) = k4_waybel_0(X0,k6_domain_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k6_waybel_0(X0,X1) = k4_waybel_0(X0,k6_domain_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

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

fof(f21,plain,(
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

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f41,plain,(
    ! [X5,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(X6,X2)
          & r1_orders_2(X1,X6,X5)
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( r2_hidden(sK2(X0,X1,X2),X2)
        & r1_orders_2(X1,sK2(X0,X1,X2),X5)
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
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

fof(f42,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f39,f41,f40])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X2)
      | ~ r2_hidden(X0,a_2_1_waybel_0(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
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

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f36,plain,(
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

fof(f37,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f36])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f76,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f50])).

fof(f71,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f48])).

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
    inference(cnf_transformation,[],[f42])).

fof(f77,plain,(
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

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f73,plain,
    ( ~ r1_orders_2(sK3,sK4,sK5)
    | ~ r2_hidden(sK5,k6_waybel_0(sK3,sK4)) ),
    inference(cnf_transformation,[],[f48])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f74,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f51])).

fof(f75,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f74])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( sK1(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_1_waybel_0(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X1,sK2(X0,X1,X2),sK1(X0,X1,X2))
      | ~ r2_hidden(X0,a_2_1_waybel_0(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_20,negated_conjecture,
    ( r1_orders_2(sK3,sK4,sK5)
    | r2_hidden(sK5,k6_waybel_0(sK3,sK4)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_886,plain,
    ( r1_orders_2(sK3,sK4,sK5) = iProver_top
    | r2_hidden(sK5,k6_waybel_0(sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_884,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_892,plain,
    ( k6_domain_1(X0,X1) = k1_tarski(X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2301,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK4) = k1_tarski(sK4)
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_884,c_892])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_23,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_7,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_65,plain,
    ( ~ l1_struct_0(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK3))
    | v2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_6,plain,
    ( l1_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_68,plain,
    ( l1_struct_0(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1169,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3))
    | k6_domain_1(u1_struct_0(sK3),sK4) = k1_tarski(sK4) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2796,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK4) = k1_tarski(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2301,c_24,c_23,c_22,c_65,c_68,c_1169])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_901,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2799,plain,
    ( m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2796,c_901])).

cnf(c_25,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_26,plain,
    ( l1_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_27,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_64,plain,
    ( l1_struct_0(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_66,plain,
    ( l1_struct_0(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_64])).

cnf(c_67,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_69,plain,
    ( l1_struct_0(sK3) = iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_67])).

cnf(c_3353,plain,
    ( m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2799,c_25,c_26,c_27,c_66,c_69])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | a_2_1_waybel_0(X1,X0) = k4_waybel_0(X1,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_891,plain,
    ( a_2_1_waybel_0(X0,X1) = k4_waybel_0(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3360,plain,
    ( a_2_1_waybel_0(sK3,k1_tarski(sK4)) = k4_waybel_0(sK3,k1_tarski(sK4))
    | v2_struct_0(sK3) = iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3353,c_891])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | k4_waybel_0(X1,k6_domain_1(u1_struct_0(X1),X0)) = k6_waybel_0(X1,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_906,plain,
    ( k4_waybel_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = k6_waybel_0(X0,X1)
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2596,plain,
    ( k4_waybel_0(sK3,k6_domain_1(u1_struct_0(sK3),sK4)) = k6_waybel_0(sK3,sK4)
    | v2_struct_0(sK3) = iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_884,c_906])).

cnf(c_1216,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ l1_orders_2(sK3)
    | k4_waybel_0(sK3,k6_domain_1(u1_struct_0(sK3),sK4)) = k6_waybel_0(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2986,plain,
    ( k4_waybel_0(sK3,k6_domain_1(u1_struct_0(sK3),sK4)) = k6_waybel_0(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2596,c_24,c_23,c_22,c_1216])).

cnf(c_2988,plain,
    ( k4_waybel_0(sK3,k1_tarski(sK4)) = k6_waybel_0(sK3,sK4) ),
    inference(light_normalisation,[status(thm)],[c_2986,c_2796])).

cnf(c_3369,plain,
    ( a_2_1_waybel_0(sK3,k1_tarski(sK4)) = k6_waybel_0(sK3,sK4)
    | v2_struct_0(sK3) = iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3360,c_2988])).

cnf(c_5073,plain,
    ( a_2_1_waybel_0(sK3,k1_tarski(sK4)) = k6_waybel_0(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3369,c_25,c_26])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,a_2_1_waybel_0(X1,X2))
    | r2_hidden(sK2(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_897,plain,
    ( r2_hidden(X0,a_2_1_waybel_0(X1,X2)) != iProver_top
    | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_orders_2(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_902,plain,
    ( X0 = X1
    | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3722,plain,
    ( sK2(X0,X1,k1_tarski(X2)) = X2
    | r2_hidden(X0,a_2_1_waybel_0(X1,k1_tarski(X2))) != iProver_top
    | m1_subset_1(k1_tarski(X2),k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_orders_2(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_897,c_902])).

cnf(c_14510,plain,
    ( sK2(X0,sK3,k1_tarski(sK4)) = sK4
    | r2_hidden(X0,k6_waybel_0(sK3,sK4)) != iProver_top
    | m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5073,c_3722])).

cnf(c_21748,plain,
    ( r2_hidden(X0,k6_waybel_0(sK3,sK4)) != iProver_top
    | sK2(X0,sK3,k1_tarski(sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_14510,c_25,c_26,c_27,c_66,c_69,c_2799])).

cnf(c_21749,plain,
    ( sK2(X0,sK3,k1_tarski(sK4)) = sK4
    | r2_hidden(X0,k6_waybel_0(sK3,sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_21748])).

cnf(c_21758,plain,
    ( sK2(sK5,sK3,k1_tarski(sK4)) = sK4
    | r1_orders_2(sK3,sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_886,c_21749])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_885,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2300,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK5) = k1_tarski(sK5)
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_885,c_892])).

cnf(c_1166,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3))
    | k6_domain_1(u1_struct_0(sK3),sK5) = k1_tarski(sK5) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2790,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK5) = k1_tarski(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2300,c_24,c_23,c_21,c_65,c_68,c_1166])).

cnf(c_2793,plain,
    ( m1_subset_1(k1_tarski(sK5),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2790,c_901])).

cnf(c_28,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3145,plain,
    ( m1_subset_1(k1_tarski(sK5),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2793,c_25,c_26,c_28,c_66,c_69])).

cnf(c_8,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r2_hidden(X1,X3)
    | r2_hidden(X2,a_2_1_waybel_0(X0,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_898,plain,
    ( r1_orders_2(X0,X1,X2) != iProver_top
    | r2_hidden(X1,X3) != iProver_top
    | r2_hidden(X2,a_2_1_waybel_0(X0,X3)) = iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_888,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1053,plain,
    ( r1_orders_2(X0,X1,X2) != iProver_top
    | r2_hidden(X1,X3) != iProver_top
    | r2_hidden(X2,a_2_1_waybel_0(X0,X3)) = iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_898,c_888])).

cnf(c_5319,plain,
    ( r1_orders_2(sK3,X0,X1) != iProver_top
    | r2_hidden(X1,a_2_1_waybel_0(sK3,k1_tarski(sK5))) = iProver_top
    | r2_hidden(X0,k1_tarski(sK5)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3145,c_1053])).

cnf(c_3152,plain,
    ( a_2_1_waybel_0(sK3,k1_tarski(sK5)) = k4_waybel_0(sK3,k1_tarski(sK5))
    | v2_struct_0(sK3) = iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3145,c_891])).

cnf(c_2595,plain,
    ( k4_waybel_0(sK3,k6_domain_1(u1_struct_0(sK3),sK5)) = k6_waybel_0(sK3,sK5)
    | v2_struct_0(sK3) = iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_885,c_906])).

cnf(c_1213,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ l1_orders_2(sK3)
    | k4_waybel_0(sK3,k6_domain_1(u1_struct_0(sK3),sK5)) = k6_waybel_0(sK3,sK5) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2981,plain,
    ( k4_waybel_0(sK3,k6_domain_1(u1_struct_0(sK3),sK5)) = k6_waybel_0(sK3,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2595,c_24,c_23,c_21,c_1213])).

cnf(c_2983,plain,
    ( k4_waybel_0(sK3,k1_tarski(sK5)) = k6_waybel_0(sK3,sK5) ),
    inference(light_normalisation,[status(thm)],[c_2981,c_2790])).

cnf(c_3161,plain,
    ( a_2_1_waybel_0(sK3,k1_tarski(sK5)) = k6_waybel_0(sK3,sK5)
    | v2_struct_0(sK3) = iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3152,c_2983])).

cnf(c_5065,plain,
    ( a_2_1_waybel_0(sK3,k1_tarski(sK5)) = k6_waybel_0(sK3,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3161,c_25,c_26])).

cnf(c_5340,plain,
    ( r1_orders_2(sK3,X0,X1) != iProver_top
    | r2_hidden(X1,k6_waybel_0(sK3,sK5)) = iProver_top
    | r2_hidden(X0,k1_tarski(sK5)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5319,c_5065])).

cnf(c_8180,plain,
    ( r1_orders_2(sK3,X0,X1) != iProver_top
    | r2_hidden(X1,k6_waybel_0(sK3,sK5)) = iProver_top
    | r2_hidden(X0,k1_tarski(sK5)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5340,c_25,c_26])).

cnf(c_21801,plain,
    ( sK2(sK5,sK3,k1_tarski(sK4)) = sK4
    | r2_hidden(sK5,k6_waybel_0(sK3,sK5)) = iProver_top
    | r2_hidden(sK4,k1_tarski(sK5)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_21758,c_8180])).

cnf(c_19,negated_conjecture,
    ( ~ r1_orders_2(sK3,sK4,sK5)
    | ~ r2_hidden(sK5,k6_waybel_0(sK3,sK4)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_30,plain,
    ( r1_orders_2(sK3,sK4,sK5) != iProver_top
    | r2_hidden(sK5,k6_waybel_0(sK3,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3,plain,
    ( r2_hidden(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1823,plain,
    ( r2_hidden(sK4,k1_tarski(sK4)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1824,plain,
    ( r2_hidden(sK4,k1_tarski(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1823])).

cnf(c_5320,plain,
    ( r1_orders_2(sK3,X0,X1) != iProver_top
    | r2_hidden(X1,a_2_1_waybel_0(sK3,k1_tarski(sK4))) = iProver_top
    | r2_hidden(X0,k1_tarski(sK4)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3353,c_1053])).

cnf(c_5327,plain,
    ( r1_orders_2(sK3,X0,X1) != iProver_top
    | r2_hidden(X1,k6_waybel_0(sK3,sK4)) = iProver_top
    | r2_hidden(X0,k1_tarski(sK4)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5320,c_5073])).

cnf(c_6563,plain,
    ( r1_orders_2(sK3,X0,X1) != iProver_top
    | r2_hidden(X1,k6_waybel_0(sK3,sK4)) = iProver_top
    | r2_hidden(X0,k1_tarski(sK4)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5327,c_25,c_26])).

cnf(c_21802,plain,
    ( sK2(sK5,sK3,k1_tarski(sK4)) = sK4
    | r2_hidden(sK5,k6_waybel_0(sK3,sK4)) = iProver_top
    | r2_hidden(sK4,k1_tarski(sK4)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_21758,c_6563])).

cnf(c_21983,plain,
    ( sK2(sK5,sK3,k1_tarski(sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_21801,c_28,c_30,c_1824,c_21758,c_21802])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,a_2_1_waybel_0(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | sK1(X0,X1,X2) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_894,plain,
    ( sK1(X0,X1,X2) = X0
    | r2_hidden(X0,a_2_1_waybel_0(X1,X2)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_orders_2(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_5076,plain,
    ( sK1(X0,sK3,k1_tarski(sK4)) = X0
    | r2_hidden(X0,k6_waybel_0(sK3,sK4)) != iProver_top
    | m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5073,c_894])).

cnf(c_6020,plain,
    ( r2_hidden(X0,k6_waybel_0(sK3,sK4)) != iProver_top
    | sK1(X0,sK3,k1_tarski(sK4)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5076,c_25,c_26,c_27,c_66,c_69,c_2799])).

cnf(c_6021,plain,
    ( sK1(X0,sK3,k1_tarski(sK4)) = X0
    | r2_hidden(X0,k6_waybel_0(sK3,sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_6020])).

cnf(c_6030,plain,
    ( sK1(sK5,sK3,k1_tarski(sK4)) = sK5
    | r1_orders_2(sK3,sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_886,c_6021])).

cnf(c_6574,plain,
    ( sK1(sK5,sK3,k1_tarski(sK4)) = sK5
    | r2_hidden(sK5,k6_waybel_0(sK3,sK4)) = iProver_top
    | r2_hidden(sK4,k1_tarski(sK4)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6030,c_6563])).

cnf(c_6838,plain,
    ( sK1(sK5,sK3,k1_tarski(sK4)) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6574,c_28,c_30,c_1824,c_6030])).

cnf(c_10,plain,
    ( r1_orders_2(X0,sK2(X1,X0,X2),sK1(X1,X0,X2))
    | ~ r2_hidden(X1,a_2_1_waybel_0(X0,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_896,plain,
    ( r1_orders_2(X0,sK2(X1,X0,X2),sK1(X1,X0,X2)) = iProver_top
    | r2_hidden(X1,a_2_1_waybel_0(X0,X2)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_6841,plain,
    ( r1_orders_2(sK3,sK2(sK5,sK3,k1_tarski(sK4)),sK5) = iProver_top
    | r2_hidden(sK5,a_2_1_waybel_0(sK3,k1_tarski(sK4))) != iProver_top
    | m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6838,c_896])).

cnf(c_6848,plain,
    ( r1_orders_2(sK3,sK2(sK5,sK3,k1_tarski(sK4)),sK5) = iProver_top
    | r2_hidden(sK5,k6_waybel_0(sK3,sK4)) != iProver_top
    | m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6841,c_5073])).

cnf(c_7923,plain,
    ( r2_hidden(sK5,k6_waybel_0(sK3,sK4)) != iProver_top
    | r1_orders_2(sK3,sK2(sK5,sK3,k1_tarski(sK4)),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6848,c_25,c_26,c_27,c_66,c_69,c_2799])).

cnf(c_7924,plain,
    ( r1_orders_2(sK3,sK2(sK5,sK3,k1_tarski(sK4)),sK5) = iProver_top
    | r2_hidden(sK5,k6_waybel_0(sK3,sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_7923])).

cnf(c_21987,plain,
    ( r1_orders_2(sK3,sK4,sK5) = iProver_top
    | r2_hidden(sK5,k6_waybel_0(sK3,sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_21983,c_7924])).

cnf(c_25730,plain,
    ( r2_hidden(sK5,k6_waybel_0(sK3,sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_21987,c_30])).

cnf(c_25735,plain,
    ( r1_orders_2(sK3,sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_886,c_25730])).

cnf(c_25740,plain,
    ( r2_hidden(sK5,k6_waybel_0(sK3,sK4)) = iProver_top
    | r2_hidden(sK4,k1_tarski(sK4)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_25735,c_6563])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_25740,c_25730,c_1824,c_28])).


%------------------------------------------------------------------------------
