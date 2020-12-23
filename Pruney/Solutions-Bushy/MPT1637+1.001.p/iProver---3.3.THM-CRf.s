%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1637+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:02 EST 2020

% Result     : Theorem 3.34s
% Output     : CNFRefutation 3.34s
% Verified   : 
% Statistics : Number of formulae       :  140 (7155 expanded)
%              Number of clauses        :   78 (1642 expanded)
%              Number of leaves         :   15 (1883 expanded)
%              Depth                    :   31
%              Number of atoms          :  563 (41667 expanded)
%              Number of equality atoms :  221 (2799 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k5_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(X2,k5_waybel_0(X0,X1))
                <=> r1_orders_2(X0,X2,X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k5_waybel_0(X0,X1))
              <~> r1_orders_2(X0,X2,X1) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k5_waybel_0(X0,X1))
              <~> r1_orders_2(X0,X2,X1) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_orders_2(X0,X2,X1)
                | ~ r2_hidden(X2,k5_waybel_0(X0,X1)) )
              & ( r1_orders_2(X0,X2,X1)
                | r2_hidden(X2,k5_waybel_0(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_orders_2(X0,X2,X1)
                | ~ r2_hidden(X2,k5_waybel_0(X0,X1)) )
              & ( r1_orders_2(X0,X2,X1)
                | r2_hidden(X2,k5_waybel_0(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_orders_2(X0,X2,X1)
            | ~ r2_hidden(X2,k5_waybel_0(X0,X1)) )
          & ( r1_orders_2(X0,X2,X1)
            | r2_hidden(X2,k5_waybel_0(X0,X1)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( ~ r1_orders_2(X0,sK5,X1)
          | ~ r2_hidden(sK5,k5_waybel_0(X0,X1)) )
        & ( r1_orders_2(X0,sK5,X1)
          | r2_hidden(sK5,k5_waybel_0(X0,X1)) )
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_orders_2(X0,X2,X1)
                | ~ r2_hidden(X2,k5_waybel_0(X0,X1)) )
              & ( r1_orders_2(X0,X2,X1)
                | r2_hidden(X2,k5_waybel_0(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ( ~ r1_orders_2(X0,X2,sK4)
              | ~ r2_hidden(X2,k5_waybel_0(X0,sK4)) )
            & ( r1_orders_2(X0,X2,sK4)
              | r2_hidden(X2,k5_waybel_0(X0,sK4)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r1_orders_2(X0,X2,X1)
                  | ~ r2_hidden(X2,k5_waybel_0(X0,X1)) )
                & ( r1_orders_2(X0,X2,X1)
                  | r2_hidden(X2,k5_waybel_0(X0,X1)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_orders_2(sK3,X2,X1)
                | ~ r2_hidden(X2,k5_waybel_0(sK3,X1)) )
              & ( r1_orders_2(sK3,X2,X1)
                | r2_hidden(X2,k5_waybel_0(sK3,X1)) )
              & m1_subset_1(X2,u1_struct_0(sK3)) )
          & m1_subset_1(X1,u1_struct_0(sK3)) )
      & l1_orders_2(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ( ~ r1_orders_2(sK3,sK5,sK4)
      | ~ r2_hidden(sK5,k5_waybel_0(sK3,sK4)) )
    & ( r1_orders_2(sK3,sK5,sK4)
      | r2_hidden(sK5,k5_waybel_0(sK3,sK4)) )
    & m1_subset_1(sK5,u1_struct_0(sK3))
    & m1_subset_1(sK4,u1_struct_0(sK3))
    & l1_orders_2(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f36,f39,f38,f37])).

fof(f61,plain,
    ( r1_orders_2(sK3,sK5,sK4)
    | r2_hidden(sK5,k5_waybel_0(sK3,sK4)) ),
    inference(cnf_transformation,[],[f40])).

fof(f59,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f40])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f57,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f58,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f47,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k3_waybel_0(X0,X1) = a_2_0_waybel_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_waybel_0(X0,X1) = a_2_0_waybel_0(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_waybel_0(X0,X1) = a_2_0_waybel_0(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k3_waybel_0(X0,X1) = a_2_0_waybel_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k5_waybel_0(X0,X1) = k3_waybel_0(X0,k6_domain_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_waybel_0(X0,X1) = k3_waybel_0(X0,k6_domain_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_waybel_0(X0,X1) = k3_waybel_0(X0,k6_domain_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k5_waybel_0(X0,X1) = k3_waybel_0(X0,k6_domain_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & l1_orders_2(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_0_waybel_0(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r1_orders_2(X1,X3,X4)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_waybel_0(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r1_orders_2(X1,X3,X4)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_waybel_0(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r1_orders_2(X1,X3,X4)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f18])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_waybel_0(X1,X2))
          | ! [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,X2)
                  | ~ r1_orders_2(X1,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( ? [X4] :
                  ( r2_hidden(X4,X2)
                  & r1_orders_2(X1,X3,X4)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_0_waybel_0(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_waybel_0(X1,X2))
          | ! [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,X2)
                  | ~ r1_orders_2(X1,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X5] :
              ( ? [X6] :
                  ( r2_hidden(X6,X2)
                  & r1_orders_2(X1,X5,X6)
                  & m1_subset_1(X6,u1_struct_0(X1)) )
              & X0 = X5
              & m1_subset_1(X5,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_0_waybel_0(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f30])).

fof(f33,plain,(
    ! [X5,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(X6,X2)
          & r1_orders_2(X1,X5,X6)
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( r2_hidden(sK2(X0,X1,X2),X2)
        & r1_orders_2(X1,X5,sK2(X0,X1,X2))
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ? [X6] :
              ( r2_hidden(X6,X2)
              & r1_orders_2(X1,X5,X6)
              & m1_subset_1(X6,u1_struct_0(X1)) )
          & X0 = X5
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ? [X6] :
            ( r2_hidden(X6,X2)
            & r1_orders_2(X1,sK1(X0,X1,X2),X6)
            & m1_subset_1(X6,u1_struct_0(X1)) )
        & sK1(X0,X1,X2) = X0
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_waybel_0(X1,X2))
          | ! [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,X2)
                  | ~ r1_orders_2(X1,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( r2_hidden(sK2(X0,X1,X2),X2)
            & r1_orders_2(X1,sK1(X0,X1,X2),sK2(X0,X1,X2))
            & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
            & sK1(X0,X1,X2) = X0
            & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_0_waybel_0(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f31,f33,f32])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X2)
      | ~ r2_hidden(X0,a_2_0_waybel_0(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
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

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f28,plain,(
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

fof(f29,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f65,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_0_waybel_0(X1,X2))
      | ~ r2_hidden(X4,X2)
      | ~ r1_orders_2(X1,X3,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f66,plain,(
    ! [X4,X2,X3,X1] :
      ( r2_hidden(X3,a_2_0_waybel_0(X1,X2))
      | ~ r2_hidden(X4,X2)
      | ~ r1_orders_2(X1,X3,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f54])).

fof(f60,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f40])).

fof(f62,plain,
    ( ~ r1_orders_2(sK3,sK5,sK4)
    | ~ r2_hidden(sK5,k5_waybel_0(sK3,sK4)) ),
    inference(cnf_transformation,[],[f40])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f63,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f43])).

fof(f64,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f63])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( sK1(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_0_waybel_0(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X1,sK1(X0,X1,X2),sK2(X0,X1,X2))
      | ~ r2_hidden(X0,a_2_0_waybel_0(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_17,negated_conjecture,
    ( r1_orders_2(sK3,sK5,sK4)
    | r2_hidden(sK5,k5_waybel_0(sK3,sK4)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_804,plain,
    ( r1_orders_2(sK3,sK5,sK4) = iProver_top
    | r2_hidden(sK5,k5_waybel_0(sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_802,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_807,plain,
    ( k6_domain_1(X0,X1) = k1_tarski(X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1415,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK4) = k1_tarski(sK4)
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_802,c_807])).

cnf(c_21,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_20,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_7,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_53,plain,
    ( ~ l1_struct_0(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK3))
    | v2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_6,plain,
    ( l1_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_56,plain,
    ( l1_struct_0(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1051,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3))
    | k6_domain_1(u1_struct_0(sK3),sK4) = k1_tarski(sK4) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1610,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK4) = k1_tarski(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1415,c_21,c_20,c_19,c_53,c_56,c_1051])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_816,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2277,plain,
    ( m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1610,c_816])).

cnf(c_22,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_23,plain,
    ( l1_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_24,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_52,plain,
    ( l1_struct_0(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_54,plain,
    ( l1_struct_0(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_52])).

cnf(c_55,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_57,plain,
    ( l1_struct_0(sK3) = iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_55])).

cnf(c_3100,plain,
    ( m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2277,c_22,c_23,c_24,c_54,c_57])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | a_2_0_waybel_0(X1,X0) = k3_waybel_0(X1,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_806,plain,
    ( a_2_0_waybel_0(X0,X1) = k3_waybel_0(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3106,plain,
    ( a_2_0_waybel_0(sK3,k1_tarski(sK4)) = k3_waybel_0(sK3,k1_tarski(sK4))
    | v2_struct_0(sK3) = iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3100,c_806])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | k3_waybel_0(X1,k6_domain_1(u1_struct_0(X1),X0)) = k5_waybel_0(X1,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_821,plain,
    ( k3_waybel_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = k5_waybel_0(X0,X1)
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2325,plain,
    ( k3_waybel_0(sK3,k6_domain_1(u1_struct_0(sK3),sK4)) = k5_waybel_0(sK3,sK4)
    | v2_struct_0(sK3) = iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_802,c_821])).

cnf(c_2329,plain,
    ( k3_waybel_0(sK3,k1_tarski(sK4)) = k5_waybel_0(sK3,sK4)
    | v2_struct_0(sK3) = iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2325,c_1610])).

cnf(c_2880,plain,
    ( k3_waybel_0(sK3,k1_tarski(sK4)) = k5_waybel_0(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2329,c_22,c_23])).

cnf(c_3110,plain,
    ( a_2_0_waybel_0(sK3,k1_tarski(sK4)) = k5_waybel_0(sK3,sK4)
    | v2_struct_0(sK3) = iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3106,c_2880])).

cnf(c_3544,plain,
    ( a_2_0_waybel_0(sK3,k1_tarski(sK4)) = k5_waybel_0(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3110,c_22,c_23])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,a_2_0_waybel_0(X1,X2))
    | r2_hidden(sK2(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_812,plain,
    ( r2_hidden(X0,a_2_0_waybel_0(X1,X2)) != iProver_top
    | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_orders_2(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_817,plain,
    ( X0 = X1
    | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2579,plain,
    ( sK2(X0,X1,k1_tarski(X2)) = X2
    | r2_hidden(X0,a_2_0_waybel_0(X1,k1_tarski(X2))) != iProver_top
    | m1_subset_1(k1_tarski(X2),k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_orders_2(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_812,c_817])).

cnf(c_5567,plain,
    ( sK2(X0,sK3,k1_tarski(sK4)) = sK4
    | r2_hidden(X0,k5_waybel_0(sK3,sK4)) != iProver_top
    | m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3544,c_2579])).

cnf(c_6183,plain,
    ( r2_hidden(X0,k5_waybel_0(sK3,sK4)) != iProver_top
    | sK2(X0,sK3,k1_tarski(sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5567,c_22,c_23,c_24,c_54,c_57,c_2277])).

cnf(c_6184,plain,
    ( sK2(X0,sK3,k1_tarski(sK4)) = sK4
    | r2_hidden(X0,k5_waybel_0(sK3,sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_6183])).

cnf(c_6193,plain,
    ( sK2(sK5,sK3,k1_tarski(sK4)) = sK4
    | r1_orders_2(sK3,sK5,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_804,c_6184])).

cnf(c_8,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(X1,a_2_0_waybel_0(X0,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_813,plain,
    ( r1_orders_2(X0,X1,X2) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(X1,a_2_0_waybel_0(X0,X3)) = iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3931,plain,
    ( r1_orders_2(sK3,X0,X1) != iProver_top
    | r2_hidden(X0,a_2_0_waybel_0(sK3,k1_tarski(sK4))) = iProver_top
    | r2_hidden(X1,k1_tarski(sK4)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3100,c_813])).

cnf(c_3939,plain,
    ( r1_orders_2(sK3,X0,X1) != iProver_top
    | r2_hidden(X0,k5_waybel_0(sK3,sK4)) = iProver_top
    | r2_hidden(X1,k1_tarski(sK4)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3931,c_3544])).

cnf(c_4847,plain,
    ( r1_orders_2(sK3,X0,X1) != iProver_top
    | r2_hidden(X0,k5_waybel_0(sK3,sK4)) = iProver_top
    | r2_hidden(X1,k1_tarski(sK4)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3939,c_22,c_23])).

cnf(c_6431,plain,
    ( sK2(sK5,sK3,k1_tarski(sK4)) = sK4
    | r2_hidden(sK4,k1_tarski(sK4)) != iProver_top
    | r2_hidden(sK5,k5_waybel_0(sK3,sK4)) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6193,c_4847])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_25,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_16,negated_conjecture,
    ( ~ r1_orders_2(sK3,sK5,sK4)
    | ~ r2_hidden(sK5,k5_waybel_0(sK3,sK4)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_27,plain,
    ( r1_orders_2(sK3,sK5,sK4) != iProver_top
    | r2_hidden(sK5,k5_waybel_0(sK3,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3,plain,
    ( r2_hidden(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2122,plain,
    ( r2_hidden(sK4,k1_tarski(sK4)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2123,plain,
    ( r2_hidden(sK4,k1_tarski(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2122])).

cnf(c_6434,plain,
    ( sK2(sK5,sK3,k1_tarski(sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6431,c_24,c_25,c_27,c_2123,c_6193])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,a_2_0_waybel_0(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | sK1(X0,X1,X2) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_809,plain,
    ( sK1(X0,X1,X2) = X0
    | r2_hidden(X0,a_2_0_waybel_0(X1,X2)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_orders_2(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3547,plain,
    ( sK1(X0,sK3,k1_tarski(sK4)) = X0
    | r2_hidden(X0,k5_waybel_0(sK3,sK4)) != iProver_top
    | m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3544,c_809])).

cnf(c_4663,plain,
    ( r2_hidden(X0,k5_waybel_0(sK3,sK4)) != iProver_top
    | sK1(X0,sK3,k1_tarski(sK4)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3547,c_22,c_23,c_24,c_54,c_57,c_2277])).

cnf(c_4664,plain,
    ( sK1(X0,sK3,k1_tarski(sK4)) = X0
    | r2_hidden(X0,k5_waybel_0(sK3,sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4663])).

cnf(c_4673,plain,
    ( sK1(sK5,sK3,k1_tarski(sK4)) = sK5
    | r1_orders_2(sK3,sK5,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_804,c_4664])).

cnf(c_4859,plain,
    ( sK1(sK5,sK3,k1_tarski(sK4)) = sK5
    | r2_hidden(sK4,k1_tarski(sK4)) != iProver_top
    | r2_hidden(sK5,k5_waybel_0(sK3,sK4)) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4673,c_4847])).

cnf(c_4891,plain,
    ( sK1(sK5,sK3,k1_tarski(sK4)) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4859,c_24,c_25,c_27,c_2123,c_4673])).

cnf(c_10,plain,
    ( r1_orders_2(X0,sK1(X1,X0,X2),sK2(X1,X0,X2))
    | ~ r2_hidden(X1,a_2_0_waybel_0(X0,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_811,plain,
    ( r1_orders_2(X0,sK1(X1,X0,X2),sK2(X1,X0,X2)) = iProver_top
    | r2_hidden(X1,a_2_0_waybel_0(X0,X2)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4894,plain,
    ( r1_orders_2(sK3,sK5,sK2(sK5,sK3,k1_tarski(sK4))) = iProver_top
    | r2_hidden(sK5,a_2_0_waybel_0(sK3,k1_tarski(sK4))) != iProver_top
    | m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4891,c_811])).

cnf(c_4901,plain,
    ( r1_orders_2(sK3,sK5,sK2(sK5,sK3,k1_tarski(sK4))) = iProver_top
    | r2_hidden(sK5,k5_waybel_0(sK3,sK4)) != iProver_top
    | m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4894,c_3544])).

cnf(c_5006,plain,
    ( r2_hidden(sK5,k5_waybel_0(sK3,sK4)) != iProver_top
    | r1_orders_2(sK3,sK5,sK2(sK5,sK3,k1_tarski(sK4))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4901,c_22,c_23,c_24,c_54,c_57,c_2277])).

cnf(c_5007,plain,
    ( r1_orders_2(sK3,sK5,sK2(sK5,sK3,k1_tarski(sK4))) = iProver_top
    | r2_hidden(sK5,k5_waybel_0(sK3,sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5006])).

cnf(c_6437,plain,
    ( r1_orders_2(sK3,sK5,sK4) = iProver_top
    | r2_hidden(sK5,k5_waybel_0(sK3,sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6434,c_5007])).

cnf(c_6915,plain,
    ( r2_hidden(sK5,k5_waybel_0(sK3,sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6437,c_27])).

cnf(c_6920,plain,
    ( r1_orders_2(sK3,sK5,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_804,c_6915])).

cnf(c_6924,plain,
    ( r2_hidden(sK4,k1_tarski(sK4)) != iProver_top
    | r2_hidden(sK5,k5_waybel_0(sK3,sK4)) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6920,c_4847])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6924,c_6915,c_2123,c_25,c_24])).


%------------------------------------------------------------------------------
