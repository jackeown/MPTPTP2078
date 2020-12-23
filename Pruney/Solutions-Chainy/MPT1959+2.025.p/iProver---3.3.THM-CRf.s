%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:29 EST 2020

% Result     : Theorem 3.21s
% Output     : CNFRefutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :  231 (2308 expanded)
%              Number of clauses        :  142 ( 588 expanded)
%              Number of leaves         :   28 ( 502 expanded)
%              Depth                    :   26
%              Number of atoms          :  834 (20014 expanded)
%              Number of equality atoms :  223 ( 789 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v1_subset_1(X1,u1_struct_0(X0))
          <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & v2_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f19,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f56,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(X0),X1)
            | ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & ( ~ r2_hidden(k3_yellow_0(X0),X1)
            | v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f57,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(X0),X1)
            | ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & ( ~ r2_hidden(k3_yellow_0(X0),X1)
            | v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f56])).

fof(f59,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(X0),X1)
            | ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & ( ~ r2_hidden(k3_yellow_0(X0),X1)
            | v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
     => ( ( r2_hidden(k3_yellow_0(X0),sK7)
          | ~ v1_subset_1(sK7,u1_struct_0(X0)) )
        & ( ~ r2_hidden(k3_yellow_0(X0),sK7)
          | v1_subset_1(sK7,u1_struct_0(X0)) )
        & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0)))
        & v13_waybel_0(sK7,X0)
        & ~ v1_xboole_0(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( r2_hidden(k3_yellow_0(X0),X1)
              | ~ v1_subset_1(X1,u1_struct_0(X0)) )
            & ( ~ r2_hidden(k3_yellow_0(X0),X1)
              | v1_subset_1(X1,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        & l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(sK6),X1)
            | ~ v1_subset_1(X1,u1_struct_0(sK6)) )
          & ( ~ r2_hidden(k3_yellow_0(sK6),X1)
            | v1_subset_1(X1,u1_struct_0(sK6)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
          & v13_waybel_0(X1,sK6)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(sK6)
      & v1_yellow_0(sK6)
      & v5_orders_2(sK6)
      & v4_orders_2(sK6)
      & v3_orders_2(sK6)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,
    ( ( r2_hidden(k3_yellow_0(sK6),sK7)
      | ~ v1_subset_1(sK7,u1_struct_0(sK6)) )
    & ( ~ r2_hidden(k3_yellow_0(sK6),sK7)
      | v1_subset_1(sK7,u1_struct_0(sK6)) )
    & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    & v13_waybel_0(sK7,sK6)
    & ~ v1_xboole_0(sK7)
    & l1_orders_2(sK6)
    & v1_yellow_0(sK6)
    & v5_orders_2(sK6)
    & v4_orders_2(sK6)
    & v3_orders_2(sK6)
    & ~ v2_struct_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f57,f59,f58])).

fof(f95,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f60])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( ! [X2] :
            ( m1_subset_1(X2,X0)
           => r2_hidden(X2,X1) )
       => X0 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f23,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f22])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & m1_subset_1(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ~ r2_hidden(sK2(X0,X1),X1)
        & m1_subset_1(sK2(X0,X1),X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f23,f46])).

fof(f65,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | m1_subset_1(sK2(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1
            & r1_yellow_0(X0,k5_waybel_0(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1
            & r1_yellow_0(X0,k5_waybel_0(X0,X1)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1
            & r1_yellow_0(X0,k5_waybel_0(X0,X1)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f90,plain,(
    v5_orders_2(sK6) ),
    inference(cnf_transformation,[],[f60])).

fof(f87,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f60])).

fof(f88,plain,(
    v3_orders_2(sK6) ),
    inference(cnf_transformation,[],[f60])).

fof(f89,plain,(
    v4_orders_2(sK6) ),
    inference(cnf_transformation,[],[f60])).

fof(f92,plain,(
    l1_orders_2(sK6) ),
    inference(cnf_transformation,[],[f60])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f73,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f93,plain,(
    ~ v1_xboole_0(sK7) ),
    inference(cnf_transformation,[],[f60])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f86,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f97,plain,
    ( r2_hidden(k3_yellow_0(sK6),sK7)
    | ~ v1_subset_1(sK7,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f60])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0] :
    ? [X1] :
      ( ~ v1_subset_1(X1,X0)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( ~ v1_subset_1(sK3(X0),X0)
        & m1_subset_1(sK3(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_subset_1(sK3(X0),X0)
      & m1_subset_1(sK3(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f5,f48])).

fof(f68,plain,(
    ! [X0] : m1_subset_1(sK3(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f49])).

fof(f69,plain,(
    ! [X0] : ~ v1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f49])).

fof(f66,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(sK2(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( ( r1_yellow_0(X0,X2)
            & r1_yellow_0(X0,X1)
            & r1_tarski(X1,X2) )
         => r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
          | ~ r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
          | ~ r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f31])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
      | ~ r1_yellow_0(X0,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ r1_tarski(X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f91,plain,(
    v1_yellow_0(sK6) ),
    inference(cnf_transformation,[],[f60])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r1_yellow_0(X0,k1_xboole_0) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f33,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f34,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f76,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r1_orders_2(X0,X2,X3)
                        & r2_hidden(X2,X1) )
                     => r2_hidden(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f35])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r1_orders_2(X0,X2,X3)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( r2_hidden(X3,X1)
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r2_hidden(X2,X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v13_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r1_orders_2(X0,X2,X3)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r1_orders_2(X0,X4,X5)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v13_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f50])).

fof(f53,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & r1_orders_2(X0,X2,X3)
          & r2_hidden(X2,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r1_orders_2(X0,X2,sK5(X0,X1))
        & r2_hidden(X2,X1)
        & m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(X3,X1)
              & r1_orders_2(X0,X2,X3)
              & r2_hidden(X2,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r2_hidden(X3,X1)
            & r1_orders_2(X0,sK4(X0,X1),X3)
            & r2_hidden(sK4(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ( ~ r2_hidden(sK5(X0,X1),X1)
                & r1_orders_2(X0,sK4(X0,X1),sK5(X0,X1))
                & r2_hidden(sK4(X0,X1),X1)
                & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r1_orders_2(X0,X4,X5)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v13_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f51,f53,f52])).

fof(f77,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r1_orders_2(X0,X4,X5)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f94,plain,(
    v13_waybel_0(sK7,sK6) ),
    inference(cnf_transformation,[],[f60])).

fof(f2,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_xboole_0(X1)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( v1_xboole_0(sK1(X0))
        & m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( v1_xboole_0(sK1(X0))
      & m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f2,f44])).

fof(f64,plain,(
    ! [X0] : v1_xboole_0(sK1(X0)) ),
    inference(cnf_transformation,[],[f45])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f42])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_yellow_0(X0,k5_waybel_0(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f96,plain,
    ( ~ r2_hidden(k3_yellow_0(sK6),sK7)
    | v1_subset_1(sK7,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_2268,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(sK2(X1,X0),X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2274,plain,
    ( X0 = X1
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(sK2(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_yellow_0(X1,k5_waybel_0(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_33,negated_conjecture,
    ( v5_orders_2(sK6) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_625,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | k1_yellow_0(X1,k5_waybel_0(X1,X0)) = X0
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_33])).

cnf(c_626,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6)
    | k1_yellow_0(sK6,k5_waybel_0(sK6,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_625])).

cnf(c_36,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_35,negated_conjecture,
    ( v3_orders_2(sK6) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_34,negated_conjecture,
    ( v4_orders_2(sK6) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_31,negated_conjecture,
    ( l1_orders_2(sK6) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_630,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | k1_yellow_0(sK6,k5_waybel_0(sK6,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_626,c_36,c_35,c_34,c_31])).

cnf(c_2263,plain,
    ( k1_yellow_0(sK6,k5_waybel_0(sK6,X0)) = X0
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_630])).

cnf(c_3476,plain,
    ( k1_yellow_0(sK6,k5_waybel_0(sK6,sK2(u1_struct_0(sK6),X0))) = sK2(u1_struct_0(sK6),X0)
    | u1_struct_0(sK6) = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2274,c_2263])).

cnf(c_7007,plain,
    ( k1_yellow_0(sK6,k5_waybel_0(sK6,sK2(u1_struct_0(sK6),sK7))) = sK2(u1_struct_0(sK6),sK7)
    | u1_struct_0(sK6) = sK7 ),
    inference(superposition,[status(thm)],[c_2268,c_3476])).

cnf(c_13,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_847,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_31])).

cnf(c_848,plain,
    ( m1_subset_1(k1_yellow_0(sK6,X0),u1_struct_0(sK6)) ),
    inference(unflattening,[status(thm)],[c_847])).

cnf(c_2256,plain,
    ( m1_subset_1(k1_yellow_0(sK6,X0),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_848])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2271,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3317,plain,
    ( r2_hidden(k1_yellow_0(sK6,X0),u1_struct_0(sK6)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2256,c_2271])).

cnf(c_12,plain,
    ( ~ l1_orders_2(X0)
    | k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_856,plain,
    ( k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_31])).

cnf(c_857,plain,
    ( k1_yellow_0(sK6,k1_xboole_0) = k3_yellow_0(sK6) ),
    inference(unflattening,[status(thm)],[c_856])).

cnf(c_2591,plain,
    ( m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_857,c_2256])).

cnf(c_3320,plain,
    ( r2_hidden(k3_yellow_0(sK6),u1_struct_0(sK6)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2591,c_2271])).

cnf(c_30,negated_conjecture,
    ( ~ v1_xboole_0(sK7) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_43,plain,
    ( v1_xboole_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_1738,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2692,plain,
    ( sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_1738])).

cnf(c_3142,plain,
    ( ~ m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6))
    | r2_hidden(k3_yellow_0(sK6),u1_struct_0(sK6))
    | v1_xboole_0(u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_3143,plain,
    ( m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6)) != iProver_top
    | r2_hidden(k3_yellow_0(sK6),u1_struct_0(sK6)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3142])).

cnf(c_1741,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2846,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(u1_struct_0(sK6))
    | X0 != u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_1741])).

cnf(c_3664,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK6))
    | v1_xboole_0(sK7)
    | sK7 != u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_2846])).

cnf(c_3665,plain,
    ( sK7 != u1_struct_0(sK6)
    | v1_xboole_0(u1_struct_0(sK6)) != iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3664])).

cnf(c_24,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_26,negated_conjecture,
    ( ~ v1_subset_1(sK7,u1_struct_0(sK6))
    | r2_hidden(k3_yellow_0(sK6),sK7) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_281,plain,
    ( ~ v1_subset_1(sK7,u1_struct_0(sK6))
    | r2_hidden(k3_yellow_0(sK6),sK7) ),
    inference(prop_impl,[status(thm)],[c_26])).

cnf(c_673,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r2_hidden(k3_yellow_0(sK6),sK7)
    | X1 = X0
    | u1_struct_0(sK6) != X1
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_281])).

cnf(c_674,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | r2_hidden(k3_yellow_0(sK6),sK7)
    | u1_struct_0(sK6) = sK7 ),
    inference(unflattening,[status(thm)],[c_673])).

cnf(c_676,plain,
    ( r2_hidden(k3_yellow_0(sK6),sK7)
    | u1_struct_0(sK6) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_674,c_28])).

cnf(c_2261,plain,
    ( u1_struct_0(sK6) = sK7
    | r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_676])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2269,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3526,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | v1_xboole_0(u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2268,c_2269])).

cnf(c_5042,plain,
    ( u1_struct_0(sK6) = sK7
    | v1_xboole_0(u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2261,c_3526])).

cnf(c_1739,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2995,plain,
    ( X0 != X1
    | sK7 != X1
    | sK7 = X0 ),
    inference(instantiation,[status(thm)],[c_1739])).

cnf(c_4089,plain,
    ( X0 != sK7
    | sK7 = X0
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_2995])).

cnf(c_5708,plain,
    ( u1_struct_0(sK6) != sK7
    | sK7 = u1_struct_0(sK6)
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_4089])).

cnf(c_6084,plain,
    ( r2_hidden(k3_yellow_0(sK6),u1_struct_0(sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3320,c_43,c_2591,c_2692,c_3143,c_3665,c_5042,c_5708])).

cnf(c_8,plain,
    ( m1_subset_1(sK3(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2272,plain,
    ( m1_subset_1(sK3(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_7,plain,
    ( ~ v1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_650,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X1 != X2
    | X1 = X0
    | sK3(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_24])).

cnf(c_651,plain,
    ( ~ m1_subset_1(sK3(X0),k1_zfmisc_1(X0))
    | X0 = sK3(X0) ),
    inference(unflattening,[status(thm)],[c_650])).

cnf(c_655,plain,
    ( X0 = sK3(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_651,c_8])).

cnf(c_2296,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2272,c_655])).

cnf(c_4443,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2296,c_2269])).

cnf(c_6089,plain,
    ( v1_xboole_0(u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6084,c_4443])).

cnf(c_6165,plain,
    ( r2_hidden(k1_yellow_0(sK6,X0),u1_struct_0(sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3317,c_43,c_2692,c_3665,c_5042,c_5708])).

cnf(c_7038,plain,
    ( u1_struct_0(sK6) = sK7
    | r2_hidden(sK2(u1_struct_0(sK6),sK7),u1_struct_0(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7007,c_6165])).

cnf(c_1747,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_1761,plain,
    ( u1_struct_0(sK6) = u1_struct_0(sK6)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_1747])).

cnf(c_1769,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_1738])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(sK2(X1,X0),X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2606,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(sK2(u1_struct_0(sK6),sK7),sK7)
    | sK7 = u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2697,plain,
    ( X0 != X1
    | X0 = sK7
    | sK7 != X1 ),
    inference(instantiation,[status(thm)],[c_1739])).

cnf(c_3022,plain,
    ( X0 != u1_struct_0(sK6)
    | X0 = sK7
    | sK7 != u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_2697])).

cnf(c_3815,plain,
    ( u1_struct_0(sK6) != u1_struct_0(sK6)
    | u1_struct_0(sK6) = sK7
    | sK7 != u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_3022])).

cnf(c_14,plain,
    ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
    | ~ r1_yellow_0(X0,X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_829,plain,
    ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
    | ~ r1_yellow_0(X0,X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ r1_tarski(X1,X2)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_31])).

cnf(c_830,plain,
    ( r1_orders_2(sK6,k1_yellow_0(sK6,X0),k1_yellow_0(sK6,X1))
    | ~ r1_yellow_0(sK6,X0)
    | ~ r1_yellow_0(sK6,X1)
    | ~ r1_tarski(X0,X1) ),
    inference(unflattening,[status(thm)],[c_829])).

cnf(c_2257,plain,
    ( r1_orders_2(sK6,k1_yellow_0(sK6,X0),k1_yellow_0(sK6,X1)) = iProver_top
    | r1_yellow_0(sK6,X0) != iProver_top
    | r1_yellow_0(sK6,X1) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_830])).

cnf(c_2898,plain,
    ( r1_orders_2(sK6,k3_yellow_0(sK6),k1_yellow_0(sK6,X0)) = iProver_top
    | r1_yellow_0(sK6,X0) != iProver_top
    | r1_yellow_0(sK6,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_857,c_2257])).

cnf(c_37,plain,
    ( v2_struct_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_40,plain,
    ( v5_orders_2(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( v1_yellow_0(sK6) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_41,plain,
    ( v1_yellow_0(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_42,plain,
    ( l1_orders_2(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_15,plain,
    ( r1_yellow_0(X0,k1_xboole_0)
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_yellow_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_76,plain,
    ( r1_yellow_0(X0,k1_xboole_0) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v5_orders_2(X0) != iProver_top
    | v1_yellow_0(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_78,plain,
    ( r1_yellow_0(sK6,k1_xboole_0) = iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v5_orders_2(sK6) != iProver_top
    | v1_yellow_0(sK6) != iProver_top
    | l1_orders_2(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_76])).

cnf(c_2923,plain,
    ( r1_yellow_0(sK6,X0) != iProver_top
    | r1_orders_2(sK6,k3_yellow_0(sK6),k1_yellow_0(sK6,X0)) = iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2898,c_37,c_40,c_41,c_42,c_78])).

cnf(c_2924,plain,
    ( r1_orders_2(sK6,k3_yellow_0(sK6),k1_yellow_0(sK6,X0)) = iProver_top
    | r1_yellow_0(sK6,X0) != iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2923])).

cnf(c_21,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ v13_waybel_0(X3,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X1,X3)
    | r2_hidden(X2,X3)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_789,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ v13_waybel_0(X3,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X1,X3)
    | r2_hidden(X2,X3)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_31])).

cnf(c_790,plain,
    ( ~ r1_orders_2(sK6,X0,X1)
    | ~ v13_waybel_0(X2,sK6)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,X2) ),
    inference(unflattening,[status(thm)],[c_789])).

cnf(c_10,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_806,plain,
    ( ~ r1_orders_2(sK6,X0,X1)
    | ~ v13_waybel_0(X2,sK6)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,X2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_790,c_10])).

cnf(c_2259,plain,
    ( r1_orders_2(sK6,X0,X1) != iProver_top
    | v13_waybel_0(X2,sK6) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X1,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_806])).

cnf(c_4155,plain,
    ( r1_orders_2(sK6,X0,X1) != iProver_top
    | v13_waybel_0(sK7,sK6) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X1,sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_2268,c_2259])).

cnf(c_45,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_29,negated_conjecture,
    ( v13_waybel_0(sK7,sK6) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1064,plain,
    ( ~ r1_orders_2(sK6,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,X2)
    | sK7 != X2
    | sK6 != sK6 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_806])).

cnf(c_1065,plain,
    ( ~ r1_orders_2(sK6,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(X0,sK7)
    | r2_hidden(X1,sK7) ),
    inference(unflattening,[status(thm)],[c_1064])).

cnf(c_1066,plain,
    ( r1_orders_2(sK6,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X1,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1065])).

cnf(c_4733,plain,
    ( r1_orders_2(sK6,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X1,sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4155,c_45,c_1066])).

cnf(c_4743,plain,
    ( r1_yellow_0(sK6,X0) != iProver_top
    | m1_subset_1(k1_yellow_0(sK6,X0),u1_struct_0(sK6)) != iProver_top
    | r2_hidden(k1_yellow_0(sK6,X0),sK7) = iProver_top
    | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2924,c_4733])).

cnf(c_44,plain,
    ( v13_waybel_0(sK7,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_849,plain,
    ( m1_subset_1(k1_yellow_0(sK6,X0),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_848])).

cnf(c_2499,plain,
    ( ~ r1_orders_2(sK6,X0,X1)
    | ~ v13_waybel_0(sK7,sK6)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(X0,sK7)
    | r2_hidden(X1,sK7) ),
    inference(instantiation,[status(thm)],[c_806])).

cnf(c_2716,plain,
    ( ~ r1_orders_2(sK6,k3_yellow_0(sK6),X0)
    | ~ v13_waybel_0(sK7,sK6)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | r2_hidden(X0,sK7)
    | ~ r2_hidden(k3_yellow_0(sK6),sK7) ),
    inference(instantiation,[status(thm)],[c_2499])).

cnf(c_3164,plain,
    ( ~ r1_orders_2(sK6,k3_yellow_0(sK6),k1_yellow_0(sK6,X0))
    | ~ v13_waybel_0(sK7,sK6)
    | ~ m1_subset_1(k1_yellow_0(sK6,X0),u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | r2_hidden(k1_yellow_0(sK6,X0),sK7)
    | ~ r2_hidden(k3_yellow_0(sK6),sK7) ),
    inference(instantiation,[status(thm)],[c_2716])).

cnf(c_3165,plain,
    ( r1_orders_2(sK6,k3_yellow_0(sK6),k1_yellow_0(sK6,X0)) != iProver_top
    | v13_waybel_0(sK7,sK6) != iProver_top
    | m1_subset_1(k1_yellow_0(sK6,X0),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_hidden(k1_yellow_0(sK6,X0),sK7) = iProver_top
    | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3164])).

cnf(c_2,plain,
    ( v1_xboole_0(sK1(X0)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2277,plain,
    ( v1_xboole_0(sK1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2278,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_6,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2273,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3525,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2273,c_2269])).

cnf(c_5097,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2278,c_3525])).

cnf(c_5104,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2277,c_5097])).

cnf(c_2659,plain,
    ( k1_yellow_0(sK6,k5_waybel_0(sK6,k1_yellow_0(sK6,X0))) = k1_yellow_0(sK6,X0) ),
    inference(superposition,[status(thm)],[c_2256,c_2263])).

cnf(c_3714,plain,
    ( r1_orders_2(sK6,k3_yellow_0(sK6),k1_yellow_0(sK6,X0)) = iProver_top
    | r1_yellow_0(sK6,k5_waybel_0(sK6,k1_yellow_0(sK6,X0))) != iProver_top
    | r1_tarski(k1_xboole_0,k5_waybel_0(sK6,k1_yellow_0(sK6,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2659,c_2924])).

cnf(c_23,plain,
    ( r1_yellow_0(X0,k5_waybel_0(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_607,plain,
    ( r1_yellow_0(X0,k5_waybel_0(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_33])).

cnf(c_608,plain,
    ( r1_yellow_0(sK6,k5_waybel_0(sK6,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(unflattening,[status(thm)],[c_607])).

cnf(c_612,plain,
    ( r1_yellow_0(sK6,k5_waybel_0(sK6,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_608,c_36,c_35,c_34,c_31])).

cnf(c_2475,plain,
    ( r1_yellow_0(sK6,k5_waybel_0(sK6,k1_yellow_0(sK6,X0)))
    | ~ m1_subset_1(k1_yellow_0(sK6,X0),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_612])).

cnf(c_2476,plain,
    ( r1_yellow_0(sK6,k5_waybel_0(sK6,k1_yellow_0(sK6,X0))) = iProver_top
    | m1_subset_1(k1_yellow_0(sK6,X0),u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2475])).

cnf(c_4971,plain,
    ( r1_orders_2(sK6,k3_yellow_0(sK6),k1_yellow_0(sK6,X0)) = iProver_top
    | r1_tarski(k1_xboole_0,k5_waybel_0(sK6,k1_yellow_0(sK6,X0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3714,c_849,c_2476])).

cnf(c_5140,plain,
    ( r1_orders_2(sK6,k3_yellow_0(sK6),k1_yellow_0(sK6,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5104,c_4971])).

cnf(c_5506,plain,
    ( r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top
    | r2_hidden(k1_yellow_0(sK6,X0),sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4743,c_44,c_45,c_849,c_3165,c_5140])).

cnf(c_5507,plain,
    ( r2_hidden(k1_yellow_0(sK6,X0),sK7) = iProver_top
    | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_5506])).

cnf(c_7040,plain,
    ( u1_struct_0(sK6) = sK7
    | r2_hidden(sK2(u1_struct_0(sK6),sK7),sK7) = iProver_top
    | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_7007,c_5507])).

cnf(c_7197,plain,
    ( r2_hidden(sK2(u1_struct_0(sK6),sK7),sK7)
    | ~ r2_hidden(k3_yellow_0(sK6),sK7)
    | u1_struct_0(sK6) = sK7 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7040])).

cnf(c_7344,plain,
    ( u1_struct_0(sK6) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7038,c_28,c_676,c_1761,c_1769,c_2606,c_3815,c_7197])).

cnf(c_7355,plain,
    ( r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7344,c_6084])).

cnf(c_27,negated_conjecture,
    ( v1_subset_1(sK7,u1_struct_0(sK6))
    | ~ r2_hidden(k3_yellow_0(sK6),sK7) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_279,plain,
    ( v1_subset_1(sK7,u1_struct_0(sK6))
    | ~ r2_hidden(k3_yellow_0(sK6),sK7) ),
    inference(prop_impl,[status(thm)],[c_27])).

cnf(c_661,plain,
    ( ~ r2_hidden(k3_yellow_0(sK6),sK7)
    | u1_struct_0(sK6) != X0
    | sK3(X0) != sK7 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_279])).

cnf(c_662,plain,
    ( ~ r2_hidden(k3_yellow_0(sK6),sK7)
    | sK3(u1_struct_0(sK6)) != sK7 ),
    inference(unflattening,[status(thm)],[c_661])).

cnf(c_2262,plain,
    ( sK3(u1_struct_0(sK6)) != sK7
    | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_662])).

cnf(c_2311,plain,
    ( u1_struct_0(sK6) != sK7
    | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2262,c_655])).

cnf(c_7356,plain,
    ( sK7 != sK7
    | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7344,c_2311])).

cnf(c_7446,plain,
    ( r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_7356])).

cnf(c_7450,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7355,c_7446])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:11:53 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.21/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.00  
% 3.21/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.21/1.00  
% 3.21/1.00  ------  iProver source info
% 3.21/1.00  
% 3.21/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.21/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.21/1.00  git: non_committed_changes: false
% 3.21/1.00  git: last_make_outside_of_git: false
% 3.21/1.00  
% 3.21/1.00  ------ 
% 3.21/1.00  
% 3.21/1.00  ------ Input Options
% 3.21/1.00  
% 3.21/1.00  --out_options                           all
% 3.21/1.00  --tptp_safe_out                         true
% 3.21/1.00  --problem_path                          ""
% 3.21/1.00  --include_path                          ""
% 3.21/1.00  --clausifier                            res/vclausify_rel
% 3.21/1.00  --clausifier_options                    --mode clausify
% 3.21/1.00  --stdin                                 false
% 3.21/1.00  --stats_out                             all
% 3.21/1.00  
% 3.21/1.00  ------ General Options
% 3.21/1.00  
% 3.21/1.00  --fof                                   false
% 3.21/1.00  --time_out_real                         305.
% 3.21/1.00  --time_out_virtual                      -1.
% 3.21/1.00  --symbol_type_check                     false
% 3.21/1.00  --clausify_out                          false
% 3.21/1.00  --sig_cnt_out                           false
% 3.21/1.00  --trig_cnt_out                          false
% 3.21/1.00  --trig_cnt_out_tolerance                1.
% 3.21/1.00  --trig_cnt_out_sk_spl                   false
% 3.21/1.00  --abstr_cl_out                          false
% 3.21/1.00  
% 3.21/1.00  ------ Global Options
% 3.21/1.00  
% 3.21/1.00  --schedule                              default
% 3.21/1.00  --add_important_lit                     false
% 3.21/1.00  --prop_solver_per_cl                    1000
% 3.21/1.00  --min_unsat_core                        false
% 3.21/1.00  --soft_assumptions                      false
% 3.21/1.00  --soft_lemma_size                       3
% 3.21/1.00  --prop_impl_unit_size                   0
% 3.21/1.00  --prop_impl_unit                        []
% 3.21/1.00  --share_sel_clauses                     true
% 3.21/1.00  --reset_solvers                         false
% 3.21/1.00  --bc_imp_inh                            [conj_cone]
% 3.21/1.00  --conj_cone_tolerance                   3.
% 3.21/1.00  --extra_neg_conj                        none
% 3.21/1.00  --large_theory_mode                     true
% 3.21/1.00  --prolific_symb_bound                   200
% 3.21/1.00  --lt_threshold                          2000
% 3.21/1.00  --clause_weak_htbl                      true
% 3.21/1.00  --gc_record_bc_elim                     false
% 3.21/1.00  
% 3.21/1.00  ------ Preprocessing Options
% 3.21/1.00  
% 3.21/1.00  --preprocessing_flag                    true
% 3.21/1.00  --time_out_prep_mult                    0.1
% 3.21/1.00  --splitting_mode                        input
% 3.21/1.00  --splitting_grd                         true
% 3.21/1.00  --splitting_cvd                         false
% 3.21/1.00  --splitting_cvd_svl                     false
% 3.21/1.00  --splitting_nvd                         32
% 3.21/1.00  --sub_typing                            true
% 3.21/1.00  --prep_gs_sim                           true
% 3.21/1.00  --prep_unflatten                        true
% 3.21/1.00  --prep_res_sim                          true
% 3.21/1.00  --prep_upred                            true
% 3.21/1.00  --prep_sem_filter                       exhaustive
% 3.21/1.00  --prep_sem_filter_out                   false
% 3.21/1.00  --pred_elim                             true
% 3.21/1.00  --res_sim_input                         true
% 3.21/1.00  --eq_ax_congr_red                       true
% 3.21/1.00  --pure_diseq_elim                       true
% 3.21/1.00  --brand_transform                       false
% 3.21/1.00  --non_eq_to_eq                          false
% 3.21/1.00  --prep_def_merge                        true
% 3.21/1.00  --prep_def_merge_prop_impl              false
% 3.21/1.00  --prep_def_merge_mbd                    true
% 3.21/1.00  --prep_def_merge_tr_red                 false
% 3.21/1.00  --prep_def_merge_tr_cl                  false
% 3.21/1.00  --smt_preprocessing                     true
% 3.21/1.00  --smt_ac_axioms                         fast
% 3.21/1.00  --preprocessed_out                      false
% 3.21/1.00  --preprocessed_stats                    false
% 3.21/1.00  
% 3.21/1.00  ------ Abstraction refinement Options
% 3.21/1.00  
% 3.21/1.00  --abstr_ref                             []
% 3.21/1.00  --abstr_ref_prep                        false
% 3.21/1.00  --abstr_ref_until_sat                   false
% 3.21/1.00  --abstr_ref_sig_restrict                funpre
% 3.21/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.21/1.00  --abstr_ref_under                       []
% 3.21/1.00  
% 3.21/1.00  ------ SAT Options
% 3.21/1.00  
% 3.21/1.00  --sat_mode                              false
% 3.21/1.00  --sat_fm_restart_options                ""
% 3.21/1.00  --sat_gr_def                            false
% 3.21/1.00  --sat_epr_types                         true
% 3.21/1.00  --sat_non_cyclic_types                  false
% 3.21/1.00  --sat_finite_models                     false
% 3.21/1.00  --sat_fm_lemmas                         false
% 3.21/1.00  --sat_fm_prep                           false
% 3.21/1.00  --sat_fm_uc_incr                        true
% 3.21/1.00  --sat_out_model                         small
% 3.21/1.00  --sat_out_clauses                       false
% 3.21/1.00  
% 3.21/1.00  ------ QBF Options
% 3.21/1.00  
% 3.21/1.00  --qbf_mode                              false
% 3.21/1.00  --qbf_elim_univ                         false
% 3.21/1.00  --qbf_dom_inst                          none
% 3.21/1.00  --qbf_dom_pre_inst                      false
% 3.21/1.00  --qbf_sk_in                             false
% 3.21/1.00  --qbf_pred_elim                         true
% 3.21/1.00  --qbf_split                             512
% 3.21/1.00  
% 3.21/1.00  ------ BMC1 Options
% 3.21/1.00  
% 3.21/1.00  --bmc1_incremental                      false
% 3.21/1.00  --bmc1_axioms                           reachable_all
% 3.21/1.00  --bmc1_min_bound                        0
% 3.21/1.00  --bmc1_max_bound                        -1
% 3.21/1.00  --bmc1_max_bound_default                -1
% 3.21/1.00  --bmc1_symbol_reachability              true
% 3.21/1.00  --bmc1_property_lemmas                  false
% 3.21/1.00  --bmc1_k_induction                      false
% 3.21/1.00  --bmc1_non_equiv_states                 false
% 3.21/1.00  --bmc1_deadlock                         false
% 3.21/1.00  --bmc1_ucm                              false
% 3.21/1.00  --bmc1_add_unsat_core                   none
% 3.21/1.00  --bmc1_unsat_core_children              false
% 3.21/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.21/1.00  --bmc1_out_stat                         full
% 3.21/1.00  --bmc1_ground_init                      false
% 3.21/1.00  --bmc1_pre_inst_next_state              false
% 3.21/1.00  --bmc1_pre_inst_state                   false
% 3.21/1.00  --bmc1_pre_inst_reach_state             false
% 3.21/1.00  --bmc1_out_unsat_core                   false
% 3.21/1.00  --bmc1_aig_witness_out                  false
% 3.21/1.00  --bmc1_verbose                          false
% 3.21/1.00  --bmc1_dump_clauses_tptp                false
% 3.21/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.21/1.00  --bmc1_dump_file                        -
% 3.21/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.21/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.21/1.00  --bmc1_ucm_extend_mode                  1
% 3.21/1.00  --bmc1_ucm_init_mode                    2
% 3.21/1.00  --bmc1_ucm_cone_mode                    none
% 3.21/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.21/1.00  --bmc1_ucm_relax_model                  4
% 3.21/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.21/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.21/1.00  --bmc1_ucm_layered_model                none
% 3.21/1.00  --bmc1_ucm_max_lemma_size               10
% 3.21/1.00  
% 3.21/1.00  ------ AIG Options
% 3.21/1.00  
% 3.21/1.00  --aig_mode                              false
% 3.21/1.00  
% 3.21/1.00  ------ Instantiation Options
% 3.21/1.00  
% 3.21/1.00  --instantiation_flag                    true
% 3.21/1.00  --inst_sos_flag                         false
% 3.21/1.00  --inst_sos_phase                        true
% 3.21/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.21/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.21/1.00  --inst_lit_sel_side                     num_symb
% 3.21/1.00  --inst_solver_per_active                1400
% 3.21/1.00  --inst_solver_calls_frac                1.
% 3.21/1.00  --inst_passive_queue_type               priority_queues
% 3.21/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.21/1.00  --inst_passive_queues_freq              [25;2]
% 3.21/1.00  --inst_dismatching                      true
% 3.21/1.00  --inst_eager_unprocessed_to_passive     true
% 3.21/1.00  --inst_prop_sim_given                   true
% 3.21/1.00  --inst_prop_sim_new                     false
% 3.21/1.00  --inst_subs_new                         false
% 3.21/1.00  --inst_eq_res_simp                      false
% 3.21/1.00  --inst_subs_given                       false
% 3.21/1.00  --inst_orphan_elimination               true
% 3.21/1.00  --inst_learning_loop_flag               true
% 3.21/1.00  --inst_learning_start                   3000
% 3.21/1.00  --inst_learning_factor                  2
% 3.21/1.00  --inst_start_prop_sim_after_learn       3
% 3.21/1.00  --inst_sel_renew                        solver
% 3.21/1.00  --inst_lit_activity_flag                true
% 3.21/1.00  --inst_restr_to_given                   false
% 3.21/1.00  --inst_activity_threshold               500
% 3.21/1.00  --inst_out_proof                        true
% 3.21/1.00  
% 3.21/1.00  ------ Resolution Options
% 3.21/1.00  
% 3.21/1.00  --resolution_flag                       true
% 3.21/1.00  --res_lit_sel                           adaptive
% 3.21/1.00  --res_lit_sel_side                      none
% 3.21/1.00  --res_ordering                          kbo
% 3.21/1.00  --res_to_prop_solver                    active
% 3.21/1.00  --res_prop_simpl_new                    false
% 3.21/1.00  --res_prop_simpl_given                  true
% 3.21/1.00  --res_passive_queue_type                priority_queues
% 3.21/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.21/1.00  --res_passive_queues_freq               [15;5]
% 3.21/1.00  --res_forward_subs                      full
% 3.21/1.00  --res_backward_subs                     full
% 3.21/1.00  --res_forward_subs_resolution           true
% 3.21/1.00  --res_backward_subs_resolution          true
% 3.21/1.00  --res_orphan_elimination                true
% 3.21/1.00  --res_time_limit                        2.
% 3.21/1.00  --res_out_proof                         true
% 3.21/1.00  
% 3.21/1.00  ------ Superposition Options
% 3.21/1.00  
% 3.21/1.00  --superposition_flag                    true
% 3.21/1.00  --sup_passive_queue_type                priority_queues
% 3.21/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.21/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.21/1.00  --demod_completeness_check              fast
% 3.21/1.00  --demod_use_ground                      true
% 3.21/1.00  --sup_to_prop_solver                    passive
% 3.21/1.00  --sup_prop_simpl_new                    true
% 3.21/1.00  --sup_prop_simpl_given                  true
% 3.21/1.00  --sup_fun_splitting                     false
% 3.21/1.00  --sup_smt_interval                      50000
% 3.21/1.00  
% 3.21/1.00  ------ Superposition Simplification Setup
% 3.21/1.00  
% 3.21/1.00  --sup_indices_passive                   []
% 3.21/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.21/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.21/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.21/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.21/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.21/1.00  --sup_full_bw                           [BwDemod]
% 3.21/1.00  --sup_immed_triv                        [TrivRules]
% 3.21/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.21/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.21/1.00  --sup_immed_bw_main                     []
% 3.21/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.21/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.21/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.21/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.21/1.00  
% 3.21/1.00  ------ Combination Options
% 3.21/1.00  
% 3.21/1.00  --comb_res_mult                         3
% 3.21/1.00  --comb_sup_mult                         2
% 3.21/1.00  --comb_inst_mult                        10
% 3.21/1.00  
% 3.21/1.00  ------ Debug Options
% 3.21/1.00  
% 3.21/1.00  --dbg_backtrace                         false
% 3.21/1.00  --dbg_dump_prop_clauses                 false
% 3.21/1.00  --dbg_dump_prop_clauses_file            -
% 3.21/1.00  --dbg_out_stat                          false
% 3.21/1.00  ------ Parsing...
% 3.21/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.21/1.00  
% 3.21/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 3.21/1.00  
% 3.21/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.21/1.00  
% 3.21/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.21/1.00  ------ Proving...
% 3.21/1.00  ------ Problem Properties 
% 3.21/1.00  
% 3.21/1.00  
% 3.21/1.00  clauses                                 30
% 3.21/1.00  conjectures                             3
% 3.21/1.00  EPR                                     4
% 3.21/1.00  Horn                                    22
% 3.21/1.00  unary                                   11
% 3.21/1.00  binary                                  6
% 3.21/1.00  lits                                    66
% 3.21/1.00  lits eq                                 8
% 3.21/1.00  fd_pure                                 0
% 3.21/1.00  fd_pseudo                               0
% 3.21/1.00  fd_cond                                 0
% 3.21/1.00  fd_pseudo_cond                          2
% 3.21/1.00  AC symbols                              0
% 3.21/1.00  
% 3.21/1.00  ------ Schedule dynamic 5 is on 
% 3.21/1.00  
% 3.21/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.21/1.00  
% 3.21/1.00  
% 3.21/1.00  ------ 
% 3.21/1.00  Current options:
% 3.21/1.00  ------ 
% 3.21/1.00  
% 3.21/1.00  ------ Input Options
% 3.21/1.00  
% 3.21/1.00  --out_options                           all
% 3.21/1.00  --tptp_safe_out                         true
% 3.21/1.00  --problem_path                          ""
% 3.21/1.00  --include_path                          ""
% 3.21/1.00  --clausifier                            res/vclausify_rel
% 3.21/1.00  --clausifier_options                    --mode clausify
% 3.21/1.00  --stdin                                 false
% 3.21/1.00  --stats_out                             all
% 3.21/1.00  
% 3.21/1.00  ------ General Options
% 3.21/1.00  
% 3.21/1.00  --fof                                   false
% 3.21/1.00  --time_out_real                         305.
% 3.21/1.00  --time_out_virtual                      -1.
% 3.21/1.00  --symbol_type_check                     false
% 3.21/1.00  --clausify_out                          false
% 3.21/1.00  --sig_cnt_out                           false
% 3.21/1.00  --trig_cnt_out                          false
% 3.21/1.00  --trig_cnt_out_tolerance                1.
% 3.21/1.00  --trig_cnt_out_sk_spl                   false
% 3.21/1.00  --abstr_cl_out                          false
% 3.21/1.00  
% 3.21/1.00  ------ Global Options
% 3.21/1.00  
% 3.21/1.00  --schedule                              default
% 3.21/1.00  --add_important_lit                     false
% 3.21/1.00  --prop_solver_per_cl                    1000
% 3.21/1.00  --min_unsat_core                        false
% 3.21/1.00  --soft_assumptions                      false
% 3.21/1.00  --soft_lemma_size                       3
% 3.21/1.00  --prop_impl_unit_size                   0
% 3.21/1.00  --prop_impl_unit                        []
% 3.21/1.00  --share_sel_clauses                     true
% 3.21/1.00  --reset_solvers                         false
% 3.21/1.00  --bc_imp_inh                            [conj_cone]
% 3.21/1.00  --conj_cone_tolerance                   3.
% 3.21/1.00  --extra_neg_conj                        none
% 3.21/1.00  --large_theory_mode                     true
% 3.21/1.00  --prolific_symb_bound                   200
% 3.21/1.00  --lt_threshold                          2000
% 3.21/1.00  --clause_weak_htbl                      true
% 3.21/1.00  --gc_record_bc_elim                     false
% 3.21/1.00  
% 3.21/1.00  ------ Preprocessing Options
% 3.21/1.00  
% 3.21/1.00  --preprocessing_flag                    true
% 3.21/1.00  --time_out_prep_mult                    0.1
% 3.21/1.00  --splitting_mode                        input
% 3.21/1.00  --splitting_grd                         true
% 3.21/1.00  --splitting_cvd                         false
% 3.21/1.00  --splitting_cvd_svl                     false
% 3.21/1.00  --splitting_nvd                         32
% 3.21/1.00  --sub_typing                            true
% 3.21/1.00  --prep_gs_sim                           true
% 3.21/1.00  --prep_unflatten                        true
% 3.21/1.00  --prep_res_sim                          true
% 3.21/1.00  --prep_upred                            true
% 3.21/1.00  --prep_sem_filter                       exhaustive
% 3.21/1.00  --prep_sem_filter_out                   false
% 3.21/1.00  --pred_elim                             true
% 3.21/1.00  --res_sim_input                         true
% 3.21/1.00  --eq_ax_congr_red                       true
% 3.21/1.00  --pure_diseq_elim                       true
% 3.21/1.00  --brand_transform                       false
% 3.21/1.00  --non_eq_to_eq                          false
% 3.21/1.00  --prep_def_merge                        true
% 3.21/1.00  --prep_def_merge_prop_impl              false
% 3.21/1.00  --prep_def_merge_mbd                    true
% 3.21/1.00  --prep_def_merge_tr_red                 false
% 3.21/1.00  --prep_def_merge_tr_cl                  false
% 3.21/1.00  --smt_preprocessing                     true
% 3.21/1.00  --smt_ac_axioms                         fast
% 3.21/1.00  --preprocessed_out                      false
% 3.21/1.00  --preprocessed_stats                    false
% 3.21/1.00  
% 3.21/1.00  ------ Abstraction refinement Options
% 3.21/1.00  
% 3.21/1.00  --abstr_ref                             []
% 3.21/1.00  --abstr_ref_prep                        false
% 3.21/1.00  --abstr_ref_until_sat                   false
% 3.21/1.00  --abstr_ref_sig_restrict                funpre
% 3.21/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.21/1.00  --abstr_ref_under                       []
% 3.21/1.00  
% 3.21/1.00  ------ SAT Options
% 3.21/1.00  
% 3.21/1.00  --sat_mode                              false
% 3.21/1.00  --sat_fm_restart_options                ""
% 3.21/1.00  --sat_gr_def                            false
% 3.21/1.00  --sat_epr_types                         true
% 3.21/1.00  --sat_non_cyclic_types                  false
% 3.21/1.00  --sat_finite_models                     false
% 3.21/1.00  --sat_fm_lemmas                         false
% 3.21/1.00  --sat_fm_prep                           false
% 3.21/1.00  --sat_fm_uc_incr                        true
% 3.21/1.00  --sat_out_model                         small
% 3.21/1.00  --sat_out_clauses                       false
% 3.21/1.00  
% 3.21/1.00  ------ QBF Options
% 3.21/1.00  
% 3.21/1.00  --qbf_mode                              false
% 3.21/1.00  --qbf_elim_univ                         false
% 3.21/1.00  --qbf_dom_inst                          none
% 3.21/1.00  --qbf_dom_pre_inst                      false
% 3.21/1.00  --qbf_sk_in                             false
% 3.21/1.00  --qbf_pred_elim                         true
% 3.21/1.00  --qbf_split                             512
% 3.21/1.00  
% 3.21/1.00  ------ BMC1 Options
% 3.21/1.00  
% 3.21/1.00  --bmc1_incremental                      false
% 3.21/1.00  --bmc1_axioms                           reachable_all
% 3.21/1.00  --bmc1_min_bound                        0
% 3.21/1.00  --bmc1_max_bound                        -1
% 3.21/1.00  --bmc1_max_bound_default                -1
% 3.21/1.00  --bmc1_symbol_reachability              true
% 3.21/1.00  --bmc1_property_lemmas                  false
% 3.21/1.00  --bmc1_k_induction                      false
% 3.21/1.00  --bmc1_non_equiv_states                 false
% 3.21/1.00  --bmc1_deadlock                         false
% 3.21/1.00  --bmc1_ucm                              false
% 3.21/1.00  --bmc1_add_unsat_core                   none
% 3.21/1.00  --bmc1_unsat_core_children              false
% 3.21/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.21/1.00  --bmc1_out_stat                         full
% 3.21/1.00  --bmc1_ground_init                      false
% 3.21/1.00  --bmc1_pre_inst_next_state              false
% 3.21/1.00  --bmc1_pre_inst_state                   false
% 3.21/1.00  --bmc1_pre_inst_reach_state             false
% 3.21/1.00  --bmc1_out_unsat_core                   false
% 3.21/1.00  --bmc1_aig_witness_out                  false
% 3.21/1.00  --bmc1_verbose                          false
% 3.21/1.00  --bmc1_dump_clauses_tptp                false
% 3.21/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.21/1.00  --bmc1_dump_file                        -
% 3.21/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.21/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.21/1.00  --bmc1_ucm_extend_mode                  1
% 3.21/1.00  --bmc1_ucm_init_mode                    2
% 3.21/1.00  --bmc1_ucm_cone_mode                    none
% 3.21/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.21/1.00  --bmc1_ucm_relax_model                  4
% 3.21/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.21/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.21/1.00  --bmc1_ucm_layered_model                none
% 3.21/1.00  --bmc1_ucm_max_lemma_size               10
% 3.21/1.00  
% 3.21/1.00  ------ AIG Options
% 3.21/1.00  
% 3.21/1.00  --aig_mode                              false
% 3.21/1.00  
% 3.21/1.00  ------ Instantiation Options
% 3.21/1.00  
% 3.21/1.00  --instantiation_flag                    true
% 3.21/1.00  --inst_sos_flag                         false
% 3.21/1.00  --inst_sos_phase                        true
% 3.21/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.21/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.21/1.00  --inst_lit_sel_side                     none
% 3.21/1.00  --inst_solver_per_active                1400
% 3.21/1.00  --inst_solver_calls_frac                1.
% 3.21/1.00  --inst_passive_queue_type               priority_queues
% 3.21/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.21/1.00  --inst_passive_queues_freq              [25;2]
% 3.21/1.00  --inst_dismatching                      true
% 3.21/1.00  --inst_eager_unprocessed_to_passive     true
% 3.21/1.00  --inst_prop_sim_given                   true
% 3.21/1.00  --inst_prop_sim_new                     false
% 3.21/1.00  --inst_subs_new                         false
% 3.21/1.00  --inst_eq_res_simp                      false
% 3.21/1.00  --inst_subs_given                       false
% 3.21/1.00  --inst_orphan_elimination               true
% 3.21/1.00  --inst_learning_loop_flag               true
% 3.21/1.00  --inst_learning_start                   3000
% 3.21/1.00  --inst_learning_factor                  2
% 3.21/1.00  --inst_start_prop_sim_after_learn       3
% 3.21/1.00  --inst_sel_renew                        solver
% 3.21/1.00  --inst_lit_activity_flag                true
% 3.21/1.00  --inst_restr_to_given                   false
% 3.21/1.00  --inst_activity_threshold               500
% 3.21/1.00  --inst_out_proof                        true
% 3.21/1.00  
% 3.21/1.00  ------ Resolution Options
% 3.21/1.00  
% 3.21/1.00  --resolution_flag                       false
% 3.21/1.00  --res_lit_sel                           adaptive
% 3.21/1.00  --res_lit_sel_side                      none
% 3.21/1.00  --res_ordering                          kbo
% 3.21/1.00  --res_to_prop_solver                    active
% 3.21/1.00  --res_prop_simpl_new                    false
% 3.21/1.00  --res_prop_simpl_given                  true
% 3.21/1.00  --res_passive_queue_type                priority_queues
% 3.21/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.21/1.00  --res_passive_queues_freq               [15;5]
% 3.21/1.00  --res_forward_subs                      full
% 3.21/1.00  --res_backward_subs                     full
% 3.21/1.00  --res_forward_subs_resolution           true
% 3.21/1.00  --res_backward_subs_resolution          true
% 3.21/1.00  --res_orphan_elimination                true
% 3.21/1.00  --res_time_limit                        2.
% 3.21/1.00  --res_out_proof                         true
% 3.21/1.00  
% 3.21/1.00  ------ Superposition Options
% 3.21/1.00  
% 3.21/1.00  --superposition_flag                    true
% 3.21/1.00  --sup_passive_queue_type                priority_queues
% 3.21/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.21/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.21/1.00  --demod_completeness_check              fast
% 3.21/1.00  --demod_use_ground                      true
% 3.21/1.00  --sup_to_prop_solver                    passive
% 3.21/1.00  --sup_prop_simpl_new                    true
% 3.21/1.00  --sup_prop_simpl_given                  true
% 3.21/1.00  --sup_fun_splitting                     false
% 3.21/1.00  --sup_smt_interval                      50000
% 3.21/1.00  
% 3.21/1.00  ------ Superposition Simplification Setup
% 3.21/1.00  
% 3.21/1.00  --sup_indices_passive                   []
% 3.21/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.21/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.21/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.21/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.21/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.21/1.00  --sup_full_bw                           [BwDemod]
% 3.21/1.00  --sup_immed_triv                        [TrivRules]
% 3.21/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.21/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.21/1.00  --sup_immed_bw_main                     []
% 3.21/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.21/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.21/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.21/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.21/1.00  
% 3.21/1.00  ------ Combination Options
% 3.21/1.00  
% 3.21/1.00  --comb_res_mult                         3
% 3.21/1.00  --comb_sup_mult                         2
% 3.21/1.00  --comb_inst_mult                        10
% 3.21/1.00  
% 3.21/1.00  ------ Debug Options
% 3.21/1.00  
% 3.21/1.00  --dbg_backtrace                         false
% 3.21/1.00  --dbg_dump_prop_clauses                 false
% 3.21/1.00  --dbg_dump_prop_clauses_file            -
% 3.21/1.00  --dbg_out_stat                          false
% 3.21/1.00  
% 3.21/1.00  
% 3.21/1.00  
% 3.21/1.00  
% 3.21/1.00  ------ Proving...
% 3.21/1.00  
% 3.21/1.00  
% 3.21/1.00  % SZS status Theorem for theBenchmark.p
% 3.21/1.00  
% 3.21/1.00   Resolution empty clause
% 3.21/1.00  
% 3.21/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.21/1.00  
% 3.21/1.00  fof(f16,conjecture,(
% 3.21/1.00    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.21/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/1.00  
% 3.21/1.00  fof(f17,negated_conjecture,(
% 3.21/1.00    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.21/1.00    inference(negated_conjecture,[],[f16])).
% 3.21/1.00  
% 3.21/1.00  fof(f19,plain,(
% 3.21/1.00    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.21/1.00    inference(pure_predicate_removal,[],[f17])).
% 3.21/1.00  
% 3.21/1.00  fof(f40,plain,(
% 3.21/1.00    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 3.21/1.00    inference(ennf_transformation,[],[f19])).
% 3.21/1.00  
% 3.21/1.00  fof(f41,plain,(
% 3.21/1.00    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 3.21/1.00    inference(flattening,[],[f40])).
% 3.21/1.00  
% 3.21/1.00  fof(f56,plain,(
% 3.21/1.00    ? [X0] : (? [X1] : (((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 3.21/1.00    inference(nnf_transformation,[],[f41])).
% 3.21/1.00  
% 3.21/1.00  fof(f57,plain,(
% 3.21/1.00    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 3.21/1.00    inference(flattening,[],[f56])).
% 3.21/1.00  
% 3.21/1.00  fof(f59,plain,(
% 3.21/1.00    ( ! [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => ((r2_hidden(k3_yellow_0(X0),sK7) | ~v1_subset_1(sK7,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),sK7) | v1_subset_1(sK7,u1_struct_0(X0))) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(sK7,X0) & ~v1_xboole_0(sK7))) )),
% 3.21/1.00    introduced(choice_axiom,[])).
% 3.21/1.00  
% 3.21/1.00  fof(f58,plain,(
% 3.21/1.00    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : ((r2_hidden(k3_yellow_0(sK6),X1) | ~v1_subset_1(X1,u1_struct_0(sK6))) & (~r2_hidden(k3_yellow_0(sK6),X1) | v1_subset_1(X1,u1_struct_0(sK6))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) & v13_waybel_0(X1,sK6) & ~v1_xboole_0(X1)) & l1_orders_2(sK6) & v1_yellow_0(sK6) & v5_orders_2(sK6) & v4_orders_2(sK6) & v3_orders_2(sK6) & ~v2_struct_0(sK6))),
% 3.21/1.00    introduced(choice_axiom,[])).
% 3.21/1.00  
% 3.21/1.00  fof(f60,plain,(
% 3.21/1.00    ((r2_hidden(k3_yellow_0(sK6),sK7) | ~v1_subset_1(sK7,u1_struct_0(sK6))) & (~r2_hidden(k3_yellow_0(sK6),sK7) | v1_subset_1(sK7,u1_struct_0(sK6))) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) & v13_waybel_0(sK7,sK6) & ~v1_xboole_0(sK7)) & l1_orders_2(sK6) & v1_yellow_0(sK6) & v5_orders_2(sK6) & v4_orders_2(sK6) & v3_orders_2(sK6) & ~v2_struct_0(sK6)),
% 3.21/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f57,f59,f58])).
% 3.21/1.00  
% 3.21/1.00  fof(f95,plain,(
% 3.21/1.00    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))),
% 3.21/1.00    inference(cnf_transformation,[],[f60])).
% 3.21/1.00  
% 3.21/1.00  fof(f3,axiom,(
% 3.21/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (! [X2] : (m1_subset_1(X2,X0) => r2_hidden(X2,X1)) => X0 = X1))),
% 3.21/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/1.00  
% 3.21/1.00  fof(f22,plain,(
% 3.21/1.00    ! [X0,X1] : ((X0 = X1 | ? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.21/1.00    inference(ennf_transformation,[],[f3])).
% 3.21/1.00  
% 3.21/1.00  fof(f23,plain,(
% 3.21/1.00    ! [X0,X1] : (X0 = X1 | ? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.21/1.00    inference(flattening,[],[f22])).
% 3.21/1.00  
% 3.21/1.00  fof(f46,plain,(
% 3.21/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),X0)))),
% 3.21/1.00    introduced(choice_axiom,[])).
% 3.21/1.00  
% 3.21/1.00  fof(f47,plain,(
% 3.21/1.00    ! [X0,X1] : (X0 = X1 | (~r2_hidden(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.21/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f23,f46])).
% 3.21/1.00  
% 3.21/1.00  fof(f65,plain,(
% 3.21/1.00    ( ! [X0,X1] : (X0 = X1 | m1_subset_1(sK2(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.21/1.00    inference(cnf_transformation,[],[f47])).
% 3.21/1.00  
% 3.21/1.00  fof(f14,axiom,(
% 3.21/1.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1 & r1_yellow_0(X0,k5_waybel_0(X0,X1)))))),
% 3.21/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/1.00  
% 3.21/1.00  fof(f37,plain,(
% 3.21/1.00    ! [X0] : (! [X1] : ((k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1 & r1_yellow_0(X0,k5_waybel_0(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.21/1.00    inference(ennf_transformation,[],[f14])).
% 3.21/1.00  
% 3.21/1.00  fof(f38,plain,(
% 3.21/1.00    ! [X0] : (! [X1] : ((k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1 & r1_yellow_0(X0,k5_waybel_0(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.21/1.00    inference(flattening,[],[f37])).
% 3.21/1.00  
% 3.21/1.00  fof(f84,plain,(
% 3.21/1.00    ( ! [X0,X1] : (k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.21/1.00    inference(cnf_transformation,[],[f38])).
% 3.21/1.00  
% 3.21/1.00  fof(f90,plain,(
% 3.21/1.00    v5_orders_2(sK6)),
% 3.21/1.00    inference(cnf_transformation,[],[f60])).
% 3.21/1.00  
% 3.21/1.00  fof(f87,plain,(
% 3.21/1.00    ~v2_struct_0(sK6)),
% 3.21/1.00    inference(cnf_transformation,[],[f60])).
% 3.21/1.00  
% 3.21/1.00  fof(f88,plain,(
% 3.21/1.00    v3_orders_2(sK6)),
% 3.21/1.00    inference(cnf_transformation,[],[f60])).
% 3.21/1.00  
% 3.21/1.00  fof(f89,plain,(
% 3.21/1.00    v4_orders_2(sK6)),
% 3.21/1.00    inference(cnf_transformation,[],[f60])).
% 3.21/1.00  
% 3.21/1.00  fof(f92,plain,(
% 3.21/1.00    l1_orders_2(sK6)),
% 3.21/1.00    inference(cnf_transformation,[],[f60])).
% 3.21/1.00  
% 3.21/1.00  fof(f10,axiom,(
% 3.21/1.00    ! [X0,X1] : (l1_orders_2(X0) => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)))),
% 3.21/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/1.00  
% 3.21/1.00  fof(f30,plain,(
% 3.21/1.00    ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 3.21/1.00    inference(ennf_transformation,[],[f10])).
% 3.21/1.00  
% 3.21/1.00  fof(f74,plain,(
% 3.21/1.00    ( ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.21/1.00    inference(cnf_transformation,[],[f30])).
% 3.21/1.00  
% 3.21/1.00  fof(f6,axiom,(
% 3.21/1.00    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.21/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/1.00  
% 3.21/1.00  fof(f24,plain,(
% 3.21/1.00    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.21/1.00    inference(ennf_transformation,[],[f6])).
% 3.21/1.00  
% 3.21/1.00  fof(f25,plain,(
% 3.21/1.00    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.21/1.00    inference(flattening,[],[f24])).
% 3.21/1.00  
% 3.21/1.00  fof(f70,plain,(
% 3.21/1.00    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.21/1.00    inference(cnf_transformation,[],[f25])).
% 3.21/1.00  
% 3.21/1.00  fof(f9,axiom,(
% 3.21/1.00    ! [X0] : (l1_orders_2(X0) => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 3.21/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/1.00  
% 3.21/1.00  fof(f29,plain,(
% 3.21/1.00    ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 3.21/1.00    inference(ennf_transformation,[],[f9])).
% 3.21/1.00  
% 3.21/1.00  fof(f73,plain,(
% 3.21/1.00    ( ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0)) )),
% 3.21/1.00    inference(cnf_transformation,[],[f29])).
% 3.21/1.00  
% 3.21/1.00  fof(f93,plain,(
% 3.21/1.00    ~v1_xboole_0(sK7)),
% 3.21/1.00    inference(cnf_transformation,[],[f60])).
% 3.21/1.00  
% 3.21/1.00  fof(f15,axiom,(
% 3.21/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 3.21/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/1.00  
% 3.21/1.00  fof(f39,plain,(
% 3.21/1.00    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.21/1.00    inference(ennf_transformation,[],[f15])).
% 3.21/1.00  
% 3.21/1.00  fof(f55,plain,(
% 3.21/1.00    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.21/1.00    inference(nnf_transformation,[],[f39])).
% 3.21/1.00  
% 3.21/1.00  fof(f86,plain,(
% 3.21/1.00    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.21/1.00    inference(cnf_transformation,[],[f55])).
% 3.21/1.00  
% 3.21/1.00  fof(f97,plain,(
% 3.21/1.00    r2_hidden(k3_yellow_0(sK6),sK7) | ~v1_subset_1(sK7,u1_struct_0(sK6))),
% 3.21/1.00    inference(cnf_transformation,[],[f60])).
% 3.21/1.00  
% 3.21/1.00  fof(f8,axiom,(
% 3.21/1.00    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.21/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/1.00  
% 3.21/1.00  fof(f28,plain,(
% 3.21/1.00    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.21/1.00    inference(ennf_transformation,[],[f8])).
% 3.21/1.00  
% 3.21/1.00  fof(f72,plain,(
% 3.21/1.00    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.21/1.00    inference(cnf_transformation,[],[f28])).
% 3.21/1.00  
% 3.21/1.00  fof(f5,axiom,(
% 3.21/1.00    ! [X0] : ? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.21/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/1.00  
% 3.21/1.00  fof(f48,plain,(
% 3.21/1.00    ! [X0] : (? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (~v1_subset_1(sK3(X0),X0) & m1_subset_1(sK3(X0),k1_zfmisc_1(X0))))),
% 3.21/1.00    introduced(choice_axiom,[])).
% 3.21/1.00  
% 3.21/1.00  fof(f49,plain,(
% 3.21/1.00    ! [X0] : (~v1_subset_1(sK3(X0),X0) & m1_subset_1(sK3(X0),k1_zfmisc_1(X0)))),
% 3.21/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f5,f48])).
% 3.21/1.00  
% 3.21/1.00  fof(f68,plain,(
% 3.21/1.00    ( ! [X0] : (m1_subset_1(sK3(X0),k1_zfmisc_1(X0))) )),
% 3.21/1.00    inference(cnf_transformation,[],[f49])).
% 3.21/1.00  
% 3.21/1.00  fof(f69,plain,(
% 3.21/1.00    ( ! [X0] : (~v1_subset_1(sK3(X0),X0)) )),
% 3.21/1.00    inference(cnf_transformation,[],[f49])).
% 3.21/1.00  
% 3.21/1.00  fof(f66,plain,(
% 3.21/1.00    ( ! [X0,X1] : (X0 = X1 | ~r2_hidden(sK2(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.21/1.00    inference(cnf_transformation,[],[f47])).
% 3.21/1.00  
% 3.21/1.00  fof(f11,axiom,(
% 3.21/1.00    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : ((r1_yellow_0(X0,X2) & r1_yellow_0(X0,X1) & r1_tarski(X1,X2)) => r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))))),
% 3.21/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/1.00  
% 3.21/1.00  fof(f31,plain,(
% 3.21/1.00    ! [X0] : (! [X1,X2] : (r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) | (~r1_yellow_0(X0,X2) | ~r1_yellow_0(X0,X1) | ~r1_tarski(X1,X2))) | ~l1_orders_2(X0))),
% 3.21/1.00    inference(ennf_transformation,[],[f11])).
% 3.21/1.00  
% 3.21/1.00  fof(f32,plain,(
% 3.21/1.00    ! [X0] : (! [X1,X2] : (r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) | ~r1_yellow_0(X0,X2) | ~r1_yellow_0(X0,X1) | ~r1_tarski(X1,X2)) | ~l1_orders_2(X0))),
% 3.21/1.00    inference(flattening,[],[f31])).
% 3.21/1.00  
% 3.21/1.00  fof(f75,plain,(
% 3.21/1.00    ( ! [X2,X0,X1] : (r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) | ~r1_yellow_0(X0,X2) | ~r1_yellow_0(X0,X1) | ~r1_tarski(X1,X2) | ~l1_orders_2(X0)) )),
% 3.21/1.00    inference(cnf_transformation,[],[f32])).
% 3.21/1.00  
% 3.21/1.00  fof(f91,plain,(
% 3.21/1.00    v1_yellow_0(sK6)),
% 3.21/1.00    inference(cnf_transformation,[],[f60])).
% 3.21/1.00  
% 3.21/1.00  fof(f12,axiom,(
% 3.21/1.00    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)))),
% 3.21/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/1.00  
% 3.21/1.00  fof(f20,plain,(
% 3.21/1.00    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => r1_yellow_0(X0,k1_xboole_0))),
% 3.21/1.00    inference(pure_predicate_removal,[],[f12])).
% 3.21/1.00  
% 3.21/1.00  fof(f33,plain,(
% 3.21/1.00    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 3.21/1.00    inference(ennf_transformation,[],[f20])).
% 3.21/1.00  
% 3.21/1.00  fof(f34,plain,(
% 3.21/1.00    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 3.21/1.00    inference(flattening,[],[f33])).
% 3.21/1.00  
% 3.21/1.00  fof(f76,plain,(
% 3.21/1.00    ( ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 3.21/1.00    inference(cnf_transformation,[],[f34])).
% 3.21/1.00  
% 3.21/1.00  fof(f13,axiom,(
% 3.21/1.00    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 3.21/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/1.00  
% 3.21/1.00  fof(f35,plain,(
% 3.21/1.00    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.21/1.00    inference(ennf_transformation,[],[f13])).
% 3.21/1.00  
% 3.21/1.00  fof(f36,plain,(
% 3.21/1.00    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.21/1.00    inference(flattening,[],[f35])).
% 3.21/1.00  
% 3.21/1.00  fof(f50,plain,(
% 3.21/1.00    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.21/1.00    inference(nnf_transformation,[],[f36])).
% 3.21/1.00  
% 3.21/1.00  fof(f51,plain,(
% 3.21/1.00    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.21/1.00    inference(rectify,[],[f50])).
% 3.21/1.00  
% 3.21/1.00  fof(f53,plain,(
% 3.21/1.00    ( ! [X2] : (! [X1,X0] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r2_hidden(sK5(X0,X1),X1) & r1_orders_2(X0,X2,sK5(X0,X1)) & r2_hidden(X2,X1) & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))))) )),
% 3.21/1.00    introduced(choice_axiom,[])).
% 3.21/1.00  
% 3.21/1.00  fof(f52,plain,(
% 3.21/1.00    ! [X1,X0] : (? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,sK4(X0,X1),X3) & r2_hidden(sK4(X0,X1),X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK4(X0,X1),u1_struct_0(X0))))),
% 3.21/1.00    introduced(choice_axiom,[])).
% 3.21/1.00  
% 3.21/1.00  fof(f54,plain,(
% 3.21/1.00    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ((~r2_hidden(sK5(X0,X1),X1) & r1_orders_2(X0,sK4(X0,X1),sK5(X0,X1)) & r2_hidden(sK4(X0,X1),X1) & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))) & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.21/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f51,f53,f52])).
% 3.21/1.00  
% 3.21/1.00  fof(f77,plain,(
% 3.21/1.00    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v13_waybel_0(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) )),
% 3.21/1.00    inference(cnf_transformation,[],[f54])).
% 3.21/1.00  
% 3.21/1.00  fof(f7,axiom,(
% 3.21/1.00    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.21/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/1.00  
% 3.21/1.00  fof(f26,plain,(
% 3.21/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.21/1.00    inference(ennf_transformation,[],[f7])).
% 3.21/1.00  
% 3.21/1.00  fof(f27,plain,(
% 3.21/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.21/1.00    inference(flattening,[],[f26])).
% 3.21/1.00  
% 3.21/1.00  fof(f71,plain,(
% 3.21/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.21/1.00    inference(cnf_transformation,[],[f27])).
% 3.21/1.00  
% 3.21/1.00  fof(f94,plain,(
% 3.21/1.00    v13_waybel_0(sK7,sK6)),
% 3.21/1.00    inference(cnf_transformation,[],[f60])).
% 3.21/1.00  
% 3.21/1.00  fof(f2,axiom,(
% 3.21/1.00    ! [X0] : ? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.21/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/1.00  
% 3.21/1.00  fof(f44,plain,(
% 3.21/1.00    ! [X0] : (? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (v1_xboole_0(sK1(X0)) & m1_subset_1(sK1(X0),k1_zfmisc_1(X0))))),
% 3.21/1.00    introduced(choice_axiom,[])).
% 3.21/1.00  
% 3.21/1.00  fof(f45,plain,(
% 3.21/1.00    ! [X0] : (v1_xboole_0(sK1(X0)) & m1_subset_1(sK1(X0),k1_zfmisc_1(X0)))),
% 3.21/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f2,f44])).
% 3.21/1.00  
% 3.21/1.00  fof(f64,plain,(
% 3.21/1.00    ( ! [X0] : (v1_xboole_0(sK1(X0))) )),
% 3.21/1.00    inference(cnf_transformation,[],[f45])).
% 3.21/1.00  
% 3.21/1.00  fof(f1,axiom,(
% 3.21/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.21/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/1.00  
% 3.21/1.00  fof(f18,plain,(
% 3.21/1.00    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 3.21/1.00    inference(unused_predicate_definition_removal,[],[f1])).
% 3.21/1.00  
% 3.21/1.00  fof(f21,plain,(
% 3.21/1.00    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 3.21/1.00    inference(ennf_transformation,[],[f18])).
% 3.21/1.00  
% 3.21/1.00  fof(f42,plain,(
% 3.21/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.21/1.00    introduced(choice_axiom,[])).
% 3.21/1.00  
% 3.21/1.00  fof(f43,plain,(
% 3.21/1.00    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.21/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f42])).
% 3.21/1.00  
% 3.21/1.00  fof(f61,plain,(
% 3.21/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.21/1.00    inference(cnf_transformation,[],[f43])).
% 3.21/1.00  
% 3.21/1.00  fof(f4,axiom,(
% 3.21/1.00    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.21/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/1.00  
% 3.21/1.00  fof(f67,plain,(
% 3.21/1.00    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.21/1.00    inference(cnf_transformation,[],[f4])).
% 3.21/1.00  
% 3.21/1.00  fof(f83,plain,(
% 3.21/1.00    ( ! [X0,X1] : (r1_yellow_0(X0,k5_waybel_0(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.21/1.00    inference(cnf_transformation,[],[f38])).
% 3.21/1.00  
% 3.21/1.00  fof(f96,plain,(
% 3.21/1.00    ~r2_hidden(k3_yellow_0(sK6),sK7) | v1_subset_1(sK7,u1_struct_0(sK6))),
% 3.21/1.00    inference(cnf_transformation,[],[f60])).
% 3.21/1.00  
% 3.21/1.00  cnf(c_28,negated_conjecture,
% 3.21/1.00      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 3.21/1.00      inference(cnf_transformation,[],[f95]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2268,plain,
% 3.21/1.00      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_5,plain,
% 3.21/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.21/1.00      | m1_subset_1(sK2(X1,X0),X1)
% 3.21/1.00      | X0 = X1 ),
% 3.21/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2274,plain,
% 3.21/1.00      ( X0 = X1
% 3.21/1.00      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.21/1.00      | m1_subset_1(sK2(X1,X0),X1) = iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_22,plain,
% 3.21/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.21/1.00      | ~ v3_orders_2(X1)
% 3.21/1.00      | ~ v4_orders_2(X1)
% 3.21/1.00      | v2_struct_0(X1)
% 3.21/1.00      | ~ v5_orders_2(X1)
% 3.21/1.00      | ~ l1_orders_2(X1)
% 3.21/1.00      | k1_yellow_0(X1,k5_waybel_0(X1,X0)) = X0 ),
% 3.21/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_33,negated_conjecture,
% 3.21/1.00      ( v5_orders_2(sK6) ),
% 3.21/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_625,plain,
% 3.21/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.21/1.00      | ~ v3_orders_2(X1)
% 3.21/1.00      | ~ v4_orders_2(X1)
% 3.21/1.00      | v2_struct_0(X1)
% 3.21/1.00      | ~ l1_orders_2(X1)
% 3.21/1.00      | k1_yellow_0(X1,k5_waybel_0(X1,X0)) = X0
% 3.21/1.00      | sK6 != X1 ),
% 3.21/1.00      inference(resolution_lifted,[status(thm)],[c_22,c_33]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_626,plain,
% 3.21/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 3.21/1.00      | ~ v3_orders_2(sK6)
% 3.21/1.00      | ~ v4_orders_2(sK6)
% 3.21/1.00      | v2_struct_0(sK6)
% 3.21/1.00      | ~ l1_orders_2(sK6)
% 3.21/1.00      | k1_yellow_0(sK6,k5_waybel_0(sK6,X0)) = X0 ),
% 3.21/1.00      inference(unflattening,[status(thm)],[c_625]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_36,negated_conjecture,
% 3.21/1.00      ( ~ v2_struct_0(sK6) ),
% 3.21/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_35,negated_conjecture,
% 3.21/1.00      ( v3_orders_2(sK6) ),
% 3.21/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_34,negated_conjecture,
% 3.21/1.00      ( v4_orders_2(sK6) ),
% 3.21/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_31,negated_conjecture,
% 3.21/1.00      ( l1_orders_2(sK6) ),
% 3.21/1.00      inference(cnf_transformation,[],[f92]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_630,plain,
% 3.21/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 3.21/1.00      | k1_yellow_0(sK6,k5_waybel_0(sK6,X0)) = X0 ),
% 3.21/1.00      inference(global_propositional_subsumption,
% 3.21/1.00                [status(thm)],
% 3.21/1.00                [c_626,c_36,c_35,c_34,c_31]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2263,plain,
% 3.21/1.00      ( k1_yellow_0(sK6,k5_waybel_0(sK6,X0)) = X0
% 3.21/1.00      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_630]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_3476,plain,
% 3.21/1.00      ( k1_yellow_0(sK6,k5_waybel_0(sK6,sK2(u1_struct_0(sK6),X0))) = sK2(u1_struct_0(sK6),X0)
% 3.21/1.00      | u1_struct_0(sK6) = X0
% 3.21/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_2274,c_2263]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_7007,plain,
% 3.21/1.00      ( k1_yellow_0(sK6,k5_waybel_0(sK6,sK2(u1_struct_0(sK6),sK7))) = sK2(u1_struct_0(sK6),sK7)
% 3.21/1.00      | u1_struct_0(sK6) = sK7 ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_2268,c_3476]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_13,plain,
% 3.21/1.00      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~ l1_orders_2(X0) ),
% 3.21/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_847,plain,
% 3.21/1.00      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | sK6 != X0 ),
% 3.21/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_31]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_848,plain,
% 3.21/1.00      ( m1_subset_1(k1_yellow_0(sK6,X0),u1_struct_0(sK6)) ),
% 3.21/1.00      inference(unflattening,[status(thm)],[c_847]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2256,plain,
% 3.21/1.00      ( m1_subset_1(k1_yellow_0(sK6,X0),u1_struct_0(sK6)) = iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_848]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_9,plain,
% 3.21/1.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.21/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2271,plain,
% 3.21/1.00      ( m1_subset_1(X0,X1) != iProver_top
% 3.21/1.00      | r2_hidden(X0,X1) = iProver_top
% 3.21/1.00      | v1_xboole_0(X1) = iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_3317,plain,
% 3.21/1.00      ( r2_hidden(k1_yellow_0(sK6,X0),u1_struct_0(sK6)) = iProver_top
% 3.21/1.00      | v1_xboole_0(u1_struct_0(sK6)) = iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_2256,c_2271]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_12,plain,
% 3.21/1.00      ( ~ l1_orders_2(X0) | k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) ),
% 3.21/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_856,plain,
% 3.21/1.00      ( k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) | sK6 != X0 ),
% 3.21/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_31]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_857,plain,
% 3.21/1.00      ( k1_yellow_0(sK6,k1_xboole_0) = k3_yellow_0(sK6) ),
% 3.21/1.00      inference(unflattening,[status(thm)],[c_856]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2591,plain,
% 3.21/1.00      ( m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6)) = iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_857,c_2256]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_3320,plain,
% 3.21/1.00      ( r2_hidden(k3_yellow_0(sK6),u1_struct_0(sK6)) = iProver_top
% 3.21/1.00      | v1_xboole_0(u1_struct_0(sK6)) = iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_2591,c_2271]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_30,negated_conjecture,
% 3.21/1.00      ( ~ v1_xboole_0(sK7) ),
% 3.21/1.00      inference(cnf_transformation,[],[f93]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_43,plain,
% 3.21/1.00      ( v1_xboole_0(sK7) != iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1738,plain,( X0 = X0 ),theory(equality) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2692,plain,
% 3.21/1.00      ( sK7 = sK7 ),
% 3.21/1.00      inference(instantiation,[status(thm)],[c_1738]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_3142,plain,
% 3.21/1.00      ( ~ m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6))
% 3.21/1.00      | r2_hidden(k3_yellow_0(sK6),u1_struct_0(sK6))
% 3.21/1.00      | v1_xboole_0(u1_struct_0(sK6)) ),
% 3.21/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_3143,plain,
% 3.21/1.00      ( m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6)) != iProver_top
% 3.21/1.00      | r2_hidden(k3_yellow_0(sK6),u1_struct_0(sK6)) = iProver_top
% 3.21/1.00      | v1_xboole_0(u1_struct_0(sK6)) = iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_3142]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1741,plain,
% 3.21/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.21/1.00      theory(equality) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2846,plain,
% 3.21/1.00      ( v1_xboole_0(X0)
% 3.21/1.00      | ~ v1_xboole_0(u1_struct_0(sK6))
% 3.21/1.00      | X0 != u1_struct_0(sK6) ),
% 3.21/1.00      inference(instantiation,[status(thm)],[c_1741]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_3664,plain,
% 3.21/1.00      ( ~ v1_xboole_0(u1_struct_0(sK6))
% 3.21/1.00      | v1_xboole_0(sK7)
% 3.21/1.00      | sK7 != u1_struct_0(sK6) ),
% 3.21/1.00      inference(instantiation,[status(thm)],[c_2846]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_3665,plain,
% 3.21/1.00      ( sK7 != u1_struct_0(sK6)
% 3.21/1.00      | v1_xboole_0(u1_struct_0(sK6)) != iProver_top
% 3.21/1.00      | v1_xboole_0(sK7) = iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_3664]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_24,plain,
% 3.21/1.00      ( v1_subset_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | X0 = X1 ),
% 3.21/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_26,negated_conjecture,
% 3.21/1.00      ( ~ v1_subset_1(sK7,u1_struct_0(sK6)) | r2_hidden(k3_yellow_0(sK6),sK7) ),
% 3.21/1.00      inference(cnf_transformation,[],[f97]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_281,plain,
% 3.21/1.00      ( ~ v1_subset_1(sK7,u1_struct_0(sK6)) | r2_hidden(k3_yellow_0(sK6),sK7) ),
% 3.21/1.00      inference(prop_impl,[status(thm)],[c_26]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_673,plain,
% 3.21/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.21/1.00      | r2_hidden(k3_yellow_0(sK6),sK7)
% 3.21/1.00      | X1 = X0
% 3.21/1.00      | u1_struct_0(sK6) != X1
% 3.21/1.00      | sK7 != X0 ),
% 3.21/1.00      inference(resolution_lifted,[status(thm)],[c_24,c_281]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_674,plain,
% 3.21/1.00      ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.21/1.00      | r2_hidden(k3_yellow_0(sK6),sK7)
% 3.21/1.00      | u1_struct_0(sK6) = sK7 ),
% 3.21/1.00      inference(unflattening,[status(thm)],[c_673]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_676,plain,
% 3.21/1.00      ( r2_hidden(k3_yellow_0(sK6),sK7) | u1_struct_0(sK6) = sK7 ),
% 3.21/1.00      inference(global_propositional_subsumption,[status(thm)],[c_674,c_28]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2261,plain,
% 3.21/1.00      ( u1_struct_0(sK6) = sK7
% 3.21/1.00      | r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_676]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_11,plain,
% 3.21/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.21/1.00      | ~ r2_hidden(X2,X0)
% 3.21/1.00      | ~ v1_xboole_0(X1) ),
% 3.21/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2269,plain,
% 3.21/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.21/1.00      | r2_hidden(X2,X0) != iProver_top
% 3.21/1.00      | v1_xboole_0(X1) != iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_3526,plain,
% 3.21/1.00      ( r2_hidden(X0,sK7) != iProver_top
% 3.21/1.00      | v1_xboole_0(u1_struct_0(sK6)) != iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_2268,c_2269]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_5042,plain,
% 3.21/1.00      ( u1_struct_0(sK6) = sK7 | v1_xboole_0(u1_struct_0(sK6)) != iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_2261,c_3526]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1739,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2995,plain,
% 3.21/1.00      ( X0 != X1 | sK7 != X1 | sK7 = X0 ),
% 3.21/1.00      inference(instantiation,[status(thm)],[c_1739]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_4089,plain,
% 3.21/1.00      ( X0 != sK7 | sK7 = X0 | sK7 != sK7 ),
% 3.21/1.00      inference(instantiation,[status(thm)],[c_2995]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_5708,plain,
% 3.21/1.00      ( u1_struct_0(sK6) != sK7 | sK7 = u1_struct_0(sK6) | sK7 != sK7 ),
% 3.21/1.00      inference(instantiation,[status(thm)],[c_4089]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_6084,plain,
% 3.21/1.00      ( r2_hidden(k3_yellow_0(sK6),u1_struct_0(sK6)) = iProver_top ),
% 3.21/1.00      inference(global_propositional_subsumption,
% 3.21/1.00                [status(thm)],
% 3.21/1.00                [c_3320,c_43,c_2591,c_2692,c_3143,c_3665,c_5042,c_5708]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_8,plain,
% 3.21/1.00      ( m1_subset_1(sK3(X0),k1_zfmisc_1(X0)) ),
% 3.21/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2272,plain,
% 3.21/1.00      ( m1_subset_1(sK3(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_7,plain,
% 3.21/1.00      ( ~ v1_subset_1(sK3(X0),X0) ),
% 3.21/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_650,plain,
% 3.21/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.21/1.00      | X1 != X2
% 3.21/1.00      | X1 = X0
% 3.21/1.00      | sK3(X2) != X0 ),
% 3.21/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_24]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_651,plain,
% 3.21/1.00      ( ~ m1_subset_1(sK3(X0),k1_zfmisc_1(X0)) | X0 = sK3(X0) ),
% 3.21/1.00      inference(unflattening,[status(thm)],[c_650]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_655,plain,
% 3.21/1.00      ( X0 = sK3(X0) ),
% 3.21/1.00      inference(global_propositional_subsumption,[status(thm)],[c_651,c_8]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2296,plain,
% 3.21/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.21/1.00      inference(light_normalisation,[status(thm)],[c_2272,c_655]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_4443,plain,
% 3.21/1.00      ( r2_hidden(X0,X1) != iProver_top | v1_xboole_0(X1) != iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_2296,c_2269]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_6089,plain,
% 3.21/1.00      ( v1_xboole_0(u1_struct_0(sK6)) != iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_6084,c_4443]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_6165,plain,
% 3.21/1.00      ( r2_hidden(k1_yellow_0(sK6,X0),u1_struct_0(sK6)) = iProver_top ),
% 3.21/1.00      inference(global_propositional_subsumption,
% 3.21/1.00                [status(thm)],
% 3.21/1.00                [c_3317,c_43,c_2692,c_3665,c_5042,c_5708]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_7038,plain,
% 3.21/1.00      ( u1_struct_0(sK6) = sK7
% 3.21/1.00      | r2_hidden(sK2(u1_struct_0(sK6),sK7),u1_struct_0(sK6)) = iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_7007,c_6165]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1747,plain,
% 3.21/1.00      ( X0 != X1 | u1_struct_0(X0) = u1_struct_0(X1) ),
% 3.21/1.00      theory(equality) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1761,plain,
% 3.21/1.00      ( u1_struct_0(sK6) = u1_struct_0(sK6) | sK6 != sK6 ),
% 3.21/1.00      inference(instantiation,[status(thm)],[c_1747]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1769,plain,
% 3.21/1.00      ( sK6 = sK6 ),
% 3.21/1.00      inference(instantiation,[status(thm)],[c_1738]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_4,plain,
% 3.21/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.21/1.00      | ~ r2_hidden(sK2(X1,X0),X0)
% 3.21/1.00      | X0 = X1 ),
% 3.21/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2606,plain,
% 3.21/1.00      ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.21/1.00      | ~ r2_hidden(sK2(u1_struct_0(sK6),sK7),sK7)
% 3.21/1.00      | sK7 = u1_struct_0(sK6) ),
% 3.21/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2697,plain,
% 3.21/1.00      ( X0 != X1 | X0 = sK7 | sK7 != X1 ),
% 3.21/1.00      inference(instantiation,[status(thm)],[c_1739]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_3022,plain,
% 3.21/1.00      ( X0 != u1_struct_0(sK6) | X0 = sK7 | sK7 != u1_struct_0(sK6) ),
% 3.21/1.00      inference(instantiation,[status(thm)],[c_2697]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_3815,plain,
% 3.21/1.00      ( u1_struct_0(sK6) != u1_struct_0(sK6)
% 3.21/1.00      | u1_struct_0(sK6) = sK7
% 3.21/1.00      | sK7 != u1_struct_0(sK6) ),
% 3.21/1.00      inference(instantiation,[status(thm)],[c_3022]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_14,plain,
% 3.21/1.00      ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
% 3.21/1.00      | ~ r1_yellow_0(X0,X2)
% 3.21/1.00      | ~ r1_yellow_0(X0,X1)
% 3.21/1.00      | ~ r1_tarski(X1,X2)
% 3.21/1.00      | ~ l1_orders_2(X0) ),
% 3.21/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_829,plain,
% 3.21/1.00      ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
% 3.21/1.00      | ~ r1_yellow_0(X0,X2)
% 3.21/1.00      | ~ r1_yellow_0(X0,X1)
% 3.21/1.00      | ~ r1_tarski(X1,X2)
% 3.21/1.00      | sK6 != X0 ),
% 3.21/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_31]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_830,plain,
% 3.21/1.00      ( r1_orders_2(sK6,k1_yellow_0(sK6,X0),k1_yellow_0(sK6,X1))
% 3.21/1.00      | ~ r1_yellow_0(sK6,X0)
% 3.21/1.00      | ~ r1_yellow_0(sK6,X1)
% 3.21/1.00      | ~ r1_tarski(X0,X1) ),
% 3.21/1.00      inference(unflattening,[status(thm)],[c_829]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2257,plain,
% 3.21/1.00      ( r1_orders_2(sK6,k1_yellow_0(sK6,X0),k1_yellow_0(sK6,X1)) = iProver_top
% 3.21/1.00      | r1_yellow_0(sK6,X0) != iProver_top
% 3.21/1.00      | r1_yellow_0(sK6,X1) != iProver_top
% 3.21/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_830]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2898,plain,
% 3.21/1.00      ( r1_orders_2(sK6,k3_yellow_0(sK6),k1_yellow_0(sK6,X0)) = iProver_top
% 3.21/1.00      | r1_yellow_0(sK6,X0) != iProver_top
% 3.21/1.00      | r1_yellow_0(sK6,k1_xboole_0) != iProver_top
% 3.21/1.00      | r1_tarski(k1_xboole_0,X0) != iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_857,c_2257]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_37,plain,
% 3.21/1.00      ( v2_struct_0(sK6) != iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_40,plain,
% 3.21/1.00      ( v5_orders_2(sK6) = iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_32,negated_conjecture,
% 3.21/1.00      ( v1_yellow_0(sK6) ),
% 3.21/1.00      inference(cnf_transformation,[],[f91]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_41,plain,
% 3.21/1.00      ( v1_yellow_0(sK6) = iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_42,plain,
% 3.21/1.00      ( l1_orders_2(sK6) = iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_15,plain,
% 3.21/1.00      ( r1_yellow_0(X0,k1_xboole_0)
% 3.21/1.00      | v2_struct_0(X0)
% 3.21/1.00      | ~ v5_orders_2(X0)
% 3.21/1.00      | ~ v1_yellow_0(X0)
% 3.21/1.00      | ~ l1_orders_2(X0) ),
% 3.21/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_76,plain,
% 3.21/1.00      ( r1_yellow_0(X0,k1_xboole_0) = iProver_top
% 3.21/1.00      | v2_struct_0(X0) = iProver_top
% 3.21/1.00      | v5_orders_2(X0) != iProver_top
% 3.21/1.00      | v1_yellow_0(X0) != iProver_top
% 3.21/1.00      | l1_orders_2(X0) != iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_78,plain,
% 3.21/1.00      ( r1_yellow_0(sK6,k1_xboole_0) = iProver_top
% 3.21/1.00      | v2_struct_0(sK6) = iProver_top
% 3.21/1.00      | v5_orders_2(sK6) != iProver_top
% 3.21/1.00      | v1_yellow_0(sK6) != iProver_top
% 3.21/1.00      | l1_orders_2(sK6) != iProver_top ),
% 3.21/1.00      inference(instantiation,[status(thm)],[c_76]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2923,plain,
% 3.21/1.00      ( r1_yellow_0(sK6,X0) != iProver_top
% 3.21/1.00      | r1_orders_2(sK6,k3_yellow_0(sK6),k1_yellow_0(sK6,X0)) = iProver_top
% 3.21/1.00      | r1_tarski(k1_xboole_0,X0) != iProver_top ),
% 3.21/1.00      inference(global_propositional_subsumption,
% 3.21/1.00                [status(thm)],
% 3.21/1.00                [c_2898,c_37,c_40,c_41,c_42,c_78]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2924,plain,
% 3.21/1.00      ( r1_orders_2(sK6,k3_yellow_0(sK6),k1_yellow_0(sK6,X0)) = iProver_top
% 3.21/1.00      | r1_yellow_0(sK6,X0) != iProver_top
% 3.21/1.00      | r1_tarski(k1_xboole_0,X0) != iProver_top ),
% 3.21/1.00      inference(renaming,[status(thm)],[c_2923]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_21,plain,
% 3.21/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 3.21/1.00      | ~ v13_waybel_0(X3,X0)
% 3.21/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.21/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.21/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 3.21/1.00      | ~ r2_hidden(X1,X3)
% 3.21/1.00      | r2_hidden(X2,X3)
% 3.21/1.00      | ~ l1_orders_2(X0) ),
% 3.21/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_789,plain,
% 3.21/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 3.21/1.00      | ~ v13_waybel_0(X3,X0)
% 3.21/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.21/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.21/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 3.21/1.00      | ~ r2_hidden(X1,X3)
% 3.21/1.00      | r2_hidden(X2,X3)
% 3.21/1.00      | sK6 != X0 ),
% 3.21/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_31]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_790,plain,
% 3.21/1.00      ( ~ r1_orders_2(sK6,X0,X1)
% 3.21/1.00      | ~ v13_waybel_0(X2,sK6)
% 3.21/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 3.21/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.21/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.21/1.00      | ~ r2_hidden(X0,X2)
% 3.21/1.00      | r2_hidden(X1,X2) ),
% 3.21/1.00      inference(unflattening,[status(thm)],[c_789]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_10,plain,
% 3.21/1.00      ( m1_subset_1(X0,X1)
% 3.21/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.21/1.00      | ~ r2_hidden(X0,X2) ),
% 3.21/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_806,plain,
% 3.21/1.00      ( ~ r1_orders_2(sK6,X0,X1)
% 3.21/1.00      | ~ v13_waybel_0(X2,sK6)
% 3.21/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.21/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.21/1.00      | ~ r2_hidden(X0,X2)
% 3.21/1.00      | r2_hidden(X1,X2) ),
% 3.21/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_790,c_10]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2259,plain,
% 3.21/1.00      ( r1_orders_2(sK6,X0,X1) != iProver_top
% 3.21/1.00      | v13_waybel_0(X2,sK6) != iProver_top
% 3.21/1.00      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 3.21/1.00      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.21/1.00      | r2_hidden(X0,X2) != iProver_top
% 3.21/1.00      | r2_hidden(X1,X2) = iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_806]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_4155,plain,
% 3.21/1.00      ( r1_orders_2(sK6,X0,X1) != iProver_top
% 3.21/1.00      | v13_waybel_0(sK7,sK6) != iProver_top
% 3.21/1.00      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 3.21/1.00      | r2_hidden(X0,sK7) != iProver_top
% 3.21/1.00      | r2_hidden(X1,sK7) = iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_2268,c_2259]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_45,plain,
% 3.21/1.00      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_29,negated_conjecture,
% 3.21/1.00      ( v13_waybel_0(sK7,sK6) ),
% 3.21/1.00      inference(cnf_transformation,[],[f94]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1064,plain,
% 3.21/1.00      ( ~ r1_orders_2(sK6,X0,X1)
% 3.21/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.21/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.21/1.00      | ~ r2_hidden(X0,X2)
% 3.21/1.00      | r2_hidden(X1,X2)
% 3.21/1.00      | sK7 != X2
% 3.21/1.00      | sK6 != sK6 ),
% 3.21/1.00      inference(resolution_lifted,[status(thm)],[c_29,c_806]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1065,plain,
% 3.21/1.00      ( ~ r1_orders_2(sK6,X0,X1)
% 3.21/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.21/1.00      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.21/1.00      | ~ r2_hidden(X0,sK7)
% 3.21/1.00      | r2_hidden(X1,sK7) ),
% 3.21/1.00      inference(unflattening,[status(thm)],[c_1064]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1066,plain,
% 3.21/1.00      ( r1_orders_2(sK6,X0,X1) != iProver_top
% 3.21/1.00      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 3.21/1.00      | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.21/1.00      | r2_hidden(X0,sK7) != iProver_top
% 3.21/1.00      | r2_hidden(X1,sK7) = iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_1065]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_4733,plain,
% 3.21/1.00      ( r1_orders_2(sK6,X0,X1) != iProver_top
% 3.21/1.00      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 3.21/1.00      | r2_hidden(X0,sK7) != iProver_top
% 3.21/1.00      | r2_hidden(X1,sK7) = iProver_top ),
% 3.21/1.00      inference(global_propositional_subsumption,
% 3.21/1.00                [status(thm)],
% 3.21/1.00                [c_4155,c_45,c_1066]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_4743,plain,
% 3.21/1.00      ( r1_yellow_0(sK6,X0) != iProver_top
% 3.21/1.00      | m1_subset_1(k1_yellow_0(sK6,X0),u1_struct_0(sK6)) != iProver_top
% 3.21/1.00      | r2_hidden(k1_yellow_0(sK6,X0),sK7) = iProver_top
% 3.21/1.00      | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top
% 3.21/1.00      | r1_tarski(k1_xboole_0,X0) != iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_2924,c_4733]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_44,plain,
% 3.21/1.00      ( v13_waybel_0(sK7,sK6) = iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_849,plain,
% 3.21/1.00      ( m1_subset_1(k1_yellow_0(sK6,X0),u1_struct_0(sK6)) = iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_848]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2499,plain,
% 3.21/1.00      ( ~ r1_orders_2(sK6,X0,X1)
% 3.21/1.00      | ~ v13_waybel_0(sK7,sK6)
% 3.21/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.21/1.00      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.21/1.00      | ~ r2_hidden(X0,sK7)
% 3.21/1.00      | r2_hidden(X1,sK7) ),
% 3.21/1.00      inference(instantiation,[status(thm)],[c_806]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2716,plain,
% 3.21/1.00      ( ~ r1_orders_2(sK6,k3_yellow_0(sK6),X0)
% 3.21/1.00      | ~ v13_waybel_0(sK7,sK6)
% 3.21/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 3.21/1.00      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.21/1.00      | r2_hidden(X0,sK7)
% 3.21/1.00      | ~ r2_hidden(k3_yellow_0(sK6),sK7) ),
% 3.21/1.00      inference(instantiation,[status(thm)],[c_2499]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_3164,plain,
% 3.21/1.00      ( ~ r1_orders_2(sK6,k3_yellow_0(sK6),k1_yellow_0(sK6,X0))
% 3.21/1.00      | ~ v13_waybel_0(sK7,sK6)
% 3.21/1.00      | ~ m1_subset_1(k1_yellow_0(sK6,X0),u1_struct_0(sK6))
% 3.21/1.00      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.21/1.00      | r2_hidden(k1_yellow_0(sK6,X0),sK7)
% 3.21/1.00      | ~ r2_hidden(k3_yellow_0(sK6),sK7) ),
% 3.21/1.00      inference(instantiation,[status(thm)],[c_2716]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_3165,plain,
% 3.21/1.00      ( r1_orders_2(sK6,k3_yellow_0(sK6),k1_yellow_0(sK6,X0)) != iProver_top
% 3.21/1.00      | v13_waybel_0(sK7,sK6) != iProver_top
% 3.21/1.00      | m1_subset_1(k1_yellow_0(sK6,X0),u1_struct_0(sK6)) != iProver_top
% 3.21/1.00      | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.21/1.00      | r2_hidden(k1_yellow_0(sK6,X0),sK7) = iProver_top
% 3.21/1.00      | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_3164]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2,plain,
% 3.21/1.00      ( v1_xboole_0(sK1(X0)) ),
% 3.21/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2277,plain,
% 3.21/1.00      ( v1_xboole_0(sK1(X0)) = iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1,plain,
% 3.21/1.00      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.21/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2278,plain,
% 3.21/1.00      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.21/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_6,plain,
% 3.21/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.21/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2273,plain,
% 3.21/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_3525,plain,
% 3.21/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 3.21/1.00      | v1_xboole_0(X1) != iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_2273,c_2269]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_5097,plain,
% 3.21/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top
% 3.21/1.00      | v1_xboole_0(X1) != iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_2278,c_3525]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_5104,plain,
% 3.21/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_2277,c_5097]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2659,plain,
% 3.21/1.00      ( k1_yellow_0(sK6,k5_waybel_0(sK6,k1_yellow_0(sK6,X0))) = k1_yellow_0(sK6,X0) ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_2256,c_2263]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_3714,plain,
% 3.21/1.00      ( r1_orders_2(sK6,k3_yellow_0(sK6),k1_yellow_0(sK6,X0)) = iProver_top
% 3.21/1.00      | r1_yellow_0(sK6,k5_waybel_0(sK6,k1_yellow_0(sK6,X0))) != iProver_top
% 3.21/1.00      | r1_tarski(k1_xboole_0,k5_waybel_0(sK6,k1_yellow_0(sK6,X0))) != iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_2659,c_2924]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_23,plain,
% 3.21/1.00      ( r1_yellow_0(X0,k5_waybel_0(X0,X1))
% 3.21/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.21/1.00      | ~ v3_orders_2(X0)
% 3.21/1.00      | ~ v4_orders_2(X0)
% 3.21/1.00      | v2_struct_0(X0)
% 3.21/1.00      | ~ v5_orders_2(X0)
% 3.21/1.00      | ~ l1_orders_2(X0) ),
% 3.21/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_607,plain,
% 3.21/1.00      ( r1_yellow_0(X0,k5_waybel_0(X0,X1))
% 3.21/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.21/1.00      | ~ v3_orders_2(X0)
% 3.21/1.00      | ~ v4_orders_2(X0)
% 3.21/1.00      | v2_struct_0(X0)
% 3.21/1.00      | ~ l1_orders_2(X0)
% 3.21/1.00      | sK6 != X0 ),
% 3.21/1.00      inference(resolution_lifted,[status(thm)],[c_23,c_33]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_608,plain,
% 3.21/1.00      ( r1_yellow_0(sK6,k5_waybel_0(sK6,X0))
% 3.21/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 3.21/1.00      | ~ v3_orders_2(sK6)
% 3.21/1.00      | ~ v4_orders_2(sK6)
% 3.21/1.00      | v2_struct_0(sK6)
% 3.21/1.00      | ~ l1_orders_2(sK6) ),
% 3.21/1.00      inference(unflattening,[status(thm)],[c_607]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_612,plain,
% 3.21/1.00      ( r1_yellow_0(sK6,k5_waybel_0(sK6,X0))
% 3.21/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
% 3.21/1.00      inference(global_propositional_subsumption,
% 3.21/1.00                [status(thm)],
% 3.21/1.00                [c_608,c_36,c_35,c_34,c_31]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2475,plain,
% 3.21/1.00      ( r1_yellow_0(sK6,k5_waybel_0(sK6,k1_yellow_0(sK6,X0)))
% 3.21/1.00      | ~ m1_subset_1(k1_yellow_0(sK6,X0),u1_struct_0(sK6)) ),
% 3.21/1.00      inference(instantiation,[status(thm)],[c_612]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2476,plain,
% 3.21/1.00      ( r1_yellow_0(sK6,k5_waybel_0(sK6,k1_yellow_0(sK6,X0))) = iProver_top
% 3.21/1.00      | m1_subset_1(k1_yellow_0(sK6,X0),u1_struct_0(sK6)) != iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_2475]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_4971,plain,
% 3.21/1.00      ( r1_orders_2(sK6,k3_yellow_0(sK6),k1_yellow_0(sK6,X0)) = iProver_top
% 3.21/1.00      | r1_tarski(k1_xboole_0,k5_waybel_0(sK6,k1_yellow_0(sK6,X0))) != iProver_top ),
% 3.21/1.00      inference(global_propositional_subsumption,
% 3.21/1.00                [status(thm)],
% 3.21/1.00                [c_3714,c_849,c_2476]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_5140,plain,
% 3.21/1.00      ( r1_orders_2(sK6,k3_yellow_0(sK6),k1_yellow_0(sK6,X0)) = iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_5104,c_4971]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_5506,plain,
% 3.21/1.00      ( r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top
% 3.21/1.00      | r2_hidden(k1_yellow_0(sK6,X0),sK7) = iProver_top ),
% 3.21/1.00      inference(global_propositional_subsumption,
% 3.21/1.00                [status(thm)],
% 3.21/1.00                [c_4743,c_44,c_45,c_849,c_3165,c_5140]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_5507,plain,
% 3.21/1.00      ( r2_hidden(k1_yellow_0(sK6,X0),sK7) = iProver_top
% 3.21/1.00      | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top ),
% 3.21/1.00      inference(renaming,[status(thm)],[c_5506]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_7040,plain,
% 3.21/1.00      ( u1_struct_0(sK6) = sK7
% 3.21/1.00      | r2_hidden(sK2(u1_struct_0(sK6),sK7),sK7) = iProver_top
% 3.21/1.00      | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_7007,c_5507]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_7197,plain,
% 3.21/1.00      ( r2_hidden(sK2(u1_struct_0(sK6),sK7),sK7)
% 3.21/1.00      | ~ r2_hidden(k3_yellow_0(sK6),sK7)
% 3.21/1.00      | u1_struct_0(sK6) = sK7 ),
% 3.21/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_7040]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_7344,plain,
% 3.21/1.00      ( u1_struct_0(sK6) = sK7 ),
% 3.21/1.00      inference(global_propositional_subsumption,
% 3.21/1.00                [status(thm)],
% 3.21/1.00                [c_7038,c_28,c_676,c_1761,c_1769,c_2606,c_3815,c_7197]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_7355,plain,
% 3.21/1.00      ( r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top ),
% 3.21/1.00      inference(demodulation,[status(thm)],[c_7344,c_6084]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_27,negated_conjecture,
% 3.21/1.00      ( v1_subset_1(sK7,u1_struct_0(sK6)) | ~ r2_hidden(k3_yellow_0(sK6),sK7) ),
% 3.21/1.00      inference(cnf_transformation,[],[f96]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_279,plain,
% 3.21/1.00      ( v1_subset_1(sK7,u1_struct_0(sK6)) | ~ r2_hidden(k3_yellow_0(sK6),sK7) ),
% 3.21/1.00      inference(prop_impl,[status(thm)],[c_27]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_661,plain,
% 3.21/1.00      ( ~ r2_hidden(k3_yellow_0(sK6),sK7)
% 3.21/1.00      | u1_struct_0(sK6) != X0
% 3.21/1.00      | sK3(X0) != sK7 ),
% 3.21/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_279]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_662,plain,
% 3.21/1.00      ( ~ r2_hidden(k3_yellow_0(sK6),sK7) | sK3(u1_struct_0(sK6)) != sK7 ),
% 3.21/1.00      inference(unflattening,[status(thm)],[c_661]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2262,plain,
% 3.21/1.00      ( sK3(u1_struct_0(sK6)) != sK7
% 3.21/1.00      | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_662]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2311,plain,
% 3.21/1.00      ( u1_struct_0(sK6) != sK7
% 3.21/1.00      | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top ),
% 3.21/1.00      inference(demodulation,[status(thm)],[c_2262,c_655]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_7356,plain,
% 3.21/1.00      ( sK7 != sK7 | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top ),
% 3.21/1.00      inference(demodulation,[status(thm)],[c_7344,c_2311]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_7446,plain,
% 3.21/1.00      ( r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top ),
% 3.21/1.00      inference(equality_resolution_simp,[status(thm)],[c_7356]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_7450,plain,
% 3.21/1.00      ( $false ),
% 3.21/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_7355,c_7446]) ).
% 3.21/1.00  
% 3.21/1.00  
% 3.21/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.21/1.00  
% 3.21/1.00  ------                               Statistics
% 3.21/1.00  
% 3.21/1.00  ------ General
% 3.21/1.00  
% 3.21/1.00  abstr_ref_over_cycles:                  0
% 3.21/1.00  abstr_ref_under_cycles:                 0
% 3.21/1.00  gc_basic_clause_elim:                   0
% 3.21/1.00  forced_gc_time:                         0
% 3.21/1.00  parsing_time:                           0.015
% 3.21/1.00  unif_index_cands_time:                  0.
% 3.21/1.00  unif_index_add_time:                    0.
% 3.21/1.00  orderings_time:                         0.
% 3.21/1.00  out_proof_time:                         0.014
% 3.21/1.00  total_time:                             0.251
% 3.21/1.00  num_of_symbols:                         59
% 3.21/1.00  num_of_terms:                           5582
% 3.21/1.00  
% 3.21/1.00  ------ Preprocessing
% 3.21/1.00  
% 3.21/1.00  num_of_splits:                          0
% 3.21/1.00  num_of_split_atoms:                     0
% 3.21/1.00  num_of_reused_defs:                     0
% 3.21/1.00  num_eq_ax_congr_red:                    37
% 3.21/1.00  num_of_sem_filtered_clauses:            1
% 3.21/1.00  num_of_subtypes:                        0
% 3.21/1.00  monotx_restored_types:                  0
% 3.21/1.00  sat_num_of_epr_types:                   0
% 3.21/1.00  sat_num_of_non_cyclic_types:            0
% 3.21/1.00  sat_guarded_non_collapsed_types:        0
% 3.21/1.00  num_pure_diseq_elim:                    0
% 3.21/1.00  simp_replaced_by:                       0
% 3.21/1.00  res_preprocessed:                       160
% 3.21/1.00  prep_upred:                             0
% 3.21/1.00  prep_unflattend:                        54
% 3.21/1.00  smt_new_axioms:                         0
% 3.21/1.00  pred_elim_cands:                        7
% 3.21/1.00  pred_elim:                              7
% 3.21/1.00  pred_elim_cl:                           7
% 3.21/1.00  pred_elim_cycles:                       17
% 3.21/1.00  merged_defs:                            2
% 3.21/1.00  merged_defs_ncl:                        0
% 3.21/1.00  bin_hyper_res:                          2
% 3.21/1.00  prep_cycles:                            4
% 3.21/1.00  pred_elim_time:                         0.026
% 3.21/1.00  splitting_time:                         0.
% 3.21/1.00  sem_filter_time:                        0.
% 3.21/1.00  monotx_time:                            0.
% 3.21/1.00  subtype_inf_time:                       0.
% 3.21/1.00  
% 3.21/1.00  ------ Problem properties
% 3.21/1.00  
% 3.21/1.00  clauses:                                30
% 3.21/1.00  conjectures:                            3
% 3.21/1.00  epr:                                    4
% 3.21/1.00  horn:                                   22
% 3.21/1.00  ground:                                 8
% 3.21/1.00  unary:                                  11
% 3.21/1.00  binary:                                 6
% 3.21/1.00  lits:                                   66
% 3.21/1.00  lits_eq:                                8
% 3.21/1.00  fd_pure:                                0
% 3.21/1.00  fd_pseudo:                              0
% 3.21/1.00  fd_cond:                                0
% 3.21/1.00  fd_pseudo_cond:                         2
% 3.21/1.00  ac_symbols:                             0
% 3.21/1.00  
% 3.21/1.00  ------ Propositional Solver
% 3.21/1.00  
% 3.21/1.00  prop_solver_calls:                      28
% 3.21/1.00  prop_fast_solver_calls:                 1278
% 3.21/1.00  smt_solver_calls:                       0
% 3.21/1.00  smt_fast_solver_calls:                  0
% 3.21/1.00  prop_num_of_clauses:                    2510
% 3.21/1.00  prop_preprocess_simplified:             6974
% 3.21/1.00  prop_fo_subsumed:                       38
% 3.21/1.00  prop_solver_time:                       0.
% 3.21/1.00  smt_solver_time:                        0.
% 3.21/1.00  smt_fast_solver_time:                   0.
% 3.21/1.00  prop_fast_solver_time:                  0.
% 3.21/1.00  prop_unsat_core_time:                   0.
% 3.21/1.00  
% 3.21/1.00  ------ QBF
% 3.21/1.00  
% 3.21/1.00  qbf_q_res:                              0
% 3.21/1.00  qbf_num_tautologies:                    0
% 3.21/1.00  qbf_prep_cycles:                        0
% 3.21/1.00  
% 3.21/1.00  ------ BMC1
% 3.21/1.00  
% 3.21/1.00  bmc1_current_bound:                     -1
% 3.21/1.00  bmc1_last_solved_bound:                 -1
% 3.21/1.00  bmc1_unsat_core_size:                   -1
% 3.21/1.00  bmc1_unsat_core_parents_size:           -1
% 3.21/1.00  bmc1_merge_next_fun:                    0
% 3.21/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.21/1.00  
% 3.21/1.00  ------ Instantiation
% 3.21/1.00  
% 3.21/1.00  inst_num_of_clauses:                    718
% 3.21/1.00  inst_num_in_passive:                    40
% 3.21/1.00  inst_num_in_active:                     357
% 3.21/1.00  inst_num_in_unprocessed:                323
% 3.21/1.00  inst_num_of_loops:                      410
% 3.21/1.00  inst_num_of_learning_restarts:          0
% 3.21/1.00  inst_num_moves_active_passive:          50
% 3.21/1.00  inst_lit_activity:                      0
% 3.21/1.00  inst_lit_activity_moves:                0
% 3.21/1.00  inst_num_tautologies:                   0
% 3.21/1.00  inst_num_prop_implied:                  0
% 3.21/1.00  inst_num_existing_simplified:           0
% 3.21/1.00  inst_num_eq_res_simplified:             0
% 3.21/1.00  inst_num_child_elim:                    0
% 3.21/1.00  inst_num_of_dismatching_blockings:      168
% 3.21/1.00  inst_num_of_non_proper_insts:           656
% 3.21/1.00  inst_num_of_duplicates:                 0
% 3.21/1.00  inst_inst_num_from_inst_to_res:         0
% 3.21/1.00  inst_dismatching_checking_time:         0.
% 3.21/1.00  
% 3.21/1.00  ------ Resolution
% 3.21/1.00  
% 3.21/1.00  res_num_of_clauses:                     0
% 3.21/1.00  res_num_in_passive:                     0
% 3.21/1.00  res_num_in_active:                      0
% 3.21/1.00  res_num_of_loops:                       164
% 3.21/1.00  res_forward_subset_subsumed:            54
% 3.21/1.00  res_backward_subset_subsumed:           4
% 3.21/1.00  res_forward_subsumed:                   0
% 3.21/1.00  res_backward_subsumed:                  0
% 3.21/1.00  res_forward_subsumption_resolution:     7
% 3.21/1.00  res_backward_subsumption_resolution:    0
% 3.21/1.00  res_clause_to_clause_subsumption:       371
% 3.21/1.00  res_orphan_elimination:                 0
% 3.21/1.00  res_tautology_del:                      58
% 3.21/1.00  res_num_eq_res_simplified:              0
% 3.21/1.00  res_num_sel_changes:                    0
% 3.21/1.00  res_moves_from_active_to_pass:          0
% 3.21/1.00  
% 3.21/1.00  ------ Superposition
% 3.21/1.00  
% 3.21/1.00  sup_time_total:                         0.
% 3.21/1.00  sup_time_generating:                    0.
% 3.21/1.00  sup_time_sim_full:                      0.
% 3.21/1.00  sup_time_sim_immed:                     0.
% 3.21/1.00  
% 3.21/1.00  sup_num_of_clauses:                     98
% 3.21/1.00  sup_num_in_active:                      45
% 3.21/1.00  sup_num_in_passive:                     53
% 3.21/1.00  sup_num_of_loops:                       80
% 3.21/1.00  sup_fw_superposition:                   122
% 3.21/1.00  sup_bw_superposition:                   71
% 3.21/1.00  sup_immediate_simplified:               52
% 3.21/1.00  sup_given_eliminated:                   0
% 3.21/1.00  comparisons_done:                       0
% 3.21/1.00  comparisons_avoided:                    5
% 3.21/1.00  
% 3.21/1.00  ------ Simplifications
% 3.21/1.00  
% 3.21/1.00  
% 3.21/1.00  sim_fw_subset_subsumed:                 25
% 3.21/1.00  sim_bw_subset_subsumed:                 24
% 3.21/1.00  sim_fw_subsumed:                        14
% 3.21/1.00  sim_bw_subsumed:                        0
% 3.21/1.00  sim_fw_subsumption_res:                 5
% 3.21/1.00  sim_bw_subsumption_res:                 0
% 3.21/1.00  sim_tautology_del:                      13
% 3.21/1.00  sim_eq_tautology_del:                   2
% 3.21/1.00  sim_eq_res_simp:                        1
% 3.21/1.00  sim_fw_demodulated:                     4
% 3.21/1.00  sim_bw_demodulated:                     28
% 3.21/1.00  sim_light_normalised:                   20
% 3.21/1.00  sim_joinable_taut:                      0
% 3.21/1.00  sim_joinable_simp:                      0
% 3.21/1.00  sim_ac_normalised:                      0
% 3.21/1.00  sim_smt_subsumption:                    0
% 3.21/1.00  
%------------------------------------------------------------------------------
