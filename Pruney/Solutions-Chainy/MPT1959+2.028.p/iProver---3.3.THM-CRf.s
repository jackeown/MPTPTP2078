%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:29 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :  176 (1085 expanded)
%              Number of clauses        :   99 ( 260 expanded)
%              Number of leaves         :   22 ( 242 expanded)
%              Depth                    :   26
%              Number of atoms          :  702 (9745 expanded)
%              Number of equality atoms :  139 ( 365 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f14,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f16,plain,(
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
    inference(pure_predicate_removal,[],[f15])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(X0),X1)
            | ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & ( ~ r2_hidden(k3_yellow_0(X0),X1)
            | v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
     => ( ( r2_hidden(k3_yellow_0(X0),sK4)
          | ~ v1_subset_1(sK4,u1_struct_0(X0)) )
        & ( ~ r2_hidden(k3_yellow_0(X0),sK4)
          | v1_subset_1(sK4,u1_struct_0(X0)) )
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
        & v13_waybel_0(sK4,X0)
        & ~ v1_xboole_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
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
          ( ( r2_hidden(k3_yellow_0(sK3),X1)
            | ~ v1_subset_1(X1,u1_struct_0(sK3)) )
          & ( ~ r2_hidden(k3_yellow_0(sK3),X1)
            | v1_subset_1(X1,u1_struct_0(sK3)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
          & v13_waybel_0(X1,sK3)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(sK3)
      & v1_yellow_0(sK3)
      & v5_orders_2(sK3)
      & v4_orders_2(sK3)
      & v3_orders_2(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ( r2_hidden(k3_yellow_0(sK3),sK4)
      | ~ v1_subset_1(sK4,u1_struct_0(sK3)) )
    & ( ~ r2_hidden(k3_yellow_0(sK3),sK4)
      | v1_subset_1(sK4,u1_struct_0(sK3)) )
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & v13_waybel_0(sK4,sK3)
    & ~ v1_xboole_0(sK4)
    & l1_orders_2(sK3)
    & v1_yellow_0(sK3)
    & v5_orders_2(sK3)
    & v4_orders_2(sK3)
    & v3_orders_2(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f46,f48,f47])).

fof(f81,plain,
    ( r2_hidden(k3_yellow_0(sK3),sK4)
    | ~ v1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f49])).

fof(f79,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f49])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( ! [X2] :
            ( m1_subset_1(X2,X0)
           => r2_hidden(X2,X1) )
       => X0 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f18])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & m1_subset_1(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ~ r2_hidden(sK0(X0,X1),X1)
        & m1_subset_1(sK0(X0,X1),X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f37])).

fof(f54,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(sK0(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f53,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | m1_subset_1(sK0(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f12,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f74,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f71,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f72,plain,(
    v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f73,plain,(
    v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f76,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_yellow_0(X0,k5_waybel_0(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( ( r1_yellow_0(X0,X2)
            & r1_yellow_0(X0,X1)
            & r1_tarski(X1,X2) )
         => r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
          | ~ r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
          | ~ r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f26])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
      | ~ r1_yellow_0(X0,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ r1_tarski(X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f75,plain,(
    v1_yellow_0(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r1_yellow_0(X0,k1_xboole_0) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f28,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f29,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f60,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f57,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f11,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & r1_orders_2(X0,X2,X3)
          & r2_hidden(X2,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r1_orders_2(X0,X2,sK2(X0,X1))
        & r2_hidden(X2,X1)
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
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
            & r1_orders_2(X0,sK1(X0,X1),X3)
            & r2_hidden(sK1(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ( ~ r2_hidden(sK2(X0,X1),X1)
                & r1_orders_2(X0,sK1(X0,X1),sK2(X0,X1))
                & r2_hidden(sK1(X0,X1),X1)
                & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f40,f42,f41])).

fof(f61,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r1_orders_2(X0,X4,X5)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f78,plain,(
    v13_waybel_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f58,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f77,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f69,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f82,plain,(
    ! [X1] :
      ( ~ v1_subset_1(X1,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ) ),
    inference(equality_resolution,[],[f69])).

fof(f80,plain,
    ( ~ r2_hidden(k3_yellow_0(sK3),sK4)
    | v1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f49])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

cnf(c_19,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_21,negated_conjecture,
    ( ~ v1_subset_1(sK4,u1_struct_0(sK3))
    | r2_hidden(k3_yellow_0(sK3),sK4) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_233,plain,
    ( ~ v1_subset_1(sK4,u1_struct_0(sK3))
    | r2_hidden(k3_yellow_0(sK3),sK4) ),
    inference(prop_impl,[status(thm)],[c_21])).

cnf(c_473,plain,
    ( r2_hidden(k3_yellow_0(sK3),sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X1 = X0
    | u1_struct_0(sK3) != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_233])).

cnf(c_474,plain,
    ( r2_hidden(k3_yellow_0(sK3),sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | u1_struct_0(sK3) = sK4 ),
    inference(unflattening,[status(thm)],[c_473])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_476,plain,
    ( r2_hidden(k3_yellow_0(sK3),sK4)
    | u1_struct_0(sK3) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_474,c_23])).

cnf(c_1765,plain,
    ( u1_struct_0(sK3) = sK4
    | r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_476])).

cnf(c_1409,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_1420,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1409])).

cnf(c_1402,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1427,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1402])).

cnf(c_3,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | X1 = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1962,plain,
    ( ~ r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | sK4 = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(sK0(X1,X0),X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1965,plain,
    ( m1_subset_1(sK0(u1_struct_0(sK3),sK4),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | sK4 = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1403,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2027,plain,
    ( X0 != X1
    | X0 = sK4
    | sK4 != X1 ),
    inference(instantiation,[status(thm)],[c_1403])).

cnf(c_2401,plain,
    ( X0 != u1_struct_0(sK3)
    | X0 = sK4
    | sK4 != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2027])).

cnf(c_2741,plain,
    ( u1_struct_0(sK3) != u1_struct_0(sK3)
    | u1_struct_0(sK3) = sK4
    | sK4 != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2401])).

cnf(c_1768,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1770,plain,
    ( X0 = X1
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(sK0(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_yellow_0(X1,k5_waybel_0(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_28,negated_conjecture,
    ( v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_525,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | k1_yellow_0(X1,k5_waybel_0(X1,X0)) = X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_28])).

cnf(c_526,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | v2_struct_0(sK3)
    | ~ l1_orders_2(sK3)
    | k1_yellow_0(sK3,k5_waybel_0(sK3,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_525])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_30,negated_conjecture,
    ( v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_29,negated_conjecture,
    ( v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_26,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_530,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | k1_yellow_0(sK3,k5_waybel_0(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_526,c_31,c_30,c_29,c_26])).

cnf(c_1763,plain,
    ( k1_yellow_0(sK3,k5_waybel_0(sK3,X0)) = X0
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_530])).

cnf(c_2266,plain,
    ( k1_yellow_0(sK3,k5_waybel_0(sK3,sK0(u1_struct_0(sK3),X0))) = sK0(u1_struct_0(sK3),X0)
    | u1_struct_0(sK3) = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1770,c_1763])).

cnf(c_3653,plain,
    ( k1_yellow_0(sK3,k5_waybel_0(sK3,sK0(u1_struct_0(sK3),sK4))) = sK0(u1_struct_0(sK3),sK4)
    | u1_struct_0(sK3) = sK4 ),
    inference(superposition,[status(thm)],[c_1768,c_2266])).

cnf(c_18,plain,
    ( r1_yellow_0(X0,k5_waybel_0(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_507,plain,
    ( r1_yellow_0(X0,k5_waybel_0(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_28])).

cnf(c_508,plain,
    ( r1_yellow_0(sK3,k5_waybel_0(sK3,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | v2_struct_0(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_507])).

cnf(c_512,plain,
    ( r1_yellow_0(sK3,k5_waybel_0(sK3,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_508,c_31,c_30,c_29,c_26])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_9,plain,
    ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
    | ~ r1_yellow_0(X0,X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_434,plain,
    ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
    | ~ r1_yellow_0(X0,X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0)
    | X2 != X3
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_9])).

cnf(c_435,plain,
    ( r1_orders_2(X0,k1_yellow_0(X0,k1_xboole_0),k1_yellow_0(X0,X1))
    | ~ r1_yellow_0(X0,X1)
    | ~ r1_yellow_0(X0,k1_xboole_0)
    | ~ l1_orders_2(X0) ),
    inference(unflattening,[status(thm)],[c_434])).

cnf(c_629,plain,
    ( r1_orders_2(X0,k1_yellow_0(X0,k1_xboole_0),k1_yellow_0(X0,X1))
    | ~ r1_yellow_0(X0,X1)
    | ~ r1_yellow_0(X0,k1_xboole_0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_435,c_26])).

cnf(c_630,plain,
    ( r1_orders_2(sK3,k1_yellow_0(sK3,k1_xboole_0),k1_yellow_0(sK3,X0))
    | ~ r1_yellow_0(sK3,X0)
    | ~ r1_yellow_0(sK3,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_629])).

cnf(c_27,negated_conjecture,
    ( v1_yellow_0(sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_10,plain,
    ( r1_yellow_0(X0,k1_xboole_0)
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_yellow_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_72,plain,
    ( r1_yellow_0(sK3,k1_xboole_0)
    | v2_struct_0(sK3)
    | ~ v5_orders_2(sK3)
    | ~ v1_yellow_0(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_634,plain,
    ( ~ r1_yellow_0(sK3,X0)
    | r1_orders_2(sK3,k1_yellow_0(sK3,k1_xboole_0),k1_yellow_0(sK3,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_630,c_31,c_28,c_27,c_26,c_72])).

cnf(c_635,plain,
    ( r1_orders_2(sK3,k1_yellow_0(sK3,k1_xboole_0),k1_yellow_0(sK3,X0))
    | ~ r1_yellow_0(sK3,X0) ),
    inference(renaming,[status(thm)],[c_634])).

cnf(c_799,plain,
    ( r1_orders_2(sK3,k1_yellow_0(sK3,k1_xboole_0),k1_yellow_0(sK3,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | k5_waybel_0(sK3,X1) != X0
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_512,c_635])).

cnf(c_800,plain,
    ( r1_orders_2(sK3,k1_yellow_0(sK3,k1_xboole_0),k1_yellow_0(sK3,k5_waybel_0(sK3,X0)))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_799])).

cnf(c_1754,plain,
    ( r1_orders_2(sK3,k1_yellow_0(sK3,k1_xboole_0),k1_yellow_0(sK3,k5_waybel_0(sK3,X0))) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_800])).

cnf(c_7,plain,
    ( ~ l1_orders_2(X0)
    | k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_694,plain,
    ( k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_26])).

cnf(c_695,plain,
    ( k1_yellow_0(sK3,k1_xboole_0) = k3_yellow_0(sK3) ),
    inference(unflattening,[status(thm)],[c_694])).

cnf(c_1807,plain,
    ( r1_orders_2(sK3,k3_yellow_0(sK3),k1_yellow_0(sK3,k5_waybel_0(sK3,X0))) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1754,c_695])).

cnf(c_3696,plain,
    ( u1_struct_0(sK3) = sK4
    | r1_orders_2(sK3,k3_yellow_0(sK3),sK0(u1_struct_0(sK3),sK4)) = iProver_top
    | m1_subset_1(sK0(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3653,c_1807])).

cnf(c_40,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1966,plain,
    ( sK4 = u1_struct_0(sK3)
    | m1_subset_1(sK0(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1965])).

cnf(c_3714,plain,
    ( r1_orders_2(sK3,k3_yellow_0(sK3),sK0(u1_struct_0(sK3),sK4)) = iProver_top
    | u1_struct_0(sK3) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3696,c_40,c_1420,c_1427,c_1966,c_2741])).

cnf(c_3715,plain,
    ( u1_struct_0(sK3) = sK4
    | r1_orders_2(sK3,k3_yellow_0(sK3),sK0(u1_struct_0(sK3),sK4)) = iProver_top ),
    inference(renaming,[status(thm)],[c_3714])).

cnf(c_16,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ v13_waybel_0(X3,X0)
    | ~ r2_hidden(X1,X3)
    | r2_hidden(X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_647,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ v13_waybel_0(X3,X0)
    | ~ r2_hidden(X1,X3)
    | r2_hidden(X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_26])).

cnf(c_648,plain,
    ( ~ r1_orders_2(sK3,X0,X1)
    | ~ v13_waybel_0(X2,sK3)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(unflattening,[status(thm)],[c_647])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_664,plain,
    ( ~ r1_orders_2(sK3,X0,X1)
    | ~ v13_waybel_0(X2,sK3)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_648,c_6])).

cnf(c_1762,plain,
    ( r1_orders_2(sK3,X0,X1) != iProver_top
    | v13_waybel_0(X2,sK3) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X1,X2) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_664])).

cnf(c_2821,plain,
    ( r1_orders_2(sK3,X0,X1) != iProver_top
    | v13_waybel_0(sK4,sK3) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X1,sK4) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1768,c_1762])).

cnf(c_24,negated_conjecture,
    ( v13_waybel_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_879,plain,
    ( ~ r1_orders_2(sK3,X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | sK4 != X2
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_664])).

cnf(c_880,plain,
    ( ~ r1_orders_2(sK3,X0,X1)
    | ~ r2_hidden(X0,sK4)
    | r2_hidden(X1,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(unflattening,[status(thm)],[c_879])).

cnf(c_881,plain,
    ( r1_orders_2(sK3,X0,X1) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X1,sK4) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_880])).

cnf(c_3149,plain,
    ( r1_orders_2(sK3,X0,X1) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X1,sK4) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2821,c_40,c_881])).

cnf(c_3720,plain,
    ( u1_struct_0(sK3) = sK4
    | r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4) = iProver_top
    | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top
    | m1_subset_1(sK0(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3715,c_3149])).

cnf(c_3721,plain,
    ( r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4)
    | ~ r2_hidden(k3_yellow_0(sK3),sK4)
    | ~ m1_subset_1(sK0(u1_struct_0(sK3),sK4),u1_struct_0(sK3))
    | u1_struct_0(sK3) = sK4 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3720])).

cnf(c_3755,plain,
    ( u1_struct_0(sK3) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1765,c_23,c_476,c_1420,c_1427,c_1962,c_1965,c_2741,c_3721])).

cnf(c_8,plain,
    ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_687,plain,
    ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_26])).

cnf(c_688,plain,
    ( m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_687])).

cnf(c_1760,plain,
    ( m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_688])).

cnf(c_3776,plain,
    ( m1_subset_1(k3_yellow_0(sK3),sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3755,c_1760])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_25,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_419,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_25])).

cnf(c_420,plain,
    ( r2_hidden(X0,sK4)
    | ~ m1_subset_1(X0,sK4) ),
    inference(unflattening,[status(thm)],[c_419])).

cnf(c_1766,plain,
    ( r2_hidden(X0,sK4) = iProver_top
    | m1_subset_1(X0,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_420])).

cnf(c_3909,plain,
    ( r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3776,c_1766])).

cnf(c_20,plain,
    ( ~ v1_subset_1(X0,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_22,negated_conjecture,
    ( v1_subset_1(sK4,u1_struct_0(sK3))
    | ~ r2_hidden(k3_yellow_0(sK3),sK4) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_231,plain,
    ( v1_subset_1(sK4,u1_struct_0(sK3))
    | ~ r2_hidden(k3_yellow_0(sK3),sK4) ),
    inference(prop_impl,[status(thm)],[c_22])).

cnf(c_487,plain,
    ( ~ r2_hidden(k3_yellow_0(sK3),sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X0))
    | u1_struct_0(sK3) != X0
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_231])).

cnf(c_488,plain,
    ( ~ r2_hidden(k3_yellow_0(sK3),sK4)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | sK4 != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_487])).

cnf(c_1764,plain,
    ( sK4 != u1_struct_0(sK3)
    | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_488])).

cnf(c_2,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1772,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1783,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1772,c_1])).

cnf(c_1851,plain,
    ( u1_struct_0(sK3) != sK4
    | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1764,c_1783])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3909,c_3755,c_1851])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:50:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.69/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/0.98  
% 2.69/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.69/0.98  
% 2.69/0.98  ------  iProver source info
% 2.69/0.98  
% 2.69/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.69/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.69/0.98  git: non_committed_changes: false
% 2.69/0.98  git: last_make_outside_of_git: false
% 2.69/0.98  
% 2.69/0.98  ------ 
% 2.69/0.98  
% 2.69/0.98  ------ Input Options
% 2.69/0.98  
% 2.69/0.98  --out_options                           all
% 2.69/0.98  --tptp_safe_out                         true
% 2.69/0.98  --problem_path                          ""
% 2.69/0.98  --include_path                          ""
% 2.69/0.98  --clausifier                            res/vclausify_rel
% 2.69/0.98  --clausifier_options                    --mode clausify
% 2.69/0.98  --stdin                                 false
% 2.69/0.98  --stats_out                             all
% 2.69/0.98  
% 2.69/0.98  ------ General Options
% 2.69/0.98  
% 2.69/0.98  --fof                                   false
% 2.69/0.98  --time_out_real                         305.
% 2.69/0.98  --time_out_virtual                      -1.
% 2.69/0.98  --symbol_type_check                     false
% 2.69/0.98  --clausify_out                          false
% 2.69/0.98  --sig_cnt_out                           false
% 2.69/0.98  --trig_cnt_out                          false
% 2.69/0.98  --trig_cnt_out_tolerance                1.
% 2.69/0.98  --trig_cnt_out_sk_spl                   false
% 2.69/0.98  --abstr_cl_out                          false
% 2.69/0.98  
% 2.69/0.98  ------ Global Options
% 2.69/0.98  
% 2.69/0.98  --schedule                              default
% 2.69/0.98  --add_important_lit                     false
% 2.69/0.98  --prop_solver_per_cl                    1000
% 2.69/0.98  --min_unsat_core                        false
% 2.69/0.98  --soft_assumptions                      false
% 2.69/0.98  --soft_lemma_size                       3
% 2.69/0.98  --prop_impl_unit_size                   0
% 2.69/0.98  --prop_impl_unit                        []
% 2.69/0.98  --share_sel_clauses                     true
% 2.69/0.98  --reset_solvers                         false
% 2.69/0.98  --bc_imp_inh                            [conj_cone]
% 2.69/0.98  --conj_cone_tolerance                   3.
% 2.69/0.98  --extra_neg_conj                        none
% 2.69/0.98  --large_theory_mode                     true
% 2.69/0.98  --prolific_symb_bound                   200
% 2.69/0.98  --lt_threshold                          2000
% 2.69/0.98  --clause_weak_htbl                      true
% 2.69/0.98  --gc_record_bc_elim                     false
% 2.69/0.98  
% 2.69/0.98  ------ Preprocessing Options
% 2.69/0.98  
% 2.69/0.98  --preprocessing_flag                    true
% 2.69/0.98  --time_out_prep_mult                    0.1
% 2.69/0.98  --splitting_mode                        input
% 2.69/0.98  --splitting_grd                         true
% 2.69/0.98  --splitting_cvd                         false
% 2.69/0.98  --splitting_cvd_svl                     false
% 2.69/0.98  --splitting_nvd                         32
% 2.69/0.98  --sub_typing                            true
% 2.69/0.98  --prep_gs_sim                           true
% 2.69/0.98  --prep_unflatten                        true
% 2.69/0.98  --prep_res_sim                          true
% 2.69/0.98  --prep_upred                            true
% 2.69/0.98  --prep_sem_filter                       exhaustive
% 2.69/0.98  --prep_sem_filter_out                   false
% 2.69/0.98  --pred_elim                             true
% 2.69/0.98  --res_sim_input                         true
% 2.69/0.98  --eq_ax_congr_red                       true
% 2.69/0.98  --pure_diseq_elim                       true
% 2.69/0.98  --brand_transform                       false
% 2.69/0.98  --non_eq_to_eq                          false
% 2.69/0.98  --prep_def_merge                        true
% 2.69/0.98  --prep_def_merge_prop_impl              false
% 2.69/0.98  --prep_def_merge_mbd                    true
% 2.69/0.98  --prep_def_merge_tr_red                 false
% 2.69/0.98  --prep_def_merge_tr_cl                  false
% 2.69/0.98  --smt_preprocessing                     true
% 2.69/0.98  --smt_ac_axioms                         fast
% 2.69/0.98  --preprocessed_out                      false
% 2.69/0.98  --preprocessed_stats                    false
% 2.69/0.98  
% 2.69/0.98  ------ Abstraction refinement Options
% 2.69/0.98  
% 2.69/0.98  --abstr_ref                             []
% 2.69/0.98  --abstr_ref_prep                        false
% 2.69/0.98  --abstr_ref_until_sat                   false
% 2.69/0.98  --abstr_ref_sig_restrict                funpre
% 2.69/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.69/0.98  --abstr_ref_under                       []
% 2.69/0.98  
% 2.69/0.98  ------ SAT Options
% 2.69/0.98  
% 2.69/0.98  --sat_mode                              false
% 2.69/0.98  --sat_fm_restart_options                ""
% 2.69/0.98  --sat_gr_def                            false
% 2.69/0.98  --sat_epr_types                         true
% 2.69/0.98  --sat_non_cyclic_types                  false
% 2.69/0.98  --sat_finite_models                     false
% 2.69/0.98  --sat_fm_lemmas                         false
% 2.69/0.98  --sat_fm_prep                           false
% 2.69/0.99  --sat_fm_uc_incr                        true
% 2.69/0.99  --sat_out_model                         small
% 2.69/0.99  --sat_out_clauses                       false
% 2.69/0.99  
% 2.69/0.99  ------ QBF Options
% 2.69/0.99  
% 2.69/0.99  --qbf_mode                              false
% 2.69/0.99  --qbf_elim_univ                         false
% 2.69/0.99  --qbf_dom_inst                          none
% 2.69/0.99  --qbf_dom_pre_inst                      false
% 2.69/0.99  --qbf_sk_in                             false
% 2.69/0.99  --qbf_pred_elim                         true
% 2.69/0.99  --qbf_split                             512
% 2.69/0.99  
% 2.69/0.99  ------ BMC1 Options
% 2.69/0.99  
% 2.69/0.99  --bmc1_incremental                      false
% 2.69/0.99  --bmc1_axioms                           reachable_all
% 2.69/0.99  --bmc1_min_bound                        0
% 2.69/0.99  --bmc1_max_bound                        -1
% 2.69/0.99  --bmc1_max_bound_default                -1
% 2.69/0.99  --bmc1_symbol_reachability              true
% 2.69/0.99  --bmc1_property_lemmas                  false
% 2.69/0.99  --bmc1_k_induction                      false
% 2.69/0.99  --bmc1_non_equiv_states                 false
% 2.69/0.99  --bmc1_deadlock                         false
% 2.69/0.99  --bmc1_ucm                              false
% 2.69/0.99  --bmc1_add_unsat_core                   none
% 2.69/0.99  --bmc1_unsat_core_children              false
% 2.69/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.69/0.99  --bmc1_out_stat                         full
% 2.69/0.99  --bmc1_ground_init                      false
% 2.69/0.99  --bmc1_pre_inst_next_state              false
% 2.69/0.99  --bmc1_pre_inst_state                   false
% 2.69/0.99  --bmc1_pre_inst_reach_state             false
% 2.69/0.99  --bmc1_out_unsat_core                   false
% 2.69/0.99  --bmc1_aig_witness_out                  false
% 2.69/0.99  --bmc1_verbose                          false
% 2.69/0.99  --bmc1_dump_clauses_tptp                false
% 2.69/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.69/0.99  --bmc1_dump_file                        -
% 2.69/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.69/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.69/0.99  --bmc1_ucm_extend_mode                  1
% 2.69/0.99  --bmc1_ucm_init_mode                    2
% 2.69/0.99  --bmc1_ucm_cone_mode                    none
% 2.69/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.69/0.99  --bmc1_ucm_relax_model                  4
% 2.69/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.69/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.69/0.99  --bmc1_ucm_layered_model                none
% 2.69/0.99  --bmc1_ucm_max_lemma_size               10
% 2.69/0.99  
% 2.69/0.99  ------ AIG Options
% 2.69/0.99  
% 2.69/0.99  --aig_mode                              false
% 2.69/0.99  
% 2.69/0.99  ------ Instantiation Options
% 2.69/0.99  
% 2.69/0.99  --instantiation_flag                    true
% 2.69/0.99  --inst_sos_flag                         false
% 2.69/0.99  --inst_sos_phase                        true
% 2.69/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.69/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.69/0.99  --inst_lit_sel_side                     num_symb
% 2.69/0.99  --inst_solver_per_active                1400
% 2.69/0.99  --inst_solver_calls_frac                1.
% 2.69/0.99  --inst_passive_queue_type               priority_queues
% 2.69/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.69/0.99  --inst_passive_queues_freq              [25;2]
% 2.69/0.99  --inst_dismatching                      true
% 2.69/0.99  --inst_eager_unprocessed_to_passive     true
% 2.69/0.99  --inst_prop_sim_given                   true
% 2.69/0.99  --inst_prop_sim_new                     false
% 2.69/0.99  --inst_subs_new                         false
% 2.69/0.99  --inst_eq_res_simp                      false
% 2.69/0.99  --inst_subs_given                       false
% 2.69/0.99  --inst_orphan_elimination               true
% 2.69/0.99  --inst_learning_loop_flag               true
% 2.69/0.99  --inst_learning_start                   3000
% 2.69/0.99  --inst_learning_factor                  2
% 2.69/0.99  --inst_start_prop_sim_after_learn       3
% 2.69/0.99  --inst_sel_renew                        solver
% 2.69/0.99  --inst_lit_activity_flag                true
% 2.69/0.99  --inst_restr_to_given                   false
% 2.69/0.99  --inst_activity_threshold               500
% 2.69/0.99  --inst_out_proof                        true
% 2.69/0.99  
% 2.69/0.99  ------ Resolution Options
% 2.69/0.99  
% 2.69/0.99  --resolution_flag                       true
% 2.69/0.99  --res_lit_sel                           adaptive
% 2.69/0.99  --res_lit_sel_side                      none
% 2.69/0.99  --res_ordering                          kbo
% 2.69/0.99  --res_to_prop_solver                    active
% 2.69/0.99  --res_prop_simpl_new                    false
% 2.69/0.99  --res_prop_simpl_given                  true
% 2.69/0.99  --res_passive_queue_type                priority_queues
% 2.69/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.69/0.99  --res_passive_queues_freq               [15;5]
% 2.69/0.99  --res_forward_subs                      full
% 2.69/0.99  --res_backward_subs                     full
% 2.69/0.99  --res_forward_subs_resolution           true
% 2.69/0.99  --res_backward_subs_resolution          true
% 2.69/0.99  --res_orphan_elimination                true
% 2.69/0.99  --res_time_limit                        2.
% 2.69/0.99  --res_out_proof                         true
% 2.69/0.99  
% 2.69/0.99  ------ Superposition Options
% 2.69/0.99  
% 2.69/0.99  --superposition_flag                    true
% 2.69/0.99  --sup_passive_queue_type                priority_queues
% 2.69/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.69/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.69/0.99  --demod_completeness_check              fast
% 2.69/0.99  --demod_use_ground                      true
% 2.69/0.99  --sup_to_prop_solver                    passive
% 2.69/0.99  --sup_prop_simpl_new                    true
% 2.69/0.99  --sup_prop_simpl_given                  true
% 2.69/0.99  --sup_fun_splitting                     false
% 2.69/0.99  --sup_smt_interval                      50000
% 2.69/0.99  
% 2.69/0.99  ------ Superposition Simplification Setup
% 2.69/0.99  
% 2.69/0.99  --sup_indices_passive                   []
% 2.69/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.69/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/0.99  --sup_full_bw                           [BwDemod]
% 2.69/0.99  --sup_immed_triv                        [TrivRules]
% 2.69/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.69/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/0.99  --sup_immed_bw_main                     []
% 2.69/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.69/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.69/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.69/0.99  
% 2.69/0.99  ------ Combination Options
% 2.69/0.99  
% 2.69/0.99  --comb_res_mult                         3
% 2.69/0.99  --comb_sup_mult                         2
% 2.69/0.99  --comb_inst_mult                        10
% 2.69/0.99  
% 2.69/0.99  ------ Debug Options
% 2.69/0.99  
% 2.69/0.99  --dbg_backtrace                         false
% 2.69/0.99  --dbg_dump_prop_clauses                 false
% 2.69/0.99  --dbg_dump_prop_clauses_file            -
% 2.69/0.99  --dbg_out_stat                          false
% 2.69/0.99  ------ Parsing...
% 2.69/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.69/0.99  
% 2.69/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 11 0s  sf_e  pe_s  pe_e 
% 2.69/0.99  
% 2.69/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.69/0.99  
% 2.69/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.69/0.99  ------ Proving...
% 2.69/0.99  ------ Problem Properties 
% 2.69/0.99  
% 2.69/0.99  
% 2.69/0.99  clauses                                 21
% 2.69/0.99  conjectures                             2
% 2.69/0.99  EPR                                     2
% 2.69/0.99  Horn                                    15
% 2.69/0.99  unary                                   7
% 2.69/0.99  binary                                  4
% 2.69/0.99  lits                                    48
% 2.69/0.99  lits eq                                 7
% 2.69/0.99  fd_pure                                 0
% 2.69/0.99  fd_pseudo                               0
% 2.69/0.99  fd_cond                                 0
% 2.69/0.99  fd_pseudo_cond                          2
% 2.69/0.99  AC symbols                              0
% 2.69/0.99  
% 2.69/0.99  ------ Schedule dynamic 5 is on 
% 2.69/0.99  
% 2.69/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.69/0.99  
% 2.69/0.99  
% 2.69/0.99  ------ 
% 2.69/0.99  Current options:
% 2.69/0.99  ------ 
% 2.69/0.99  
% 2.69/0.99  ------ Input Options
% 2.69/0.99  
% 2.69/0.99  --out_options                           all
% 2.69/0.99  --tptp_safe_out                         true
% 2.69/0.99  --problem_path                          ""
% 2.69/0.99  --include_path                          ""
% 2.69/0.99  --clausifier                            res/vclausify_rel
% 2.69/0.99  --clausifier_options                    --mode clausify
% 2.69/0.99  --stdin                                 false
% 2.69/0.99  --stats_out                             all
% 2.69/0.99  
% 2.69/0.99  ------ General Options
% 2.69/0.99  
% 2.69/0.99  --fof                                   false
% 2.69/0.99  --time_out_real                         305.
% 2.69/0.99  --time_out_virtual                      -1.
% 2.69/0.99  --symbol_type_check                     false
% 2.69/0.99  --clausify_out                          false
% 2.69/0.99  --sig_cnt_out                           false
% 2.69/0.99  --trig_cnt_out                          false
% 2.69/0.99  --trig_cnt_out_tolerance                1.
% 2.69/0.99  --trig_cnt_out_sk_spl                   false
% 2.69/0.99  --abstr_cl_out                          false
% 2.69/0.99  
% 2.69/0.99  ------ Global Options
% 2.69/0.99  
% 2.69/0.99  --schedule                              default
% 2.69/0.99  --add_important_lit                     false
% 2.69/0.99  --prop_solver_per_cl                    1000
% 2.69/0.99  --min_unsat_core                        false
% 2.69/0.99  --soft_assumptions                      false
% 2.69/0.99  --soft_lemma_size                       3
% 2.69/0.99  --prop_impl_unit_size                   0
% 2.69/0.99  --prop_impl_unit                        []
% 2.69/0.99  --share_sel_clauses                     true
% 2.69/0.99  --reset_solvers                         false
% 2.69/0.99  --bc_imp_inh                            [conj_cone]
% 2.69/0.99  --conj_cone_tolerance                   3.
% 2.69/0.99  --extra_neg_conj                        none
% 2.69/0.99  --large_theory_mode                     true
% 2.69/0.99  --prolific_symb_bound                   200
% 2.69/0.99  --lt_threshold                          2000
% 2.69/0.99  --clause_weak_htbl                      true
% 2.69/0.99  --gc_record_bc_elim                     false
% 2.69/0.99  
% 2.69/0.99  ------ Preprocessing Options
% 2.69/0.99  
% 2.69/0.99  --preprocessing_flag                    true
% 2.69/0.99  --time_out_prep_mult                    0.1
% 2.69/0.99  --splitting_mode                        input
% 2.69/0.99  --splitting_grd                         true
% 2.69/0.99  --splitting_cvd                         false
% 2.69/0.99  --splitting_cvd_svl                     false
% 2.69/0.99  --splitting_nvd                         32
% 2.69/0.99  --sub_typing                            true
% 2.69/0.99  --prep_gs_sim                           true
% 2.69/0.99  --prep_unflatten                        true
% 2.69/0.99  --prep_res_sim                          true
% 2.69/0.99  --prep_upred                            true
% 2.69/0.99  --prep_sem_filter                       exhaustive
% 2.69/0.99  --prep_sem_filter_out                   false
% 2.69/0.99  --pred_elim                             true
% 2.69/0.99  --res_sim_input                         true
% 2.69/0.99  --eq_ax_congr_red                       true
% 2.69/0.99  --pure_diseq_elim                       true
% 2.69/0.99  --brand_transform                       false
% 2.69/0.99  --non_eq_to_eq                          false
% 2.69/0.99  --prep_def_merge                        true
% 2.69/0.99  --prep_def_merge_prop_impl              false
% 2.69/0.99  --prep_def_merge_mbd                    true
% 2.69/0.99  --prep_def_merge_tr_red                 false
% 2.69/0.99  --prep_def_merge_tr_cl                  false
% 2.69/0.99  --smt_preprocessing                     true
% 2.69/0.99  --smt_ac_axioms                         fast
% 2.69/0.99  --preprocessed_out                      false
% 2.69/0.99  --preprocessed_stats                    false
% 2.69/0.99  
% 2.69/0.99  ------ Abstraction refinement Options
% 2.69/0.99  
% 2.69/0.99  --abstr_ref                             []
% 2.69/0.99  --abstr_ref_prep                        false
% 2.69/0.99  --abstr_ref_until_sat                   false
% 2.69/0.99  --abstr_ref_sig_restrict                funpre
% 2.69/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.69/0.99  --abstr_ref_under                       []
% 2.69/0.99  
% 2.69/0.99  ------ SAT Options
% 2.69/0.99  
% 2.69/0.99  --sat_mode                              false
% 2.69/0.99  --sat_fm_restart_options                ""
% 2.69/0.99  --sat_gr_def                            false
% 2.69/0.99  --sat_epr_types                         true
% 2.69/0.99  --sat_non_cyclic_types                  false
% 2.69/0.99  --sat_finite_models                     false
% 2.69/0.99  --sat_fm_lemmas                         false
% 2.69/0.99  --sat_fm_prep                           false
% 2.69/0.99  --sat_fm_uc_incr                        true
% 2.69/0.99  --sat_out_model                         small
% 2.69/0.99  --sat_out_clauses                       false
% 2.69/0.99  
% 2.69/0.99  ------ QBF Options
% 2.69/0.99  
% 2.69/0.99  --qbf_mode                              false
% 2.69/0.99  --qbf_elim_univ                         false
% 2.69/0.99  --qbf_dom_inst                          none
% 2.69/0.99  --qbf_dom_pre_inst                      false
% 2.69/0.99  --qbf_sk_in                             false
% 2.69/0.99  --qbf_pred_elim                         true
% 2.69/0.99  --qbf_split                             512
% 2.69/0.99  
% 2.69/0.99  ------ BMC1 Options
% 2.69/0.99  
% 2.69/0.99  --bmc1_incremental                      false
% 2.69/0.99  --bmc1_axioms                           reachable_all
% 2.69/0.99  --bmc1_min_bound                        0
% 2.69/0.99  --bmc1_max_bound                        -1
% 2.69/0.99  --bmc1_max_bound_default                -1
% 2.69/0.99  --bmc1_symbol_reachability              true
% 2.69/0.99  --bmc1_property_lemmas                  false
% 2.69/0.99  --bmc1_k_induction                      false
% 2.69/0.99  --bmc1_non_equiv_states                 false
% 2.69/0.99  --bmc1_deadlock                         false
% 2.69/0.99  --bmc1_ucm                              false
% 2.69/0.99  --bmc1_add_unsat_core                   none
% 2.69/0.99  --bmc1_unsat_core_children              false
% 2.69/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.69/0.99  --bmc1_out_stat                         full
% 2.69/0.99  --bmc1_ground_init                      false
% 2.69/0.99  --bmc1_pre_inst_next_state              false
% 2.69/0.99  --bmc1_pre_inst_state                   false
% 2.69/0.99  --bmc1_pre_inst_reach_state             false
% 2.69/0.99  --bmc1_out_unsat_core                   false
% 2.69/0.99  --bmc1_aig_witness_out                  false
% 2.69/0.99  --bmc1_verbose                          false
% 2.69/0.99  --bmc1_dump_clauses_tptp                false
% 2.69/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.69/0.99  --bmc1_dump_file                        -
% 2.69/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.69/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.69/0.99  --bmc1_ucm_extend_mode                  1
% 2.69/0.99  --bmc1_ucm_init_mode                    2
% 2.69/0.99  --bmc1_ucm_cone_mode                    none
% 2.69/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.69/0.99  --bmc1_ucm_relax_model                  4
% 2.69/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.69/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.69/0.99  --bmc1_ucm_layered_model                none
% 2.69/0.99  --bmc1_ucm_max_lemma_size               10
% 2.69/0.99  
% 2.69/0.99  ------ AIG Options
% 2.69/0.99  
% 2.69/0.99  --aig_mode                              false
% 2.69/0.99  
% 2.69/0.99  ------ Instantiation Options
% 2.69/0.99  
% 2.69/0.99  --instantiation_flag                    true
% 2.69/0.99  --inst_sos_flag                         false
% 2.69/0.99  --inst_sos_phase                        true
% 2.69/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.69/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.69/0.99  --inst_lit_sel_side                     none
% 2.69/0.99  --inst_solver_per_active                1400
% 2.69/0.99  --inst_solver_calls_frac                1.
% 2.69/0.99  --inst_passive_queue_type               priority_queues
% 2.69/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.69/0.99  --inst_passive_queues_freq              [25;2]
% 2.69/0.99  --inst_dismatching                      true
% 2.69/0.99  --inst_eager_unprocessed_to_passive     true
% 2.69/0.99  --inst_prop_sim_given                   true
% 2.69/0.99  --inst_prop_sim_new                     false
% 2.69/0.99  --inst_subs_new                         false
% 2.69/0.99  --inst_eq_res_simp                      false
% 2.69/0.99  --inst_subs_given                       false
% 2.69/0.99  --inst_orphan_elimination               true
% 2.69/0.99  --inst_learning_loop_flag               true
% 2.69/0.99  --inst_learning_start                   3000
% 2.69/0.99  --inst_learning_factor                  2
% 2.69/0.99  --inst_start_prop_sim_after_learn       3
% 2.69/0.99  --inst_sel_renew                        solver
% 2.69/0.99  --inst_lit_activity_flag                true
% 2.69/0.99  --inst_restr_to_given                   false
% 2.69/0.99  --inst_activity_threshold               500
% 2.69/0.99  --inst_out_proof                        true
% 2.69/0.99  
% 2.69/0.99  ------ Resolution Options
% 2.69/0.99  
% 2.69/0.99  --resolution_flag                       false
% 2.69/0.99  --res_lit_sel                           adaptive
% 2.69/0.99  --res_lit_sel_side                      none
% 2.69/0.99  --res_ordering                          kbo
% 2.69/0.99  --res_to_prop_solver                    active
% 2.69/0.99  --res_prop_simpl_new                    false
% 2.69/0.99  --res_prop_simpl_given                  true
% 2.69/0.99  --res_passive_queue_type                priority_queues
% 2.69/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.69/0.99  --res_passive_queues_freq               [15;5]
% 2.69/0.99  --res_forward_subs                      full
% 2.69/0.99  --res_backward_subs                     full
% 2.69/0.99  --res_forward_subs_resolution           true
% 2.69/0.99  --res_backward_subs_resolution          true
% 2.69/0.99  --res_orphan_elimination                true
% 2.69/0.99  --res_time_limit                        2.
% 2.69/0.99  --res_out_proof                         true
% 2.69/0.99  
% 2.69/0.99  ------ Superposition Options
% 2.69/0.99  
% 2.69/0.99  --superposition_flag                    true
% 2.69/0.99  --sup_passive_queue_type                priority_queues
% 2.69/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.69/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.69/0.99  --demod_completeness_check              fast
% 2.69/0.99  --demod_use_ground                      true
% 2.69/0.99  --sup_to_prop_solver                    passive
% 2.69/0.99  --sup_prop_simpl_new                    true
% 2.69/0.99  --sup_prop_simpl_given                  true
% 2.69/0.99  --sup_fun_splitting                     false
% 2.69/0.99  --sup_smt_interval                      50000
% 2.69/0.99  
% 2.69/0.99  ------ Superposition Simplification Setup
% 2.69/0.99  
% 2.69/0.99  --sup_indices_passive                   []
% 2.69/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.69/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/0.99  --sup_full_bw                           [BwDemod]
% 2.69/0.99  --sup_immed_triv                        [TrivRules]
% 2.69/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.69/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/0.99  --sup_immed_bw_main                     []
% 2.69/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.69/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.69/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.69/0.99  
% 2.69/0.99  ------ Combination Options
% 2.69/0.99  
% 2.69/0.99  --comb_res_mult                         3
% 2.69/0.99  --comb_sup_mult                         2
% 2.69/0.99  --comb_inst_mult                        10
% 2.69/0.99  
% 2.69/0.99  ------ Debug Options
% 2.69/0.99  
% 2.69/0.99  --dbg_backtrace                         false
% 2.69/0.99  --dbg_dump_prop_clauses                 false
% 2.69/0.99  --dbg_dump_prop_clauses_file            -
% 2.69/0.99  --dbg_out_stat                          false
% 2.69/0.99  
% 2.69/0.99  
% 2.69/0.99  
% 2.69/0.99  
% 2.69/0.99  ------ Proving...
% 2.69/0.99  
% 2.69/0.99  
% 2.69/0.99  % SZS status Theorem for theBenchmark.p
% 2.69/0.99  
% 2.69/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.69/0.99  
% 2.69/0.99  fof(f13,axiom,(
% 2.69/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 2.69/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.99  
% 2.69/0.99  fof(f34,plain,(
% 2.69/0.99    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.69/0.99    inference(ennf_transformation,[],[f13])).
% 2.69/0.99  
% 2.69/0.99  fof(f44,plain,(
% 2.69/0.99    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.69/0.99    inference(nnf_transformation,[],[f34])).
% 2.69/0.99  
% 2.69/0.99  fof(f70,plain,(
% 2.69/0.99    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.69/0.99    inference(cnf_transformation,[],[f44])).
% 2.69/0.99  
% 2.69/0.99  fof(f14,conjecture,(
% 2.69/0.99    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 2.69/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.99  
% 2.69/0.99  fof(f15,negated_conjecture,(
% 2.69/0.99    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 2.69/0.99    inference(negated_conjecture,[],[f14])).
% 2.69/0.99  
% 2.69/0.99  fof(f16,plain,(
% 2.69/0.99    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 2.69/0.99    inference(pure_predicate_removal,[],[f15])).
% 2.69/0.99  
% 2.69/0.99  fof(f35,plain,(
% 2.69/0.99    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 2.69/0.99    inference(ennf_transformation,[],[f16])).
% 2.69/0.99  
% 2.69/0.99  fof(f36,plain,(
% 2.69/0.99    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 2.69/0.99    inference(flattening,[],[f35])).
% 2.69/0.99  
% 2.69/0.99  fof(f45,plain,(
% 2.69/0.99    ? [X0] : (? [X1] : (((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 2.69/0.99    inference(nnf_transformation,[],[f36])).
% 2.69/0.99  
% 2.69/0.99  fof(f46,plain,(
% 2.69/0.99    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 2.69/0.99    inference(flattening,[],[f45])).
% 2.69/0.99  
% 2.69/0.99  fof(f48,plain,(
% 2.69/0.99    ( ! [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => ((r2_hidden(k3_yellow_0(X0),sK4) | ~v1_subset_1(sK4,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),sK4) | v1_subset_1(sK4,u1_struct_0(X0))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(sK4,X0) & ~v1_xboole_0(sK4))) )),
% 2.69/0.99    introduced(choice_axiom,[])).
% 2.69/0.99  
% 2.69/0.99  fof(f47,plain,(
% 2.69/0.99    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : ((r2_hidden(k3_yellow_0(sK3),X1) | ~v1_subset_1(X1,u1_struct_0(sK3))) & (~r2_hidden(k3_yellow_0(sK3),X1) | v1_subset_1(X1,u1_struct_0(sK3))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) & v13_waybel_0(X1,sK3) & ~v1_xboole_0(X1)) & l1_orders_2(sK3) & v1_yellow_0(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3))),
% 2.69/0.99    introduced(choice_axiom,[])).
% 2.69/0.99  
% 2.69/0.99  fof(f49,plain,(
% 2.69/0.99    ((r2_hidden(k3_yellow_0(sK3),sK4) | ~v1_subset_1(sK4,u1_struct_0(sK3))) & (~r2_hidden(k3_yellow_0(sK3),sK4) | v1_subset_1(sK4,u1_struct_0(sK3))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) & v13_waybel_0(sK4,sK3) & ~v1_xboole_0(sK4)) & l1_orders_2(sK3) & v1_yellow_0(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3)),
% 2.69/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f46,f48,f47])).
% 2.69/0.99  
% 2.69/0.99  fof(f81,plain,(
% 2.69/0.99    r2_hidden(k3_yellow_0(sK3),sK4) | ~v1_subset_1(sK4,u1_struct_0(sK3))),
% 2.69/0.99    inference(cnf_transformation,[],[f49])).
% 2.69/0.99  
% 2.69/0.99  fof(f79,plain,(
% 2.69/0.99    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 2.69/0.99    inference(cnf_transformation,[],[f49])).
% 2.69/0.99  
% 2.69/0.99  fof(f4,axiom,(
% 2.69/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (! [X2] : (m1_subset_1(X2,X0) => r2_hidden(X2,X1)) => X0 = X1))),
% 2.69/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.99  
% 2.69/0.99  fof(f18,plain,(
% 2.69/0.99    ! [X0,X1] : ((X0 = X1 | ? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.69/0.99    inference(ennf_transformation,[],[f4])).
% 2.69/0.99  
% 2.69/0.99  fof(f19,plain,(
% 2.69/0.99    ! [X0,X1] : (X0 = X1 | ? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.69/0.99    inference(flattening,[],[f18])).
% 2.69/0.99  
% 2.69/0.99  fof(f37,plain,(
% 2.69/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),X0)))),
% 2.69/0.99    introduced(choice_axiom,[])).
% 2.69/0.99  
% 2.69/0.99  fof(f38,plain,(
% 2.69/0.99    ! [X0,X1] : (X0 = X1 | (~r2_hidden(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.69/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f37])).
% 2.69/0.99  
% 2.69/0.99  fof(f54,plain,(
% 2.69/0.99    ( ! [X0,X1] : (X0 = X1 | ~r2_hidden(sK0(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.69/0.99    inference(cnf_transformation,[],[f38])).
% 2.69/0.99  
% 2.69/0.99  fof(f53,plain,(
% 2.69/0.99    ( ! [X0,X1] : (X0 = X1 | m1_subset_1(sK0(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.69/0.99    inference(cnf_transformation,[],[f38])).
% 2.69/0.99  
% 2.69/0.99  fof(f12,axiom,(
% 2.69/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1 & r1_yellow_0(X0,k5_waybel_0(X0,X1)))))),
% 2.69/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.99  
% 2.69/0.99  fof(f32,plain,(
% 2.69/0.99    ! [X0] : (! [X1] : ((k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1 & r1_yellow_0(X0,k5_waybel_0(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.69/0.99    inference(ennf_transformation,[],[f12])).
% 2.69/0.99  
% 2.69/0.99  fof(f33,plain,(
% 2.69/0.99    ! [X0] : (! [X1] : ((k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1 & r1_yellow_0(X0,k5_waybel_0(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.69/0.99    inference(flattening,[],[f32])).
% 2.69/0.99  
% 2.69/0.99  fof(f68,plain,(
% 2.69/0.99    ( ! [X0,X1] : (k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.69/0.99    inference(cnf_transformation,[],[f33])).
% 2.69/0.99  
% 2.69/0.99  fof(f74,plain,(
% 2.69/0.99    v5_orders_2(sK3)),
% 2.69/0.99    inference(cnf_transformation,[],[f49])).
% 2.69/0.99  
% 2.69/0.99  fof(f71,plain,(
% 2.69/0.99    ~v2_struct_0(sK3)),
% 2.69/0.99    inference(cnf_transformation,[],[f49])).
% 2.69/0.99  
% 2.69/0.99  fof(f72,plain,(
% 2.69/0.99    v3_orders_2(sK3)),
% 2.69/0.99    inference(cnf_transformation,[],[f49])).
% 2.69/0.99  
% 2.69/0.99  fof(f73,plain,(
% 2.69/0.99    v4_orders_2(sK3)),
% 2.69/0.99    inference(cnf_transformation,[],[f49])).
% 2.69/0.99  
% 2.69/0.99  fof(f76,plain,(
% 2.69/0.99    l1_orders_2(sK3)),
% 2.69/0.99    inference(cnf_transformation,[],[f49])).
% 2.69/0.99  
% 2.69/0.99  fof(f67,plain,(
% 2.69/0.99    ( ! [X0,X1] : (r1_yellow_0(X0,k5_waybel_0(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.69/0.99    inference(cnf_transformation,[],[f33])).
% 2.69/0.99  
% 2.69/0.99  fof(f1,axiom,(
% 2.69/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.69/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.99  
% 2.69/0.99  fof(f50,plain,(
% 2.69/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.69/0.99    inference(cnf_transformation,[],[f1])).
% 2.69/0.99  
% 2.69/0.99  fof(f9,axiom,(
% 2.69/0.99    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : ((r1_yellow_0(X0,X2) & r1_yellow_0(X0,X1) & r1_tarski(X1,X2)) => r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))))),
% 2.69/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.99  
% 2.69/0.99  fof(f26,plain,(
% 2.69/0.99    ! [X0] : (! [X1,X2] : (r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) | (~r1_yellow_0(X0,X2) | ~r1_yellow_0(X0,X1) | ~r1_tarski(X1,X2))) | ~l1_orders_2(X0))),
% 2.69/0.99    inference(ennf_transformation,[],[f9])).
% 2.69/0.99  
% 2.69/0.99  fof(f27,plain,(
% 2.69/0.99    ! [X0] : (! [X1,X2] : (r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) | ~r1_yellow_0(X0,X2) | ~r1_yellow_0(X0,X1) | ~r1_tarski(X1,X2)) | ~l1_orders_2(X0))),
% 2.69/0.99    inference(flattening,[],[f26])).
% 2.69/0.99  
% 2.69/0.99  fof(f59,plain,(
% 2.69/0.99    ( ! [X2,X0,X1] : (r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) | ~r1_yellow_0(X0,X2) | ~r1_yellow_0(X0,X1) | ~r1_tarski(X1,X2) | ~l1_orders_2(X0)) )),
% 2.69/0.99    inference(cnf_transformation,[],[f27])).
% 2.69/0.99  
% 2.69/0.99  fof(f75,plain,(
% 2.69/0.99    v1_yellow_0(sK3)),
% 2.69/0.99    inference(cnf_transformation,[],[f49])).
% 2.69/0.99  
% 2.69/0.99  fof(f10,axiom,(
% 2.69/0.99    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)))),
% 2.69/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.99  
% 2.69/0.99  fof(f17,plain,(
% 2.69/0.99    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => r1_yellow_0(X0,k1_xboole_0))),
% 2.69/0.99    inference(pure_predicate_removal,[],[f10])).
% 2.69/0.99  
% 2.69/0.99  fof(f28,plain,(
% 2.69/0.99    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 2.69/0.99    inference(ennf_transformation,[],[f17])).
% 2.69/0.99  
% 2.69/0.99  fof(f29,plain,(
% 2.69/0.99    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.69/0.99    inference(flattening,[],[f28])).
% 2.69/0.99  
% 2.69/0.99  fof(f60,plain,(
% 2.69/0.99    ( ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 2.69/0.99    inference(cnf_transformation,[],[f29])).
% 2.69/0.99  
% 2.69/0.99  fof(f7,axiom,(
% 2.69/0.99    ! [X0] : (l1_orders_2(X0) => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 2.69/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.99  
% 2.69/0.99  fof(f24,plain,(
% 2.69/0.99    ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 2.69/0.99    inference(ennf_transformation,[],[f7])).
% 2.69/0.99  
% 2.69/0.99  fof(f57,plain,(
% 2.69/0.99    ( ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0)) )),
% 2.69/0.99    inference(cnf_transformation,[],[f24])).
% 2.69/0.99  
% 2.69/0.99  fof(f11,axiom,(
% 2.69/0.99    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 2.69/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.99  
% 2.69/0.99  fof(f30,plain,(
% 2.69/0.99    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 2.69/0.99    inference(ennf_transformation,[],[f11])).
% 2.69/0.99  
% 2.69/0.99  fof(f31,plain,(
% 2.69/0.99    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 2.69/0.99    inference(flattening,[],[f30])).
% 2.69/0.99  
% 2.69/0.99  fof(f39,plain,(
% 2.69/0.99    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 2.69/0.99    inference(nnf_transformation,[],[f31])).
% 2.69/0.99  
% 2.69/0.99  fof(f40,plain,(
% 2.69/0.99    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 2.69/0.99    inference(rectify,[],[f39])).
% 2.69/0.99  
% 2.69/0.99  fof(f42,plain,(
% 2.69/0.99    ( ! [X2] : (! [X1,X0] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r2_hidden(sK2(X0,X1),X1) & r1_orders_2(X0,X2,sK2(X0,X1)) & r2_hidden(X2,X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))))) )),
% 2.69/0.99    introduced(choice_axiom,[])).
% 2.69/0.99  
% 2.69/0.99  fof(f41,plain,(
% 2.69/0.99    ! [X1,X0] : (? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,sK1(X0,X1),X3) & r2_hidden(sK1(X0,X1),X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))))),
% 2.69/0.99    introduced(choice_axiom,[])).
% 2.69/0.99  
% 2.69/0.99  fof(f43,plain,(
% 2.69/0.99    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ((~r2_hidden(sK2(X0,X1),X1) & r1_orders_2(X0,sK1(X0,X1),sK2(X0,X1)) & r2_hidden(sK1(X0,X1),X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 2.69/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f40,f42,f41])).
% 2.69/0.99  
% 2.69/0.99  fof(f61,plain,(
% 2.69/0.99    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v13_waybel_0(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) )),
% 2.69/0.99    inference(cnf_transformation,[],[f43])).
% 2.69/0.99  
% 2.69/0.99  fof(f6,axiom,(
% 2.69/0.99    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.69/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.99  
% 2.69/0.99  fof(f22,plain,(
% 2.69/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.69/0.99    inference(ennf_transformation,[],[f6])).
% 2.69/0.99  
% 2.69/0.99  fof(f23,plain,(
% 2.69/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.69/0.99    inference(flattening,[],[f22])).
% 2.69/0.99  
% 2.69/0.99  fof(f56,plain,(
% 2.69/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.69/0.99    inference(cnf_transformation,[],[f23])).
% 2.69/0.99  
% 2.69/0.99  fof(f78,plain,(
% 2.69/0.99    v13_waybel_0(sK4,sK3)),
% 2.69/0.99    inference(cnf_transformation,[],[f49])).
% 2.69/0.99  
% 2.69/0.99  fof(f8,axiom,(
% 2.69/0.99    ! [X0] : (l1_orders_2(X0) => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)))),
% 2.69/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.99  
% 2.69/0.99  fof(f25,plain,(
% 2.69/0.99    ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 2.69/0.99    inference(ennf_transformation,[],[f8])).
% 2.69/0.99  
% 2.69/0.99  fof(f58,plain,(
% 2.69/0.99    ( ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.69/0.99    inference(cnf_transformation,[],[f25])).
% 2.69/0.99  
% 2.69/0.99  fof(f5,axiom,(
% 2.69/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.69/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.99  
% 2.69/0.99  fof(f20,plain,(
% 2.69/0.99    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.69/0.99    inference(ennf_transformation,[],[f5])).
% 2.69/0.99  
% 2.69/0.99  fof(f21,plain,(
% 2.69/0.99    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.69/0.99    inference(flattening,[],[f20])).
% 2.69/0.99  
% 2.69/0.99  fof(f55,plain,(
% 2.69/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.69/0.99    inference(cnf_transformation,[],[f21])).
% 2.69/0.99  
% 2.69/0.99  fof(f77,plain,(
% 2.69/0.99    ~v1_xboole_0(sK4)),
% 2.69/0.99    inference(cnf_transformation,[],[f49])).
% 2.69/0.99  
% 2.69/0.99  fof(f69,plain,(
% 2.69/0.99    ( ! [X0,X1] : (X0 != X1 | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.69/0.99    inference(cnf_transformation,[],[f44])).
% 2.69/0.99  
% 2.69/0.99  fof(f82,plain,(
% 2.69/0.99    ( ! [X1] : (~v1_subset_1(X1,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X1))) )),
% 2.69/0.99    inference(equality_resolution,[],[f69])).
% 2.69/0.99  
% 2.69/0.99  fof(f80,plain,(
% 2.69/0.99    ~r2_hidden(k3_yellow_0(sK3),sK4) | v1_subset_1(sK4,u1_struct_0(sK3))),
% 2.69/0.99    inference(cnf_transformation,[],[f49])).
% 2.69/0.99  
% 2.69/0.99  fof(f3,axiom,(
% 2.69/0.99    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 2.69/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.99  
% 2.69/0.99  fof(f52,plain,(
% 2.69/0.99    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 2.69/0.99    inference(cnf_transformation,[],[f3])).
% 2.69/0.99  
% 2.69/0.99  fof(f2,axiom,(
% 2.69/0.99    ! [X0] : k2_subset_1(X0) = X0),
% 2.69/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.99  
% 2.69/0.99  fof(f51,plain,(
% 2.69/0.99    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.69/0.99    inference(cnf_transformation,[],[f2])).
% 2.69/0.99  
% 2.69/0.99  cnf(c_19,plain,
% 2.69/0.99      ( v1_subset_1(X0,X1)
% 2.69/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.69/0.99      | X0 = X1 ),
% 2.69/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_21,negated_conjecture,
% 2.69/0.99      ( ~ v1_subset_1(sK4,u1_struct_0(sK3))
% 2.69/0.99      | r2_hidden(k3_yellow_0(sK3),sK4) ),
% 2.69/0.99      inference(cnf_transformation,[],[f81]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_233,plain,
% 2.69/0.99      ( ~ v1_subset_1(sK4,u1_struct_0(sK3))
% 2.69/0.99      | r2_hidden(k3_yellow_0(sK3),sK4) ),
% 2.69/0.99      inference(prop_impl,[status(thm)],[c_21]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_473,plain,
% 2.69/0.99      ( r2_hidden(k3_yellow_0(sK3),sK4)
% 2.69/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.69/0.99      | X1 = X0
% 2.69/0.99      | u1_struct_0(sK3) != X1
% 2.69/0.99      | sK4 != X0 ),
% 2.69/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_233]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_474,plain,
% 2.69/0.99      ( r2_hidden(k3_yellow_0(sK3),sK4)
% 2.69/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.69/0.99      | u1_struct_0(sK3) = sK4 ),
% 2.69/0.99      inference(unflattening,[status(thm)],[c_473]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_23,negated_conjecture,
% 2.69/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.69/0.99      inference(cnf_transformation,[],[f79]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_476,plain,
% 2.69/0.99      ( r2_hidden(k3_yellow_0(sK3),sK4) | u1_struct_0(sK3) = sK4 ),
% 2.69/0.99      inference(global_propositional_subsumption,
% 2.69/0.99                [status(thm)],
% 2.69/0.99                [c_474,c_23]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_1765,plain,
% 2.69/0.99      ( u1_struct_0(sK3) = sK4
% 2.69/0.99      | r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top ),
% 2.69/0.99      inference(predicate_to_equality,[status(thm)],[c_476]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_1409,plain,
% 2.69/0.99      ( X0 != X1 | u1_struct_0(X0) = u1_struct_0(X1) ),
% 2.69/0.99      theory(equality) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_1420,plain,
% 2.69/0.99      ( u1_struct_0(sK3) = u1_struct_0(sK3) | sK3 != sK3 ),
% 2.69/0.99      inference(instantiation,[status(thm)],[c_1409]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_1402,plain,( X0 = X0 ),theory(equality) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_1427,plain,
% 2.69/0.99      ( sK3 = sK3 ),
% 2.69/0.99      inference(instantiation,[status(thm)],[c_1402]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_3,plain,
% 2.69/0.99      ( ~ r2_hidden(sK0(X0,X1),X1)
% 2.69/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
% 2.69/0.99      | X1 = X0 ),
% 2.69/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_1962,plain,
% 2.69/0.99      ( ~ r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4)
% 2.69/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.69/0.99      | sK4 = u1_struct_0(sK3) ),
% 2.69/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_4,plain,
% 2.69/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.69/0.99      | m1_subset_1(sK0(X1,X0),X1)
% 2.69/0.99      | X0 = X1 ),
% 2.69/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_1965,plain,
% 2.69/0.99      ( m1_subset_1(sK0(u1_struct_0(sK3),sK4),u1_struct_0(sK3))
% 2.69/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.69/0.99      | sK4 = u1_struct_0(sK3) ),
% 2.69/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_1403,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_2027,plain,
% 2.69/0.99      ( X0 != X1 | X0 = sK4 | sK4 != X1 ),
% 2.69/0.99      inference(instantiation,[status(thm)],[c_1403]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_2401,plain,
% 2.69/0.99      ( X0 != u1_struct_0(sK3) | X0 = sK4 | sK4 != u1_struct_0(sK3) ),
% 2.69/0.99      inference(instantiation,[status(thm)],[c_2027]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_2741,plain,
% 2.69/0.99      ( u1_struct_0(sK3) != u1_struct_0(sK3)
% 2.69/0.99      | u1_struct_0(sK3) = sK4
% 2.69/0.99      | sK4 != u1_struct_0(sK3) ),
% 2.69/0.99      inference(instantiation,[status(thm)],[c_2401]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_1768,plain,
% 2.69/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 2.69/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_1770,plain,
% 2.69/0.99      ( X0 = X1
% 2.69/0.99      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.69/0.99      | m1_subset_1(sK0(X1,X0),X1) = iProver_top ),
% 2.69/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_17,plain,
% 2.69/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.69/0.99      | ~ v3_orders_2(X1)
% 2.69/0.99      | ~ v4_orders_2(X1)
% 2.69/0.99      | v2_struct_0(X1)
% 2.69/0.99      | ~ v5_orders_2(X1)
% 2.69/0.99      | ~ l1_orders_2(X1)
% 2.69/0.99      | k1_yellow_0(X1,k5_waybel_0(X1,X0)) = X0 ),
% 2.69/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_28,negated_conjecture,
% 2.69/0.99      ( v5_orders_2(sK3) ),
% 2.69/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_525,plain,
% 2.69/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.69/0.99      | ~ v3_orders_2(X1)
% 2.69/0.99      | ~ v4_orders_2(X1)
% 2.69/0.99      | v2_struct_0(X1)
% 2.69/0.99      | ~ l1_orders_2(X1)
% 2.69/0.99      | k1_yellow_0(X1,k5_waybel_0(X1,X0)) = X0
% 2.69/0.99      | sK3 != X1 ),
% 2.69/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_28]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_526,plain,
% 2.69/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.69/0.99      | ~ v3_orders_2(sK3)
% 2.69/0.99      | ~ v4_orders_2(sK3)
% 2.69/0.99      | v2_struct_0(sK3)
% 2.69/0.99      | ~ l1_orders_2(sK3)
% 2.69/0.99      | k1_yellow_0(sK3,k5_waybel_0(sK3,X0)) = X0 ),
% 2.69/0.99      inference(unflattening,[status(thm)],[c_525]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_31,negated_conjecture,
% 2.69/0.99      ( ~ v2_struct_0(sK3) ),
% 2.69/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_30,negated_conjecture,
% 2.69/0.99      ( v3_orders_2(sK3) ),
% 2.69/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_29,negated_conjecture,
% 2.69/0.99      ( v4_orders_2(sK3) ),
% 2.69/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_26,negated_conjecture,
% 2.69/0.99      ( l1_orders_2(sK3) ),
% 2.69/0.99      inference(cnf_transformation,[],[f76]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_530,plain,
% 2.69/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.69/0.99      | k1_yellow_0(sK3,k5_waybel_0(sK3,X0)) = X0 ),
% 2.69/0.99      inference(global_propositional_subsumption,
% 2.69/0.99                [status(thm)],
% 2.69/0.99                [c_526,c_31,c_30,c_29,c_26]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_1763,plain,
% 2.69/0.99      ( k1_yellow_0(sK3,k5_waybel_0(sK3,X0)) = X0
% 2.69/0.99      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
% 2.69/0.99      inference(predicate_to_equality,[status(thm)],[c_530]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_2266,plain,
% 2.69/0.99      ( k1_yellow_0(sK3,k5_waybel_0(sK3,sK0(u1_struct_0(sK3),X0))) = sK0(u1_struct_0(sK3),X0)
% 2.69/0.99      | u1_struct_0(sK3) = X0
% 2.69/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.69/0.99      inference(superposition,[status(thm)],[c_1770,c_1763]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_3653,plain,
% 2.69/0.99      ( k1_yellow_0(sK3,k5_waybel_0(sK3,sK0(u1_struct_0(sK3),sK4))) = sK0(u1_struct_0(sK3),sK4)
% 2.69/0.99      | u1_struct_0(sK3) = sK4 ),
% 2.69/0.99      inference(superposition,[status(thm)],[c_1768,c_2266]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_18,plain,
% 2.69/0.99      ( r1_yellow_0(X0,k5_waybel_0(X0,X1))
% 2.69/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.69/0.99      | ~ v3_orders_2(X0)
% 2.69/0.99      | ~ v4_orders_2(X0)
% 2.69/0.99      | v2_struct_0(X0)
% 2.69/0.99      | ~ v5_orders_2(X0)
% 2.69/0.99      | ~ l1_orders_2(X0) ),
% 2.69/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_507,plain,
% 2.69/0.99      ( r1_yellow_0(X0,k5_waybel_0(X0,X1))
% 2.69/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.69/0.99      | ~ v3_orders_2(X0)
% 2.69/0.99      | ~ v4_orders_2(X0)
% 2.69/0.99      | v2_struct_0(X0)
% 2.69/0.99      | ~ l1_orders_2(X0)
% 2.69/0.99      | sK3 != X0 ),
% 2.69/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_28]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_508,plain,
% 2.69/0.99      ( r1_yellow_0(sK3,k5_waybel_0(sK3,X0))
% 2.69/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.69/0.99      | ~ v3_orders_2(sK3)
% 2.69/0.99      | ~ v4_orders_2(sK3)
% 2.69/0.99      | v2_struct_0(sK3)
% 2.69/0.99      | ~ l1_orders_2(sK3) ),
% 2.69/0.99      inference(unflattening,[status(thm)],[c_507]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_512,plain,
% 2.69/0.99      ( r1_yellow_0(sK3,k5_waybel_0(sK3,X0))
% 2.69/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 2.69/0.99      inference(global_propositional_subsumption,
% 2.69/0.99                [status(thm)],
% 2.69/0.99                [c_508,c_31,c_30,c_29,c_26]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_0,plain,
% 2.69/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 2.69/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_9,plain,
% 2.69/0.99      ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
% 2.69/0.99      | ~ r1_yellow_0(X0,X2)
% 2.69/0.99      | ~ r1_yellow_0(X0,X1)
% 2.69/0.99      | ~ r1_tarski(X1,X2)
% 2.69/0.99      | ~ l1_orders_2(X0) ),
% 2.69/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_434,plain,
% 2.69/0.99      ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
% 2.69/0.99      | ~ r1_yellow_0(X0,X2)
% 2.69/0.99      | ~ r1_yellow_0(X0,X1)
% 2.69/0.99      | ~ l1_orders_2(X0)
% 2.69/0.99      | X2 != X3
% 2.69/0.99      | k1_xboole_0 != X1 ),
% 2.69/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_9]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_435,plain,
% 2.69/0.99      ( r1_orders_2(X0,k1_yellow_0(X0,k1_xboole_0),k1_yellow_0(X0,X1))
% 2.69/0.99      | ~ r1_yellow_0(X0,X1)
% 2.69/0.99      | ~ r1_yellow_0(X0,k1_xboole_0)
% 2.69/0.99      | ~ l1_orders_2(X0) ),
% 2.69/0.99      inference(unflattening,[status(thm)],[c_434]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_629,plain,
% 2.69/0.99      ( r1_orders_2(X0,k1_yellow_0(X0,k1_xboole_0),k1_yellow_0(X0,X1))
% 2.69/0.99      | ~ r1_yellow_0(X0,X1)
% 2.69/0.99      | ~ r1_yellow_0(X0,k1_xboole_0)
% 2.69/0.99      | sK3 != X0 ),
% 2.69/0.99      inference(resolution_lifted,[status(thm)],[c_435,c_26]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_630,plain,
% 2.69/0.99      ( r1_orders_2(sK3,k1_yellow_0(sK3,k1_xboole_0),k1_yellow_0(sK3,X0))
% 2.69/0.99      | ~ r1_yellow_0(sK3,X0)
% 2.69/0.99      | ~ r1_yellow_0(sK3,k1_xboole_0) ),
% 2.69/0.99      inference(unflattening,[status(thm)],[c_629]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_27,negated_conjecture,
% 2.69/0.99      ( v1_yellow_0(sK3) ),
% 2.69/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_10,plain,
% 2.69/0.99      ( r1_yellow_0(X0,k1_xboole_0)
% 2.69/0.99      | v2_struct_0(X0)
% 2.69/0.99      | ~ v5_orders_2(X0)
% 2.69/0.99      | ~ v1_yellow_0(X0)
% 2.69/0.99      | ~ l1_orders_2(X0) ),
% 2.69/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_72,plain,
% 2.69/0.99      ( r1_yellow_0(sK3,k1_xboole_0)
% 2.69/0.99      | v2_struct_0(sK3)
% 2.69/0.99      | ~ v5_orders_2(sK3)
% 2.69/0.99      | ~ v1_yellow_0(sK3)
% 2.69/0.99      | ~ l1_orders_2(sK3) ),
% 2.69/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_634,plain,
% 2.69/0.99      ( ~ r1_yellow_0(sK3,X0)
% 2.69/0.99      | r1_orders_2(sK3,k1_yellow_0(sK3,k1_xboole_0),k1_yellow_0(sK3,X0)) ),
% 2.69/0.99      inference(global_propositional_subsumption,
% 2.69/0.99                [status(thm)],
% 2.69/0.99                [c_630,c_31,c_28,c_27,c_26,c_72]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_635,plain,
% 2.69/0.99      ( r1_orders_2(sK3,k1_yellow_0(sK3,k1_xboole_0),k1_yellow_0(sK3,X0))
% 2.69/0.99      | ~ r1_yellow_0(sK3,X0) ),
% 2.69/0.99      inference(renaming,[status(thm)],[c_634]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_799,plain,
% 2.69/0.99      ( r1_orders_2(sK3,k1_yellow_0(sK3,k1_xboole_0),k1_yellow_0(sK3,X0))
% 2.69/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.69/0.99      | k5_waybel_0(sK3,X1) != X0
% 2.69/0.99      | sK3 != sK3 ),
% 2.69/0.99      inference(resolution_lifted,[status(thm)],[c_512,c_635]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_800,plain,
% 2.69/0.99      ( r1_orders_2(sK3,k1_yellow_0(sK3,k1_xboole_0),k1_yellow_0(sK3,k5_waybel_0(sK3,X0)))
% 2.69/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 2.69/0.99      inference(unflattening,[status(thm)],[c_799]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_1754,plain,
% 2.69/0.99      ( r1_orders_2(sK3,k1_yellow_0(sK3,k1_xboole_0),k1_yellow_0(sK3,k5_waybel_0(sK3,X0))) = iProver_top
% 2.69/0.99      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
% 2.69/0.99      inference(predicate_to_equality,[status(thm)],[c_800]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_7,plain,
% 2.69/0.99      ( ~ l1_orders_2(X0)
% 2.69/0.99      | k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) ),
% 2.69/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_694,plain,
% 2.69/0.99      ( k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) | sK3 != X0 ),
% 2.69/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_26]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_695,plain,
% 2.69/0.99      ( k1_yellow_0(sK3,k1_xboole_0) = k3_yellow_0(sK3) ),
% 2.69/0.99      inference(unflattening,[status(thm)],[c_694]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_1807,plain,
% 2.69/0.99      ( r1_orders_2(sK3,k3_yellow_0(sK3),k1_yellow_0(sK3,k5_waybel_0(sK3,X0))) = iProver_top
% 2.69/0.99      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
% 2.69/0.99      inference(light_normalisation,[status(thm)],[c_1754,c_695]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_3696,plain,
% 2.69/0.99      ( u1_struct_0(sK3) = sK4
% 2.69/0.99      | r1_orders_2(sK3,k3_yellow_0(sK3),sK0(u1_struct_0(sK3),sK4)) = iProver_top
% 2.69/0.99      | m1_subset_1(sK0(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) != iProver_top ),
% 2.69/0.99      inference(superposition,[status(thm)],[c_3653,c_1807]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_40,plain,
% 2.69/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 2.69/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_1966,plain,
% 2.69/0.99      ( sK4 = u1_struct_0(sK3)
% 2.69/0.99      | m1_subset_1(sK0(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) = iProver_top
% 2.69/0.99      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.69/0.99      inference(predicate_to_equality,[status(thm)],[c_1965]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_3714,plain,
% 2.69/0.99      ( r1_orders_2(sK3,k3_yellow_0(sK3),sK0(u1_struct_0(sK3),sK4)) = iProver_top
% 2.69/0.99      | u1_struct_0(sK3) = sK4 ),
% 2.69/0.99      inference(global_propositional_subsumption,
% 2.69/0.99                [status(thm)],
% 2.69/0.99                [c_3696,c_40,c_1420,c_1427,c_1966,c_2741]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_3715,plain,
% 2.69/0.99      ( u1_struct_0(sK3) = sK4
% 2.69/0.99      | r1_orders_2(sK3,k3_yellow_0(sK3),sK0(u1_struct_0(sK3),sK4)) = iProver_top ),
% 2.69/0.99      inference(renaming,[status(thm)],[c_3714]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_16,plain,
% 2.69/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 2.69/0.99      | ~ v13_waybel_0(X3,X0)
% 2.69/0.99      | ~ r2_hidden(X1,X3)
% 2.69/0.99      | r2_hidden(X2,X3)
% 2.69/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.69/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.69/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 2.69/0.99      | ~ l1_orders_2(X0) ),
% 2.69/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_647,plain,
% 2.69/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 2.69/0.99      | ~ v13_waybel_0(X3,X0)
% 2.69/0.99      | ~ r2_hidden(X1,X3)
% 2.69/0.99      | r2_hidden(X2,X3)
% 2.69/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.69/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.69/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 2.69/0.99      | sK3 != X0 ),
% 2.69/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_26]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_648,plain,
% 2.69/0.99      ( ~ r1_orders_2(sK3,X0,X1)
% 2.69/0.99      | ~ v13_waybel_0(X2,sK3)
% 2.69/0.99      | ~ r2_hidden(X0,X2)
% 2.69/0.99      | r2_hidden(X1,X2)
% 2.69/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.69/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.69/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.69/0.99      inference(unflattening,[status(thm)],[c_647]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_6,plain,
% 2.69/0.99      ( ~ r2_hidden(X0,X1)
% 2.69/0.99      | m1_subset_1(X0,X2)
% 2.69/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 2.69/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_664,plain,
% 2.69/0.99      ( ~ r1_orders_2(sK3,X0,X1)
% 2.69/0.99      | ~ v13_waybel_0(X2,sK3)
% 2.69/0.99      | ~ r2_hidden(X0,X2)
% 2.69/0.99      | r2_hidden(X1,X2)
% 2.69/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.69/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.69/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_648,c_6]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_1762,plain,
% 2.69/0.99      ( r1_orders_2(sK3,X0,X1) != iProver_top
% 2.69/0.99      | v13_waybel_0(X2,sK3) != iProver_top
% 2.69/0.99      | r2_hidden(X0,X2) != iProver_top
% 2.69/0.99      | r2_hidden(X1,X2) = iProver_top
% 2.69/0.99      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 2.69/0.99      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.69/0.99      inference(predicate_to_equality,[status(thm)],[c_664]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_2821,plain,
% 2.69/0.99      ( r1_orders_2(sK3,X0,X1) != iProver_top
% 2.69/0.99      | v13_waybel_0(sK4,sK3) != iProver_top
% 2.69/0.99      | r2_hidden(X0,sK4) != iProver_top
% 2.69/0.99      | r2_hidden(X1,sK4) = iProver_top
% 2.69/0.99      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top ),
% 2.69/0.99      inference(superposition,[status(thm)],[c_1768,c_1762]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_24,negated_conjecture,
% 2.69/0.99      ( v13_waybel_0(sK4,sK3) ),
% 2.69/0.99      inference(cnf_transformation,[],[f78]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_879,plain,
% 2.69/0.99      ( ~ r1_orders_2(sK3,X0,X1)
% 2.69/0.99      | ~ r2_hidden(X0,X2)
% 2.69/0.99      | r2_hidden(X1,X2)
% 2.69/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.69/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.69/0.99      | sK4 != X2
% 2.69/0.99      | sK3 != sK3 ),
% 2.69/0.99      inference(resolution_lifted,[status(thm)],[c_24,c_664]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_880,plain,
% 2.69/0.99      ( ~ r1_orders_2(sK3,X0,X1)
% 2.69/0.99      | ~ r2_hidden(X0,sK4)
% 2.69/0.99      | r2_hidden(X1,sK4)
% 2.69/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.69/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.69/0.99      inference(unflattening,[status(thm)],[c_879]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_881,plain,
% 2.69/0.99      ( r1_orders_2(sK3,X0,X1) != iProver_top
% 2.69/0.99      | r2_hidden(X0,sK4) != iProver_top
% 2.69/0.99      | r2_hidden(X1,sK4) = iProver_top
% 2.69/0.99      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 2.69/0.99      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.69/0.99      inference(predicate_to_equality,[status(thm)],[c_880]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_3149,plain,
% 2.69/0.99      ( r1_orders_2(sK3,X0,X1) != iProver_top
% 2.69/0.99      | r2_hidden(X0,sK4) != iProver_top
% 2.69/0.99      | r2_hidden(X1,sK4) = iProver_top
% 2.69/0.99      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top ),
% 2.69/0.99      inference(global_propositional_subsumption,
% 2.69/0.99                [status(thm)],
% 2.69/0.99                [c_2821,c_40,c_881]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_3720,plain,
% 2.69/0.99      ( u1_struct_0(sK3) = sK4
% 2.69/0.99      | r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4) = iProver_top
% 2.69/0.99      | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top
% 2.69/0.99      | m1_subset_1(sK0(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) != iProver_top ),
% 2.69/0.99      inference(superposition,[status(thm)],[c_3715,c_3149]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_3721,plain,
% 2.69/0.99      ( r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4)
% 2.69/0.99      | ~ r2_hidden(k3_yellow_0(sK3),sK4)
% 2.69/0.99      | ~ m1_subset_1(sK0(u1_struct_0(sK3),sK4),u1_struct_0(sK3))
% 2.69/0.99      | u1_struct_0(sK3) = sK4 ),
% 2.69/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_3720]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_3755,plain,
% 2.69/0.99      ( u1_struct_0(sK3) = sK4 ),
% 2.69/0.99      inference(global_propositional_subsumption,
% 2.69/0.99                [status(thm)],
% 2.69/0.99                [c_1765,c_23,c_476,c_1420,c_1427,c_1962,c_1965,c_2741,
% 2.69/0.99                 c_3721]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_8,plain,
% 2.69/0.99      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
% 2.69/0.99      | ~ l1_orders_2(X0) ),
% 2.69/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_687,plain,
% 2.69/0.99      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | sK3 != X0 ),
% 2.69/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_26]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_688,plain,
% 2.69/0.99      ( m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3)) ),
% 2.69/0.99      inference(unflattening,[status(thm)],[c_687]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_1760,plain,
% 2.69/0.99      ( m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3)) = iProver_top ),
% 2.69/0.99      inference(predicate_to_equality,[status(thm)],[c_688]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_3776,plain,
% 2.69/0.99      ( m1_subset_1(k3_yellow_0(sK3),sK4) = iProver_top ),
% 2.69/0.99      inference(demodulation,[status(thm)],[c_3755,c_1760]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_5,plain,
% 2.69/0.99      ( r2_hidden(X0,X1) | ~ m1_subset_1(X0,X1) | v1_xboole_0(X1) ),
% 2.69/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_25,negated_conjecture,
% 2.69/0.99      ( ~ v1_xboole_0(sK4) ),
% 2.69/0.99      inference(cnf_transformation,[],[f77]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_419,plain,
% 2.69/0.99      ( r2_hidden(X0,X1) | ~ m1_subset_1(X0,X1) | sK4 != X1 ),
% 2.69/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_25]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_420,plain,
% 2.69/0.99      ( r2_hidden(X0,sK4) | ~ m1_subset_1(X0,sK4) ),
% 2.69/0.99      inference(unflattening,[status(thm)],[c_419]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_1766,plain,
% 2.69/0.99      ( r2_hidden(X0,sK4) = iProver_top
% 2.69/0.99      | m1_subset_1(X0,sK4) != iProver_top ),
% 2.69/0.99      inference(predicate_to_equality,[status(thm)],[c_420]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_3909,plain,
% 2.69/0.99      ( r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top ),
% 2.69/0.99      inference(superposition,[status(thm)],[c_3776,c_1766]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_20,plain,
% 2.69/0.99      ( ~ v1_subset_1(X0,X0) | ~ m1_subset_1(X0,k1_zfmisc_1(X0)) ),
% 2.69/0.99      inference(cnf_transformation,[],[f82]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_22,negated_conjecture,
% 2.69/0.99      ( v1_subset_1(sK4,u1_struct_0(sK3))
% 2.69/0.99      | ~ r2_hidden(k3_yellow_0(sK3),sK4) ),
% 2.69/0.99      inference(cnf_transformation,[],[f80]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_231,plain,
% 2.69/0.99      ( v1_subset_1(sK4,u1_struct_0(sK3))
% 2.69/0.99      | ~ r2_hidden(k3_yellow_0(sK3),sK4) ),
% 2.69/0.99      inference(prop_impl,[status(thm)],[c_22]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_487,plain,
% 2.69/0.99      ( ~ r2_hidden(k3_yellow_0(sK3),sK4)
% 2.69/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(X0))
% 2.69/0.99      | u1_struct_0(sK3) != X0
% 2.69/0.99      | sK4 != X0 ),
% 2.69/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_231]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_488,plain,
% 2.69/0.99      ( ~ r2_hidden(k3_yellow_0(sK3),sK4)
% 2.69/0.99      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.69/0.99      | sK4 != u1_struct_0(sK3) ),
% 2.69/0.99      inference(unflattening,[status(thm)],[c_487]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_1764,plain,
% 2.69/0.99      ( sK4 != u1_struct_0(sK3)
% 2.69/0.99      | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top
% 2.69/0.99      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.69/0.99      inference(predicate_to_equality,[status(thm)],[c_488]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_2,plain,
% 2.69/0.99      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 2.69/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_1772,plain,
% 2.69/0.99      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 2.69/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_1,plain,
% 2.69/0.99      ( k2_subset_1(X0) = X0 ),
% 2.69/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_1783,plain,
% 2.69/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.69/0.99      inference(light_normalisation,[status(thm)],[c_1772,c_1]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_1851,plain,
% 2.69/0.99      ( u1_struct_0(sK3) != sK4
% 2.69/0.99      | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
% 2.69/0.99      inference(forward_subsumption_resolution,
% 2.69/0.99                [status(thm)],
% 2.69/0.99                [c_1764,c_1783]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(contradiction,plain,
% 2.69/0.99      ( $false ),
% 2.69/0.99      inference(minisat,[status(thm)],[c_3909,c_3755,c_1851]) ).
% 2.69/0.99  
% 2.69/0.99  
% 2.69/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.69/0.99  
% 2.69/0.99  ------                               Statistics
% 2.69/0.99  
% 2.69/0.99  ------ General
% 2.69/0.99  
% 2.69/0.99  abstr_ref_over_cycles:                  0
% 2.69/0.99  abstr_ref_under_cycles:                 0
% 2.69/0.99  gc_basic_clause_elim:                   0
% 2.69/0.99  forced_gc_time:                         0
% 2.69/0.99  parsing_time:                           0.009
% 2.69/0.99  unif_index_cands_time:                  0.
% 2.69/0.99  unif_index_add_time:                    0.
% 2.69/0.99  orderings_time:                         0.
% 2.69/0.99  out_proof_time:                         0.009
% 2.69/0.99  total_time:                             0.143
% 2.69/0.99  num_of_symbols:                         57
% 2.69/0.99  num_of_terms:                           3008
% 2.69/0.99  
% 2.69/0.99  ------ Preprocessing
% 2.69/0.99  
% 2.69/0.99  num_of_splits:                          0
% 2.69/0.99  num_of_split_atoms:                     0
% 2.69/0.99  num_of_reused_defs:                     0
% 2.69/0.99  num_eq_ax_congr_red:                    25
% 2.69/0.99  num_of_sem_filtered_clauses:            1
% 2.69/0.99  num_of_subtypes:                        0
% 2.69/0.99  monotx_restored_types:                  0
% 2.69/0.99  sat_num_of_epr_types:                   0
% 2.69/0.99  sat_num_of_non_cyclic_types:            0
% 2.69/0.99  sat_guarded_non_collapsed_types:        0
% 2.69/0.99  num_pure_diseq_elim:                    0
% 2.69/0.99  simp_replaced_by:                       0
% 2.69/0.99  res_preprocessed:                       122
% 2.69/0.99  prep_upred:                             0
% 2.69/0.99  prep_unflattend:                        52
% 2.69/0.99  smt_new_axioms:                         0
% 2.69/0.99  pred_elim_cands:                        4
% 2.69/0.99  pred_elim:                              10
% 2.69/0.99  pred_elim_cl:                           11
% 2.69/0.99  pred_elim_cycles:                       15
% 2.69/0.99  merged_defs:                            2
% 2.69/0.99  merged_defs_ncl:                        0
% 2.69/0.99  bin_hyper_res:                          2
% 2.69/0.99  prep_cycles:                            4
% 2.69/0.99  pred_elim_time:                         0.016
% 2.69/0.99  splitting_time:                         0.
% 2.69/0.99  sem_filter_time:                        0.
% 2.69/0.99  monotx_time:                            0.
% 2.69/0.99  subtype_inf_time:                       0.
% 2.69/0.99  
% 2.69/0.99  ------ Problem properties
% 2.69/0.99  
% 2.69/0.99  clauses:                                21
% 2.69/0.99  conjectures:                            2
% 2.69/0.99  epr:                                    2
% 2.69/0.99  horn:                                   15
% 2.69/0.99  ground:                                 7
% 2.69/0.99  unary:                                  7
% 2.69/0.99  binary:                                 4
% 2.69/0.99  lits:                                   48
% 2.69/0.99  lits_eq:                                7
% 2.69/0.99  fd_pure:                                0
% 2.69/0.99  fd_pseudo:                              0
% 2.69/0.99  fd_cond:                                0
% 2.69/0.99  fd_pseudo_cond:                         2
% 2.69/0.99  ac_symbols:                             0
% 2.69/0.99  
% 2.69/0.99  ------ Propositional Solver
% 2.69/0.99  
% 2.69/0.99  prop_solver_calls:                      27
% 2.69/0.99  prop_fast_solver_calls:                 912
% 2.69/0.99  smt_solver_calls:                       0
% 2.69/0.99  smt_fast_solver_calls:                  0
% 2.69/0.99  prop_num_of_clauses:                    1138
% 2.69/0.99  prop_preprocess_simplified:             4714
% 2.69/0.99  prop_fo_subsumed:                       19
% 2.69/0.99  prop_solver_time:                       0.
% 2.69/0.99  smt_solver_time:                        0.
% 2.69/0.99  smt_fast_solver_time:                   0.
% 2.69/0.99  prop_fast_solver_time:                  0.
% 2.69/0.99  prop_unsat_core_time:                   0.
% 2.69/0.99  
% 2.69/0.99  ------ QBF
% 2.69/0.99  
% 2.69/0.99  qbf_q_res:                              0
% 2.69/0.99  qbf_num_tautologies:                    0
% 2.69/0.99  qbf_prep_cycles:                        0
% 2.69/0.99  
% 2.69/0.99  ------ BMC1
% 2.69/0.99  
% 2.69/0.99  bmc1_current_bound:                     -1
% 2.69/0.99  bmc1_last_solved_bound:                 -1
% 2.69/0.99  bmc1_unsat_core_size:                   -1
% 2.69/0.99  bmc1_unsat_core_parents_size:           -1
% 2.69/0.99  bmc1_merge_next_fun:                    0
% 2.69/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.69/0.99  
% 2.69/0.99  ------ Instantiation
% 2.69/0.99  
% 2.69/0.99  inst_num_of_clauses:                    315
% 2.69/0.99  inst_num_in_passive:                    138
% 2.69/0.99  inst_num_in_active:                     170
% 2.69/0.99  inst_num_in_unprocessed:                7
% 2.69/0.99  inst_num_of_loops:                      190
% 2.69/0.99  inst_num_of_learning_restarts:          0
% 2.69/0.99  inst_num_moves_active_passive:          18
% 2.69/0.99  inst_lit_activity:                      0
% 2.69/0.99  inst_lit_activity_moves:                0
% 2.69/0.99  inst_num_tautologies:                   0
% 2.69/0.99  inst_num_prop_implied:                  0
% 2.69/0.99  inst_num_existing_simplified:           0
% 2.69/0.99  inst_num_eq_res_simplified:             0
% 2.69/0.99  inst_num_child_elim:                    0
% 2.69/0.99  inst_num_of_dismatching_blockings:      24
% 2.69/0.99  inst_num_of_non_proper_insts:           321
% 2.69/0.99  inst_num_of_duplicates:                 0
% 2.69/0.99  inst_inst_num_from_inst_to_res:         0
% 2.69/0.99  inst_dismatching_checking_time:         0.
% 2.69/0.99  
% 2.69/0.99  ------ Resolution
% 2.69/0.99  
% 2.69/0.99  res_num_of_clauses:                     0
% 2.69/0.99  res_num_in_passive:                     0
% 2.69/0.99  res_num_in_active:                      0
% 2.69/0.99  res_num_of_loops:                       126
% 2.69/0.99  res_forward_subset_subsumed:            39
% 2.69/0.99  res_backward_subset_subsumed:           0
% 2.69/0.99  res_forward_subsumed:                   0
% 2.69/0.99  res_backward_subsumed:                  0
% 2.69/0.99  res_forward_subsumption_resolution:     5
% 2.69/0.99  res_backward_subsumption_resolution:    0
% 2.69/0.99  res_clause_to_clause_subsumption:       189
% 2.69/0.99  res_orphan_elimination:                 0
% 2.69/0.99  res_tautology_del:                      31
% 2.69/0.99  res_num_eq_res_simplified:              0
% 2.69/0.99  res_num_sel_changes:                    0
% 2.69/0.99  res_moves_from_active_to_pass:          0
% 2.69/0.99  
% 2.69/0.99  ------ Superposition
% 2.69/0.99  
% 2.69/0.99  sup_time_total:                         0.
% 2.69/0.99  sup_time_generating:                    0.
% 2.69/0.99  sup_time_sim_full:                      0.
% 2.69/0.99  sup_time_sim_immed:                     0.
% 2.69/0.99  
% 2.69/0.99  sup_num_of_clauses:                     41
% 2.69/0.99  sup_num_in_active:                      16
% 2.69/0.99  sup_num_in_passive:                     25
% 2.69/0.99  sup_num_of_loops:                       36
% 2.69/0.99  sup_fw_superposition:                   25
% 2.69/0.99  sup_bw_superposition:                   16
% 2.69/0.99  sup_immediate_simplified:               10
% 2.69/0.99  sup_given_eliminated:                   0
% 2.69/0.99  comparisons_done:                       0
% 2.69/0.99  comparisons_avoided:                    5
% 2.69/0.99  
% 2.69/0.99  ------ Simplifications
% 2.69/0.99  
% 2.69/0.99  
% 2.69/0.99  sim_fw_subset_subsumed:                 6
% 2.69/0.99  sim_bw_subset_subsumed:                 3
% 2.69/0.99  sim_fw_subsumed:                        4
% 2.69/0.99  sim_bw_subsumed:                        0
% 2.69/0.99  sim_fw_subsumption_res:                 1
% 2.69/0.99  sim_bw_subsumption_res:                 0
% 2.69/0.99  sim_tautology_del:                      3
% 2.69/0.99  sim_eq_tautology_del:                   3
% 2.69/0.99  sim_eq_res_simp:                        1
% 2.69/0.99  sim_fw_demodulated:                     0
% 2.69/0.99  sim_bw_demodulated:                     20
% 2.69/0.99  sim_light_normalised:                   7
% 2.69/0.99  sim_joinable_taut:                      0
% 2.69/0.99  sim_joinable_simp:                      0
% 2.69/0.99  sim_ac_normalised:                      0
% 2.69/0.99  sim_smt_subsumption:                    0
% 2.69/0.99  
%------------------------------------------------------------------------------
