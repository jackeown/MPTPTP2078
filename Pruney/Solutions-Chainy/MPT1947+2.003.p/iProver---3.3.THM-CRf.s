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
% DateTime   : Thu Dec  3 12:28:19 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :  154 (2340 expanded)
%              Number of clauses        :  100 ( 585 expanded)
%              Number of leaves         :   16 ( 651 expanded)
%              Depth                    :   26
%              Number of atoms          :  756 (19454 expanded)
%              Number of equality atoms :  140 (2267 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   20 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).

fof(f46,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v1_yellow_6(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => k11_yellow_6(X0,X1) = k4_yellow_6(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v8_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v1_yellow_6(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => k11_yellow_6(X0,X1) = k4_yellow_6(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k11_yellow_6(X0,X1) != k4_yellow_6(X0,X1)
          & l1_waybel_0(X1,X0)
          & v1_yellow_6(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v8_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k11_yellow_6(X0,X1) != k4_yellow_6(X0,X1)
          & l1_waybel_0(X1,X0)
          & v1_yellow_6(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v8_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k11_yellow_6(X0,X1) != k4_yellow_6(X0,X1)
          & l1_waybel_0(X1,X0)
          & v1_yellow_6(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
     => ( k11_yellow_6(X0,sK2) != k4_yellow_6(X0,sK2)
        & l1_waybel_0(sK2,X0)
        & v1_yellow_6(sK2,X0)
        & v7_waybel_0(sK2)
        & v4_orders_2(sK2)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k11_yellow_6(X0,X1) != k4_yellow_6(X0,X1)
            & l1_waybel_0(X1,X0)
            & v1_yellow_6(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k11_yellow_6(sK1,X1) != k4_yellow_6(sK1,X1)
          & l1_waybel_0(X1,sK1)
          & v1_yellow_6(X1,sK1)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK1)
      & v8_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( k11_yellow_6(sK1,sK2) != k4_yellow_6(sK1,sK2)
    & l1_waybel_0(sK2,sK1)
    & v1_yellow_6(sK2,sK1)
    & v7_waybel_0(sK2)
    & v4_orders_2(sK2)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v8_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f35,f43,f42])).

fof(f73,plain,(
    v1_yellow_6(sK2,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f56,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v1_yellow_6(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => k2_waybel_0(X0,X1,X2) = k4_yellow_6(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_waybel_0(X0,X1,X2) = k4_yellow_6(X0,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v1_yellow_6(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_waybel_0(X0,X1,X2) = k4_yellow_6(X0,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v1_yellow_6(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k2_waybel_0(X0,X1,X2) = k4_yellow_6(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v1_yellow_6(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f69,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f66,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f70,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f71,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f72,plain,(
    v7_waybel_0(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f74,plain,(
    l1_waybel_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f75,plain,(
    k11_yellow_6(sK1,sK2) != k4_yellow_6(sK1,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v1_yellow_6(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1))
          | ~ l1_waybel_0(X1,X0)
          | ~ v1_yellow_6(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1))
          | ~ l1_waybel_0(X1,X0)
          | ~ v1_yellow_6(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v1_yellow_6(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f67,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v3_yellow_6(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( k11_yellow_6(X0,X1) = X2
              <=> r2_hidden(X2,k10_yellow_6(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k11_yellow_6(X0,X1) = X2
              <=> r2_hidden(X2,k10_yellow_6(X0,X1)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v3_yellow_6(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k11_yellow_6(X0,X1) = X2
              <=> r2_hidden(X2,k10_yellow_6(X0,X1)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v3_yellow_6(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k11_yellow_6(X0,X1) = X2
                  | ~ r2_hidden(X2,k10_yellow_6(X0,X1)) )
                & ( r2_hidden(X2,k10_yellow_6(X0,X1))
                  | k11_yellow_6(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v3_yellow_6(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k11_yellow_6(X0,X1) = X2
      | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v3_yellow_6(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f68,plain,(
    v8_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => ( ( v1_yellow_6(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ( v3_yellow_6(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_yellow_6(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
          | ~ v1_yellow_6(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_yellow_6(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
          | ~ v1_yellow_6(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v3_yellow_6(X1,X0)
      | ~ v1_yellow_6(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1533,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_7,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1527,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2001,plain,
    ( m1_subset_1(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1533,c_1527])).

cnf(c_23,negated_conjecture,
    ( v1_yellow_6(sK2,sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_11,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_19,plain,
    ( ~ v1_yellow_6(X0,X1)
    | ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_struct_0(X1)
    | k2_waybel_0(X1,X0,X2) = k4_yellow_6(X1,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_323,plain,
    ( ~ v1_yellow_6(X0,X1)
    | ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X3)
    | X1 != X3
    | k2_waybel_0(X1,X0,X2) = k4_yellow_6(X1,X0) ),
    inference(resolution_lifted,[status(thm)],[c_11,c_19])).

cnf(c_324,plain,
    ( ~ v1_yellow_6(X0,X1)
    | ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k2_waybel_0(X1,X0,X2) = k4_yellow_6(X1,X0) ),
    inference(unflattening,[status(thm)],[c_323])).

cnf(c_27,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_579,plain,
    ( ~ v1_yellow_6(X0,X1)
    | ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k2_waybel_0(X1,X0,X2) = k4_yellow_6(X1,X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_324,c_27])).

cnf(c_580,plain,
    ( ~ v1_yellow_6(X0,sK1)
    | ~ l1_waybel_0(X0,sK1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK1)
    | k2_waybel_0(sK1,X0,X1) = k4_yellow_6(sK1,X0) ),
    inference(unflattening,[status(thm)],[c_579])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_584,plain,
    ( v2_struct_0(X0)
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_waybel_0(X0,sK1)
    | ~ v1_yellow_6(X0,sK1)
    | k2_waybel_0(sK1,X0,X1) = k4_yellow_6(sK1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_580,c_30])).

cnf(c_585,plain,
    ( ~ v1_yellow_6(X0,sK1)
    | ~ l1_waybel_0(X0,sK1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k2_waybel_0(sK1,X0,X1) = k4_yellow_6(sK1,X0) ),
    inference(renaming,[status(thm)],[c_584])).

cnf(c_623,plain,
    ( ~ l1_waybel_0(X0,sK1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k2_waybel_0(sK1,X0,X1) = k4_yellow_6(sK1,X0)
    | sK2 != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_585])).

cnf(c_624,plain,
    ( ~ l1_waybel_0(sK2,sK1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ v4_orders_2(sK2)
    | ~ v7_waybel_0(sK2)
    | v2_struct_0(sK2)
    | k2_waybel_0(sK1,sK2,X0) = k4_yellow_6(sK1,sK2) ),
    inference(unflattening,[status(thm)],[c_623])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_25,negated_conjecture,
    ( v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_24,negated_conjecture,
    ( v7_waybel_0(sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_22,negated_conjecture,
    ( l1_waybel_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_628,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | k2_waybel_0(sK1,sK2,X0) = k4_yellow_6(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_624,c_26,c_25,c_24,c_22])).

cnf(c_1524,plain,
    ( k2_waybel_0(sK1,sK2,X0) = k4_yellow_6(sK1,sK2)
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_628])).

cnf(c_2551,plain,
    ( k2_waybel_0(sK1,sK2,sK0(u1_struct_0(sK2))) = k4_yellow_6(sK1,sK2)
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2001,c_1524])).

cnf(c_2,plain,
    ( m1_subset_1(X0,X1)
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1531,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2455,plain,
    ( k2_waybel_0(sK1,sK2,X0) = k4_yellow_6(sK1,sK2)
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1531,c_1524])).

cnf(c_35,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_36,plain,
    ( v4_orders_2(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_37,plain,
    ( v7_waybel_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_39,plain,
    ( l1_waybel_0(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_21,negated_conjecture,
    ( k11_yellow_6(sK1,sK2) != k4_yellow_6(sK1,sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_20,plain,
    ( ~ v1_yellow_6(X0,X1)
    | ~ l1_waybel_0(X0,X1)
    | r2_hidden(k4_yellow_6(X1,X0),k10_yellow_6(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_29,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_483,plain,
    ( ~ v1_yellow_6(X0,X1)
    | ~ l1_waybel_0(X0,X1)
    | r2_hidden(k4_yellow_6(X1,X0),k10_yellow_6(X1,X0))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_29])).

cnf(c_484,plain,
    ( ~ v1_yellow_6(X0,sK1)
    | ~ l1_waybel_0(X0,sK1)
    | r2_hidden(k4_yellow_6(sK1,X0),k10_yellow_6(sK1,X0))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_483])).

cnf(c_488,plain,
    ( ~ v1_yellow_6(X0,sK1)
    | ~ l1_waybel_0(X0,sK1)
    | r2_hidden(k4_yellow_6(sK1,X0),k10_yellow_6(sK1,X0))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_484,c_30,c_27])).

cnf(c_652,plain,
    ( ~ l1_waybel_0(X0,sK1)
    | r2_hidden(k4_yellow_6(sK1,X0),k10_yellow_6(sK1,X0))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | sK2 != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_488])).

cnf(c_653,plain,
    ( ~ l1_waybel_0(sK2,sK1)
    | r2_hidden(k4_yellow_6(sK1,sK2),k10_yellow_6(sK1,sK2))
    | ~ v4_orders_2(sK2)
    | ~ v7_waybel_0(sK2)
    | v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_652])).

cnf(c_654,plain,
    ( l1_waybel_0(sK2,sK1) != iProver_top
    | r2_hidden(k4_yellow_6(sK1,sK2),k10_yellow_6(sK1,sK2)) = iProver_top
    | v4_orders_2(sK2) != iProver_top
    | v7_waybel_0(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_653])).

cnf(c_12,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(k2_waybel_0(X1,X0,X2),u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_356,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(k2_waybel_0(X1,X0,X2),u1_struct_0(X1))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X3)
    | X1 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_12])).

cnf(c_357,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(k2_waybel_0(X1,X0,X2),u1_struct_0(X1))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_356])).

cnf(c_557,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(k2_waybel_0(X1,X0,X2),u1_struct_0(X1))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_357,c_27])).

cnf(c_558,plain,
    ( ~ l1_waybel_0(X0,sK1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(k2_waybel_0(sK1,X0,X1),u1_struct_0(sK1))
    | v2_struct_0(X0)
    | v2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_557])).

cnf(c_562,plain,
    ( v2_struct_0(X0)
    | m1_subset_1(k2_waybel_0(sK1,X0,X1),u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_waybel_0(X0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_558,c_30])).

cnf(c_563,plain,
    ( ~ l1_waybel_0(X0,sK1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(k2_waybel_0(sK1,X0,X1),u1_struct_0(sK1))
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_562])).

cnf(c_712,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k2_waybel_0(sK1,X1,X0),u1_struct_0(sK1))
    | v2_struct_0(X1)
    | sK2 != X1
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_563])).

cnf(c_713,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | m1_subset_1(k2_waybel_0(sK1,sK2,X0),u1_struct_0(sK1))
    | v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_712])).

cnf(c_714,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k2_waybel_0(sK1,sK2,X0),u1_struct_0(sK1)) = iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_713])).

cnf(c_1652,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2))
    | ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1653,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2)) = iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1652])).

cnf(c_1266,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1771,plain,
    ( k4_yellow_6(sK1,sK2) = k4_yellow_6(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1266])).

cnf(c_17,plain,
    ( ~ v3_yellow_6(X0,X1)
    | ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k10_yellow_6(X1,X0))
    | ~ v8_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | k11_yellow_6(X1,X0) = X2 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_28,negated_conjecture,
    ( v8_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_430,plain,
    ( ~ v3_yellow_6(X0,X1)
    | ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k10_yellow_6(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k11_yellow_6(X1,X0) = X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_28])).

cnf(c_431,plain,
    ( ~ v3_yellow_6(X0,sK1)
    | ~ l1_waybel_0(X0,sK1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ r2_hidden(X1,k10_yellow_6(sK1,X0))
    | ~ v2_pre_topc(sK1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | k11_yellow_6(sK1,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_430])).

cnf(c_435,plain,
    ( ~ r2_hidden(X1,k10_yellow_6(sK1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ l1_waybel_0(X0,sK1)
    | ~ v3_yellow_6(X0,sK1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k11_yellow_6(sK1,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_431,c_30,c_29,c_27])).

cnf(c_436,plain,
    ( ~ v3_yellow_6(X0,sK1)
    | ~ l1_waybel_0(X0,sK1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ r2_hidden(X1,k10_yellow_6(sK1,X0))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k11_yellow_6(sK1,X0) = X1 ),
    inference(renaming,[status(thm)],[c_435])).

cnf(c_13,plain,
    ( ~ v1_yellow_6(X0,X1)
    | v3_yellow_6(X0,X1)
    | ~ l1_waybel_0(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_513,plain,
    ( ~ v1_yellow_6(X0,X1)
    | v3_yellow_6(X0,X1)
    | ~ l1_waybel_0(X0,X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_29])).

cnf(c_514,plain,
    ( ~ v1_yellow_6(X0,sK1)
    | v3_yellow_6(X0,sK1)
    | ~ l1_waybel_0(X0,sK1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_513])).

cnf(c_518,plain,
    ( ~ v1_yellow_6(X0,sK1)
    | v3_yellow_6(X0,sK1)
    | ~ l1_waybel_0(X0,sK1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_514,c_30,c_27])).

cnf(c_641,plain,
    ( v3_yellow_6(X0,sK1)
    | ~ l1_waybel_0(X0,sK1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | sK2 != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_518])).

cnf(c_642,plain,
    ( v3_yellow_6(sK2,sK1)
    | ~ l1_waybel_0(sK2,sK1)
    | ~ v4_orders_2(sK2)
    | ~ v7_waybel_0(sK2)
    | v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_641])).

cnf(c_644,plain,
    ( v3_yellow_6(sK2,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_642,c_26,c_25,c_24,c_22])).

cnf(c_670,plain,
    ( ~ l1_waybel_0(X0,sK1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ r2_hidden(X1,k10_yellow_6(sK1,X0))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k11_yellow_6(sK1,X0) = X1
    | sK2 != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_436,c_644])).

cnf(c_671,plain,
    ( ~ l1_waybel_0(sK2,sK1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ r2_hidden(X0,k10_yellow_6(sK1,sK2))
    | ~ v4_orders_2(sK2)
    | ~ v7_waybel_0(sK2)
    | v2_struct_0(sK2)
    | k11_yellow_6(sK1,sK2) = X0 ),
    inference(unflattening,[status(thm)],[c_670])).

cnf(c_675,plain,
    ( ~ r2_hidden(X0,k10_yellow_6(sK1,sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | k11_yellow_6(sK1,sK2) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_671,c_26,c_25,c_24,c_22])).

cnf(c_676,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ r2_hidden(X0,k10_yellow_6(sK1,sK2))
    | k11_yellow_6(sK1,sK2) = X0 ),
    inference(renaming,[status(thm)],[c_675])).

cnf(c_1790,plain,
    ( ~ m1_subset_1(k2_waybel_0(sK1,sK2,X0),u1_struct_0(sK1))
    | ~ r2_hidden(k2_waybel_0(sK1,sK2,X0),k10_yellow_6(sK1,sK2))
    | k11_yellow_6(sK1,sK2) = k2_waybel_0(sK1,sK2,X0) ),
    inference(instantiation,[status(thm)],[c_676])).

cnf(c_1791,plain,
    ( k11_yellow_6(sK1,sK2) = k2_waybel_0(sK1,sK2,X0)
    | m1_subset_1(k2_waybel_0(sK1,sK2,X0),u1_struct_0(sK1)) != iProver_top
    | r2_hidden(k2_waybel_0(sK1,sK2,X0),k10_yellow_6(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1790])).

cnf(c_1927,plain,
    ( k10_yellow_6(sK1,sK2) = k10_yellow_6(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1266])).

cnf(c_1267,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1628,plain,
    ( k4_yellow_6(sK1,sK2) != X0
    | k11_yellow_6(sK1,sK2) != X0
    | k11_yellow_6(sK1,sK2) = k4_yellow_6(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1267])).

cnf(c_1949,plain,
    ( k4_yellow_6(sK1,sK2) != k2_waybel_0(sK1,sK2,X0)
    | k11_yellow_6(sK1,sK2) != k2_waybel_0(sK1,sK2,X0)
    | k11_yellow_6(sK1,sK2) = k4_yellow_6(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1628])).

cnf(c_1268,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1630,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_yellow_6(sK1,sK2),k10_yellow_6(sK1,sK2))
    | X0 != k4_yellow_6(sK1,sK2)
    | X1 != k10_yellow_6(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1268])).

cnf(c_1785,plain,
    ( r2_hidden(k2_waybel_0(sK1,sK2,X0),X1)
    | ~ r2_hidden(k4_yellow_6(sK1,sK2),k10_yellow_6(sK1,sK2))
    | X1 != k10_yellow_6(sK1,sK2)
    | k2_waybel_0(sK1,sK2,X0) != k4_yellow_6(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1630])).

cnf(c_2192,plain,
    ( r2_hidden(k2_waybel_0(sK1,sK2,X0),k10_yellow_6(sK1,sK2))
    | ~ r2_hidden(k4_yellow_6(sK1,sK2),k10_yellow_6(sK1,sK2))
    | k2_waybel_0(sK1,sK2,X0) != k4_yellow_6(sK1,sK2)
    | k10_yellow_6(sK1,sK2) != k10_yellow_6(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1785])).

cnf(c_2193,plain,
    ( k2_waybel_0(sK1,sK2,X0) != k4_yellow_6(sK1,sK2)
    | k10_yellow_6(sK1,sK2) != k10_yellow_6(sK1,sK2)
    | r2_hidden(k2_waybel_0(sK1,sK2,X0),k10_yellow_6(sK1,sK2)) = iProver_top
    | r2_hidden(k4_yellow_6(sK1,sK2),k10_yellow_6(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2192])).

cnf(c_1995,plain,
    ( k2_waybel_0(sK1,sK2,X0) != X1
    | k4_yellow_6(sK1,sK2) != X1
    | k4_yellow_6(sK1,sK2) = k2_waybel_0(sK1,sK2,X0) ),
    inference(instantiation,[status(thm)],[c_1267])).

cnf(c_2531,plain,
    ( k2_waybel_0(sK1,sK2,X0) != k4_yellow_6(sK1,sK2)
    | k4_yellow_6(sK1,sK2) = k2_waybel_0(sK1,sK2,X0)
    | k4_yellow_6(sK1,sK2) != k4_yellow_6(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1995])).

cnf(c_2635,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2455,c_35,c_36,c_37,c_39,c_21,c_654,c_714,c_1653,c_1771,c_1791,c_1927,c_1949,c_2193,c_2531])).

cnf(c_2646,plain,
    ( k2_waybel_0(sK1,sK2,sK0(u1_struct_0(sK2))) = k4_yellow_6(sK1,sK2)
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2551,c_2635])).

cnf(c_2705,plain,
    ( k2_waybel_0(sK1,sK2,sK0(u1_struct_0(sK2))) = k4_yellow_6(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_2551,c_2646])).

cnf(c_717,plain,
    ( m1_subset_1(k2_waybel_0(sK1,sK2,X0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_713,c_26])).

cnf(c_718,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | m1_subset_1(k2_waybel_0(sK1,sK2,X0),u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_717])).

cnf(c_1520,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k2_waybel_0(sK1,sK2,X0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_718])).

cnf(c_2793,plain,
    ( m1_subset_1(k4_yellow_6(sK1,sK2),u1_struct_0(sK1)) = iProver_top
    | m1_subset_1(sK0(u1_struct_0(sK2)),u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2705,c_1520])).

cnf(c_655,plain,
    ( r2_hidden(k4_yellow_6(sK1,sK2),k10_yellow_6(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_653,c_26,c_25,c_24,c_22])).

cnf(c_911,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | k4_yellow_6(sK1,sK2) != X0
    | k10_yellow_6(sK1,sK2) != k10_yellow_6(sK1,sK2)
    | k11_yellow_6(sK1,sK2) = X0 ),
    inference(resolution_lifted,[status(thm)],[c_655,c_676])).

cnf(c_912,plain,
    ( ~ m1_subset_1(k4_yellow_6(sK1,sK2),u1_struct_0(sK1))
    | k11_yellow_6(sK1,sK2) = k4_yellow_6(sK1,sK2) ),
    inference(unflattening,[status(thm)],[c_911])).

cnf(c_913,plain,
    ( k11_yellow_6(sK1,sK2) = k4_yellow_6(sK1,sK2)
    | m1_subset_1(k4_yellow_6(sK1,sK2),u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_912])).

cnf(c_2814,plain,
    ( m1_subset_1(sK0(u1_struct_0(sK2)),u1_struct_0(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2793,c_21,c_913])).

cnf(c_2820,plain,
    ( v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2001,c_2814])).

cnf(c_2926,plain,
    ( v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2820,c_2635])).

cnf(c_2932,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_2820,c_2926])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:44:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.20/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.00  
% 2.20/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.20/1.00  
% 2.20/1.00  ------  iProver source info
% 2.20/1.00  
% 2.20/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.20/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.20/1.00  git: non_committed_changes: false
% 2.20/1.00  git: last_make_outside_of_git: false
% 2.20/1.00  
% 2.20/1.00  ------ 
% 2.20/1.00  
% 2.20/1.00  ------ Input Options
% 2.20/1.00  
% 2.20/1.00  --out_options                           all
% 2.20/1.00  --tptp_safe_out                         true
% 2.20/1.00  --problem_path                          ""
% 2.20/1.00  --include_path                          ""
% 2.20/1.00  --clausifier                            res/vclausify_rel
% 2.20/1.00  --clausifier_options                    --mode clausify
% 2.20/1.00  --stdin                                 false
% 2.20/1.00  --stats_out                             all
% 2.20/1.00  
% 2.20/1.00  ------ General Options
% 2.20/1.00  
% 2.20/1.00  --fof                                   false
% 2.20/1.00  --time_out_real                         305.
% 2.20/1.00  --time_out_virtual                      -1.
% 2.20/1.00  --symbol_type_check                     false
% 2.20/1.00  --clausify_out                          false
% 2.20/1.00  --sig_cnt_out                           false
% 2.20/1.00  --trig_cnt_out                          false
% 2.20/1.00  --trig_cnt_out_tolerance                1.
% 2.20/1.00  --trig_cnt_out_sk_spl                   false
% 2.20/1.00  --abstr_cl_out                          false
% 2.20/1.00  
% 2.20/1.00  ------ Global Options
% 2.20/1.00  
% 2.20/1.00  --schedule                              default
% 2.20/1.00  --add_important_lit                     false
% 2.20/1.00  --prop_solver_per_cl                    1000
% 2.20/1.00  --min_unsat_core                        false
% 2.20/1.00  --soft_assumptions                      false
% 2.20/1.00  --soft_lemma_size                       3
% 2.20/1.00  --prop_impl_unit_size                   0
% 2.20/1.00  --prop_impl_unit                        []
% 2.20/1.00  --share_sel_clauses                     true
% 2.20/1.00  --reset_solvers                         false
% 2.20/1.00  --bc_imp_inh                            [conj_cone]
% 2.20/1.00  --conj_cone_tolerance                   3.
% 2.20/1.00  --extra_neg_conj                        none
% 2.20/1.00  --large_theory_mode                     true
% 2.20/1.00  --prolific_symb_bound                   200
% 2.20/1.00  --lt_threshold                          2000
% 2.20/1.00  --clause_weak_htbl                      true
% 2.20/1.00  --gc_record_bc_elim                     false
% 2.20/1.00  
% 2.20/1.00  ------ Preprocessing Options
% 2.20/1.00  
% 2.20/1.00  --preprocessing_flag                    true
% 2.20/1.00  --time_out_prep_mult                    0.1
% 2.20/1.00  --splitting_mode                        input
% 2.20/1.00  --splitting_grd                         true
% 2.20/1.00  --splitting_cvd                         false
% 2.20/1.00  --splitting_cvd_svl                     false
% 2.20/1.00  --splitting_nvd                         32
% 2.20/1.00  --sub_typing                            true
% 2.20/1.00  --prep_gs_sim                           true
% 2.20/1.00  --prep_unflatten                        true
% 2.20/1.00  --prep_res_sim                          true
% 2.20/1.00  --prep_upred                            true
% 2.20/1.00  --prep_sem_filter                       exhaustive
% 2.20/1.00  --prep_sem_filter_out                   false
% 2.20/1.00  --pred_elim                             true
% 2.20/1.00  --res_sim_input                         true
% 2.20/1.00  --eq_ax_congr_red                       true
% 2.20/1.00  --pure_diseq_elim                       true
% 2.20/1.00  --brand_transform                       false
% 2.20/1.00  --non_eq_to_eq                          false
% 2.20/1.00  --prep_def_merge                        true
% 2.20/1.00  --prep_def_merge_prop_impl              false
% 2.20/1.00  --prep_def_merge_mbd                    true
% 2.20/1.00  --prep_def_merge_tr_red                 false
% 2.20/1.00  --prep_def_merge_tr_cl                  false
% 2.20/1.00  --smt_preprocessing                     true
% 2.20/1.00  --smt_ac_axioms                         fast
% 2.20/1.00  --preprocessed_out                      false
% 2.20/1.00  --preprocessed_stats                    false
% 2.20/1.00  
% 2.20/1.00  ------ Abstraction refinement Options
% 2.20/1.00  
% 2.20/1.00  --abstr_ref                             []
% 2.20/1.00  --abstr_ref_prep                        false
% 2.20/1.00  --abstr_ref_until_sat                   false
% 2.20/1.00  --abstr_ref_sig_restrict                funpre
% 2.20/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.20/1.00  --abstr_ref_under                       []
% 2.20/1.00  
% 2.20/1.00  ------ SAT Options
% 2.20/1.00  
% 2.20/1.00  --sat_mode                              false
% 2.20/1.00  --sat_fm_restart_options                ""
% 2.20/1.00  --sat_gr_def                            false
% 2.20/1.00  --sat_epr_types                         true
% 2.20/1.00  --sat_non_cyclic_types                  false
% 2.20/1.00  --sat_finite_models                     false
% 2.20/1.00  --sat_fm_lemmas                         false
% 2.20/1.00  --sat_fm_prep                           false
% 2.20/1.00  --sat_fm_uc_incr                        true
% 2.20/1.00  --sat_out_model                         small
% 2.20/1.00  --sat_out_clauses                       false
% 2.20/1.00  
% 2.20/1.00  ------ QBF Options
% 2.20/1.00  
% 2.20/1.00  --qbf_mode                              false
% 2.20/1.00  --qbf_elim_univ                         false
% 2.20/1.00  --qbf_dom_inst                          none
% 2.20/1.00  --qbf_dom_pre_inst                      false
% 2.20/1.00  --qbf_sk_in                             false
% 2.20/1.00  --qbf_pred_elim                         true
% 2.20/1.00  --qbf_split                             512
% 2.20/1.00  
% 2.20/1.00  ------ BMC1 Options
% 2.20/1.00  
% 2.20/1.00  --bmc1_incremental                      false
% 2.20/1.00  --bmc1_axioms                           reachable_all
% 2.20/1.00  --bmc1_min_bound                        0
% 2.20/1.00  --bmc1_max_bound                        -1
% 2.20/1.00  --bmc1_max_bound_default                -1
% 2.20/1.00  --bmc1_symbol_reachability              true
% 2.20/1.00  --bmc1_property_lemmas                  false
% 2.20/1.00  --bmc1_k_induction                      false
% 2.20/1.00  --bmc1_non_equiv_states                 false
% 2.20/1.00  --bmc1_deadlock                         false
% 2.20/1.00  --bmc1_ucm                              false
% 2.20/1.00  --bmc1_add_unsat_core                   none
% 2.20/1.00  --bmc1_unsat_core_children              false
% 2.20/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.20/1.00  --bmc1_out_stat                         full
% 2.20/1.00  --bmc1_ground_init                      false
% 2.20/1.00  --bmc1_pre_inst_next_state              false
% 2.20/1.00  --bmc1_pre_inst_state                   false
% 2.20/1.00  --bmc1_pre_inst_reach_state             false
% 2.20/1.00  --bmc1_out_unsat_core                   false
% 2.20/1.00  --bmc1_aig_witness_out                  false
% 2.20/1.00  --bmc1_verbose                          false
% 2.20/1.00  --bmc1_dump_clauses_tptp                false
% 2.20/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.20/1.00  --bmc1_dump_file                        -
% 2.20/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.20/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.20/1.00  --bmc1_ucm_extend_mode                  1
% 2.20/1.00  --bmc1_ucm_init_mode                    2
% 2.20/1.00  --bmc1_ucm_cone_mode                    none
% 2.20/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.20/1.00  --bmc1_ucm_relax_model                  4
% 2.20/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.20/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.20/1.00  --bmc1_ucm_layered_model                none
% 2.20/1.00  --bmc1_ucm_max_lemma_size               10
% 2.20/1.00  
% 2.20/1.00  ------ AIG Options
% 2.20/1.00  
% 2.20/1.00  --aig_mode                              false
% 2.20/1.00  
% 2.20/1.00  ------ Instantiation Options
% 2.20/1.00  
% 2.20/1.00  --instantiation_flag                    true
% 2.20/1.00  --inst_sos_flag                         false
% 2.20/1.00  --inst_sos_phase                        true
% 2.20/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.20/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.20/1.00  --inst_lit_sel_side                     num_symb
% 2.20/1.00  --inst_solver_per_active                1400
% 2.20/1.00  --inst_solver_calls_frac                1.
% 2.20/1.00  --inst_passive_queue_type               priority_queues
% 2.20/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.20/1.00  --inst_passive_queues_freq              [25;2]
% 2.20/1.00  --inst_dismatching                      true
% 2.20/1.00  --inst_eager_unprocessed_to_passive     true
% 2.20/1.00  --inst_prop_sim_given                   true
% 2.20/1.00  --inst_prop_sim_new                     false
% 2.20/1.00  --inst_subs_new                         false
% 2.20/1.00  --inst_eq_res_simp                      false
% 2.20/1.00  --inst_subs_given                       false
% 2.20/1.00  --inst_orphan_elimination               true
% 2.20/1.00  --inst_learning_loop_flag               true
% 2.20/1.00  --inst_learning_start                   3000
% 2.20/1.00  --inst_learning_factor                  2
% 2.20/1.00  --inst_start_prop_sim_after_learn       3
% 2.20/1.00  --inst_sel_renew                        solver
% 2.20/1.00  --inst_lit_activity_flag                true
% 2.20/1.00  --inst_restr_to_given                   false
% 2.20/1.00  --inst_activity_threshold               500
% 2.20/1.00  --inst_out_proof                        true
% 2.20/1.00  
% 2.20/1.00  ------ Resolution Options
% 2.20/1.00  
% 2.20/1.00  --resolution_flag                       true
% 2.20/1.00  --res_lit_sel                           adaptive
% 2.20/1.00  --res_lit_sel_side                      none
% 2.20/1.00  --res_ordering                          kbo
% 2.20/1.00  --res_to_prop_solver                    active
% 2.20/1.00  --res_prop_simpl_new                    false
% 2.20/1.00  --res_prop_simpl_given                  true
% 2.20/1.00  --res_passive_queue_type                priority_queues
% 2.20/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.20/1.00  --res_passive_queues_freq               [15;5]
% 2.20/1.00  --res_forward_subs                      full
% 2.20/1.00  --res_backward_subs                     full
% 2.20/1.00  --res_forward_subs_resolution           true
% 2.20/1.00  --res_backward_subs_resolution          true
% 2.20/1.00  --res_orphan_elimination                true
% 2.20/1.00  --res_time_limit                        2.
% 2.20/1.00  --res_out_proof                         true
% 2.20/1.00  
% 2.20/1.00  ------ Superposition Options
% 2.20/1.00  
% 2.20/1.00  --superposition_flag                    true
% 2.20/1.00  --sup_passive_queue_type                priority_queues
% 2.20/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.20/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.20/1.00  --demod_completeness_check              fast
% 2.20/1.00  --demod_use_ground                      true
% 2.20/1.00  --sup_to_prop_solver                    passive
% 2.20/1.00  --sup_prop_simpl_new                    true
% 2.20/1.00  --sup_prop_simpl_given                  true
% 2.20/1.00  --sup_fun_splitting                     false
% 2.20/1.00  --sup_smt_interval                      50000
% 2.20/1.00  
% 2.20/1.00  ------ Superposition Simplification Setup
% 2.20/1.00  
% 2.20/1.00  --sup_indices_passive                   []
% 2.20/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.20/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.20/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.20/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.20/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.20/1.00  --sup_full_bw                           [BwDemod]
% 2.20/1.00  --sup_immed_triv                        [TrivRules]
% 2.20/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.20/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.20/1.00  --sup_immed_bw_main                     []
% 2.20/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.20/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.20/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.20/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.20/1.00  
% 2.20/1.00  ------ Combination Options
% 2.20/1.00  
% 2.20/1.00  --comb_res_mult                         3
% 2.20/1.00  --comb_sup_mult                         2
% 2.20/1.00  --comb_inst_mult                        10
% 2.20/1.00  
% 2.20/1.00  ------ Debug Options
% 2.20/1.00  
% 2.20/1.00  --dbg_backtrace                         false
% 2.20/1.00  --dbg_dump_prop_clauses                 false
% 2.20/1.00  --dbg_dump_prop_clauses_file            -
% 2.20/1.00  --dbg_out_stat                          false
% 2.20/1.00  ------ Parsing...
% 2.20/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.20/1.00  
% 2.20/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 9 0s  sf_e  pe_s  pe_e 
% 2.20/1.00  
% 2.20/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.20/1.00  
% 2.20/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.20/1.00  ------ Proving...
% 2.20/1.00  ------ Problem Properties 
% 2.20/1.00  
% 2.20/1.00  
% 2.20/1.00  clauses                                 15
% 2.20/1.00  conjectures                             1
% 2.20/1.00  EPR                                     5
% 2.20/1.00  Horn                                    13
% 2.20/1.00  unary                                   3
% 2.20/1.00  binary                                  7
% 2.20/1.00  lits                                    32
% 2.20/1.00  lits eq                                 3
% 2.20/1.00  fd_pure                                 0
% 2.20/1.00  fd_pseudo                               0
% 2.20/1.00  fd_cond                                 1
% 2.20/1.00  fd_pseudo_cond                          0
% 2.20/1.00  AC symbols                              0
% 2.20/1.00  
% 2.20/1.00  ------ Schedule dynamic 5 is on 
% 2.20/1.00  
% 2.20/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.20/1.00  
% 2.20/1.00  
% 2.20/1.00  ------ 
% 2.20/1.00  Current options:
% 2.20/1.00  ------ 
% 2.20/1.00  
% 2.20/1.00  ------ Input Options
% 2.20/1.00  
% 2.20/1.00  --out_options                           all
% 2.20/1.00  --tptp_safe_out                         true
% 2.20/1.00  --problem_path                          ""
% 2.20/1.00  --include_path                          ""
% 2.20/1.00  --clausifier                            res/vclausify_rel
% 2.20/1.00  --clausifier_options                    --mode clausify
% 2.20/1.00  --stdin                                 false
% 2.20/1.00  --stats_out                             all
% 2.20/1.00  
% 2.20/1.00  ------ General Options
% 2.20/1.00  
% 2.20/1.00  --fof                                   false
% 2.20/1.00  --time_out_real                         305.
% 2.20/1.00  --time_out_virtual                      -1.
% 2.20/1.00  --symbol_type_check                     false
% 2.20/1.00  --clausify_out                          false
% 2.20/1.00  --sig_cnt_out                           false
% 2.20/1.00  --trig_cnt_out                          false
% 2.20/1.00  --trig_cnt_out_tolerance                1.
% 2.20/1.00  --trig_cnt_out_sk_spl                   false
% 2.20/1.00  --abstr_cl_out                          false
% 2.20/1.00  
% 2.20/1.00  ------ Global Options
% 2.20/1.00  
% 2.20/1.00  --schedule                              default
% 2.20/1.00  --add_important_lit                     false
% 2.20/1.00  --prop_solver_per_cl                    1000
% 2.20/1.00  --min_unsat_core                        false
% 2.20/1.00  --soft_assumptions                      false
% 2.20/1.00  --soft_lemma_size                       3
% 2.20/1.00  --prop_impl_unit_size                   0
% 2.20/1.00  --prop_impl_unit                        []
% 2.20/1.00  --share_sel_clauses                     true
% 2.20/1.00  --reset_solvers                         false
% 2.20/1.00  --bc_imp_inh                            [conj_cone]
% 2.20/1.00  --conj_cone_tolerance                   3.
% 2.20/1.00  --extra_neg_conj                        none
% 2.20/1.00  --large_theory_mode                     true
% 2.20/1.00  --prolific_symb_bound                   200
% 2.20/1.00  --lt_threshold                          2000
% 2.20/1.00  --clause_weak_htbl                      true
% 2.20/1.00  --gc_record_bc_elim                     false
% 2.20/1.00  
% 2.20/1.00  ------ Preprocessing Options
% 2.20/1.00  
% 2.20/1.00  --preprocessing_flag                    true
% 2.20/1.00  --time_out_prep_mult                    0.1
% 2.20/1.00  --splitting_mode                        input
% 2.20/1.00  --splitting_grd                         true
% 2.20/1.00  --splitting_cvd                         false
% 2.20/1.00  --splitting_cvd_svl                     false
% 2.20/1.00  --splitting_nvd                         32
% 2.20/1.00  --sub_typing                            true
% 2.20/1.00  --prep_gs_sim                           true
% 2.20/1.00  --prep_unflatten                        true
% 2.20/1.00  --prep_res_sim                          true
% 2.20/1.00  --prep_upred                            true
% 2.20/1.00  --prep_sem_filter                       exhaustive
% 2.20/1.00  --prep_sem_filter_out                   false
% 2.20/1.00  --pred_elim                             true
% 2.20/1.00  --res_sim_input                         true
% 2.20/1.00  --eq_ax_congr_red                       true
% 2.20/1.00  --pure_diseq_elim                       true
% 2.20/1.00  --brand_transform                       false
% 2.20/1.00  --non_eq_to_eq                          false
% 2.20/1.00  --prep_def_merge                        true
% 2.20/1.00  --prep_def_merge_prop_impl              false
% 2.20/1.00  --prep_def_merge_mbd                    true
% 2.20/1.00  --prep_def_merge_tr_red                 false
% 2.20/1.00  --prep_def_merge_tr_cl                  false
% 2.20/1.00  --smt_preprocessing                     true
% 2.20/1.00  --smt_ac_axioms                         fast
% 2.20/1.00  --preprocessed_out                      false
% 2.20/1.00  --preprocessed_stats                    false
% 2.20/1.00  
% 2.20/1.00  ------ Abstraction refinement Options
% 2.20/1.00  
% 2.20/1.00  --abstr_ref                             []
% 2.20/1.00  --abstr_ref_prep                        false
% 2.20/1.00  --abstr_ref_until_sat                   false
% 2.20/1.00  --abstr_ref_sig_restrict                funpre
% 2.20/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.20/1.00  --abstr_ref_under                       []
% 2.20/1.00  
% 2.20/1.00  ------ SAT Options
% 2.20/1.00  
% 2.20/1.00  --sat_mode                              false
% 2.20/1.00  --sat_fm_restart_options                ""
% 2.20/1.00  --sat_gr_def                            false
% 2.20/1.00  --sat_epr_types                         true
% 2.20/1.00  --sat_non_cyclic_types                  false
% 2.20/1.00  --sat_finite_models                     false
% 2.20/1.00  --sat_fm_lemmas                         false
% 2.20/1.00  --sat_fm_prep                           false
% 2.20/1.00  --sat_fm_uc_incr                        true
% 2.20/1.00  --sat_out_model                         small
% 2.20/1.00  --sat_out_clauses                       false
% 2.20/1.00  
% 2.20/1.00  ------ QBF Options
% 2.20/1.00  
% 2.20/1.00  --qbf_mode                              false
% 2.20/1.00  --qbf_elim_univ                         false
% 2.20/1.00  --qbf_dom_inst                          none
% 2.20/1.00  --qbf_dom_pre_inst                      false
% 2.20/1.00  --qbf_sk_in                             false
% 2.20/1.00  --qbf_pred_elim                         true
% 2.20/1.00  --qbf_split                             512
% 2.20/1.00  
% 2.20/1.00  ------ BMC1 Options
% 2.20/1.00  
% 2.20/1.00  --bmc1_incremental                      false
% 2.20/1.00  --bmc1_axioms                           reachable_all
% 2.20/1.00  --bmc1_min_bound                        0
% 2.20/1.00  --bmc1_max_bound                        -1
% 2.20/1.00  --bmc1_max_bound_default                -1
% 2.20/1.00  --bmc1_symbol_reachability              true
% 2.20/1.00  --bmc1_property_lemmas                  false
% 2.20/1.00  --bmc1_k_induction                      false
% 2.20/1.00  --bmc1_non_equiv_states                 false
% 2.20/1.00  --bmc1_deadlock                         false
% 2.20/1.00  --bmc1_ucm                              false
% 2.20/1.00  --bmc1_add_unsat_core                   none
% 2.20/1.00  --bmc1_unsat_core_children              false
% 2.20/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.20/1.00  --bmc1_out_stat                         full
% 2.20/1.00  --bmc1_ground_init                      false
% 2.20/1.00  --bmc1_pre_inst_next_state              false
% 2.20/1.00  --bmc1_pre_inst_state                   false
% 2.20/1.00  --bmc1_pre_inst_reach_state             false
% 2.20/1.00  --bmc1_out_unsat_core                   false
% 2.20/1.00  --bmc1_aig_witness_out                  false
% 2.20/1.00  --bmc1_verbose                          false
% 2.20/1.00  --bmc1_dump_clauses_tptp                false
% 2.20/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.20/1.00  --bmc1_dump_file                        -
% 2.20/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.20/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.20/1.00  --bmc1_ucm_extend_mode                  1
% 2.20/1.00  --bmc1_ucm_init_mode                    2
% 2.20/1.00  --bmc1_ucm_cone_mode                    none
% 2.20/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.20/1.00  --bmc1_ucm_relax_model                  4
% 2.20/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.20/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.20/1.00  --bmc1_ucm_layered_model                none
% 2.20/1.00  --bmc1_ucm_max_lemma_size               10
% 2.20/1.00  
% 2.20/1.00  ------ AIG Options
% 2.20/1.00  
% 2.20/1.00  --aig_mode                              false
% 2.20/1.00  
% 2.20/1.00  ------ Instantiation Options
% 2.20/1.00  
% 2.20/1.00  --instantiation_flag                    true
% 2.20/1.00  --inst_sos_flag                         false
% 2.20/1.00  --inst_sos_phase                        true
% 2.20/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.20/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.20/1.00  --inst_lit_sel_side                     none
% 2.20/1.00  --inst_solver_per_active                1400
% 2.20/1.00  --inst_solver_calls_frac                1.
% 2.20/1.00  --inst_passive_queue_type               priority_queues
% 2.20/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.20/1.00  --inst_passive_queues_freq              [25;2]
% 2.20/1.00  --inst_dismatching                      true
% 2.20/1.00  --inst_eager_unprocessed_to_passive     true
% 2.20/1.00  --inst_prop_sim_given                   true
% 2.20/1.00  --inst_prop_sim_new                     false
% 2.20/1.00  --inst_subs_new                         false
% 2.20/1.00  --inst_eq_res_simp                      false
% 2.20/1.00  --inst_subs_given                       false
% 2.20/1.00  --inst_orphan_elimination               true
% 2.20/1.00  --inst_learning_loop_flag               true
% 2.20/1.00  --inst_learning_start                   3000
% 2.20/1.00  --inst_learning_factor                  2
% 2.20/1.00  --inst_start_prop_sim_after_learn       3
% 2.20/1.00  --inst_sel_renew                        solver
% 2.20/1.00  --inst_lit_activity_flag                true
% 2.20/1.00  --inst_restr_to_given                   false
% 2.20/1.00  --inst_activity_threshold               500
% 2.20/1.00  --inst_out_proof                        true
% 2.20/1.00  
% 2.20/1.00  ------ Resolution Options
% 2.20/1.00  
% 2.20/1.00  --resolution_flag                       false
% 2.20/1.00  --res_lit_sel                           adaptive
% 2.20/1.00  --res_lit_sel_side                      none
% 2.20/1.00  --res_ordering                          kbo
% 2.20/1.00  --res_to_prop_solver                    active
% 2.20/1.00  --res_prop_simpl_new                    false
% 2.20/1.00  --res_prop_simpl_given                  true
% 2.20/1.00  --res_passive_queue_type                priority_queues
% 2.20/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.20/1.00  --res_passive_queues_freq               [15;5]
% 2.20/1.00  --res_forward_subs                      full
% 2.20/1.00  --res_backward_subs                     full
% 2.20/1.00  --res_forward_subs_resolution           true
% 2.20/1.00  --res_backward_subs_resolution          true
% 2.20/1.00  --res_orphan_elimination                true
% 2.20/1.00  --res_time_limit                        2.
% 2.20/1.00  --res_out_proof                         true
% 2.20/1.00  
% 2.20/1.00  ------ Superposition Options
% 2.20/1.00  
% 2.20/1.00  --superposition_flag                    true
% 2.20/1.00  --sup_passive_queue_type                priority_queues
% 2.20/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.20/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.20/1.00  --demod_completeness_check              fast
% 2.20/1.00  --demod_use_ground                      true
% 2.20/1.00  --sup_to_prop_solver                    passive
% 2.20/1.00  --sup_prop_simpl_new                    true
% 2.20/1.00  --sup_prop_simpl_given                  true
% 2.20/1.00  --sup_fun_splitting                     false
% 2.20/1.00  --sup_smt_interval                      50000
% 2.20/1.00  
% 2.20/1.00  ------ Superposition Simplification Setup
% 2.20/1.00  
% 2.20/1.00  --sup_indices_passive                   []
% 2.20/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.20/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.20/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.20/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.20/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.20/1.00  --sup_full_bw                           [BwDemod]
% 2.20/1.00  --sup_immed_triv                        [TrivRules]
% 2.20/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.20/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.20/1.00  --sup_immed_bw_main                     []
% 2.20/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.20/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.20/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.20/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.20/1.00  
% 2.20/1.00  ------ Combination Options
% 2.20/1.00  
% 2.20/1.00  --comb_res_mult                         3
% 2.20/1.00  --comb_sup_mult                         2
% 2.20/1.00  --comb_inst_mult                        10
% 2.20/1.00  
% 2.20/1.00  ------ Debug Options
% 2.20/1.00  
% 2.20/1.00  --dbg_backtrace                         false
% 2.20/1.00  --dbg_dump_prop_clauses                 false
% 2.20/1.00  --dbg_dump_prop_clauses_file            -
% 2.20/1.00  --dbg_out_stat                          false
% 2.20/1.00  
% 2.20/1.00  
% 2.20/1.00  
% 2.20/1.00  
% 2.20/1.00  ------ Proving...
% 2.20/1.00  
% 2.20/1.00  
% 2.20/1.00  % SZS status Theorem for theBenchmark.p
% 2.20/1.00  
% 2.20/1.00   Resolution empty clause
% 2.20/1.00  
% 2.20/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.20/1.00  
% 2.20/1.00  fof(f1,axiom,(
% 2.20/1.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.20/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.20/1.00  
% 2.20/1.00  fof(f36,plain,(
% 2.20/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.20/1.00    inference(nnf_transformation,[],[f1])).
% 2.20/1.00  
% 2.20/1.00  fof(f37,plain,(
% 2.20/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.20/1.00    inference(rectify,[],[f36])).
% 2.20/1.00  
% 2.20/1.00  fof(f38,plain,(
% 2.20/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.20/1.00    introduced(choice_axiom,[])).
% 2.20/1.00  
% 2.20/1.00  fof(f39,plain,(
% 2.20/1.00    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.20/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).
% 2.20/1.00  
% 2.20/1.00  fof(f46,plain,(
% 2.20/1.00    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 2.20/1.00    inference(cnf_transformation,[],[f39])).
% 2.20/1.00  
% 2.20/1.00  fof(f4,axiom,(
% 2.20/1.00    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 2.20/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.20/1.01  
% 2.20/1.01  fof(f18,plain,(
% 2.20/1.01    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 2.20/1.01    inference(ennf_transformation,[],[f4])).
% 2.20/1.01  
% 2.20/1.01  fof(f52,plain,(
% 2.20/1.01    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 2.20/1.01    inference(cnf_transformation,[],[f18])).
% 2.20/1.01  
% 2.20/1.01  fof(f14,conjecture,(
% 2.20/1.01    ! [X0] : ((l1_pre_topc(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v1_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => k11_yellow_6(X0,X1) = k4_yellow_6(X0,X1)))),
% 2.20/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.20/1.01  
% 2.20/1.01  fof(f15,negated_conjecture,(
% 2.20/1.01    ~! [X0] : ((l1_pre_topc(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v1_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => k11_yellow_6(X0,X1) = k4_yellow_6(X0,X1)))),
% 2.20/1.01    inference(negated_conjecture,[],[f14])).
% 2.20/1.01  
% 2.20/1.01  fof(f34,plain,(
% 2.20/1.01    ? [X0] : (? [X1] : (k11_yellow_6(X0,X1) != k4_yellow_6(X0,X1) & (l1_waybel_0(X1,X0) & v1_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.20/1.01    inference(ennf_transformation,[],[f15])).
% 2.20/1.01  
% 2.20/1.01  fof(f35,plain,(
% 2.20/1.01    ? [X0] : (? [X1] : (k11_yellow_6(X0,X1) != k4_yellow_6(X0,X1) & l1_waybel_0(X1,X0) & v1_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.20/1.01    inference(flattening,[],[f34])).
% 2.20/1.01  
% 2.20/1.01  fof(f43,plain,(
% 2.20/1.01    ( ! [X0] : (? [X1] : (k11_yellow_6(X0,X1) != k4_yellow_6(X0,X1) & l1_waybel_0(X1,X0) & v1_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (k11_yellow_6(X0,sK2) != k4_yellow_6(X0,sK2) & l1_waybel_0(sK2,X0) & v1_yellow_6(sK2,X0) & v7_waybel_0(sK2) & v4_orders_2(sK2) & ~v2_struct_0(sK2))) )),
% 2.20/1.01    introduced(choice_axiom,[])).
% 2.20/1.01  
% 2.20/1.01  fof(f42,plain,(
% 2.20/1.01    ? [X0] : (? [X1] : (k11_yellow_6(X0,X1) != k4_yellow_6(X0,X1) & l1_waybel_0(X1,X0) & v1_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (k11_yellow_6(sK1,X1) != k4_yellow_6(sK1,X1) & l1_waybel_0(X1,sK1) & v1_yellow_6(X1,sK1) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v8_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.20/1.01    introduced(choice_axiom,[])).
% 2.20/1.01  
% 2.20/1.01  fof(f44,plain,(
% 2.20/1.01    (k11_yellow_6(sK1,sK2) != k4_yellow_6(sK1,sK2) & l1_waybel_0(sK2,sK1) & v1_yellow_6(sK2,sK1) & v7_waybel_0(sK2) & v4_orders_2(sK2) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v8_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 2.20/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f35,f43,f42])).
% 2.20/1.01  
% 2.20/1.01  fof(f73,plain,(
% 2.20/1.01    v1_yellow_6(sK2,sK1)),
% 2.20/1.01    inference(cnf_transformation,[],[f44])).
% 2.20/1.01  
% 2.20/1.01  fof(f8,axiom,(
% 2.20/1.01    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.20/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.20/1.01  
% 2.20/1.01  fof(f23,plain,(
% 2.20/1.01    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.20/1.01    inference(ennf_transformation,[],[f8])).
% 2.20/1.01  
% 2.20/1.01  fof(f56,plain,(
% 2.20/1.01    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.20/1.01    inference(cnf_transformation,[],[f23])).
% 2.20/1.01  
% 2.20/1.01  fof(f12,axiom,(
% 2.20/1.01    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v1_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => k2_waybel_0(X0,X1,X2) = k4_yellow_6(X0,X1))))),
% 2.20/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.20/1.01  
% 2.20/1.01  fof(f30,plain,(
% 2.20/1.01    ! [X0] : (! [X1] : (! [X2] : (k2_waybel_0(X0,X1,X2) = k4_yellow_6(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~l1_waybel_0(X1,X0) | ~v1_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.20/1.01    inference(ennf_transformation,[],[f12])).
% 2.20/1.01  
% 2.20/1.01  fof(f31,plain,(
% 2.20/1.01    ! [X0] : (! [X1] : (! [X2] : (k2_waybel_0(X0,X1,X2) = k4_yellow_6(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~l1_waybel_0(X1,X0) | ~v1_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.20/1.01    inference(flattening,[],[f30])).
% 2.20/1.01  
% 2.20/1.01  fof(f64,plain,(
% 2.20/1.01    ( ! [X2,X0,X1] : (k2_waybel_0(X0,X1,X2) = k4_yellow_6(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | ~v1_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.20/1.01    inference(cnf_transformation,[],[f31])).
% 2.20/1.01  
% 2.20/1.01  fof(f69,plain,(
% 2.20/1.01    l1_pre_topc(sK1)),
% 2.20/1.01    inference(cnf_transformation,[],[f44])).
% 2.20/1.01  
% 2.20/1.01  fof(f66,plain,(
% 2.20/1.01    ~v2_struct_0(sK1)),
% 2.20/1.01    inference(cnf_transformation,[],[f44])).
% 2.20/1.01  
% 2.20/1.01  fof(f70,plain,(
% 2.20/1.01    ~v2_struct_0(sK2)),
% 2.20/1.01    inference(cnf_transformation,[],[f44])).
% 2.20/1.01  
% 2.20/1.01  fof(f71,plain,(
% 2.20/1.01    v4_orders_2(sK2)),
% 2.20/1.01    inference(cnf_transformation,[],[f44])).
% 2.20/1.01  
% 2.20/1.01  fof(f72,plain,(
% 2.20/1.01    v7_waybel_0(sK2)),
% 2.20/1.01    inference(cnf_transformation,[],[f44])).
% 2.20/1.01  
% 2.20/1.01  fof(f74,plain,(
% 2.20/1.01    l1_waybel_0(sK2,sK1)),
% 2.20/1.01    inference(cnf_transformation,[],[f44])).
% 2.20/1.01  
% 2.20/1.01  fof(f2,axiom,(
% 2.20/1.01    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.20/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.20/1.01  
% 2.20/1.01  fof(f17,plain,(
% 2.20/1.01    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.20/1.01    inference(ennf_transformation,[],[f2])).
% 2.20/1.01  
% 2.20/1.01  fof(f40,plain,(
% 2.20/1.01    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 2.20/1.01    inference(nnf_transformation,[],[f17])).
% 2.20/1.01  
% 2.20/1.01  fof(f50,plain,(
% 2.20/1.01    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 2.20/1.01    inference(cnf_transformation,[],[f40])).
% 2.20/1.01  
% 2.20/1.01  fof(f75,plain,(
% 2.20/1.01    k11_yellow_6(sK1,sK2) != k4_yellow_6(sK1,sK2)),
% 2.20/1.01    inference(cnf_transformation,[],[f44])).
% 2.20/1.01  
% 2.20/1.01  fof(f13,axiom,(
% 2.20/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v1_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1))))),
% 2.20/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.20/1.01  
% 2.20/1.01  fof(f32,plain,(
% 2.20/1.01    ! [X0] : (! [X1] : (r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1)) | (~l1_waybel_0(X1,X0) | ~v1_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.20/1.01    inference(ennf_transformation,[],[f13])).
% 2.20/1.01  
% 2.20/1.01  fof(f33,plain,(
% 2.20/1.01    ! [X0] : (! [X1] : (r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v1_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.20/1.01    inference(flattening,[],[f32])).
% 2.20/1.01  
% 2.20/1.01  fof(f65,plain,(
% 2.20/1.01    ( ! [X0,X1] : (r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v1_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.20/1.01    inference(cnf_transformation,[],[f33])).
% 2.20/1.01  
% 2.20/1.01  fof(f67,plain,(
% 2.20/1.01    v2_pre_topc(sK1)),
% 2.20/1.01    inference(cnf_transformation,[],[f44])).
% 2.20/1.01  
% 2.20/1.01  fof(f9,axiom,(
% 2.20/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X1)) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0)))),
% 2.20/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.20/1.01  
% 2.20/1.01  fof(f24,plain,(
% 2.20/1.01    ! [X0,X1,X2] : (m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.20/1.01    inference(ennf_transformation,[],[f9])).
% 2.20/1.01  
% 2.20/1.01  fof(f25,plain,(
% 2.20/1.01    ! [X0,X1,X2] : (m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.20/1.01    inference(flattening,[],[f24])).
% 2.20/1.01  
% 2.20/1.01  fof(f57,plain,(
% 2.20/1.01    ( ! [X2,X0,X1] : (m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.20/1.01    inference(cnf_transformation,[],[f25])).
% 2.20/1.01  
% 2.20/1.01  fof(f11,axiom,(
% 2.20/1.01    ! [X0] : ((l1_pre_topc(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k11_yellow_6(X0,X1) = X2 <=> r2_hidden(X2,k10_yellow_6(X0,X1))))))),
% 2.20/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.20/1.01  
% 2.20/1.01  fof(f28,plain,(
% 2.20/1.01    ! [X0] : (! [X1] : (! [X2] : ((k11_yellow_6(X0,X1) = X2 <=> r2_hidden(X2,k10_yellow_6(X0,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.20/1.01    inference(ennf_transformation,[],[f11])).
% 2.20/1.01  
% 2.20/1.01  fof(f29,plain,(
% 2.20/1.01    ! [X0] : (! [X1] : (! [X2] : ((k11_yellow_6(X0,X1) = X2 <=> r2_hidden(X2,k10_yellow_6(X0,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.20/1.01    inference(flattening,[],[f28])).
% 2.20/1.01  
% 2.20/1.01  fof(f41,plain,(
% 2.20/1.01    ! [X0] : (! [X1] : (! [X2] : (((k11_yellow_6(X0,X1) = X2 | ~r2_hidden(X2,k10_yellow_6(X0,X1))) & (r2_hidden(X2,k10_yellow_6(X0,X1)) | k11_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.20/1.01    inference(nnf_transformation,[],[f29])).
% 2.20/1.01  
% 2.20/1.01  fof(f63,plain,(
% 2.20/1.01    ( ! [X2,X0,X1] : (k11_yellow_6(X0,X1) = X2 | ~r2_hidden(X2,k10_yellow_6(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.20/1.01    inference(cnf_transformation,[],[f41])).
% 2.20/1.01  
% 2.20/1.01  fof(f68,plain,(
% 2.20/1.01    v8_pre_topc(sK1)),
% 2.20/1.01    inference(cnf_transformation,[],[f44])).
% 2.20/1.01  
% 2.20/1.01  fof(f10,axiom,(
% 2.20/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (l1_waybel_0(X1,X0) => ((v1_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)))))),
% 2.20/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.20/1.01  
% 2.20/1.01  fof(f26,plain,(
% 2.20/1.01    ! [X0] : (! [X1] : (((v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | (~v1_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | ~l1_waybel_0(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.20/1.01    inference(ennf_transformation,[],[f10])).
% 2.20/1.01  
% 2.20/1.01  fof(f27,plain,(
% 2.20/1.01    ! [X0] : (! [X1] : ((v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.20/1.01    inference(flattening,[],[f26])).
% 2.20/1.01  
% 2.20/1.01  fof(f61,plain,(
% 2.20/1.01    ( ! [X0,X1] : (v3_yellow_6(X1,X0) | ~v1_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.20/1.01    inference(cnf_transformation,[],[f27])).
% 2.20/1.01  
% 2.20/1.01  cnf(c_0,plain,
% 2.20/1.01      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 2.20/1.01      inference(cnf_transformation,[],[f46]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_1533,plain,
% 2.20/1.01      ( r2_hidden(sK0(X0),X0) = iProver_top | v1_xboole_0(X0) = iProver_top ),
% 2.20/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_7,plain,
% 2.20/1.01      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 2.20/1.01      inference(cnf_transformation,[],[f52]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_1527,plain,
% 2.20/1.01      ( m1_subset_1(X0,X1) = iProver_top | r2_hidden(X0,X1) != iProver_top ),
% 2.20/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_2001,plain,
% 2.20/1.01      ( m1_subset_1(sK0(X0),X0) = iProver_top | v1_xboole_0(X0) = iProver_top ),
% 2.20/1.01      inference(superposition,[status(thm)],[c_1533,c_1527]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_23,negated_conjecture,
% 2.20/1.01      ( v1_yellow_6(sK2,sK1) ),
% 2.20/1.01      inference(cnf_transformation,[],[f73]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_11,plain,
% 2.20/1.01      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.20/1.01      inference(cnf_transformation,[],[f56]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_19,plain,
% 2.20/1.01      ( ~ v1_yellow_6(X0,X1)
% 2.20/1.01      | ~ l1_waybel_0(X0,X1)
% 2.20/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.20/1.01      | ~ v4_orders_2(X0)
% 2.20/1.01      | ~ v7_waybel_0(X0)
% 2.20/1.01      | v2_struct_0(X1)
% 2.20/1.01      | v2_struct_0(X0)
% 2.20/1.01      | ~ l1_struct_0(X1)
% 2.20/1.01      | k2_waybel_0(X1,X0,X2) = k4_yellow_6(X1,X0) ),
% 2.20/1.01      inference(cnf_transformation,[],[f64]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_323,plain,
% 2.20/1.01      ( ~ v1_yellow_6(X0,X1)
% 2.20/1.01      | ~ l1_waybel_0(X0,X1)
% 2.20/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.20/1.01      | ~ v4_orders_2(X0)
% 2.20/1.01      | ~ v7_waybel_0(X0)
% 2.20/1.01      | v2_struct_0(X0)
% 2.20/1.01      | v2_struct_0(X1)
% 2.20/1.01      | ~ l1_pre_topc(X3)
% 2.20/1.01      | X1 != X3
% 2.20/1.01      | k2_waybel_0(X1,X0,X2) = k4_yellow_6(X1,X0) ),
% 2.20/1.01      inference(resolution_lifted,[status(thm)],[c_11,c_19]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_324,plain,
% 2.20/1.01      ( ~ v1_yellow_6(X0,X1)
% 2.20/1.01      | ~ l1_waybel_0(X0,X1)
% 2.20/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.20/1.01      | ~ v4_orders_2(X0)
% 2.20/1.01      | ~ v7_waybel_0(X0)
% 2.20/1.01      | v2_struct_0(X0)
% 2.20/1.01      | v2_struct_0(X1)
% 2.20/1.01      | ~ l1_pre_topc(X1)
% 2.20/1.01      | k2_waybel_0(X1,X0,X2) = k4_yellow_6(X1,X0) ),
% 2.20/1.01      inference(unflattening,[status(thm)],[c_323]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_27,negated_conjecture,
% 2.20/1.01      ( l1_pre_topc(sK1) ),
% 2.20/1.01      inference(cnf_transformation,[],[f69]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_579,plain,
% 2.20/1.01      ( ~ v1_yellow_6(X0,X1)
% 2.20/1.01      | ~ l1_waybel_0(X0,X1)
% 2.20/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.20/1.01      | ~ v4_orders_2(X0)
% 2.20/1.01      | ~ v7_waybel_0(X0)
% 2.20/1.01      | v2_struct_0(X0)
% 2.20/1.01      | v2_struct_0(X1)
% 2.20/1.01      | k2_waybel_0(X1,X0,X2) = k4_yellow_6(X1,X0)
% 2.20/1.01      | sK1 != X1 ),
% 2.20/1.01      inference(resolution_lifted,[status(thm)],[c_324,c_27]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_580,plain,
% 2.20/1.01      ( ~ v1_yellow_6(X0,sK1)
% 2.20/1.01      | ~ l1_waybel_0(X0,sK1)
% 2.20/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.20/1.01      | ~ v4_orders_2(X0)
% 2.20/1.01      | ~ v7_waybel_0(X0)
% 2.20/1.01      | v2_struct_0(X0)
% 2.20/1.01      | v2_struct_0(sK1)
% 2.20/1.01      | k2_waybel_0(sK1,X0,X1) = k4_yellow_6(sK1,X0) ),
% 2.20/1.01      inference(unflattening,[status(thm)],[c_579]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_30,negated_conjecture,
% 2.20/1.01      ( ~ v2_struct_0(sK1) ),
% 2.20/1.01      inference(cnf_transformation,[],[f66]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_584,plain,
% 2.20/1.01      ( v2_struct_0(X0)
% 2.20/1.01      | ~ v7_waybel_0(X0)
% 2.20/1.01      | ~ v4_orders_2(X0)
% 2.20/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.20/1.01      | ~ l1_waybel_0(X0,sK1)
% 2.20/1.01      | ~ v1_yellow_6(X0,sK1)
% 2.20/1.01      | k2_waybel_0(sK1,X0,X1) = k4_yellow_6(sK1,X0) ),
% 2.20/1.01      inference(global_propositional_subsumption,[status(thm)],[c_580,c_30]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_585,plain,
% 2.20/1.01      ( ~ v1_yellow_6(X0,sK1)
% 2.20/1.01      | ~ l1_waybel_0(X0,sK1)
% 2.20/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.20/1.01      | ~ v4_orders_2(X0)
% 2.20/1.01      | ~ v7_waybel_0(X0)
% 2.20/1.01      | v2_struct_0(X0)
% 2.20/1.01      | k2_waybel_0(sK1,X0,X1) = k4_yellow_6(sK1,X0) ),
% 2.20/1.01      inference(renaming,[status(thm)],[c_584]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_623,plain,
% 2.20/1.01      ( ~ l1_waybel_0(X0,sK1)
% 2.20/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.20/1.01      | ~ v4_orders_2(X0)
% 2.20/1.01      | ~ v7_waybel_0(X0)
% 2.20/1.01      | v2_struct_0(X0)
% 2.20/1.01      | k2_waybel_0(sK1,X0,X1) = k4_yellow_6(sK1,X0)
% 2.20/1.01      | sK2 != X0
% 2.20/1.01      | sK1 != sK1 ),
% 2.20/1.01      inference(resolution_lifted,[status(thm)],[c_23,c_585]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_624,plain,
% 2.20/1.01      ( ~ l1_waybel_0(sK2,sK1)
% 2.20/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.20/1.01      | ~ v4_orders_2(sK2)
% 2.20/1.01      | ~ v7_waybel_0(sK2)
% 2.20/1.01      | v2_struct_0(sK2)
% 2.20/1.01      | k2_waybel_0(sK1,sK2,X0) = k4_yellow_6(sK1,sK2) ),
% 2.20/1.01      inference(unflattening,[status(thm)],[c_623]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_26,negated_conjecture,
% 2.20/1.01      ( ~ v2_struct_0(sK2) ),
% 2.20/1.01      inference(cnf_transformation,[],[f70]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_25,negated_conjecture,
% 2.20/1.01      ( v4_orders_2(sK2) ),
% 2.20/1.01      inference(cnf_transformation,[],[f71]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_24,negated_conjecture,
% 2.20/1.01      ( v7_waybel_0(sK2) ),
% 2.20/1.01      inference(cnf_transformation,[],[f72]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_22,negated_conjecture,
% 2.20/1.01      ( l1_waybel_0(sK2,sK1) ),
% 2.20/1.01      inference(cnf_transformation,[],[f74]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_628,plain,
% 2.20/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.20/1.01      | k2_waybel_0(sK1,sK2,X0) = k4_yellow_6(sK1,sK2) ),
% 2.20/1.01      inference(global_propositional_subsumption,
% 2.20/1.01                [status(thm)],
% 2.20/1.01                [c_624,c_26,c_25,c_24,c_22]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_1524,plain,
% 2.20/1.01      ( k2_waybel_0(sK1,sK2,X0) = k4_yellow_6(sK1,sK2)
% 2.20/1.01      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
% 2.20/1.01      inference(predicate_to_equality,[status(thm)],[c_628]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_2551,plain,
% 2.20/1.01      ( k2_waybel_0(sK1,sK2,sK0(u1_struct_0(sK2))) = k4_yellow_6(sK1,sK2)
% 2.20/1.01      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 2.20/1.01      inference(superposition,[status(thm)],[c_2001,c_1524]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_2,plain,
% 2.20/1.01      ( m1_subset_1(X0,X1) | ~ v1_xboole_0(X1) | ~ v1_xboole_0(X0) ),
% 2.20/1.01      inference(cnf_transformation,[],[f50]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_1531,plain,
% 2.20/1.01      ( m1_subset_1(X0,X1) = iProver_top
% 2.20/1.01      | v1_xboole_0(X1) != iProver_top
% 2.20/1.01      | v1_xboole_0(X0) != iProver_top ),
% 2.20/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_2455,plain,
% 2.20/1.01      ( k2_waybel_0(sK1,sK2,X0) = k4_yellow_6(sK1,sK2)
% 2.20/1.01      | v1_xboole_0(X0) != iProver_top
% 2.20/1.01      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 2.20/1.01      inference(superposition,[status(thm)],[c_1531,c_1524]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_35,plain,
% 2.20/1.01      ( v2_struct_0(sK2) != iProver_top ),
% 2.20/1.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_36,plain,
% 2.20/1.01      ( v4_orders_2(sK2) = iProver_top ),
% 2.20/1.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_37,plain,
% 2.20/1.01      ( v7_waybel_0(sK2) = iProver_top ),
% 2.20/1.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_39,plain,
% 2.20/1.01      ( l1_waybel_0(sK2,sK1) = iProver_top ),
% 2.20/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_21,negated_conjecture,
% 2.20/1.01      ( k11_yellow_6(sK1,sK2) != k4_yellow_6(sK1,sK2) ),
% 2.20/1.01      inference(cnf_transformation,[],[f75]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_20,plain,
% 2.20/1.01      ( ~ v1_yellow_6(X0,X1)
% 2.20/1.01      | ~ l1_waybel_0(X0,X1)
% 2.20/1.01      | r2_hidden(k4_yellow_6(X1,X0),k10_yellow_6(X1,X0))
% 2.20/1.01      | ~ v2_pre_topc(X1)
% 2.20/1.01      | ~ v4_orders_2(X0)
% 2.20/1.01      | ~ v7_waybel_0(X0)
% 2.20/1.01      | v2_struct_0(X1)
% 2.20/1.01      | v2_struct_0(X0)
% 2.20/1.01      | ~ l1_pre_topc(X1) ),
% 2.20/1.01      inference(cnf_transformation,[],[f65]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_29,negated_conjecture,
% 2.20/1.01      ( v2_pre_topc(sK1) ),
% 2.20/1.01      inference(cnf_transformation,[],[f67]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_483,plain,
% 2.20/1.01      ( ~ v1_yellow_6(X0,X1)
% 2.20/1.01      | ~ l1_waybel_0(X0,X1)
% 2.20/1.01      | r2_hidden(k4_yellow_6(X1,X0),k10_yellow_6(X1,X0))
% 2.20/1.01      | ~ v4_orders_2(X0)
% 2.20/1.01      | ~ v7_waybel_0(X0)
% 2.20/1.01      | v2_struct_0(X0)
% 2.20/1.01      | v2_struct_0(X1)
% 2.20/1.01      | ~ l1_pre_topc(X1)
% 2.20/1.01      | sK1 != X1 ),
% 2.20/1.01      inference(resolution_lifted,[status(thm)],[c_20,c_29]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_484,plain,
% 2.20/1.01      ( ~ v1_yellow_6(X0,sK1)
% 2.20/1.01      | ~ l1_waybel_0(X0,sK1)
% 2.20/1.01      | r2_hidden(k4_yellow_6(sK1,X0),k10_yellow_6(sK1,X0))
% 2.20/1.01      | ~ v4_orders_2(X0)
% 2.20/1.01      | ~ v7_waybel_0(X0)
% 2.20/1.01      | v2_struct_0(X0)
% 2.20/1.01      | v2_struct_0(sK1)
% 2.20/1.01      | ~ l1_pre_topc(sK1) ),
% 2.20/1.01      inference(unflattening,[status(thm)],[c_483]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_488,plain,
% 2.20/1.01      ( ~ v1_yellow_6(X0,sK1)
% 2.20/1.01      | ~ l1_waybel_0(X0,sK1)
% 2.20/1.01      | r2_hidden(k4_yellow_6(sK1,X0),k10_yellow_6(sK1,X0))
% 2.20/1.01      | ~ v4_orders_2(X0)
% 2.20/1.01      | ~ v7_waybel_0(X0)
% 2.20/1.01      | v2_struct_0(X0) ),
% 2.20/1.01      inference(global_propositional_subsumption,
% 2.20/1.01                [status(thm)],
% 2.20/1.01                [c_484,c_30,c_27]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_652,plain,
% 2.20/1.01      ( ~ l1_waybel_0(X0,sK1)
% 2.20/1.01      | r2_hidden(k4_yellow_6(sK1,X0),k10_yellow_6(sK1,X0))
% 2.20/1.01      | ~ v4_orders_2(X0)
% 2.20/1.01      | ~ v7_waybel_0(X0)
% 2.20/1.01      | v2_struct_0(X0)
% 2.20/1.01      | sK2 != X0
% 2.20/1.01      | sK1 != sK1 ),
% 2.20/1.01      inference(resolution_lifted,[status(thm)],[c_23,c_488]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_653,plain,
% 2.20/1.01      ( ~ l1_waybel_0(sK2,sK1)
% 2.20/1.01      | r2_hidden(k4_yellow_6(sK1,sK2),k10_yellow_6(sK1,sK2))
% 2.20/1.01      | ~ v4_orders_2(sK2)
% 2.20/1.01      | ~ v7_waybel_0(sK2)
% 2.20/1.01      | v2_struct_0(sK2) ),
% 2.20/1.01      inference(unflattening,[status(thm)],[c_652]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_654,plain,
% 2.20/1.01      ( l1_waybel_0(sK2,sK1) != iProver_top
% 2.20/1.01      | r2_hidden(k4_yellow_6(sK1,sK2),k10_yellow_6(sK1,sK2)) = iProver_top
% 2.20/1.01      | v4_orders_2(sK2) != iProver_top
% 2.20/1.01      | v7_waybel_0(sK2) != iProver_top
% 2.20/1.01      | v2_struct_0(sK2) = iProver_top ),
% 2.20/1.01      inference(predicate_to_equality,[status(thm)],[c_653]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_12,plain,
% 2.20/1.01      ( ~ l1_waybel_0(X0,X1)
% 2.20/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.20/1.01      | m1_subset_1(k2_waybel_0(X1,X0,X2),u1_struct_0(X1))
% 2.20/1.01      | v2_struct_0(X1)
% 2.20/1.01      | v2_struct_0(X0)
% 2.20/1.01      | ~ l1_struct_0(X1) ),
% 2.20/1.01      inference(cnf_transformation,[],[f57]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_356,plain,
% 2.20/1.01      ( ~ l1_waybel_0(X0,X1)
% 2.20/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.20/1.01      | m1_subset_1(k2_waybel_0(X1,X0,X2),u1_struct_0(X1))
% 2.20/1.01      | v2_struct_0(X0)
% 2.20/1.01      | v2_struct_0(X1)
% 2.20/1.01      | ~ l1_pre_topc(X3)
% 2.20/1.01      | X1 != X3 ),
% 2.20/1.01      inference(resolution_lifted,[status(thm)],[c_11,c_12]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_357,plain,
% 2.20/1.01      ( ~ l1_waybel_0(X0,X1)
% 2.20/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.20/1.01      | m1_subset_1(k2_waybel_0(X1,X0,X2),u1_struct_0(X1))
% 2.20/1.01      | v2_struct_0(X0)
% 2.20/1.01      | v2_struct_0(X1)
% 2.20/1.01      | ~ l1_pre_topc(X1) ),
% 2.20/1.01      inference(unflattening,[status(thm)],[c_356]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_557,plain,
% 2.20/1.01      ( ~ l1_waybel_0(X0,X1)
% 2.20/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.20/1.01      | m1_subset_1(k2_waybel_0(X1,X0,X2),u1_struct_0(X1))
% 2.20/1.01      | v2_struct_0(X0)
% 2.20/1.01      | v2_struct_0(X1)
% 2.20/1.01      | sK1 != X1 ),
% 2.20/1.01      inference(resolution_lifted,[status(thm)],[c_357,c_27]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_558,plain,
% 2.20/1.01      ( ~ l1_waybel_0(X0,sK1)
% 2.20/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.20/1.01      | m1_subset_1(k2_waybel_0(sK1,X0,X1),u1_struct_0(sK1))
% 2.20/1.01      | v2_struct_0(X0)
% 2.20/1.01      | v2_struct_0(sK1) ),
% 2.20/1.01      inference(unflattening,[status(thm)],[c_557]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_562,plain,
% 2.20/1.01      ( v2_struct_0(X0)
% 2.20/1.01      | m1_subset_1(k2_waybel_0(sK1,X0,X1),u1_struct_0(sK1))
% 2.20/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.20/1.01      | ~ l1_waybel_0(X0,sK1) ),
% 2.20/1.01      inference(global_propositional_subsumption,[status(thm)],[c_558,c_30]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_563,plain,
% 2.20/1.01      ( ~ l1_waybel_0(X0,sK1)
% 2.20/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.20/1.01      | m1_subset_1(k2_waybel_0(sK1,X0,X1),u1_struct_0(sK1))
% 2.20/1.01      | v2_struct_0(X0) ),
% 2.20/1.01      inference(renaming,[status(thm)],[c_562]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_712,plain,
% 2.20/1.01      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.20/1.01      | m1_subset_1(k2_waybel_0(sK1,X1,X0),u1_struct_0(sK1))
% 2.20/1.01      | v2_struct_0(X1)
% 2.20/1.01      | sK2 != X1
% 2.20/1.01      | sK1 != sK1 ),
% 2.20/1.01      inference(resolution_lifted,[status(thm)],[c_22,c_563]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_713,plain,
% 2.20/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.20/1.01      | m1_subset_1(k2_waybel_0(sK1,sK2,X0),u1_struct_0(sK1))
% 2.20/1.01      | v2_struct_0(sK2) ),
% 2.20/1.01      inference(unflattening,[status(thm)],[c_712]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_714,plain,
% 2.20/1.01      ( m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 2.20/1.01      | m1_subset_1(k2_waybel_0(sK1,sK2,X0),u1_struct_0(sK1)) = iProver_top
% 2.20/1.01      | v2_struct_0(sK2) = iProver_top ),
% 2.20/1.01      inference(predicate_to_equality,[status(thm)],[c_713]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_1652,plain,
% 2.20/1.01      ( m1_subset_1(X0,u1_struct_0(sK2))
% 2.20/1.01      | ~ v1_xboole_0(X0)
% 2.20/1.01      | ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 2.20/1.01      inference(instantiation,[status(thm)],[c_2]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_1653,plain,
% 2.20/1.01      ( m1_subset_1(X0,u1_struct_0(sK2)) = iProver_top
% 2.20/1.01      | v1_xboole_0(X0) != iProver_top
% 2.20/1.01      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 2.20/1.01      inference(predicate_to_equality,[status(thm)],[c_1652]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_1266,plain,( X0 = X0 ),theory(equality) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_1771,plain,
% 2.20/1.01      ( k4_yellow_6(sK1,sK2) = k4_yellow_6(sK1,sK2) ),
% 2.20/1.01      inference(instantiation,[status(thm)],[c_1266]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_17,plain,
% 2.20/1.01      ( ~ v3_yellow_6(X0,X1)
% 2.20/1.01      | ~ l1_waybel_0(X0,X1)
% 2.20/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.20/1.01      | ~ r2_hidden(X2,k10_yellow_6(X1,X0))
% 2.20/1.01      | ~ v8_pre_topc(X1)
% 2.20/1.01      | ~ v2_pre_topc(X1)
% 2.20/1.01      | ~ v4_orders_2(X0)
% 2.20/1.01      | ~ v7_waybel_0(X0)
% 2.20/1.01      | v2_struct_0(X1)
% 2.20/1.01      | v2_struct_0(X0)
% 2.20/1.01      | ~ l1_pre_topc(X1)
% 2.20/1.01      | k11_yellow_6(X1,X0) = X2 ),
% 2.20/1.01      inference(cnf_transformation,[],[f63]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_28,negated_conjecture,
% 2.20/1.01      ( v8_pre_topc(sK1) ),
% 2.20/1.01      inference(cnf_transformation,[],[f68]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_430,plain,
% 2.20/1.01      ( ~ v3_yellow_6(X0,X1)
% 2.20/1.01      | ~ l1_waybel_0(X0,X1)
% 2.20/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.20/1.01      | ~ r2_hidden(X2,k10_yellow_6(X1,X0))
% 2.20/1.01      | ~ v2_pre_topc(X1)
% 2.20/1.01      | ~ v4_orders_2(X0)
% 2.20/1.01      | ~ v7_waybel_0(X0)
% 2.20/1.01      | v2_struct_0(X0)
% 2.20/1.01      | v2_struct_0(X1)
% 2.20/1.01      | ~ l1_pre_topc(X1)
% 2.20/1.01      | k11_yellow_6(X1,X0) = X2
% 2.20/1.01      | sK1 != X1 ),
% 2.20/1.01      inference(resolution_lifted,[status(thm)],[c_17,c_28]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_431,plain,
% 2.20/1.01      ( ~ v3_yellow_6(X0,sK1)
% 2.20/1.01      | ~ l1_waybel_0(X0,sK1)
% 2.20/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.20/1.01      | ~ r2_hidden(X1,k10_yellow_6(sK1,X0))
% 2.20/1.01      | ~ v2_pre_topc(sK1)
% 2.20/1.01      | ~ v4_orders_2(X0)
% 2.20/1.01      | ~ v7_waybel_0(X0)
% 2.20/1.01      | v2_struct_0(X0)
% 2.20/1.01      | v2_struct_0(sK1)
% 2.20/1.01      | ~ l1_pre_topc(sK1)
% 2.20/1.01      | k11_yellow_6(sK1,X0) = X1 ),
% 2.20/1.01      inference(unflattening,[status(thm)],[c_430]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_435,plain,
% 2.20/1.01      ( ~ r2_hidden(X1,k10_yellow_6(sK1,X0))
% 2.20/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.20/1.01      | ~ l1_waybel_0(X0,sK1)
% 2.20/1.01      | ~ v3_yellow_6(X0,sK1)
% 2.20/1.01      | ~ v4_orders_2(X0)
% 2.20/1.01      | ~ v7_waybel_0(X0)
% 2.20/1.01      | v2_struct_0(X0)
% 2.20/1.01      | k11_yellow_6(sK1,X0) = X1 ),
% 2.20/1.01      inference(global_propositional_subsumption,
% 2.20/1.01                [status(thm)],
% 2.20/1.01                [c_431,c_30,c_29,c_27]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_436,plain,
% 2.20/1.01      ( ~ v3_yellow_6(X0,sK1)
% 2.20/1.01      | ~ l1_waybel_0(X0,sK1)
% 2.20/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.20/1.01      | ~ r2_hidden(X1,k10_yellow_6(sK1,X0))
% 2.20/1.01      | ~ v4_orders_2(X0)
% 2.20/1.01      | ~ v7_waybel_0(X0)
% 2.20/1.01      | v2_struct_0(X0)
% 2.20/1.01      | k11_yellow_6(sK1,X0) = X1 ),
% 2.20/1.01      inference(renaming,[status(thm)],[c_435]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_13,plain,
% 2.20/1.01      ( ~ v1_yellow_6(X0,X1)
% 2.20/1.01      | v3_yellow_6(X0,X1)
% 2.20/1.01      | ~ l1_waybel_0(X0,X1)
% 2.20/1.01      | ~ v2_pre_topc(X1)
% 2.20/1.01      | ~ v4_orders_2(X0)
% 2.20/1.01      | ~ v7_waybel_0(X0)
% 2.20/1.01      | v2_struct_0(X1)
% 2.20/1.01      | v2_struct_0(X0)
% 2.20/1.01      | ~ l1_pre_topc(X1) ),
% 2.20/1.01      inference(cnf_transformation,[],[f61]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_513,plain,
% 2.20/1.01      ( ~ v1_yellow_6(X0,X1)
% 2.20/1.01      | v3_yellow_6(X0,X1)
% 2.20/1.01      | ~ l1_waybel_0(X0,X1)
% 2.20/1.01      | ~ v4_orders_2(X0)
% 2.20/1.01      | ~ v7_waybel_0(X0)
% 2.20/1.01      | v2_struct_0(X0)
% 2.20/1.01      | v2_struct_0(X1)
% 2.20/1.01      | ~ l1_pre_topc(X1)
% 2.20/1.01      | sK1 != X1 ),
% 2.20/1.01      inference(resolution_lifted,[status(thm)],[c_13,c_29]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_514,plain,
% 2.20/1.01      ( ~ v1_yellow_6(X0,sK1)
% 2.20/1.01      | v3_yellow_6(X0,sK1)
% 2.20/1.01      | ~ l1_waybel_0(X0,sK1)
% 2.20/1.01      | ~ v4_orders_2(X0)
% 2.20/1.01      | ~ v7_waybel_0(X0)
% 2.20/1.01      | v2_struct_0(X0)
% 2.20/1.01      | v2_struct_0(sK1)
% 2.20/1.01      | ~ l1_pre_topc(sK1) ),
% 2.20/1.01      inference(unflattening,[status(thm)],[c_513]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_518,plain,
% 2.20/1.01      ( ~ v1_yellow_6(X0,sK1)
% 2.20/1.01      | v3_yellow_6(X0,sK1)
% 2.20/1.01      | ~ l1_waybel_0(X0,sK1)
% 2.20/1.01      | ~ v4_orders_2(X0)
% 2.20/1.01      | ~ v7_waybel_0(X0)
% 2.20/1.01      | v2_struct_0(X0) ),
% 2.20/1.01      inference(global_propositional_subsumption,
% 2.20/1.01                [status(thm)],
% 2.20/1.01                [c_514,c_30,c_27]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_641,plain,
% 2.20/1.01      ( v3_yellow_6(X0,sK1)
% 2.20/1.01      | ~ l1_waybel_0(X0,sK1)
% 2.20/1.01      | ~ v4_orders_2(X0)
% 2.20/1.01      | ~ v7_waybel_0(X0)
% 2.20/1.01      | v2_struct_0(X0)
% 2.20/1.01      | sK2 != X0
% 2.20/1.01      | sK1 != sK1 ),
% 2.20/1.01      inference(resolution_lifted,[status(thm)],[c_23,c_518]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_642,plain,
% 2.20/1.01      ( v3_yellow_6(sK2,sK1)
% 2.20/1.01      | ~ l1_waybel_0(sK2,sK1)
% 2.20/1.01      | ~ v4_orders_2(sK2)
% 2.20/1.01      | ~ v7_waybel_0(sK2)
% 2.20/1.01      | v2_struct_0(sK2) ),
% 2.20/1.01      inference(unflattening,[status(thm)],[c_641]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_644,plain,
% 2.20/1.01      ( v3_yellow_6(sK2,sK1) ),
% 2.20/1.01      inference(global_propositional_subsumption,
% 2.20/1.01                [status(thm)],
% 2.20/1.01                [c_642,c_26,c_25,c_24,c_22]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_670,plain,
% 2.20/1.01      ( ~ l1_waybel_0(X0,sK1)
% 2.20/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.20/1.01      | ~ r2_hidden(X1,k10_yellow_6(sK1,X0))
% 2.20/1.01      | ~ v4_orders_2(X0)
% 2.20/1.01      | ~ v7_waybel_0(X0)
% 2.20/1.01      | v2_struct_0(X0)
% 2.20/1.01      | k11_yellow_6(sK1,X0) = X1
% 2.20/1.01      | sK2 != X0
% 2.20/1.01      | sK1 != sK1 ),
% 2.20/1.01      inference(resolution_lifted,[status(thm)],[c_436,c_644]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_671,plain,
% 2.20/1.01      ( ~ l1_waybel_0(sK2,sK1)
% 2.20/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.20/1.01      | ~ r2_hidden(X0,k10_yellow_6(sK1,sK2))
% 2.20/1.01      | ~ v4_orders_2(sK2)
% 2.20/1.01      | ~ v7_waybel_0(sK2)
% 2.20/1.01      | v2_struct_0(sK2)
% 2.20/1.01      | k11_yellow_6(sK1,sK2) = X0 ),
% 2.20/1.01      inference(unflattening,[status(thm)],[c_670]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_675,plain,
% 2.20/1.01      ( ~ r2_hidden(X0,k10_yellow_6(sK1,sK2))
% 2.20/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.20/1.01      | k11_yellow_6(sK1,sK2) = X0 ),
% 2.20/1.01      inference(global_propositional_subsumption,
% 2.20/1.01                [status(thm)],
% 2.20/1.01                [c_671,c_26,c_25,c_24,c_22]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_676,plain,
% 2.20/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.20/1.01      | ~ r2_hidden(X0,k10_yellow_6(sK1,sK2))
% 2.20/1.01      | k11_yellow_6(sK1,sK2) = X0 ),
% 2.20/1.01      inference(renaming,[status(thm)],[c_675]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_1790,plain,
% 2.20/1.01      ( ~ m1_subset_1(k2_waybel_0(sK1,sK2,X0),u1_struct_0(sK1))
% 2.20/1.01      | ~ r2_hidden(k2_waybel_0(sK1,sK2,X0),k10_yellow_6(sK1,sK2))
% 2.20/1.01      | k11_yellow_6(sK1,sK2) = k2_waybel_0(sK1,sK2,X0) ),
% 2.20/1.01      inference(instantiation,[status(thm)],[c_676]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_1791,plain,
% 2.20/1.01      ( k11_yellow_6(sK1,sK2) = k2_waybel_0(sK1,sK2,X0)
% 2.20/1.01      | m1_subset_1(k2_waybel_0(sK1,sK2,X0),u1_struct_0(sK1)) != iProver_top
% 2.20/1.01      | r2_hidden(k2_waybel_0(sK1,sK2,X0),k10_yellow_6(sK1,sK2)) != iProver_top ),
% 2.20/1.01      inference(predicate_to_equality,[status(thm)],[c_1790]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_1927,plain,
% 2.20/1.01      ( k10_yellow_6(sK1,sK2) = k10_yellow_6(sK1,sK2) ),
% 2.20/1.01      inference(instantiation,[status(thm)],[c_1266]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_1267,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_1628,plain,
% 2.20/1.01      ( k4_yellow_6(sK1,sK2) != X0
% 2.20/1.01      | k11_yellow_6(sK1,sK2) != X0
% 2.20/1.01      | k11_yellow_6(sK1,sK2) = k4_yellow_6(sK1,sK2) ),
% 2.20/1.01      inference(instantiation,[status(thm)],[c_1267]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_1949,plain,
% 2.20/1.01      ( k4_yellow_6(sK1,sK2) != k2_waybel_0(sK1,sK2,X0)
% 2.20/1.01      | k11_yellow_6(sK1,sK2) != k2_waybel_0(sK1,sK2,X0)
% 2.20/1.01      | k11_yellow_6(sK1,sK2) = k4_yellow_6(sK1,sK2) ),
% 2.20/1.01      inference(instantiation,[status(thm)],[c_1628]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_1268,plain,
% 2.20/1.01      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.20/1.01      theory(equality) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_1630,plain,
% 2.20/1.01      ( r2_hidden(X0,X1)
% 2.20/1.01      | ~ r2_hidden(k4_yellow_6(sK1,sK2),k10_yellow_6(sK1,sK2))
% 2.20/1.01      | X0 != k4_yellow_6(sK1,sK2)
% 2.20/1.01      | X1 != k10_yellow_6(sK1,sK2) ),
% 2.20/1.01      inference(instantiation,[status(thm)],[c_1268]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_1785,plain,
% 2.20/1.01      ( r2_hidden(k2_waybel_0(sK1,sK2,X0),X1)
% 2.20/1.01      | ~ r2_hidden(k4_yellow_6(sK1,sK2),k10_yellow_6(sK1,sK2))
% 2.20/1.01      | X1 != k10_yellow_6(sK1,sK2)
% 2.20/1.01      | k2_waybel_0(sK1,sK2,X0) != k4_yellow_6(sK1,sK2) ),
% 2.20/1.01      inference(instantiation,[status(thm)],[c_1630]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_2192,plain,
% 2.20/1.01      ( r2_hidden(k2_waybel_0(sK1,sK2,X0),k10_yellow_6(sK1,sK2))
% 2.20/1.01      | ~ r2_hidden(k4_yellow_6(sK1,sK2),k10_yellow_6(sK1,sK2))
% 2.20/1.01      | k2_waybel_0(sK1,sK2,X0) != k4_yellow_6(sK1,sK2)
% 2.20/1.01      | k10_yellow_6(sK1,sK2) != k10_yellow_6(sK1,sK2) ),
% 2.20/1.01      inference(instantiation,[status(thm)],[c_1785]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_2193,plain,
% 2.20/1.01      ( k2_waybel_0(sK1,sK2,X0) != k4_yellow_6(sK1,sK2)
% 2.20/1.01      | k10_yellow_6(sK1,sK2) != k10_yellow_6(sK1,sK2)
% 2.20/1.01      | r2_hidden(k2_waybel_0(sK1,sK2,X0),k10_yellow_6(sK1,sK2)) = iProver_top
% 2.20/1.01      | r2_hidden(k4_yellow_6(sK1,sK2),k10_yellow_6(sK1,sK2)) != iProver_top ),
% 2.20/1.01      inference(predicate_to_equality,[status(thm)],[c_2192]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_1995,plain,
% 2.20/1.01      ( k2_waybel_0(sK1,sK2,X0) != X1
% 2.20/1.01      | k4_yellow_6(sK1,sK2) != X1
% 2.20/1.01      | k4_yellow_6(sK1,sK2) = k2_waybel_0(sK1,sK2,X0) ),
% 2.20/1.01      inference(instantiation,[status(thm)],[c_1267]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_2531,plain,
% 2.20/1.01      ( k2_waybel_0(sK1,sK2,X0) != k4_yellow_6(sK1,sK2)
% 2.20/1.01      | k4_yellow_6(sK1,sK2) = k2_waybel_0(sK1,sK2,X0)
% 2.20/1.01      | k4_yellow_6(sK1,sK2) != k4_yellow_6(sK1,sK2) ),
% 2.20/1.01      inference(instantiation,[status(thm)],[c_1995]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_2635,plain,
% 2.20/1.01      ( v1_xboole_0(X0) != iProver_top
% 2.20/1.01      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 2.20/1.01      inference(global_propositional_subsumption,
% 2.20/1.01                [status(thm)],
% 2.20/1.01                [c_2455,c_35,c_36,c_37,c_39,c_21,c_654,c_714,c_1653,c_1771,
% 2.20/1.01                 c_1791,c_1927,c_1949,c_2193,c_2531]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_2646,plain,
% 2.20/1.01      ( k2_waybel_0(sK1,sK2,sK0(u1_struct_0(sK2))) = k4_yellow_6(sK1,sK2)
% 2.20/1.01      | v1_xboole_0(X0) != iProver_top ),
% 2.20/1.01      inference(superposition,[status(thm)],[c_2551,c_2635]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_2705,plain,
% 2.20/1.01      ( k2_waybel_0(sK1,sK2,sK0(u1_struct_0(sK2))) = k4_yellow_6(sK1,sK2) ),
% 2.20/1.01      inference(superposition,[status(thm)],[c_2551,c_2646]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_717,plain,
% 2.20/1.01      ( m1_subset_1(k2_waybel_0(sK1,sK2,X0),u1_struct_0(sK1))
% 2.20/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 2.20/1.01      inference(global_propositional_subsumption,[status(thm)],[c_713,c_26]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_718,plain,
% 2.20/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.20/1.01      | m1_subset_1(k2_waybel_0(sK1,sK2,X0),u1_struct_0(sK1)) ),
% 2.20/1.01      inference(renaming,[status(thm)],[c_717]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_1520,plain,
% 2.20/1.01      ( m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 2.20/1.01      | m1_subset_1(k2_waybel_0(sK1,sK2,X0),u1_struct_0(sK1)) = iProver_top ),
% 2.20/1.01      inference(predicate_to_equality,[status(thm)],[c_718]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_2793,plain,
% 2.20/1.01      ( m1_subset_1(k4_yellow_6(sK1,sK2),u1_struct_0(sK1)) = iProver_top
% 2.20/1.01      | m1_subset_1(sK0(u1_struct_0(sK2)),u1_struct_0(sK2)) != iProver_top ),
% 2.20/1.01      inference(superposition,[status(thm)],[c_2705,c_1520]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_655,plain,
% 2.20/1.01      ( r2_hidden(k4_yellow_6(sK1,sK2),k10_yellow_6(sK1,sK2)) ),
% 2.20/1.01      inference(global_propositional_subsumption,
% 2.20/1.01                [status(thm)],
% 2.20/1.01                [c_653,c_26,c_25,c_24,c_22]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_911,plain,
% 2.20/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.20/1.01      | k4_yellow_6(sK1,sK2) != X0
% 2.20/1.01      | k10_yellow_6(sK1,sK2) != k10_yellow_6(sK1,sK2)
% 2.20/1.01      | k11_yellow_6(sK1,sK2) = X0 ),
% 2.20/1.01      inference(resolution_lifted,[status(thm)],[c_655,c_676]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_912,plain,
% 2.20/1.01      ( ~ m1_subset_1(k4_yellow_6(sK1,sK2),u1_struct_0(sK1))
% 2.20/1.01      | k11_yellow_6(sK1,sK2) = k4_yellow_6(sK1,sK2) ),
% 2.20/1.01      inference(unflattening,[status(thm)],[c_911]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_913,plain,
% 2.20/1.01      ( k11_yellow_6(sK1,sK2) = k4_yellow_6(sK1,sK2)
% 2.20/1.01      | m1_subset_1(k4_yellow_6(sK1,sK2),u1_struct_0(sK1)) != iProver_top ),
% 2.20/1.01      inference(predicate_to_equality,[status(thm)],[c_912]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_2814,plain,
% 2.20/1.01      ( m1_subset_1(sK0(u1_struct_0(sK2)),u1_struct_0(sK2)) != iProver_top ),
% 2.20/1.01      inference(global_propositional_subsumption,
% 2.20/1.01                [status(thm)],
% 2.20/1.01                [c_2793,c_21,c_913]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_2820,plain,
% 2.20/1.01      ( v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 2.20/1.01      inference(superposition,[status(thm)],[c_2001,c_2814]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_2926,plain,
% 2.20/1.01      ( v1_xboole_0(X0) != iProver_top ),
% 2.20/1.01      inference(superposition,[status(thm)],[c_2820,c_2635]) ).
% 2.20/1.01  
% 2.20/1.01  cnf(c_2932,plain,
% 2.20/1.01      ( $false ),
% 2.20/1.01      inference(superposition,[status(thm)],[c_2820,c_2926]) ).
% 2.20/1.01  
% 2.20/1.01  
% 2.20/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.20/1.01  
% 2.20/1.01  ------                               Statistics
% 2.20/1.01  
% 2.20/1.01  ------ General
% 2.20/1.01  
% 2.20/1.01  abstr_ref_over_cycles:                  0
% 2.20/1.01  abstr_ref_under_cycles:                 0
% 2.20/1.01  gc_basic_clause_elim:                   0
% 2.20/1.01  forced_gc_time:                         0
% 2.20/1.01  parsing_time:                           0.008
% 2.20/1.01  unif_index_cands_time:                  0.
% 2.20/1.01  unif_index_add_time:                    0.
% 2.20/1.01  orderings_time:                         0.
% 2.20/1.01  out_proof_time:                         0.02
% 2.20/1.01  total_time:                             0.101
% 2.20/1.01  num_of_symbols:                         55
% 2.20/1.01  num_of_terms:                           1821
% 2.20/1.01  
% 2.20/1.01  ------ Preprocessing
% 2.20/1.01  
% 2.20/1.01  num_of_splits:                          0
% 2.20/1.01  num_of_split_atoms:                     0
% 2.20/1.01  num_of_reused_defs:                     0
% 2.20/1.01  num_eq_ax_congr_red:                    22
% 2.20/1.01  num_of_sem_filtered_clauses:            1
% 2.20/1.01  num_of_subtypes:                        0
% 2.20/1.01  monotx_restored_types:                  0
% 2.20/1.01  sat_num_of_epr_types:                   0
% 2.20/1.01  sat_num_of_non_cyclic_types:            0
% 2.20/1.01  sat_guarded_non_collapsed_types:        0
% 2.20/1.01  num_pure_diseq_elim:                    0
% 2.20/1.01  simp_replaced_by:                       0
% 2.20/1.01  res_preprocessed:                       91
% 2.20/1.01  prep_upred:                             0
% 2.20/1.01  prep_unflattend:                        82
% 2.20/1.01  smt_new_axioms:                         0
% 2.20/1.01  pred_elim_cands:                        3
% 2.20/1.01  pred_elim:                              11
% 2.20/1.01  pred_elim_cl:                           12
% 2.20/1.01  pred_elim_cycles:                       13
% 2.20/1.01  merged_defs:                            0
% 2.20/1.01  merged_defs_ncl:                        0
% 2.20/1.01  bin_hyper_res:                          0
% 2.20/1.01  prep_cycles:                            4
% 2.20/1.01  pred_elim_time:                         0.01
% 2.20/1.01  splitting_time:                         0.
% 2.20/1.01  sem_filter_time:                        0.
% 2.20/1.01  monotx_time:                            0.
% 2.20/1.01  subtype_inf_time:                       0.
% 2.20/1.01  
% 2.20/1.01  ------ Problem properties
% 2.20/1.01  
% 2.20/1.01  clauses:                                15
% 2.20/1.01  conjectures:                            1
% 2.20/1.01  epr:                                    5
% 2.20/1.01  horn:                                   13
% 2.20/1.01  ground:                                 3
% 2.20/1.01  unary:                                  3
% 2.20/1.01  binary:                                 7
% 2.20/1.01  lits:                                   32
% 2.20/1.01  lits_eq:                                3
% 2.20/1.01  fd_pure:                                0
% 2.20/1.01  fd_pseudo:                              0
% 2.20/1.01  fd_cond:                                1
% 2.20/1.01  fd_pseudo_cond:                         0
% 2.20/1.01  ac_symbols:                             0
% 2.20/1.01  
% 2.20/1.01  ------ Propositional Solver
% 2.20/1.01  
% 2.20/1.01  prop_solver_calls:                      27
% 2.20/1.01  prop_fast_solver_calls:                 786
% 2.20/1.01  smt_solver_calls:                       0
% 2.20/1.01  smt_fast_solver_calls:                  0
% 2.20/1.01  prop_num_of_clauses:                    810
% 2.20/1.01  prop_preprocess_simplified:             3650
% 2.20/1.01  prop_fo_subsumed:                       43
% 2.20/1.01  prop_solver_time:                       0.
% 2.20/1.01  smt_solver_time:                        0.
% 2.20/1.01  smt_fast_solver_time:                   0.
% 2.20/1.01  prop_fast_solver_time:                  0.
% 2.20/1.01  prop_unsat_core_time:                   0.
% 2.20/1.01  
% 2.20/1.01  ------ QBF
% 2.20/1.01  
% 2.20/1.01  qbf_q_res:                              0
% 2.20/1.01  qbf_num_tautologies:                    0
% 2.20/1.01  qbf_prep_cycles:                        0
% 2.20/1.01  
% 2.20/1.01  ------ BMC1
% 2.20/1.01  
% 2.20/1.01  bmc1_current_bound:                     -1
% 2.20/1.01  bmc1_last_solved_bound:                 -1
% 2.20/1.01  bmc1_unsat_core_size:                   -1
% 2.20/1.01  bmc1_unsat_core_parents_size:           -1
% 2.20/1.01  bmc1_merge_next_fun:                    0
% 2.20/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.20/1.01  
% 2.20/1.01  ------ Instantiation
% 2.20/1.01  
% 2.20/1.01  inst_num_of_clauses:                    231
% 2.20/1.01  inst_num_in_passive:                    67
% 2.20/1.01  inst_num_in_active:                     147
% 2.20/1.01  inst_num_in_unprocessed:                17
% 2.20/1.01  inst_num_of_loops:                      170
% 2.20/1.01  inst_num_of_learning_restarts:          0
% 2.20/1.01  inst_num_moves_active_passive:          20
% 2.20/1.01  inst_lit_activity:                      0
% 2.20/1.01  inst_lit_activity_moves:                0
% 2.20/1.01  inst_num_tautologies:                   0
% 2.20/1.01  inst_num_prop_implied:                  0
% 2.20/1.01  inst_num_existing_simplified:           0
% 2.20/1.01  inst_num_eq_res_simplified:             0
% 2.20/1.01  inst_num_child_elim:                    0
% 2.20/1.01  inst_num_of_dismatching_blockings:      38
% 2.20/1.01  inst_num_of_non_proper_insts:           207
% 2.20/1.01  inst_num_of_duplicates:                 0
% 2.20/1.01  inst_inst_num_from_inst_to_res:         0
% 2.20/1.01  inst_dismatching_checking_time:         0.
% 2.20/1.01  
% 2.20/1.01  ------ Resolution
% 2.20/1.01  
% 2.20/1.01  res_num_of_clauses:                     0
% 2.20/1.01  res_num_in_passive:                     0
% 2.20/1.01  res_num_in_active:                      0
% 2.20/1.01  res_num_of_loops:                       95
% 2.20/1.01  res_forward_subset_subsumed:            31
% 2.20/1.01  res_backward_subset_subsumed:           0
% 2.20/1.01  res_forward_subsumed:                   0
% 2.20/1.01  res_backward_subsumed:                  0
% 2.20/1.01  res_forward_subsumption_resolution:     0
% 2.20/1.01  res_backward_subsumption_resolution:    1
% 2.20/1.01  res_clause_to_clause_subsumption:       90
% 2.20/1.01  res_orphan_elimination:                 0
% 2.20/1.01  res_tautology_del:                      26
% 2.20/1.01  res_num_eq_res_simplified:              0
% 2.20/1.01  res_num_sel_changes:                    0
% 2.20/1.01  res_moves_from_active_to_pass:          0
% 2.20/1.01  
% 2.20/1.01  ------ Superposition
% 2.20/1.01  
% 2.20/1.01  sup_time_total:                         0.
% 2.20/1.01  sup_time_generating:                    0.
% 2.20/1.01  sup_time_sim_full:                      0.
% 2.20/1.01  sup_time_sim_immed:                     0.
% 2.20/1.01  
% 2.20/1.01  sup_num_of_clauses:                     35
% 2.20/1.01  sup_num_in_active:                      31
% 2.20/1.01  sup_num_in_passive:                     4
% 2.20/1.01  sup_num_of_loops:                       33
% 2.20/1.01  sup_fw_superposition:                   23
% 2.20/1.01  sup_bw_superposition:                   23
% 2.20/1.01  sup_immediate_simplified:               14
% 2.20/1.01  sup_given_eliminated:                   0
% 2.20/1.01  comparisons_done:                       0
% 2.20/1.01  comparisons_avoided:                    0
% 2.20/1.01  
% 2.20/1.01  ------ Simplifications
% 2.20/1.01  
% 2.20/1.01  
% 2.20/1.01  sim_fw_subset_subsumed:                 9
% 2.20/1.01  sim_bw_subset_subsumed:                 6
% 2.20/1.01  sim_fw_subsumed:                        2
% 2.20/1.01  sim_bw_subsumed:                        1
% 2.20/1.01  sim_fw_subsumption_res:                 1
% 2.20/1.01  sim_bw_subsumption_res:                 0
% 2.20/1.01  sim_tautology_del:                      6
% 2.20/1.01  sim_eq_tautology_del:                   1
% 2.20/1.01  sim_eq_res_simp:                        0
% 2.20/1.01  sim_fw_demodulated:                     0
% 2.20/1.01  sim_bw_demodulated:                     0
% 2.20/1.01  sim_light_normalised:                   0
% 2.20/1.01  sim_joinable_taut:                      0
% 2.20/1.01  sim_joinable_simp:                      0
% 2.20/1.01  sim_ac_normalised:                      0
% 2.20/1.01  sim_smt_subsumption:                    0
% 2.20/1.01  
%------------------------------------------------------------------------------
