%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:40 EST 2020

% Result     : Theorem 1.46s
% Output     : Refutation 1.46s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 991 expanded)
%              Number of leaves         :   11 ( 190 expanded)
%              Depth                    :   32
%              Number of atoms          :  316 (4823 expanded)
%              Number of equality atoms :    7 (  50 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f268,plain,(
    $false ),
    inference(subsumption_resolution,[],[f258,f257])).

fof(f257,plain,(
    ! [X0] : r2_hidden(k2_waybel_0(sK0,sK1,sK4(sK0,sK1,k6_subset_1(X0,X0),k4_yellow_6(sK1,sK2(sK1)))),X0) ),
    inference(resolution,[],[f231,f68])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k6_subset_1(X0,X1))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k6_subset_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f57,f48])).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f231,plain,(
    ! [X0] : r2_hidden(k2_waybel_0(sK0,sK1,sK4(sK0,sK1,k6_subset_1(X0,X0),k4_yellow_6(sK1,sK2(sK1)))),k6_subset_1(X0,X0)) ),
    inference(resolution,[],[f228,f153])).

fof(f153,plain,(
    ! [X0] :
      ( ~ r2_waybel_0(sK0,sK1,X0)
      | r2_hidden(k2_waybel_0(sK0,sK1,sK4(sK0,sK1,X0,k4_yellow_6(sK1,sK2(sK1)))),X0) ) ),
    inference(subsumption_resolution,[],[f152,f35])).

fof(f35,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_yellow_6)).

fof(f152,plain,(
    ! [X0] :
      ( r2_hidden(k2_waybel_0(sK0,sK1,sK4(sK0,sK1,X0,k4_yellow_6(sK1,sK2(sK1)))),X0)
      | ~ r2_waybel_0(sK0,sK1,X0)
      | ~ l1_struct_0(sK0) ) ),
    inference(resolution,[],[f151,f32])).

fof(f32,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f151,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(sK1,X1)
      | r2_hidden(k2_waybel_0(sK0,sK1,sK4(sK0,sK1,X0,k4_yellow_6(sK1,sK2(sK1)))),X0)
      | ~ r2_waybel_0(sK0,sK1,X0)
      | ~ l1_struct_0(X1) ) ),
    inference(resolution,[],[f150,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_0)).

fof(f150,plain,(
    ! [X0] :
      ( ~ l1_orders_2(sK1)
      | ~ r2_waybel_0(sK0,sK1,X0)
      | r2_hidden(k2_waybel_0(sK0,sK1,sK4(sK0,sK1,X0,k4_yellow_6(sK1,sK2(sK1)))),X0) ) ),
    inference(resolution,[],[f149,f36])).

fof(f36,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f149,plain,(
    ! [X0] :
      ( ~ l1_struct_0(sK1)
      | r2_hidden(k2_waybel_0(sK0,sK1,sK4(sK0,sK1,X0,k4_yellow_6(sK1,sK2(sK1)))),X0)
      | ~ r2_waybel_0(sK0,sK1,X0) ) ),
    inference(resolution,[],[f148,f38])).

fof(f38,plain,(
    ! [X0] :
      ( l1_waybel_0(sK2(X0),X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] : l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ? [X1] : l1_waybel_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_l1_waybel_0)).

fof(f148,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X0,sK1)
      | ~ r2_waybel_0(sK0,sK1,X1)
      | r2_hidden(k2_waybel_0(sK0,sK1,sK4(sK0,sK1,X1,k4_yellow_6(sK1,X0))),X1) ) ),
    inference(subsumption_resolution,[],[f147,f35])).

fof(f147,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X0,sK1)
      | ~ r2_waybel_0(sK0,sK1,X1)
      | r2_hidden(k2_waybel_0(sK0,sK1,sK4(sK0,sK1,X1,k4_yellow_6(sK1,X0))),X1)
      | ~ l1_struct_0(sK0) ) ),
    inference(resolution,[],[f146,f32])).

fof(f146,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_waybel_0(sK1,X2)
      | ~ l1_waybel_0(X1,sK1)
      | ~ r2_waybel_0(sK0,sK1,X0)
      | r2_hidden(k2_waybel_0(sK0,sK1,sK4(sK0,sK1,X0,k4_yellow_6(sK1,X1))),X0)
      | ~ l1_struct_0(X2) ) ),
    inference(resolution,[],[f145,f37])).

fof(f145,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(sK1)
      | r2_hidden(k2_waybel_0(sK0,sK1,sK4(sK0,sK1,X0,k4_yellow_6(sK1,X1))),X0)
      | ~ l1_waybel_0(X1,sK1)
      | ~ r2_waybel_0(sK0,sK1,X0) ) ),
    inference(resolution,[],[f144,f36])).

fof(f144,plain,(
    ! [X8,X7] :
      ( ~ l1_struct_0(sK1)
      | ~ r2_waybel_0(sK0,sK1,X7)
      | r2_hidden(k2_waybel_0(sK0,sK1,sK4(sK0,sK1,X7,k4_yellow_6(sK1,X8))),X7)
      | ~ l1_waybel_0(X8,sK1) ) ),
    inference(subsumption_resolution,[],[f141,f29])).

fof(f29,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f141,plain,(
    ! [X8,X7] :
      ( r2_hidden(k2_waybel_0(sK0,sK1,sK4(sK0,sK1,X7,k4_yellow_6(sK1,X8))),X7)
      | ~ r2_waybel_0(sK0,sK1,X7)
      | ~ l1_struct_0(sK1)
      | ~ l1_waybel_0(X8,sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f138,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_yellow_6)).

fof(f138,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK1))
      | r2_hidden(k2_waybel_0(sK0,sK1,sK4(sK0,sK1,X3,X2)),X3)
      | ~ r2_waybel_0(sK0,sK1,X3) ) ),
    inference(subsumption_resolution,[],[f136,f29])).

fof(f136,plain,(
    ! [X2,X3] :
      ( v2_struct_0(sK1)
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | r2_hidden(k2_waybel_0(sK0,sK1,sK4(sK0,sK1,X3,X2)),X3)
      | ~ r2_waybel_0(sK0,sK1,X3) ) ),
    inference(resolution,[],[f134,f32])).

fof(f134,plain,(
    ! [X12,X10,X11] :
      ( ~ l1_waybel_0(X10,sK0)
      | v2_struct_0(X10)
      | ~ m1_subset_1(X11,u1_struct_0(X10))
      | r2_hidden(k2_waybel_0(sK0,X10,sK4(sK0,X10,X12,X11)),X12)
      | ~ r2_waybel_0(sK0,X10,X12) ) ),
    inference(subsumption_resolution,[],[f80,f35])).

fof(f80,plain,(
    ! [X12,X10,X11] :
      ( ~ l1_struct_0(sK0)
      | v2_struct_0(X10)
      | ~ l1_waybel_0(X10,sK0)
      | ~ m1_subset_1(X11,u1_struct_0(X10))
      | r2_hidden(k2_waybel_0(sK0,X10,sK4(sK0,X10,X12,X11)),X12)
      | ~ r2_waybel_0(sK0,X10,X12) ) ),
    inference(resolution,[],[f34,f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | r2_hidden(k2_waybel_0(X0,X1,sK4(X0,X1,X2,X3)),X2)
      | ~ r2_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ! [X3] :
                  ( ? [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      & r1_orders_2(X1,X3,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ! [X3] :
                  ( ? [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      & r1_orders_2(X1,X3,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ? [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      & r1_orders_2(X1,X3,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_waybel_0)).

fof(f34,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f228,plain,(
    ! [X0] : r2_waybel_0(sK0,sK1,k6_subset_1(X0,X0)) ),
    inference(subsumption_resolution,[],[f227,f29])).

fof(f227,plain,(
    ! [X0] :
      ( v2_struct_0(sK1)
      | r2_waybel_0(sK0,sK1,k6_subset_1(X0,X0)) ) ),
    inference(subsumption_resolution,[],[f225,f32])).

fof(f225,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(sK1,sK0)
      | v2_struct_0(sK1)
      | r2_waybel_0(sK0,sK1,k6_subset_1(X0,X0)) ) ),
    inference(resolution,[],[f217,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_waybel_0(sK0,X0,k6_subset_1(u1_struct_0(sK0),X1))
      | ~ l1_waybel_0(X0,sK0)
      | v2_struct_0(X0)
      | r2_waybel_0(sK0,X0,X1) ) ),
    inference(subsumption_resolution,[],[f76,f35])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(sK0)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(X0,sK0)
      | r1_waybel_0(sK0,X0,k6_subset_1(u1_struct_0(sK0),X1))
      | r2_waybel_0(sK0,X0,X1) ) ),
    inference(resolution,[],[f34,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
      | r2_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_waybel_0)).

fof(f217,plain,(
    ! [X0] : ~ r1_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),k6_subset_1(X0,X0))) ),
    inference(resolution,[],[f216,f89])).

fof(f89,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,u1_struct_0(sK0))
      | ~ r1_waybel_0(sK0,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f88,f29])).

fof(f88,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,u1_struct_0(sK0))
      | ~ r1_waybel_0(sK0,sK1,X0)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f87,f32])).

fof(f87,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(sK1,sK0)
      | ~ r1_tarski(X0,u1_struct_0(sK0))
      | ~ r1_waybel_0(sK0,sK1,X0)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f86,f33])).

fof(f33,plain,(
    ~ r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f86,plain,(
    ! [X17,X18,X16] :
      ( r1_waybel_0(sK0,X16,X18)
      | ~ l1_waybel_0(X16,sK0)
      | ~ r1_tarski(X17,X18)
      | ~ r1_waybel_0(sK0,X16,X17)
      | v2_struct_0(X16) ) ),
    inference(subsumption_resolution,[],[f82,f35])).

fof(f82,plain,(
    ! [X17,X18,X16] :
      ( ~ l1_struct_0(sK0)
      | v2_struct_0(X16)
      | ~ l1_waybel_0(X16,sK0)
      | ~ r1_tarski(X17,X18)
      | ~ r1_waybel_0(sK0,X16,X17)
      | r1_waybel_0(sK0,X16,X18) ) ),
    inference(resolution,[],[f34,f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ r1_tarski(X2,X3)
      | ~ r1_waybel_0(X0,X1,X2)
      | r1_waybel_0(X0,X1,X3) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ( ( r2_waybel_0(X0,X1,X3)
                  | ~ r2_waybel_0(X0,X1,X2) )
                & ( r1_waybel_0(X0,X1,X3)
                  | ~ r1_waybel_0(X0,X1,X2) ) )
              | ~ r1_tarski(X2,X3) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ( ( r2_waybel_0(X0,X1,X3)
                  | ~ r2_waybel_0(X0,X1,X2) )
                & ( r1_waybel_0(X0,X1,X3)
                  | ~ r1_waybel_0(X0,X1,X2) ) )
              | ~ r1_tarski(X2,X3) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2,X3] :
              ( r1_tarski(X2,X3)
             => ( ( r2_waybel_0(X0,X1,X2)
                 => r2_waybel_0(X0,X1,X3) )
                & ( r1_waybel_0(X0,X1,X2)
                 => r1_waybel_0(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_0)).

fof(f216,plain,(
    ! [X0] : r1_tarski(k6_subset_1(u1_struct_0(sK0),k6_subset_1(X0,X0)),u1_struct_0(sK0)) ),
    inference(duplicate_literal_removal,[],[f215])).

fof(f215,plain,(
    ! [X0] :
      ( r1_tarski(k6_subset_1(u1_struct_0(sK0),k6_subset_1(X0,X0)),u1_struct_0(sK0))
      | r1_tarski(k6_subset_1(u1_struct_0(sK0),k6_subset_1(X0,X0)),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f188,f187])).

fof(f187,plain,(
    ! [X6,X5] :
      ( r2_hidden(k2_waybel_0(sK0,sK1,sK4(sK0,sK1,k6_subset_1(X5,X6),k4_yellow_6(sK1,sK2(sK1)))),X5)
      | r1_tarski(k6_subset_1(u1_struct_0(sK0),k6_subset_1(X5,X6)),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f169,f68])).

fof(f169,plain,(
    ! [X0] :
      ( r2_hidden(k2_waybel_0(sK0,sK1,sK4(sK0,sK1,X0,k4_yellow_6(sK1,sK2(sK1)))),X0)
      | r1_tarski(k6_subset_1(u1_struct_0(sK0),X0),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f163,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f163,plain,(
    ! [X0] :
      ( r2_hidden(sK5(k6_subset_1(u1_struct_0(sK0),X0),u1_struct_0(sK0)),u1_struct_0(sK0))
      | r2_hidden(k2_waybel_0(sK0,sK1,sK4(sK0,sK1,X0,k4_yellow_6(sK1,sK2(sK1)))),X0) ) ),
    inference(resolution,[],[f156,f68])).

fof(f156,plain,(
    ! [X4] :
      ( r2_hidden(sK5(k6_subset_1(u1_struct_0(sK0),X4),u1_struct_0(sK0)),k6_subset_1(u1_struct_0(sK0),X4))
      | r2_hidden(k2_waybel_0(sK0,sK1,sK4(sK0,sK1,X4,k4_yellow_6(sK1,sK2(sK1)))),X4) ) ),
    inference(resolution,[],[f153,f94])).

fof(f94,plain,(
    ! [X0] :
      ( r2_waybel_0(sK0,sK1,X0)
      | r2_hidden(sK5(k6_subset_1(u1_struct_0(sK0),X0),u1_struct_0(sK0)),k6_subset_1(u1_struct_0(sK0),X0)) ) ),
    inference(subsumption_resolution,[],[f93,f29])).

fof(f93,plain,(
    ! [X0] :
      ( r2_hidden(sK5(k6_subset_1(u1_struct_0(sK0),X0),u1_struct_0(sK0)),k6_subset_1(u1_struct_0(sK0),X0))
      | v2_struct_0(sK1)
      | r2_waybel_0(sK0,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f91,f32])).

fof(f91,plain,(
    ! [X0] :
      ( r2_hidden(sK5(k6_subset_1(u1_struct_0(sK0),X0),u1_struct_0(sK0)),k6_subset_1(u1_struct_0(sK0),X0))
      | ~ l1_waybel_0(sK1,sK0)
      | v2_struct_0(sK1)
      | r2_waybel_0(sK0,sK1,X0) ) ),
    inference(resolution,[],[f90,f83])).

fof(f90,plain,(
    ! [X0] :
      ( ~ r1_waybel_0(sK0,sK1,X0)
      | r2_hidden(sK5(X0,u1_struct_0(sK0)),X0) ) ),
    inference(resolution,[],[f89,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f188,plain,(
    ! [X8,X7] :
      ( ~ r2_hidden(k2_waybel_0(sK0,sK1,sK4(sK0,sK1,k6_subset_1(X7,X8),k4_yellow_6(sK1,sK2(sK1)))),X8)
      | r1_tarski(k6_subset_1(u1_struct_0(sK0),k6_subset_1(X7,X8)),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f169,f67])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k6_subset_1(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k6_subset_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f58,f48])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f258,plain,(
    ! [X1] : ~ r2_hidden(k2_waybel_0(sK0,sK1,sK4(sK0,sK1,k6_subset_1(X1,X1),k4_yellow_6(sK1,sK2(sK1)))),X1) ),
    inference(resolution,[],[f231,f67])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:49:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 1.19/0.53  % (9523)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.19/0.54  % (9542)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.19/0.54  % (9526)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.19/0.54  % (9539)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.19/0.54  % (9525)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.19/0.54  % (9534)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.46/0.55  % (9531)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.46/0.55  % (9531)Refutation not found, incomplete strategy% (9531)------------------------------
% 1.46/0.55  % (9531)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.55  % (9521)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.46/0.55  % (9543)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.46/0.56  % (9535)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.46/0.56  % (9547)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.46/0.56  % (9522)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.46/0.56  % (9527)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.46/0.56  % (9549)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.46/0.57  % (9531)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.57  
% 1.46/0.57  % (9531)Memory used [KB]: 10746
% 1.46/0.57  % (9531)Time elapsed: 0.141 s
% 1.46/0.57  % (9531)------------------------------
% 1.46/0.57  % (9531)------------------------------
% 1.46/0.57  % (9532)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.46/0.57  % (9528)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.46/0.57  % (9529)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.46/0.57  % (9530)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.46/0.58  % (9528)Refutation not found, incomplete strategy% (9528)------------------------------
% 1.46/0.58  % (9528)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.58  % (9541)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.46/0.58  % (9546)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.46/0.58  % (9520)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.46/0.58  % (9524)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.46/0.58  % (9533)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.46/0.58  % (9528)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.58  
% 1.46/0.58  % (9528)Memory used [KB]: 10746
% 1.46/0.58  % (9528)Time elapsed: 0.131 s
% 1.46/0.58  % (9528)------------------------------
% 1.46/0.58  % (9528)------------------------------
% 1.46/0.59  % (9540)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.46/0.59  % (9536)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.46/0.60  % (9545)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.46/0.60  % (9544)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.46/0.60  % (9537)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.46/0.60  % (9538)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.46/0.60  % (9541)Refutation found. Thanks to Tanya!
% 1.46/0.60  % SZS status Theorem for theBenchmark
% 1.46/0.60  % (9548)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.46/0.61  % (9537)Refutation not found, incomplete strategy% (9537)------------------------------
% 1.46/0.61  % (9537)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.61  % SZS output start Proof for theBenchmark
% 1.46/0.61  fof(f268,plain,(
% 1.46/0.61    $false),
% 1.46/0.61    inference(subsumption_resolution,[],[f258,f257])).
% 1.46/0.61  fof(f257,plain,(
% 1.46/0.61    ( ! [X0] : (r2_hidden(k2_waybel_0(sK0,sK1,sK4(sK0,sK1,k6_subset_1(X0,X0),k4_yellow_6(sK1,sK2(sK1)))),X0)) )),
% 1.46/0.61    inference(resolution,[],[f231,f68])).
% 1.46/0.61  fof(f68,plain,(
% 1.46/0.61    ( ! [X0,X3,X1] : (~r2_hidden(X3,k6_subset_1(X0,X1)) | r2_hidden(X3,X0)) )),
% 1.46/0.61    inference(equality_resolution,[],[f62])).
% 1.46/0.61  fof(f62,plain,(
% 1.46/0.61    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k6_subset_1(X0,X1) != X2) )),
% 1.46/0.61    inference(definition_unfolding,[],[f57,f48])).
% 1.46/0.61  fof(f48,plain,(
% 1.46/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.46/0.61    inference(cnf_transformation,[],[f3])).
% 1.46/0.61  fof(f3,axiom,(
% 1.46/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.46/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.46/0.61  fof(f57,plain,(
% 1.46/0.61    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.46/0.61    inference(cnf_transformation,[],[f2])).
% 1.46/0.61  fof(f2,axiom,(
% 1.46/0.61    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.46/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.46/0.61  fof(f231,plain,(
% 1.46/0.61    ( ! [X0] : (r2_hidden(k2_waybel_0(sK0,sK1,sK4(sK0,sK1,k6_subset_1(X0,X0),k4_yellow_6(sK1,sK2(sK1)))),k6_subset_1(X0,X0))) )),
% 1.46/0.61    inference(resolution,[],[f228,f153])).
% 1.46/0.61  fof(f153,plain,(
% 1.46/0.61    ( ! [X0] : (~r2_waybel_0(sK0,sK1,X0) | r2_hidden(k2_waybel_0(sK0,sK1,sK4(sK0,sK1,X0,k4_yellow_6(sK1,sK2(sK1)))),X0)) )),
% 1.46/0.61    inference(subsumption_resolution,[],[f152,f35])).
% 1.46/0.61  fof(f35,plain,(
% 1.46/0.61    l1_struct_0(sK0)),
% 1.46/0.61    inference(cnf_transformation,[],[f15])).
% 1.46/0.61  fof(f15,plain,(
% 1.46/0.61    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 1.46/0.61    inference(flattening,[],[f14])).
% 1.46/0.61  fof(f14,plain,(
% 1.46/0.61    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & (l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 1.46/0.61    inference(ennf_transformation,[],[f13])).
% 1.46/0.61  fof(f13,negated_conjecture,(
% 1.46/0.61    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 1.46/0.61    inference(negated_conjecture,[],[f12])).
% 1.46/0.61  fof(f12,conjecture,(
% 1.46/0.61    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 1.46/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_yellow_6)).
% 1.46/0.61  fof(f152,plain,(
% 1.46/0.61    ( ! [X0] : (r2_hidden(k2_waybel_0(sK0,sK1,sK4(sK0,sK1,X0,k4_yellow_6(sK1,sK2(sK1)))),X0) | ~r2_waybel_0(sK0,sK1,X0) | ~l1_struct_0(sK0)) )),
% 1.46/0.61    inference(resolution,[],[f151,f32])).
% 1.46/0.61  fof(f32,plain,(
% 1.46/0.61    l1_waybel_0(sK1,sK0)),
% 1.46/0.61    inference(cnf_transformation,[],[f15])).
% 1.46/0.61  fof(f151,plain,(
% 1.46/0.61    ( ! [X0,X1] : (~l1_waybel_0(sK1,X1) | r2_hidden(k2_waybel_0(sK0,sK1,sK4(sK0,sK1,X0,k4_yellow_6(sK1,sK2(sK1)))),X0) | ~r2_waybel_0(sK0,sK1,X0) | ~l1_struct_0(X1)) )),
% 1.46/0.61    inference(resolution,[],[f150,f37])).
% 1.46/0.61  fof(f37,plain,(
% 1.46/0.61    ( ! [X0,X1] : (l1_orders_2(X1) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 1.46/0.61    inference(cnf_transformation,[],[f17])).
% 1.46/0.61  fof(f17,plain,(
% 1.46/0.61    ! [X0] : (! [X1] : (l1_orders_2(X1) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 1.46/0.61    inference(ennf_transformation,[],[f7])).
% 1.46/0.61  fof(f7,axiom,(
% 1.46/0.61    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => l1_orders_2(X1)))),
% 1.46/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_0)).
% 1.46/0.61  fof(f150,plain,(
% 1.46/0.61    ( ! [X0] : (~l1_orders_2(sK1) | ~r2_waybel_0(sK0,sK1,X0) | r2_hidden(k2_waybel_0(sK0,sK1,sK4(sK0,sK1,X0,k4_yellow_6(sK1,sK2(sK1)))),X0)) )),
% 1.46/0.61    inference(resolution,[],[f149,f36])).
% 1.46/0.61  fof(f36,plain,(
% 1.46/0.61    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 1.46/0.61    inference(cnf_transformation,[],[f16])).
% 1.46/0.61  fof(f16,plain,(
% 1.46/0.61    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 1.46/0.61    inference(ennf_transformation,[],[f5])).
% 1.46/0.61  fof(f5,axiom,(
% 1.46/0.61    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 1.46/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 1.46/0.61  fof(f149,plain,(
% 1.46/0.61    ( ! [X0] : (~l1_struct_0(sK1) | r2_hidden(k2_waybel_0(sK0,sK1,sK4(sK0,sK1,X0,k4_yellow_6(sK1,sK2(sK1)))),X0) | ~r2_waybel_0(sK0,sK1,X0)) )),
% 1.46/0.61    inference(resolution,[],[f148,f38])).
% 1.46/0.61  fof(f38,plain,(
% 1.46/0.61    ( ! [X0] : (l1_waybel_0(sK2(X0),X0) | ~l1_struct_0(X0)) )),
% 1.46/0.61    inference(cnf_transformation,[],[f18])).
% 1.46/0.61  fof(f18,plain,(
% 1.46/0.61    ! [X0] : (? [X1] : l1_waybel_0(X1,X0) | ~l1_struct_0(X0))),
% 1.46/0.61    inference(ennf_transformation,[],[f8])).
% 1.46/0.61  fof(f8,axiom,(
% 1.46/0.61    ! [X0] : (l1_struct_0(X0) => ? [X1] : l1_waybel_0(X1,X0))),
% 1.46/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_l1_waybel_0)).
% 1.46/0.61  fof(f148,plain,(
% 1.46/0.61    ( ! [X0,X1] : (~l1_waybel_0(X0,sK1) | ~r2_waybel_0(sK0,sK1,X1) | r2_hidden(k2_waybel_0(sK0,sK1,sK4(sK0,sK1,X1,k4_yellow_6(sK1,X0))),X1)) )),
% 1.46/0.61    inference(subsumption_resolution,[],[f147,f35])).
% 1.46/0.61  fof(f147,plain,(
% 1.46/0.61    ( ! [X0,X1] : (~l1_waybel_0(X0,sK1) | ~r2_waybel_0(sK0,sK1,X1) | r2_hidden(k2_waybel_0(sK0,sK1,sK4(sK0,sK1,X1,k4_yellow_6(sK1,X0))),X1) | ~l1_struct_0(sK0)) )),
% 1.46/0.61    inference(resolution,[],[f146,f32])).
% 1.46/0.61  fof(f146,plain,(
% 1.46/0.61    ( ! [X2,X0,X1] : (~l1_waybel_0(sK1,X2) | ~l1_waybel_0(X1,sK1) | ~r2_waybel_0(sK0,sK1,X0) | r2_hidden(k2_waybel_0(sK0,sK1,sK4(sK0,sK1,X0,k4_yellow_6(sK1,X1))),X0) | ~l1_struct_0(X2)) )),
% 1.46/0.61    inference(resolution,[],[f145,f37])).
% 1.46/0.61  fof(f145,plain,(
% 1.46/0.61    ( ! [X0,X1] : (~l1_orders_2(sK1) | r2_hidden(k2_waybel_0(sK0,sK1,sK4(sK0,sK1,X0,k4_yellow_6(sK1,X1))),X0) | ~l1_waybel_0(X1,sK1) | ~r2_waybel_0(sK0,sK1,X0)) )),
% 1.46/0.61    inference(resolution,[],[f144,f36])).
% 1.46/0.61  fof(f144,plain,(
% 1.46/0.61    ( ! [X8,X7] : (~l1_struct_0(sK1) | ~r2_waybel_0(sK0,sK1,X7) | r2_hidden(k2_waybel_0(sK0,sK1,sK4(sK0,sK1,X7,k4_yellow_6(sK1,X8))),X7) | ~l1_waybel_0(X8,sK1)) )),
% 1.46/0.61    inference(subsumption_resolution,[],[f141,f29])).
% 1.46/0.61  fof(f29,plain,(
% 1.46/0.61    ~v2_struct_0(sK1)),
% 1.46/0.61    inference(cnf_transformation,[],[f15])).
% 1.46/0.61  fof(f141,plain,(
% 1.46/0.61    ( ! [X8,X7] : (r2_hidden(k2_waybel_0(sK0,sK1,sK4(sK0,sK1,X7,k4_yellow_6(sK1,X8))),X7) | ~r2_waybel_0(sK0,sK1,X7) | ~l1_struct_0(sK1) | ~l1_waybel_0(X8,sK1) | v2_struct_0(sK1)) )),
% 1.46/0.61    inference(resolution,[],[f138,f49])).
% 1.46/0.61  fof(f49,plain,(
% 1.46/0.61    ( ! [X0,X1] : (m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0)) | ~l1_struct_0(X0) | ~l1_waybel_0(X1,X0) | v2_struct_0(X0)) )),
% 1.46/0.61    inference(cnf_transformation,[],[f26])).
% 1.46/0.61  fof(f26,plain,(
% 1.46/0.61    ! [X0,X1] : (m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.46/0.61    inference(flattening,[],[f25])).
% 1.46/0.61  fof(f25,plain,(
% 1.46/0.61    ! [X0,X1] : (m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0)) | (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.46/0.61    inference(ennf_transformation,[],[f11])).
% 1.46/0.61  fof(f11,axiom,(
% 1.46/0.61    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0) & ~v2_struct_0(X0)) => m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0)))),
% 1.46/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_yellow_6)).
% 1.46/0.61  fof(f138,plain,(
% 1.46/0.61    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK1)) | r2_hidden(k2_waybel_0(sK0,sK1,sK4(sK0,sK1,X3,X2)),X3) | ~r2_waybel_0(sK0,sK1,X3)) )),
% 1.46/0.61    inference(subsumption_resolution,[],[f136,f29])).
% 1.46/0.61  fof(f136,plain,(
% 1.46/0.61    ( ! [X2,X3] : (v2_struct_0(sK1) | ~m1_subset_1(X2,u1_struct_0(sK1)) | r2_hidden(k2_waybel_0(sK0,sK1,sK4(sK0,sK1,X3,X2)),X3) | ~r2_waybel_0(sK0,sK1,X3)) )),
% 1.46/0.61    inference(resolution,[],[f134,f32])).
% 1.46/0.61  fof(f134,plain,(
% 1.46/0.61    ( ! [X12,X10,X11] : (~l1_waybel_0(X10,sK0) | v2_struct_0(X10) | ~m1_subset_1(X11,u1_struct_0(X10)) | r2_hidden(k2_waybel_0(sK0,X10,sK4(sK0,X10,X12,X11)),X12) | ~r2_waybel_0(sK0,X10,X12)) )),
% 1.46/0.61    inference(subsumption_resolution,[],[f80,f35])).
% 1.46/0.61  fof(f80,plain,(
% 1.46/0.61    ( ! [X12,X10,X11] : (~l1_struct_0(sK0) | v2_struct_0(X10) | ~l1_waybel_0(X10,sK0) | ~m1_subset_1(X11,u1_struct_0(X10)) | r2_hidden(k2_waybel_0(sK0,X10,sK4(sK0,X10,X12,X11)),X12) | ~r2_waybel_0(sK0,X10,X12)) )),
% 1.46/0.61    inference(resolution,[],[f34,f44])).
% 1.46/0.61  fof(f44,plain,(
% 1.46/0.61    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~l1_struct_0(X0) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X3,u1_struct_0(X1)) | r2_hidden(k2_waybel_0(X0,X1,sK4(X0,X1,X2,X3)),X2) | ~r2_waybel_0(X0,X1,X2)) )),
% 1.46/0.61    inference(cnf_transformation,[],[f22])).
% 1.46/0.61  fof(f22,plain,(
% 1.46/0.61    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.46/0.61    inference(flattening,[],[f21])).
% 1.46/0.61  fof(f21,plain,(
% 1.46/0.61    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.46/0.61    inference(ennf_transformation,[],[f6])).
% 1.46/0.61  fof(f6,axiom,(
% 1.46/0.61    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1)))))))),
% 1.46/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_waybel_0)).
% 1.46/0.61  fof(f34,plain,(
% 1.46/0.61    ~v2_struct_0(sK0)),
% 1.46/0.61    inference(cnf_transformation,[],[f15])).
% 1.46/0.61  fof(f228,plain,(
% 1.46/0.61    ( ! [X0] : (r2_waybel_0(sK0,sK1,k6_subset_1(X0,X0))) )),
% 1.46/0.61    inference(subsumption_resolution,[],[f227,f29])).
% 1.46/0.61  fof(f227,plain,(
% 1.46/0.61    ( ! [X0] : (v2_struct_0(sK1) | r2_waybel_0(sK0,sK1,k6_subset_1(X0,X0))) )),
% 1.46/0.61    inference(subsumption_resolution,[],[f225,f32])).
% 1.46/0.61  fof(f225,plain,(
% 1.46/0.61    ( ! [X0] : (~l1_waybel_0(sK1,sK0) | v2_struct_0(sK1) | r2_waybel_0(sK0,sK1,k6_subset_1(X0,X0))) )),
% 1.46/0.61    inference(resolution,[],[f217,f83])).
% 1.46/0.61  fof(f83,plain,(
% 1.46/0.61    ( ! [X0,X1] : (r1_waybel_0(sK0,X0,k6_subset_1(u1_struct_0(sK0),X1)) | ~l1_waybel_0(X0,sK0) | v2_struct_0(X0) | r2_waybel_0(sK0,X0,X1)) )),
% 1.46/0.61    inference(subsumption_resolution,[],[f76,f35])).
% 1.46/0.61  fof(f76,plain,(
% 1.46/0.61    ( ! [X0,X1] : (~l1_struct_0(sK0) | v2_struct_0(X0) | ~l1_waybel_0(X0,sK0) | r1_waybel_0(sK0,X0,k6_subset_1(u1_struct_0(sK0),X1)) | r2_waybel_0(sK0,X0,X1)) )),
% 1.46/0.61    inference(resolution,[],[f34,f39])).
% 1.46/0.61  fof(f39,plain,(
% 1.46/0.61    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_struct_0(X0) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | r2_waybel_0(X0,X1,X2)) )),
% 1.46/0.61    inference(cnf_transformation,[],[f20])).
% 1.46/0.61  fof(f20,plain,(
% 1.46/0.61    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.46/0.61    inference(flattening,[],[f19])).
% 1.46/0.61  fof(f19,plain,(
% 1.46/0.61    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.46/0.61    inference(ennf_transformation,[],[f9])).
% 1.46/0.61  fof(f9,axiom,(
% 1.46/0.61    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)))))),
% 1.46/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_waybel_0)).
% 1.46/0.61  fof(f217,plain,(
% 1.46/0.61    ( ! [X0] : (~r1_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),k6_subset_1(X0,X0)))) )),
% 1.46/0.61    inference(resolution,[],[f216,f89])).
% 1.46/0.61  fof(f89,plain,(
% 1.46/0.61    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK0)) | ~r1_waybel_0(sK0,sK1,X0)) )),
% 1.46/0.61    inference(subsumption_resolution,[],[f88,f29])).
% 1.46/0.61  fof(f88,plain,(
% 1.46/0.61    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK0)) | ~r1_waybel_0(sK0,sK1,X0) | v2_struct_0(sK1)) )),
% 1.46/0.61    inference(subsumption_resolution,[],[f87,f32])).
% 1.46/0.61  fof(f87,plain,(
% 1.46/0.61    ( ! [X0] : (~l1_waybel_0(sK1,sK0) | ~r1_tarski(X0,u1_struct_0(sK0)) | ~r1_waybel_0(sK0,sK1,X0) | v2_struct_0(sK1)) )),
% 1.46/0.61    inference(resolution,[],[f86,f33])).
% 1.46/0.61  fof(f33,plain,(
% 1.46/0.61    ~r1_waybel_0(sK0,sK1,u1_struct_0(sK0))),
% 1.46/0.61    inference(cnf_transformation,[],[f15])).
% 1.46/0.61  fof(f86,plain,(
% 1.46/0.61    ( ! [X17,X18,X16] : (r1_waybel_0(sK0,X16,X18) | ~l1_waybel_0(X16,sK0) | ~r1_tarski(X17,X18) | ~r1_waybel_0(sK0,X16,X17) | v2_struct_0(X16)) )),
% 1.46/0.61    inference(subsumption_resolution,[],[f82,f35])).
% 1.46/0.61  fof(f82,plain,(
% 1.46/0.61    ( ! [X17,X18,X16] : (~l1_struct_0(sK0) | v2_struct_0(X16) | ~l1_waybel_0(X16,sK0) | ~r1_tarski(X17,X18) | ~r1_waybel_0(sK0,X16,X17) | r1_waybel_0(sK0,X16,X18)) )),
% 1.46/0.61    inference(resolution,[],[f34,f47])).
% 1.46/0.61  fof(f47,plain,(
% 1.46/0.61    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~l1_struct_0(X0) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | ~r1_tarski(X2,X3) | ~r1_waybel_0(X0,X1,X2) | r1_waybel_0(X0,X1,X3)) )),
% 1.46/0.61    inference(cnf_transformation,[],[f24])).
% 1.46/0.61  fof(f24,plain,(
% 1.46/0.61    ! [X0] : (! [X1] : (! [X2,X3] : (((r2_waybel_0(X0,X1,X3) | ~r2_waybel_0(X0,X1,X2)) & (r1_waybel_0(X0,X1,X3) | ~r1_waybel_0(X0,X1,X2))) | ~r1_tarski(X2,X3)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.46/0.61    inference(flattening,[],[f23])).
% 1.46/0.61  fof(f23,plain,(
% 1.46/0.61    ! [X0] : (! [X1] : (! [X2,X3] : (((r2_waybel_0(X0,X1,X3) | ~r2_waybel_0(X0,X1,X2)) & (r1_waybel_0(X0,X1,X3) | ~r1_waybel_0(X0,X1,X2))) | ~r1_tarski(X2,X3)) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.46/0.61    inference(ennf_transformation,[],[f10])).
% 1.46/0.61  fof(f10,axiom,(
% 1.46/0.61    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2,X3] : (r1_tarski(X2,X3) => ((r2_waybel_0(X0,X1,X2) => r2_waybel_0(X0,X1,X3)) & (r1_waybel_0(X0,X1,X2) => r1_waybel_0(X0,X1,X3))))))),
% 1.46/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_0)).
% 1.46/0.61  fof(f216,plain,(
% 1.46/0.61    ( ! [X0] : (r1_tarski(k6_subset_1(u1_struct_0(sK0),k6_subset_1(X0,X0)),u1_struct_0(sK0))) )),
% 1.46/0.61    inference(duplicate_literal_removal,[],[f215])).
% 1.46/0.61  fof(f215,plain,(
% 1.46/0.61    ( ! [X0] : (r1_tarski(k6_subset_1(u1_struct_0(sK0),k6_subset_1(X0,X0)),u1_struct_0(sK0)) | r1_tarski(k6_subset_1(u1_struct_0(sK0),k6_subset_1(X0,X0)),u1_struct_0(sK0))) )),
% 1.46/0.61    inference(resolution,[],[f188,f187])).
% 1.46/0.61  fof(f187,plain,(
% 1.46/0.61    ( ! [X6,X5] : (r2_hidden(k2_waybel_0(sK0,sK1,sK4(sK0,sK1,k6_subset_1(X5,X6),k4_yellow_6(sK1,sK2(sK1)))),X5) | r1_tarski(k6_subset_1(u1_struct_0(sK0),k6_subset_1(X5,X6)),u1_struct_0(sK0))) )),
% 1.46/0.61    inference(resolution,[],[f169,f68])).
% 1.46/0.61  fof(f169,plain,(
% 1.46/0.61    ( ! [X0] : (r2_hidden(k2_waybel_0(sK0,sK1,sK4(sK0,sK1,X0,k4_yellow_6(sK1,sK2(sK1)))),X0) | r1_tarski(k6_subset_1(u1_struct_0(sK0),X0),u1_struct_0(sK0))) )),
% 1.46/0.61    inference(resolution,[],[f163,f52])).
% 1.46/0.61  fof(f52,plain,(
% 1.46/0.61    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.46/0.61    inference(cnf_transformation,[],[f27])).
% 1.46/0.61  fof(f27,plain,(
% 1.46/0.61    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.46/0.61    inference(ennf_transformation,[],[f1])).
% 1.46/0.61  fof(f1,axiom,(
% 1.46/0.61    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.46/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.46/0.61  fof(f163,plain,(
% 1.46/0.61    ( ! [X0] : (r2_hidden(sK5(k6_subset_1(u1_struct_0(sK0),X0),u1_struct_0(sK0)),u1_struct_0(sK0)) | r2_hidden(k2_waybel_0(sK0,sK1,sK4(sK0,sK1,X0,k4_yellow_6(sK1,sK2(sK1)))),X0)) )),
% 1.46/0.61    inference(resolution,[],[f156,f68])).
% 1.46/0.61  fof(f156,plain,(
% 1.46/0.61    ( ! [X4] : (r2_hidden(sK5(k6_subset_1(u1_struct_0(sK0),X4),u1_struct_0(sK0)),k6_subset_1(u1_struct_0(sK0),X4)) | r2_hidden(k2_waybel_0(sK0,sK1,sK4(sK0,sK1,X4,k4_yellow_6(sK1,sK2(sK1)))),X4)) )),
% 1.46/0.61    inference(resolution,[],[f153,f94])).
% 1.46/0.61  fof(f94,plain,(
% 1.46/0.61    ( ! [X0] : (r2_waybel_0(sK0,sK1,X0) | r2_hidden(sK5(k6_subset_1(u1_struct_0(sK0),X0),u1_struct_0(sK0)),k6_subset_1(u1_struct_0(sK0),X0))) )),
% 1.46/0.61    inference(subsumption_resolution,[],[f93,f29])).
% 1.46/0.61  fof(f93,plain,(
% 1.46/0.61    ( ! [X0] : (r2_hidden(sK5(k6_subset_1(u1_struct_0(sK0),X0),u1_struct_0(sK0)),k6_subset_1(u1_struct_0(sK0),X0)) | v2_struct_0(sK1) | r2_waybel_0(sK0,sK1,X0)) )),
% 1.46/0.61    inference(subsumption_resolution,[],[f91,f32])).
% 1.46/0.61  fof(f91,plain,(
% 1.46/0.61    ( ! [X0] : (r2_hidden(sK5(k6_subset_1(u1_struct_0(sK0),X0),u1_struct_0(sK0)),k6_subset_1(u1_struct_0(sK0),X0)) | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK1) | r2_waybel_0(sK0,sK1,X0)) )),
% 1.46/0.61    inference(resolution,[],[f90,f83])).
% 1.46/0.61  fof(f90,plain,(
% 1.46/0.61    ( ! [X0] : (~r1_waybel_0(sK0,sK1,X0) | r2_hidden(sK5(X0,u1_struct_0(sK0)),X0)) )),
% 1.46/0.61    inference(resolution,[],[f89,f51])).
% 1.46/0.61  fof(f51,plain,(
% 1.46/0.61    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK5(X0,X1),X0)) )),
% 1.46/0.61    inference(cnf_transformation,[],[f27])).
% 1.46/0.61  fof(f188,plain,(
% 1.46/0.61    ( ! [X8,X7] : (~r2_hidden(k2_waybel_0(sK0,sK1,sK4(sK0,sK1,k6_subset_1(X7,X8),k4_yellow_6(sK1,sK2(sK1)))),X8) | r1_tarski(k6_subset_1(u1_struct_0(sK0),k6_subset_1(X7,X8)),u1_struct_0(sK0))) )),
% 1.46/0.61    inference(resolution,[],[f169,f67])).
% 1.46/0.61  fof(f67,plain,(
% 1.46/0.61    ( ! [X0,X3,X1] : (~r2_hidden(X3,k6_subset_1(X0,X1)) | ~r2_hidden(X3,X1)) )),
% 1.46/0.61    inference(equality_resolution,[],[f61])).
% 1.46/0.61  fof(f61,plain,(
% 1.46/0.61    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k6_subset_1(X0,X1) != X2) )),
% 1.46/0.61    inference(definition_unfolding,[],[f58,f48])).
% 1.46/0.61  fof(f58,plain,(
% 1.46/0.61    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.46/0.61    inference(cnf_transformation,[],[f2])).
% 1.46/0.61  fof(f258,plain,(
% 1.46/0.61    ( ! [X1] : (~r2_hidden(k2_waybel_0(sK0,sK1,sK4(sK0,sK1,k6_subset_1(X1,X1),k4_yellow_6(sK1,sK2(sK1)))),X1)) )),
% 1.46/0.61    inference(resolution,[],[f231,f67])).
% 1.46/0.61  % SZS output end Proof for theBenchmark
% 1.46/0.61  % (9541)------------------------------
% 1.46/0.61  % (9541)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.61  % (9541)Termination reason: Refutation
% 1.46/0.61  
% 1.46/0.61  % (9541)Memory used [KB]: 1918
% 1.46/0.61  % (9541)Time elapsed: 0.180 s
% 1.46/0.61  % (9541)------------------------------
% 1.46/0.61  % (9541)------------------------------
% 1.46/0.61  % (9519)Success in time 0.255 s
%------------------------------------------------------------------------------
