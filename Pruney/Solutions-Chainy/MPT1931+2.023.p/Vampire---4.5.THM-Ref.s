%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:40 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 703 expanded)
%              Number of leaves         :    9 ( 136 expanded)
%              Depth                    :   30
%              Number of atoms          :  259 (3499 expanded)
%              Number of equality atoms :    7 (  50 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f406,plain,(
    $false ),
    inference(subsumption_resolution,[],[f377,f376])).

fof(f376,plain,(
    ! [X0] : r2_hidden(sK6(k6_subset_1(X0,X0)),X0) ),
    inference(resolution,[],[f373,f58])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k6_subset_1(X0,X1))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k6_subset_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f47,f38])).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f47,plain,(
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

fof(f373,plain,(
    ! [X4] : r2_hidden(sK6(k6_subset_1(X4,X4)),k6_subset_1(X4,X4)) ),
    inference(resolution,[],[f367,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(sK6(X1),X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

fof(f367,plain,(
    ! [X7] : r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,k6_subset_1(X7,X7),sK4(u1_struct_0(sK1)))),k6_subset_1(X7,X7)) ),
    inference(resolution,[],[f245,f37])).

fof(f37,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f245,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK1))
      | r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,k6_subset_1(X0,X0),X1)),k6_subset_1(X0,X0)) ) ),
    inference(resolution,[],[f244,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ r2_waybel_0(sK0,sK1,X1)
      | r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,X1,X0)),X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f116,f21])).

fof(f21,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
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

fof(f116,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,X1,X0)),X1)
      | ~ r2_waybel_0(sK0,sK1,X1) ) ),
    inference(resolution,[],[f71,f24])).

fof(f24,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f71,plain,(
    ! [X12,X10,X11] :
      ( ~ l1_waybel_0(X10,sK0)
      | v2_struct_0(X10)
      | ~ m1_subset_1(X11,u1_struct_0(X10))
      | r2_hidden(k2_waybel_0(sK0,X10,sK3(sK0,X10,X12,X11)),X12)
      | ~ r2_waybel_0(sK0,X10,X12) ) ),
    inference(subsumption_resolution,[],[f64,f26])).

fof(f26,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f64,plain,(
    ! [X12,X10,X11] :
      ( v2_struct_0(sK0)
      | v2_struct_0(X10)
      | ~ l1_waybel_0(X10,sK0)
      | ~ m1_subset_1(X11,u1_struct_0(X10))
      | r2_hidden(k2_waybel_0(sK0,X10,sK3(sK0,X10,X12,X11)),X12)
      | ~ r2_waybel_0(sK0,X10,X12) ) ),
    inference(resolution,[],[f27,f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X3)),X2)
      | ~ r2_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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

fof(f27,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f244,plain,(
    ! [X2] : r2_waybel_0(sK0,sK1,k6_subset_1(X2,X2)) ),
    inference(subsumption_resolution,[],[f243,f21])).

fof(f243,plain,(
    ! [X2] :
      ( v2_struct_0(sK1)
      | r2_waybel_0(sK0,sK1,k6_subset_1(X2,X2)) ) ),
    inference(subsumption_resolution,[],[f242,f24])).

fof(f242,plain,(
    ! [X2] :
      ( ~ l1_waybel_0(sK1,sK0)
      | v2_struct_0(sK1)
      | r2_waybel_0(sK0,sK1,k6_subset_1(X2,X2)) ) ),
    inference(resolution,[],[f233,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_waybel_0(sK0,X0,k6_subset_1(u1_struct_0(sK0),X1))
      | ~ l1_waybel_0(X0,sK0)
      | v2_struct_0(X0)
      | r2_waybel_0(sK0,X0,X1) ) ),
    inference(subsumption_resolution,[],[f60,f26])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(X0,sK0)
      | r1_waybel_0(sK0,X0,k6_subset_1(u1_struct_0(sK0),X1))
      | r2_waybel_0(sK0,X0,X1) ) ),
    inference(resolution,[],[f27,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
      | r2_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f233,plain,(
    ! [X2] : ~ r1_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),k6_subset_1(X2,X2))) ),
    inference(resolution,[],[f230,f76])).

fof(f76,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,u1_struct_0(sK0))
      | ~ r1_waybel_0(sK0,sK1,X0) ) ),
    inference(resolution,[],[f75,f25])).

fof(f25,plain,(
    ~ r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_waybel_0(sK0,sK1,X1)
      | ~ r1_waybel_0(sK0,sK1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(subsumption_resolution,[],[f74,f21])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK1)
      | ~ r1_tarski(X0,X1)
      | ~ r1_waybel_0(sK0,sK1,X0)
      | r1_waybel_0(sK0,sK1,X1) ) ),
    inference(resolution,[],[f73,f24])).

fof(f73,plain,(
    ! [X17,X18,X16] :
      ( ~ l1_waybel_0(X16,sK0)
      | v2_struct_0(X16)
      | ~ r1_tarski(X17,X18)
      | ~ r1_waybel_0(sK0,X16,X17)
      | r1_waybel_0(sK0,X16,X18) ) ),
    inference(subsumption_resolution,[],[f66,f26])).

fof(f66,plain,(
    ! [X17,X18,X16] :
      ( v2_struct_0(sK0)
      | v2_struct_0(X16)
      | ~ l1_waybel_0(X16,sK0)
      | ~ r1_tarski(X17,X18)
      | ~ r1_waybel_0(sK0,X16,X17)
      | r1_waybel_0(sK0,X16,X18) ) ),
    inference(resolution,[],[f27,f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ r1_tarski(X2,X3)
      | ~ r1_waybel_0(X0,X1,X2)
      | r1_waybel_0(X0,X1,X3) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f230,plain,(
    ! [X0] : r1_tarski(k6_subset_1(u1_struct_0(sK0),k6_subset_1(X0,X0)),u1_struct_0(sK0)) ),
    inference(duplicate_literal_removal,[],[f229])).

fof(f229,plain,(
    ! [X0] :
      ( r1_tarski(k6_subset_1(u1_struct_0(sK0),k6_subset_1(X0,X0)),u1_struct_0(sK0))
      | r1_tarski(k6_subset_1(u1_struct_0(sK0),k6_subset_1(X0,X0)),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f207,f206])).

fof(f206,plain,(
    ! [X6,X5] :
      ( r2_hidden(sK6(k6_subset_1(X5,X6)),X5)
      | r1_tarski(k6_subset_1(u1_struct_0(sK0),k6_subset_1(X5,X6)),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f195,f58])).

fof(f195,plain,(
    ! [X2] :
      ( r2_hidden(sK6(X2),X2)
      | r1_tarski(k6_subset_1(u1_struct_0(sK0),X2),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f144,f43])).

fof(f144,plain,(
    ! [X0] :
      ( r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,X0,sK4(u1_struct_0(sK1)))),X0)
      | r1_tarski(k6_subset_1(u1_struct_0(sK0),X0),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f135,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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

fof(f135,plain,(
    ! [X0] :
      ( r2_hidden(sK5(k6_subset_1(u1_struct_0(sK0),X0),u1_struct_0(sK0)),u1_struct_0(sK0))
      | r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,X0,sK4(u1_struct_0(sK1)))),X0) ) ),
    inference(resolution,[],[f132,f58])).

fof(f132,plain,(
    ! [X7] :
      ( r2_hidden(sK5(k6_subset_1(u1_struct_0(sK0),X7),u1_struct_0(sK0)),k6_subset_1(u1_struct_0(sK0),X7))
      | r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,X7,sK4(u1_struct_0(sK1)))),X7) ) ),
    inference(resolution,[],[f120,f37])).

fof(f120,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X7,u1_struct_0(sK1))
      | r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,X6,X7)),X6)
      | r2_hidden(sK5(k6_subset_1(u1_struct_0(sK0),X6),u1_struct_0(sK0)),k6_subset_1(u1_struct_0(sK0),X6)) ) ),
    inference(resolution,[],[f117,f81])).

fof(f81,plain,(
    ! [X2] :
      ( r2_waybel_0(sK0,sK1,X2)
      | r2_hidden(sK5(k6_subset_1(u1_struct_0(sK0),X2),u1_struct_0(sK0)),k6_subset_1(u1_struct_0(sK0),X2)) ) ),
    inference(subsumption_resolution,[],[f80,f21])).

fof(f80,plain,(
    ! [X2] :
      ( r2_hidden(sK5(k6_subset_1(u1_struct_0(sK0),X2),u1_struct_0(sK0)),k6_subset_1(u1_struct_0(sK0),X2))
      | v2_struct_0(sK1)
      | r2_waybel_0(sK0,sK1,X2) ) ),
    inference(subsumption_resolution,[],[f79,f24])).

fof(f79,plain,(
    ! [X2] :
      ( r2_hidden(sK5(k6_subset_1(u1_struct_0(sK0),X2),u1_struct_0(sK0)),k6_subset_1(u1_struct_0(sK0),X2))
      | ~ l1_waybel_0(sK1,sK0)
      | v2_struct_0(sK1)
      | r2_waybel_0(sK0,sK1,X2) ) ),
    inference(resolution,[],[f77,f67])).

fof(f77,plain,(
    ! [X0] :
      ( ~ r1_waybel_0(sK0,sK1,X0)
      | r2_hidden(sK5(X0,u1_struct_0(sK0)),X0) ) ),
    inference(resolution,[],[f76,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f207,plain,(
    ! [X8,X7] :
      ( ~ r2_hidden(sK6(k6_subset_1(X7,X8)),X8)
      | r1_tarski(k6_subset_1(u1_struct_0(sK0),k6_subset_1(X7,X8)),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f195,f57])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k6_subset_1(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k6_subset_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f48,f38])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f377,plain,(
    ! [X1] : ~ r2_hidden(sK6(k6_subset_1(X1,X1)),X1) ),
    inference(resolution,[],[f373,f57])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:54:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.52  % (27651)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (27652)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (27653)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (27650)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (27650)Refutation not found, incomplete strategy% (27650)------------------------------
% 0.21/0.53  % (27650)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (27650)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (27650)Memory used [KB]: 1663
% 0.21/0.53  % (27650)Time elapsed: 0.002 s
% 0.21/0.53  % (27650)------------------------------
% 0.21/0.53  % (27650)------------------------------
% 0.21/0.53  % (27681)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (27673)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (27655)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (27677)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (27654)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (27675)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (27663)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (27674)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (27676)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (27679)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (27666)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (27665)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (27671)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (27668)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (27656)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (27661)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (27659)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (27661)Refutation not found, incomplete strategy% (27661)------------------------------
% 0.21/0.55  % (27661)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (27661)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (27661)Memory used [KB]: 10618
% 0.21/0.55  % (27661)Time elapsed: 0.138 s
% 0.21/0.55  % (27661)------------------------------
% 0.21/0.55  % (27661)------------------------------
% 0.21/0.55  % (27667)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (27660)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (27659)Refutation not found, incomplete strategy% (27659)------------------------------
% 0.21/0.55  % (27659)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (27659)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (27659)Memory used [KB]: 10746
% 0.21/0.55  % (27659)Time elapsed: 0.138 s
% 0.21/0.55  % (27659)------------------------------
% 0.21/0.55  % (27659)------------------------------
% 0.21/0.55  % (27660)Refutation not found, incomplete strategy% (27660)------------------------------
% 0.21/0.55  % (27660)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (27660)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (27660)Memory used [KB]: 10618
% 0.21/0.55  % (27660)Time elapsed: 0.001 s
% 0.21/0.55  % (27660)------------------------------
% 0.21/0.55  % (27660)------------------------------
% 0.21/0.55  % (27669)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (27669)Refutation not found, incomplete strategy% (27669)------------------------------
% 0.21/0.55  % (27669)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (27662)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (27669)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (27669)Memory used [KB]: 10618
% 0.21/0.55  % (27669)Time elapsed: 0.137 s
% 0.21/0.55  % (27669)------------------------------
% 0.21/0.55  % (27669)------------------------------
% 0.21/0.55  % (27670)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (27662)Refutation not found, incomplete strategy% (27662)------------------------------
% 0.21/0.55  % (27662)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (27662)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (27662)Memory used [KB]: 10618
% 0.21/0.55  % (27662)Time elapsed: 0.139 s
% 0.21/0.55  % (27662)------------------------------
% 0.21/0.55  % (27662)------------------------------
% 0.21/0.55  % (27677)Refutation not found, incomplete strategy% (27677)------------------------------
% 0.21/0.55  % (27677)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (27680)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (27677)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (27677)Memory used [KB]: 6268
% 0.21/0.55  % (27677)Time elapsed: 0.139 s
% 0.21/0.55  % (27677)------------------------------
% 0.21/0.55  % (27677)------------------------------
% 0.21/0.55  % (27678)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.56  % (27678)Refutation not found, incomplete strategy% (27678)------------------------------
% 0.21/0.56  % (27678)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (27678)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (27678)Memory used [KB]: 10746
% 0.21/0.56  % (27678)Time elapsed: 0.147 s
% 0.21/0.56  % (27678)------------------------------
% 0.21/0.56  % (27678)------------------------------
% 0.21/0.56  % (27658)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.56  % (27672)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.56  % (27673)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.56  % SZS output start Proof for theBenchmark
% 0.21/0.56  fof(f406,plain,(
% 0.21/0.56    $false),
% 0.21/0.56    inference(subsumption_resolution,[],[f377,f376])).
% 0.21/0.56  fof(f376,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(sK6(k6_subset_1(X0,X0)),X0)) )),
% 0.21/0.56    inference(resolution,[],[f373,f58])).
% 0.21/0.56  fof(f58,plain,(
% 0.21/0.56    ( ! [X0,X3,X1] : (~r2_hidden(X3,k6_subset_1(X0,X1)) | r2_hidden(X3,X0)) )),
% 0.21/0.56    inference(equality_resolution,[],[f52])).
% 0.21/0.56  fof(f52,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k6_subset_1(X0,X1) != X2) )),
% 0.21/0.56    inference(definition_unfolding,[],[f47,f38])).
% 0.21/0.56  fof(f38,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f5])).
% 0.21/0.56  fof(f5,axiom,(
% 0.21/0.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.21/0.56  fof(f47,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.56    inference(cnf_transformation,[],[f2])).
% 0.21/0.56  fof(f2,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.21/0.56  fof(f373,plain,(
% 0.21/0.56    ( ! [X4] : (r2_hidden(sK6(k6_subset_1(X4,X4)),k6_subset_1(X4,X4))) )),
% 0.21/0.56    inference(resolution,[],[f367,f43])).
% 0.21/0.56  fof(f43,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r2_hidden(sK6(X1),X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f20])).
% 0.21/0.56  fof(f20,plain,(
% 0.21/0.56    ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.56    inference(ennf_transformation,[],[f3])).
% 0.21/0.56  fof(f3,axiom,(
% 0.21/0.56    ! [X0,X1] : ~(! [X2] : ~(! [X3] : ~(r2_hidden(X3,X2) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).
% 0.21/0.56  fof(f367,plain,(
% 0.21/0.56    ( ! [X7] : (r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,k6_subset_1(X7,X7),sK4(u1_struct_0(sK1)))),k6_subset_1(X7,X7))) )),
% 0.21/0.56    inference(resolution,[],[f245,f37])).
% 0.21/0.56  fof(f37,plain,(
% 0.21/0.56    ( ! [X0] : (m1_subset_1(sK4(X0),X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f4])).
% 0.21/0.56  fof(f4,axiom,(
% 0.21/0.56    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 0.21/0.56  fof(f245,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK1)) | r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,k6_subset_1(X0,X0),X1)),k6_subset_1(X0,X0))) )),
% 0.21/0.56    inference(resolution,[],[f244,f117])).
% 0.21/0.56  fof(f117,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r2_waybel_0(sK0,sK1,X1) | r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,X1,X0)),X1) | ~m1_subset_1(X0,u1_struct_0(sK1))) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f116,f21])).
% 0.21/0.56  fof(f21,plain,(
% 0.21/0.56    ~v2_struct_0(sK1)),
% 0.21/0.56    inference(cnf_transformation,[],[f12])).
% 0.21/0.56  fof(f12,plain,(
% 0.21/0.56    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 0.21/0.56    inference(flattening,[],[f11])).
% 0.21/0.56  fof(f11,plain,(
% 0.21/0.56    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & (l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f10])).
% 0.21/0.56  fof(f10,negated_conjecture,(
% 0.21/0.56    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 0.21/0.56    inference(negated_conjecture,[],[f9])).
% 0.21/0.56  fof(f9,conjecture,(
% 0.21/0.56    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_yellow_6)).
% 0.21/0.56  fof(f116,plain,(
% 0.21/0.56    ( ! [X0,X1] : (v2_struct_0(sK1) | ~m1_subset_1(X0,u1_struct_0(sK1)) | r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,X1,X0)),X1) | ~r2_waybel_0(sK0,sK1,X1)) )),
% 0.21/0.56    inference(resolution,[],[f71,f24])).
% 0.21/0.56  fof(f24,plain,(
% 0.21/0.56    l1_waybel_0(sK1,sK0)),
% 0.21/0.56    inference(cnf_transformation,[],[f12])).
% 0.21/0.56  fof(f71,plain,(
% 0.21/0.56    ( ! [X12,X10,X11] : (~l1_waybel_0(X10,sK0) | v2_struct_0(X10) | ~m1_subset_1(X11,u1_struct_0(X10)) | r2_hidden(k2_waybel_0(sK0,X10,sK3(sK0,X10,X12,X11)),X12) | ~r2_waybel_0(sK0,X10,X12)) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f64,f26])).
% 0.21/0.56  fof(f26,plain,(
% 0.21/0.56    ~v2_struct_0(sK0)),
% 0.21/0.56    inference(cnf_transformation,[],[f12])).
% 0.21/0.56  fof(f64,plain,(
% 0.21/0.56    ( ! [X12,X10,X11] : (v2_struct_0(sK0) | v2_struct_0(X10) | ~l1_waybel_0(X10,sK0) | ~m1_subset_1(X11,u1_struct_0(X10)) | r2_hidden(k2_waybel_0(sK0,X10,sK3(sK0,X10,X12,X11)),X12) | ~r2_waybel_0(sK0,X10,X12)) )),
% 0.21/0.56    inference(resolution,[],[f27,f33])).
% 0.21/0.56  fof(f33,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (~l1_struct_0(X0) | v2_struct_0(X0) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X3,u1_struct_0(X1)) | r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X3)),X2) | ~r2_waybel_0(X0,X1,X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f16])).
% 0.21/0.56  fof(f16,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.56    inference(flattening,[],[f15])).
% 0.21/0.56  fof(f15,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f6])).
% 0.21/0.56  fof(f6,axiom,(
% 0.21/0.56    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1)))))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_waybel_0)).
% 0.21/0.56  fof(f27,plain,(
% 0.21/0.56    l1_struct_0(sK0)),
% 0.21/0.56    inference(cnf_transformation,[],[f12])).
% 0.21/0.56  fof(f244,plain,(
% 0.21/0.56    ( ! [X2] : (r2_waybel_0(sK0,sK1,k6_subset_1(X2,X2))) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f243,f21])).
% 0.21/0.56  fof(f243,plain,(
% 0.21/0.56    ( ! [X2] : (v2_struct_0(sK1) | r2_waybel_0(sK0,sK1,k6_subset_1(X2,X2))) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f242,f24])).
% 0.21/0.56  fof(f242,plain,(
% 0.21/0.56    ( ! [X2] : (~l1_waybel_0(sK1,sK0) | v2_struct_0(sK1) | r2_waybel_0(sK0,sK1,k6_subset_1(X2,X2))) )),
% 0.21/0.56    inference(resolution,[],[f233,f67])).
% 0.21/0.56  fof(f67,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r1_waybel_0(sK0,X0,k6_subset_1(u1_struct_0(sK0),X1)) | ~l1_waybel_0(X0,sK0) | v2_struct_0(X0) | r2_waybel_0(sK0,X0,X1)) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f60,f26])).
% 0.21/0.56  fof(f60,plain,(
% 0.21/0.56    ( ! [X0,X1] : (v2_struct_0(sK0) | v2_struct_0(X0) | ~l1_waybel_0(X0,sK0) | r1_waybel_0(sK0,X0,k6_subset_1(u1_struct_0(sK0),X1)) | r2_waybel_0(sK0,X0,X1)) )),
% 0.21/0.56    inference(resolution,[],[f27,f28])).
% 0.21/0.56  fof(f28,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~l1_struct_0(X0) | v2_struct_0(X0) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | r2_waybel_0(X0,X1,X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f14])).
% 0.21/0.56  fof(f14,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.56    inference(flattening,[],[f13])).
% 0.21/0.56  fof(f13,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f7])).
% 0.21/0.56  fof(f7,axiom,(
% 0.21/0.56    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_waybel_0)).
% 0.21/0.56  fof(f233,plain,(
% 0.21/0.56    ( ! [X2] : (~r1_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),k6_subset_1(X2,X2)))) )),
% 0.21/0.56    inference(resolution,[],[f230,f76])).
% 0.21/0.56  fof(f76,plain,(
% 0.21/0.56    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK0)) | ~r1_waybel_0(sK0,sK1,X0)) )),
% 0.21/0.56    inference(resolution,[],[f75,f25])).
% 0.21/0.56  fof(f25,plain,(
% 0.21/0.56    ~r1_waybel_0(sK0,sK1,u1_struct_0(sK0))),
% 0.21/0.56    inference(cnf_transformation,[],[f12])).
% 0.21/0.56  fof(f75,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r1_waybel_0(sK0,sK1,X1) | ~r1_waybel_0(sK0,sK1,X0) | ~r1_tarski(X0,X1)) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f74,f21])).
% 0.21/0.56  fof(f74,plain,(
% 0.21/0.56    ( ! [X0,X1] : (v2_struct_0(sK1) | ~r1_tarski(X0,X1) | ~r1_waybel_0(sK0,sK1,X0) | r1_waybel_0(sK0,sK1,X1)) )),
% 0.21/0.56    inference(resolution,[],[f73,f24])).
% 0.21/0.56  fof(f73,plain,(
% 0.21/0.56    ( ! [X17,X18,X16] : (~l1_waybel_0(X16,sK0) | v2_struct_0(X16) | ~r1_tarski(X17,X18) | ~r1_waybel_0(sK0,X16,X17) | r1_waybel_0(sK0,X16,X18)) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f66,f26])).
% 0.21/0.56  fof(f66,plain,(
% 0.21/0.56    ( ! [X17,X18,X16] : (v2_struct_0(sK0) | v2_struct_0(X16) | ~l1_waybel_0(X16,sK0) | ~r1_tarski(X17,X18) | ~r1_waybel_0(sK0,X16,X17) | r1_waybel_0(sK0,X16,X18)) )),
% 0.21/0.56    inference(resolution,[],[f27,f36])).
% 0.21/0.56  fof(f36,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (~l1_struct_0(X0) | v2_struct_0(X0) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | ~r1_tarski(X2,X3) | ~r1_waybel_0(X0,X1,X2) | r1_waybel_0(X0,X1,X3)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f18])).
% 0.21/0.56  fof(f18,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (! [X2,X3] : (((r2_waybel_0(X0,X1,X3) | ~r2_waybel_0(X0,X1,X2)) & (r1_waybel_0(X0,X1,X3) | ~r1_waybel_0(X0,X1,X2))) | ~r1_tarski(X2,X3)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.56    inference(flattening,[],[f17])).
% 0.21/0.56  fof(f17,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (! [X2,X3] : (((r2_waybel_0(X0,X1,X3) | ~r2_waybel_0(X0,X1,X2)) & (r1_waybel_0(X0,X1,X3) | ~r1_waybel_0(X0,X1,X2))) | ~r1_tarski(X2,X3)) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f8])).
% 0.21/0.56  fof(f8,axiom,(
% 0.21/0.56    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2,X3] : (r1_tarski(X2,X3) => ((r2_waybel_0(X0,X1,X2) => r2_waybel_0(X0,X1,X3)) & (r1_waybel_0(X0,X1,X2) => r1_waybel_0(X0,X1,X3))))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_0)).
% 0.21/0.56  fof(f230,plain,(
% 0.21/0.56    ( ! [X0] : (r1_tarski(k6_subset_1(u1_struct_0(sK0),k6_subset_1(X0,X0)),u1_struct_0(sK0))) )),
% 0.21/0.56    inference(duplicate_literal_removal,[],[f229])).
% 0.21/0.56  fof(f229,plain,(
% 0.21/0.56    ( ! [X0] : (r1_tarski(k6_subset_1(u1_struct_0(sK0),k6_subset_1(X0,X0)),u1_struct_0(sK0)) | r1_tarski(k6_subset_1(u1_struct_0(sK0),k6_subset_1(X0,X0)),u1_struct_0(sK0))) )),
% 0.21/0.56    inference(resolution,[],[f207,f206])).
% 0.21/0.56  fof(f206,plain,(
% 0.21/0.56    ( ! [X6,X5] : (r2_hidden(sK6(k6_subset_1(X5,X6)),X5) | r1_tarski(k6_subset_1(u1_struct_0(sK0),k6_subset_1(X5,X6)),u1_struct_0(sK0))) )),
% 0.21/0.56    inference(resolution,[],[f195,f58])).
% 0.21/0.56  fof(f195,plain,(
% 0.21/0.56    ( ! [X2] : (r2_hidden(sK6(X2),X2) | r1_tarski(k6_subset_1(u1_struct_0(sK0),X2),u1_struct_0(sK0))) )),
% 0.21/0.56    inference(resolution,[],[f144,f43])).
% 0.21/0.56  fof(f144,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,X0,sK4(u1_struct_0(sK1)))),X0) | r1_tarski(k6_subset_1(u1_struct_0(sK0),X0),u1_struct_0(sK0))) )),
% 0.21/0.56    inference(resolution,[],[f135,f41])).
% 0.21/0.56  fof(f41,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f19])).
% 0.21/0.56  fof(f19,plain,(
% 0.21/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f1])).
% 0.21/0.56  fof(f1,axiom,(
% 0.21/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.56  fof(f135,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(sK5(k6_subset_1(u1_struct_0(sK0),X0),u1_struct_0(sK0)),u1_struct_0(sK0)) | r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,X0,sK4(u1_struct_0(sK1)))),X0)) )),
% 0.21/0.56    inference(resolution,[],[f132,f58])).
% 0.21/0.56  fof(f132,plain,(
% 0.21/0.56    ( ! [X7] : (r2_hidden(sK5(k6_subset_1(u1_struct_0(sK0),X7),u1_struct_0(sK0)),k6_subset_1(u1_struct_0(sK0),X7)) | r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,X7,sK4(u1_struct_0(sK1)))),X7)) )),
% 0.21/0.56    inference(resolution,[],[f120,f37])).
% 0.21/0.56  fof(f120,plain,(
% 0.21/0.56    ( ! [X6,X7] : (~m1_subset_1(X7,u1_struct_0(sK1)) | r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,X6,X7)),X6) | r2_hidden(sK5(k6_subset_1(u1_struct_0(sK0),X6),u1_struct_0(sK0)),k6_subset_1(u1_struct_0(sK0),X6))) )),
% 0.21/0.56    inference(resolution,[],[f117,f81])).
% 0.21/0.56  fof(f81,plain,(
% 0.21/0.56    ( ! [X2] : (r2_waybel_0(sK0,sK1,X2) | r2_hidden(sK5(k6_subset_1(u1_struct_0(sK0),X2),u1_struct_0(sK0)),k6_subset_1(u1_struct_0(sK0),X2))) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f80,f21])).
% 0.21/0.56  fof(f80,plain,(
% 0.21/0.56    ( ! [X2] : (r2_hidden(sK5(k6_subset_1(u1_struct_0(sK0),X2),u1_struct_0(sK0)),k6_subset_1(u1_struct_0(sK0),X2)) | v2_struct_0(sK1) | r2_waybel_0(sK0,sK1,X2)) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f79,f24])).
% 0.21/0.56  fof(f79,plain,(
% 0.21/0.56    ( ! [X2] : (r2_hidden(sK5(k6_subset_1(u1_struct_0(sK0),X2),u1_struct_0(sK0)),k6_subset_1(u1_struct_0(sK0),X2)) | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK1) | r2_waybel_0(sK0,sK1,X2)) )),
% 0.21/0.56    inference(resolution,[],[f77,f67])).
% 0.21/0.56  fof(f77,plain,(
% 0.21/0.56    ( ! [X0] : (~r1_waybel_0(sK0,sK1,X0) | r2_hidden(sK5(X0,u1_struct_0(sK0)),X0)) )),
% 0.21/0.56    inference(resolution,[],[f76,f40])).
% 0.21/0.56  fof(f40,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK5(X0,X1),X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f19])).
% 0.21/0.56  fof(f207,plain,(
% 0.21/0.56    ( ! [X8,X7] : (~r2_hidden(sK6(k6_subset_1(X7,X8)),X8) | r1_tarski(k6_subset_1(u1_struct_0(sK0),k6_subset_1(X7,X8)),u1_struct_0(sK0))) )),
% 0.21/0.56    inference(resolution,[],[f195,f57])).
% 0.21/0.56  fof(f57,plain,(
% 0.21/0.56    ( ! [X0,X3,X1] : (~r2_hidden(X3,k6_subset_1(X0,X1)) | ~r2_hidden(X3,X1)) )),
% 0.21/0.56    inference(equality_resolution,[],[f51])).
% 0.21/0.56  fof(f51,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k6_subset_1(X0,X1) != X2) )),
% 0.21/0.56    inference(definition_unfolding,[],[f48,f38])).
% 0.21/0.56  fof(f48,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.56    inference(cnf_transformation,[],[f2])).
% 0.21/0.56  fof(f377,plain,(
% 0.21/0.56    ( ! [X1] : (~r2_hidden(sK6(k6_subset_1(X1,X1)),X1)) )),
% 0.21/0.56    inference(resolution,[],[f373,f57])).
% 0.21/0.56  % SZS output end Proof for theBenchmark
% 0.21/0.56  % (27673)------------------------------
% 0.21/0.56  % (27673)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (27673)Termination reason: Refutation
% 0.21/0.56  
% 0.21/0.56  % (27673)Memory used [KB]: 1918
% 0.21/0.56  % (27673)Time elapsed: 0.129 s
% 0.21/0.56  % (27673)------------------------------
% 0.21/0.56  % (27673)------------------------------
% 0.21/0.56  % (27642)Success in time 0.2 s
%------------------------------------------------------------------------------
