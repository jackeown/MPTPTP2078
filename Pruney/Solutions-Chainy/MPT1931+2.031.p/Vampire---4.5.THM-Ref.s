%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:41 EST 2020

% Result     : Theorem 1.51s
% Output     : Refutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 210 expanded)
%              Number of leaves         :    6 (  52 expanded)
%              Depth                    :   15
%              Number of atoms          :  237 ( 876 expanded)
%              Number of equality atoms :   28 (  94 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1227,plain,(
    $false ),
    inference(global_subsumption,[],[f20,f1226])).

fof(f1226,plain,(
    r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f1216,f347])).

fof(f347,plain,(
    ! [X2,X3] : k6_subset_1(X2,k6_subset_1(X3,X3)) = X2 ),
    inference(duplicate_literal_removal,[],[f331])).

fof(f331,plain,(
    ! [X2,X3] :
      ( k6_subset_1(X2,k6_subset_1(X3,X3)) = X2
      | k6_subset_1(X2,k6_subset_1(X3,X3)) = X2 ) ),
    inference(resolution,[],[f266,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1,X0),X0)
      | k6_subset_1(X0,X1) = X0 ) ),
    inference(factoring,[],[f51])).

fof(f51,plain,(
    ! [X6,X8,X7] :
      ( r2_hidden(sK4(X6,X7,X8),X8)
      | k6_subset_1(X6,X7) = X8
      | r2_hidden(sK4(X6,X7,X8),X6) ) ),
    inference(resolution,[],[f40,f33])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( ~ sP5(X3,X1,X0)
      | r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( sP5(sK4(X0,X1,X2),X1,X0)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | k6_subset_1(X0,X1) = X2 ) ),
    inference(definition_unfolding,[],[f37,f30])).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( sP5(sK4(X0,X1,X2),X1,X0)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f266,plain,(
    ! [X14,X15,X16] :
      ( ~ r2_hidden(sK4(X14,k6_subset_1(X15,X15),X14),X16)
      | k6_subset_1(X14,k6_subset_1(X15,X15)) = X14 ) ),
    inference(resolution,[],[f256,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k6_subset_1(X1,X1))
      | ~ r2_hidden(X0,X2) ) ),
    inference(resolution,[],[f77,f34])).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( ~ sP5(X3,X1,X0)
      | ~ r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f77,plain,(
    ! [X14,X12,X13] :
      ( sP5(X14,X13,k6_subset_1(X12,X12))
      | ~ r2_hidden(X14,k6_subset_1(X12,X12)) ) ),
    inference(superposition,[],[f43,f71])).

fof(f71,plain,(
    ! [X0,X1] : k6_subset_1(X0,X0) = k6_subset_1(k6_subset_1(X0,X0),X1) ),
    inference(duplicate_literal_removal,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k6_subset_1(X0,X0) = k6_subset_1(k6_subset_1(X0,X0),X1)
      | k6_subset_1(X0,X0) = k6_subset_1(k6_subset_1(X0,X0),X1) ) ),
    inference(resolution,[],[f65,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(k6_subset_1(X0,X1),X2,k6_subset_1(X0,X1)),X1)
      | k6_subset_1(X0,X1) = k6_subset_1(k6_subset_1(X0,X1),X2) ) ),
    inference(resolution,[],[f59,f34])).

fof(f59,plain,(
    ! [X2,X3,X1] :
      ( sP5(sK4(k6_subset_1(X1,X2),X3,k6_subset_1(X1,X2)),X2,X1)
      | k6_subset_1(X1,X2) = k6_subset_1(k6_subset_1(X1,X2),X3) ) ),
    inference(resolution,[],[f56,f43])).

fof(f65,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(sK4(k6_subset_1(X3,X4),X5,k6_subset_1(X3,X4)),X3)
      | k6_subset_1(X3,X4) = k6_subset_1(k6_subset_1(X3,X4),X5) ) ),
    inference(resolution,[],[f59,f33])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k6_subset_1(X0,X1))
      | sP5(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( sP5(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k6_subset_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f36,f30])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( sP5(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f256,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK4(X2,X3,X2),X3)
      | k6_subset_1(X2,X3) = X2 ) ),
    inference(duplicate_literal_removal,[],[f249])).

fof(f249,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK4(X2,X3,X2),X3)
      | k6_subset_1(X2,X3) = X2
      | k6_subset_1(X2,X3) = X2 ) ),
    inference(resolution,[],[f187,f56])).

fof(f187,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(sK4(X3,X4,X3),X3)
      | r2_hidden(sK4(X3,X4,X3),X4)
      | k6_subset_1(X3,X4) = X3 ) ),
    inference(duplicate_literal_removal,[],[f182])).

fof(f182,plain,(
    ! [X4,X3] :
      ( k6_subset_1(X3,X4) = X3
      | r2_hidden(sK4(X3,X4,X3),X4)
      | ~ r2_hidden(sK4(X3,X4,X3),X3)
      | k6_subset_1(X3,X4) = X3 ) ),
    inference(resolution,[],[f48,f56])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X2)
      | k6_subset_1(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X0) ) ),
    inference(resolution,[],[f39,f32])).

fof(f32,plain,(
    ! [X0,X3,X1] :
      ( sP5(X3,X1,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ sP5(sK4(X0,X1,X2),X1,X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | k6_subset_1(X0,X1) = X2 ) ),
    inference(definition_unfolding,[],[f38,f30])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ sP5(sK4(X0,X1,X2),X1,X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1216,plain,(
    ! [X0] : r1_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),k6_subset_1(X0,X0))) ),
    inference(unit_resulting_resolution,[],[f22,f21,f16,f19,f1202,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X0)
      | r2_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f1202,plain,(
    ! [X0] : ~ r2_waybel_0(sK0,sK1,k6_subset_1(X0,X0)) ),
    inference(unit_resulting_resolution,[],[f16,f22,f21,f19,f61,f798])).

fof(f798,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r2_waybel_0(X5,X4,k6_subset_1(X7,X7))
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | v2_struct_0(X5)
      | ~ l1_waybel_0(X4,X5)
      | ~ l1_struct_0(X5)
      | v2_struct_0(X4) ) ),
    inference(duplicate_literal_removal,[],[f784])).

fof(f784,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ l1_waybel_0(X4,X5)
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | v2_struct_0(X5)
      | ~ r2_waybel_0(X5,X4,k6_subset_1(X7,X7))
      | ~ l1_struct_0(X5)
      | v2_struct_0(X4)
      | ~ l1_waybel_0(X4,X5)
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | v2_struct_0(X5)
      | ~ r2_waybel_0(X5,X4,k6_subset_1(X7,X7))
      | ~ l1_struct_0(X5)
      | v2_struct_0(X4) ) ),
    inference(resolution,[],[f224,f223])).

fof(f223,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(k2_waybel_0(X1,X0,sK3(X1,X0,k6_subset_1(X3,X4),X2)),X4)
      | ~ l1_waybel_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X1)
      | ~ r2_waybel_0(X1,X0,k6_subset_1(X3,X4))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f106,f34])).

fof(f106,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP5(k2_waybel_0(X0,X1,sK3(X0,X1,k6_subset_1(X3,X4),X2)),X4,X3)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | v2_struct_0(X0)
      | ~ r2_waybel_0(X0,X1,k6_subset_1(X3,X4))
      | ~ l1_struct_0(X0) ) ),
    inference(resolution,[],[f28,f43])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X3)),X2)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | v2_struct_0(X0)
      | ~ r2_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f224,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( r2_hidden(k2_waybel_0(X6,X5,sK3(X6,X5,k6_subset_1(X8,X9),X7)),X8)
      | ~ l1_waybel_0(X5,X6)
      | ~ m1_subset_1(X7,u1_struct_0(X5))
      | v2_struct_0(X6)
      | ~ r2_waybel_0(X6,X5,k6_subset_1(X8,X9))
      | ~ l1_struct_0(X6)
      | v2_struct_0(X5) ) ),
    inference(resolution,[],[f106,f33])).

fof(f61,plain,(
    m1_subset_1(o_2_2_yellow_6(sK0,sK1),u1_struct_0(sK1)) ),
    inference(unit_resulting_resolution,[],[f21,f16,f18,f17,f19,f22,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(o_2_2_yellow_6(X0,X1),u1_struct_0(X1))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(o_2_2_yellow_6(X0,X1),u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(o_2_2_yellow_6(X0,X1),u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(o_2_2_yellow_6(X0,X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_2_2_yellow_6)).

fof(f17,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
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

fof(f18,plain,(
    v7_waybel_0(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f19,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f16,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f21,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f22,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f20,plain,(
    ~ r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:45:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (13978)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.48  % (14000)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.49  % (13992)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.49  % (13986)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.50  % (14000)Refutation not found, incomplete strategy% (14000)------------------------------
% 0.20/0.50  % (14000)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (13992)Refutation not found, incomplete strategy% (13992)------------------------------
% 0.20/0.50  % (13992)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (13986)Refutation not found, incomplete strategy% (13986)------------------------------
% 0.20/0.50  % (13986)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (14000)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (14000)Memory used [KB]: 6268
% 0.20/0.50  % (14000)Time elapsed: 0.113 s
% 0.20/0.50  % (14000)------------------------------
% 0.20/0.50  % (14000)------------------------------
% 0.20/0.50  % (13998)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.50  % (13990)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.51  % (13992)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (13992)Memory used [KB]: 10618
% 0.20/0.51  % (13992)Time elapsed: 0.115 s
% 0.20/0.51  % (13992)------------------------------
% 0.20/0.51  % (13992)------------------------------
% 0.20/0.51  % (13986)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (13986)Memory used [KB]: 10618
% 0.20/0.51  % (13986)Time elapsed: 0.114 s
% 0.20/0.51  % (13986)------------------------------
% 0.20/0.51  % (13986)------------------------------
% 0.20/0.51  % (13979)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (13977)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (13982)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.51  % (13983)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.52  % (13988)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.52  % (13977)Refutation not found, incomplete strategy% (13977)------------------------------
% 0.20/0.52  % (13977)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (13977)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (13977)Memory used [KB]: 10618
% 0.20/0.52  % (13977)Time elapsed: 0.118 s
% 0.20/0.52  % (13977)------------------------------
% 0.20/0.52  % (13977)------------------------------
% 0.20/0.53  % (13996)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.53  % (13980)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  % (13999)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.36/0.53  % (13979)Refutation not found, incomplete strategy% (13979)------------------------------
% 1.36/0.53  % (13979)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.53  % (13979)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.53  
% 1.36/0.53  % (13979)Memory used [KB]: 6268
% 1.36/0.53  % (13979)Time elapsed: 0.128 s
% 1.36/0.53  % (13979)------------------------------
% 1.36/0.53  % (13979)------------------------------
% 1.36/0.53  % (13975)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.36/0.53  % (13981)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.36/0.53  % (14004)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.36/0.53  % (13997)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.36/0.54  % (13985)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.36/0.54  % (13983)Refutation not found, incomplete strategy% (13983)------------------------------
% 1.36/0.54  % (13983)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (13983)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (13983)Memory used [KB]: 10746
% 1.36/0.54  % (13983)Time elapsed: 0.127 s
% 1.36/0.54  % (13983)------------------------------
% 1.36/0.54  % (13983)------------------------------
% 1.36/0.54  % (13976)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.36/0.54  % (13985)Refutation not found, incomplete strategy% (13985)------------------------------
% 1.36/0.54  % (13985)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (13985)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (13985)Memory used [KB]: 10618
% 1.36/0.54  % (13985)Time elapsed: 0.132 s
% 1.36/0.54  % (13985)------------------------------
% 1.36/0.54  % (13985)------------------------------
% 1.36/0.54  % (14002)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.36/0.54  % (13991)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.36/0.54  % (13987)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.36/0.54  % (13997)Refutation not found, incomplete strategy% (13997)------------------------------
% 1.36/0.54  % (13997)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (13996)Refutation not found, incomplete strategy% (13996)------------------------------
% 1.36/0.54  % (13996)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (13996)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (13996)Memory used [KB]: 1663
% 1.36/0.54  % (13996)Time elapsed: 0.130 s
% 1.36/0.54  % (13996)------------------------------
% 1.36/0.54  % (13996)------------------------------
% 1.36/0.54  % (13997)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (13997)Memory used [KB]: 10746
% 1.36/0.54  % (13997)Time elapsed: 0.126 s
% 1.36/0.54  % (13997)------------------------------
% 1.36/0.54  % (13997)------------------------------
% 1.36/0.55  % (13994)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.36/0.55  % (14003)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.51/0.55  % (13995)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.51/0.55  % (13995)Refutation not found, incomplete strategy% (13995)------------------------------
% 1.51/0.55  % (13995)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.55  % (13995)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.55  
% 1.51/0.55  % (13995)Memory used [KB]: 10746
% 1.51/0.55  % (13995)Time elapsed: 0.152 s
% 1.51/0.55  % (13995)------------------------------
% 1.51/0.55  % (13995)------------------------------
% 1.51/0.55  % (13984)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.51/0.56  % (14001)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.51/0.57  % (14001)Refutation not found, incomplete strategy% (14001)------------------------------
% 1.51/0.57  % (14001)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.57  % (14001)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.57  
% 1.51/0.57  % (14001)Memory used [KB]: 10746
% 1.51/0.57  % (14001)Time elapsed: 0.153 s
% 1.51/0.57  % (14001)------------------------------
% 1.51/0.57  % (14001)------------------------------
% 1.51/0.57  % (13993)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.51/0.58  % (13989)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.51/0.59  % (13999)Refutation found. Thanks to Tanya!
% 1.51/0.59  % SZS status Theorem for theBenchmark
% 1.51/0.59  % SZS output start Proof for theBenchmark
% 1.51/0.61  fof(f1227,plain,(
% 1.51/0.61    $false),
% 1.51/0.61    inference(global_subsumption,[],[f20,f1226])).
% 1.51/0.61  fof(f1226,plain,(
% 1.51/0.61    r1_waybel_0(sK0,sK1,u1_struct_0(sK0))),
% 1.51/0.61    inference(forward_demodulation,[],[f1216,f347])).
% 1.51/0.61  fof(f347,plain,(
% 1.51/0.61    ( ! [X2,X3] : (k6_subset_1(X2,k6_subset_1(X3,X3)) = X2) )),
% 1.51/0.61    inference(duplicate_literal_removal,[],[f331])).
% 1.51/0.61  fof(f331,plain,(
% 1.51/0.61    ( ! [X2,X3] : (k6_subset_1(X2,k6_subset_1(X3,X3)) = X2 | k6_subset_1(X2,k6_subset_1(X3,X3)) = X2) )),
% 1.51/0.61    inference(resolution,[],[f266,f56])).
% 1.51/0.61  fof(f56,plain,(
% 1.51/0.61    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1,X0),X0) | k6_subset_1(X0,X1) = X0) )),
% 1.51/0.61    inference(factoring,[],[f51])).
% 1.51/0.61  fof(f51,plain,(
% 1.51/0.61    ( ! [X6,X8,X7] : (r2_hidden(sK4(X6,X7,X8),X8) | k6_subset_1(X6,X7) = X8 | r2_hidden(sK4(X6,X7,X8),X6)) )),
% 1.51/0.61    inference(resolution,[],[f40,f33])).
% 1.51/0.61  fof(f33,plain,(
% 1.51/0.61    ( ! [X0,X3,X1] : (~sP5(X3,X1,X0) | r2_hidden(X3,X0)) )),
% 1.51/0.61    inference(cnf_transformation,[],[f1])).
% 1.51/0.61  fof(f1,axiom,(
% 1.51/0.61    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.51/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.51/0.61  fof(f40,plain,(
% 1.51/0.61    ( ! [X2,X0,X1] : (sP5(sK4(X0,X1,X2),X1,X0) | r2_hidden(sK4(X0,X1,X2),X2) | k6_subset_1(X0,X1) = X2) )),
% 1.51/0.61    inference(definition_unfolding,[],[f37,f30])).
% 1.51/0.61  fof(f30,plain,(
% 1.51/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.51/0.61    inference(cnf_transformation,[],[f2])).
% 1.51/0.61  fof(f2,axiom,(
% 1.51/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.51/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.51/0.61  fof(f37,plain,(
% 1.51/0.61    ( ! [X2,X0,X1] : (sP5(sK4(X0,X1,X2),X1,X0) | r2_hidden(sK4(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 1.51/0.61    inference(cnf_transformation,[],[f1])).
% 1.51/0.61  fof(f266,plain,(
% 1.51/0.61    ( ! [X14,X15,X16] : (~r2_hidden(sK4(X14,k6_subset_1(X15,X15),X14),X16) | k6_subset_1(X14,k6_subset_1(X15,X15)) = X14) )),
% 1.51/0.61    inference(resolution,[],[f256,f78])).
% 1.51/0.61  fof(f78,plain,(
% 1.51/0.61    ( ! [X2,X0,X1] : (~r2_hidden(X0,k6_subset_1(X1,X1)) | ~r2_hidden(X0,X2)) )),
% 1.51/0.61    inference(resolution,[],[f77,f34])).
% 1.51/0.61  fof(f34,plain,(
% 1.51/0.61    ( ! [X0,X3,X1] : (~sP5(X3,X1,X0) | ~r2_hidden(X3,X1)) )),
% 1.51/0.61    inference(cnf_transformation,[],[f1])).
% 1.51/0.61  fof(f77,plain,(
% 1.51/0.61    ( ! [X14,X12,X13] : (sP5(X14,X13,k6_subset_1(X12,X12)) | ~r2_hidden(X14,k6_subset_1(X12,X12))) )),
% 1.51/0.61    inference(superposition,[],[f43,f71])).
% 1.51/0.61  fof(f71,plain,(
% 1.51/0.61    ( ! [X0,X1] : (k6_subset_1(X0,X0) = k6_subset_1(k6_subset_1(X0,X0),X1)) )),
% 1.51/0.61    inference(duplicate_literal_removal,[],[f67])).
% 1.51/0.61  fof(f67,plain,(
% 1.51/0.61    ( ! [X0,X1] : (k6_subset_1(X0,X0) = k6_subset_1(k6_subset_1(X0,X0),X1) | k6_subset_1(X0,X0) = k6_subset_1(k6_subset_1(X0,X0),X1)) )),
% 1.51/0.61    inference(resolution,[],[f65,f64])).
% 1.51/0.61  fof(f64,plain,(
% 1.51/0.61    ( ! [X2,X0,X1] : (~r2_hidden(sK4(k6_subset_1(X0,X1),X2,k6_subset_1(X0,X1)),X1) | k6_subset_1(X0,X1) = k6_subset_1(k6_subset_1(X0,X1),X2)) )),
% 1.51/0.61    inference(resolution,[],[f59,f34])).
% 1.51/0.61  fof(f59,plain,(
% 1.51/0.61    ( ! [X2,X3,X1] : (sP5(sK4(k6_subset_1(X1,X2),X3,k6_subset_1(X1,X2)),X2,X1) | k6_subset_1(X1,X2) = k6_subset_1(k6_subset_1(X1,X2),X3)) )),
% 1.51/0.61    inference(resolution,[],[f56,f43])).
% 1.51/0.61  fof(f65,plain,(
% 1.51/0.61    ( ! [X4,X5,X3] : (r2_hidden(sK4(k6_subset_1(X3,X4),X5,k6_subset_1(X3,X4)),X3) | k6_subset_1(X3,X4) = k6_subset_1(k6_subset_1(X3,X4),X5)) )),
% 1.51/0.61    inference(resolution,[],[f59,f33])).
% 1.51/0.61  fof(f43,plain,(
% 1.51/0.61    ( ! [X0,X3,X1] : (~r2_hidden(X3,k6_subset_1(X0,X1)) | sP5(X3,X1,X0)) )),
% 1.51/0.61    inference(equality_resolution,[],[f41])).
% 1.51/0.61  fof(f41,plain,(
% 1.51/0.61    ( ! [X2,X0,X3,X1] : (sP5(X3,X1,X0) | ~r2_hidden(X3,X2) | k6_subset_1(X0,X1) != X2) )),
% 1.51/0.61    inference(definition_unfolding,[],[f36,f30])).
% 1.51/0.61  fof(f36,plain,(
% 1.51/0.61    ( ! [X2,X0,X3,X1] : (sP5(X3,X1,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.51/0.61    inference(cnf_transformation,[],[f1])).
% 1.51/0.61  fof(f256,plain,(
% 1.51/0.61    ( ! [X2,X3] : (r2_hidden(sK4(X2,X3,X2),X3) | k6_subset_1(X2,X3) = X2) )),
% 1.51/0.61    inference(duplicate_literal_removal,[],[f249])).
% 1.51/0.61  fof(f249,plain,(
% 1.51/0.61    ( ! [X2,X3] : (r2_hidden(sK4(X2,X3,X2),X3) | k6_subset_1(X2,X3) = X2 | k6_subset_1(X2,X3) = X2) )),
% 1.51/0.61    inference(resolution,[],[f187,f56])).
% 1.51/0.61  fof(f187,plain,(
% 1.51/0.61    ( ! [X4,X3] : (~r2_hidden(sK4(X3,X4,X3),X3) | r2_hidden(sK4(X3,X4,X3),X4) | k6_subset_1(X3,X4) = X3) )),
% 1.51/0.61    inference(duplicate_literal_removal,[],[f182])).
% 1.51/0.61  fof(f182,plain,(
% 1.51/0.61    ( ! [X4,X3] : (k6_subset_1(X3,X4) = X3 | r2_hidden(sK4(X3,X4,X3),X4) | ~r2_hidden(sK4(X3,X4,X3),X3) | k6_subset_1(X3,X4) = X3) )),
% 1.51/0.61    inference(resolution,[],[f48,f56])).
% 1.51/0.61  fof(f48,plain,(
% 1.51/0.61    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X2) | k6_subset_1(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0)) )),
% 1.51/0.61    inference(resolution,[],[f39,f32])).
% 1.51/0.61  fof(f32,plain,(
% 1.51/0.61    ( ! [X0,X3,X1] : (sP5(X3,X1,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) )),
% 1.51/0.61    inference(cnf_transformation,[],[f1])).
% 1.51/0.61  fof(f39,plain,(
% 1.51/0.61    ( ! [X2,X0,X1] : (~sP5(sK4(X0,X1,X2),X1,X0) | ~r2_hidden(sK4(X0,X1,X2),X2) | k6_subset_1(X0,X1) = X2) )),
% 1.51/0.61    inference(definition_unfolding,[],[f38,f30])).
% 1.51/0.61  fof(f38,plain,(
% 1.51/0.61    ( ! [X2,X0,X1] : (~sP5(sK4(X0,X1,X2),X1,X0) | ~r2_hidden(sK4(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 1.51/0.61    inference(cnf_transformation,[],[f1])).
% 1.51/0.61  fof(f1216,plain,(
% 1.51/0.61    ( ! [X0] : (r1_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),k6_subset_1(X0,X0)))) )),
% 1.51/0.61    inference(unit_resulting_resolution,[],[f22,f21,f16,f19,f1202,f23])).
% 1.51/0.61  fof(f23,plain,(
% 1.51/0.61    ( ! [X2,X0,X1] : (r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | ~l1_struct_0(X0) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | v2_struct_0(X0) | r2_waybel_0(X0,X1,X2)) )),
% 1.51/0.61    inference(cnf_transformation,[],[f11])).
% 1.51/0.61  fof(f11,plain,(
% 1.51/0.61    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.51/0.61    inference(flattening,[],[f10])).
% 1.51/0.61  fof(f10,plain,(
% 1.51/0.61    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.51/0.61    inference(ennf_transformation,[],[f4])).
% 1.51/0.61  fof(f4,axiom,(
% 1.51/0.61    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)))))),
% 1.51/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_waybel_0)).
% 1.51/0.61  fof(f1202,plain,(
% 1.51/0.61    ( ! [X0] : (~r2_waybel_0(sK0,sK1,k6_subset_1(X0,X0))) )),
% 1.51/0.61    inference(unit_resulting_resolution,[],[f16,f22,f21,f19,f61,f798])).
% 1.51/0.61  fof(f798,plain,(
% 1.51/0.61    ( ! [X6,X4,X7,X5] : (~r2_waybel_0(X5,X4,k6_subset_1(X7,X7)) | ~m1_subset_1(X6,u1_struct_0(X4)) | v2_struct_0(X5) | ~l1_waybel_0(X4,X5) | ~l1_struct_0(X5) | v2_struct_0(X4)) )),
% 1.51/0.61    inference(duplicate_literal_removal,[],[f784])).
% 1.51/0.61  fof(f784,plain,(
% 1.51/0.61    ( ! [X6,X4,X7,X5] : (~l1_waybel_0(X4,X5) | ~m1_subset_1(X6,u1_struct_0(X4)) | v2_struct_0(X5) | ~r2_waybel_0(X5,X4,k6_subset_1(X7,X7)) | ~l1_struct_0(X5) | v2_struct_0(X4) | ~l1_waybel_0(X4,X5) | ~m1_subset_1(X6,u1_struct_0(X4)) | v2_struct_0(X5) | ~r2_waybel_0(X5,X4,k6_subset_1(X7,X7)) | ~l1_struct_0(X5) | v2_struct_0(X4)) )),
% 1.51/0.61    inference(resolution,[],[f224,f223])).
% 1.51/0.61  fof(f223,plain,(
% 1.51/0.61    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(k2_waybel_0(X1,X0,sK3(X1,X0,k6_subset_1(X3,X4),X2)),X4) | ~l1_waybel_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(X1) | ~r2_waybel_0(X1,X0,k6_subset_1(X3,X4)) | ~l1_struct_0(X1) | v2_struct_0(X0)) )),
% 1.51/0.61    inference(resolution,[],[f106,f34])).
% 1.51/0.61  fof(f106,plain,(
% 1.51/0.61    ( ! [X4,X2,X0,X3,X1] : (sP5(k2_waybel_0(X0,X1,sK3(X0,X1,k6_subset_1(X3,X4),X2)),X4,X3) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | v2_struct_0(X0) | ~r2_waybel_0(X0,X1,k6_subset_1(X3,X4)) | ~l1_struct_0(X0)) )),
% 1.51/0.61    inference(resolution,[],[f28,f43])).
% 1.51/0.61  fof(f28,plain,(
% 1.51/0.61    ( ! [X2,X0,X3,X1] : (r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X3)),X2) | ~l1_struct_0(X0) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X3,u1_struct_0(X1)) | v2_struct_0(X0) | ~r2_waybel_0(X0,X1,X2)) )),
% 1.51/0.61    inference(cnf_transformation,[],[f13])).
% 1.51/0.61  fof(f13,plain,(
% 1.51/0.61    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.51/0.61    inference(flattening,[],[f12])).
% 1.51/0.61  fof(f12,plain,(
% 1.51/0.61    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.51/0.61    inference(ennf_transformation,[],[f3])).
% 1.51/0.61  fof(f3,axiom,(
% 1.51/0.61    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1)))))))),
% 1.51/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_waybel_0)).
% 1.51/0.61  fof(f224,plain,(
% 1.51/0.61    ( ! [X6,X8,X7,X5,X9] : (r2_hidden(k2_waybel_0(X6,X5,sK3(X6,X5,k6_subset_1(X8,X9),X7)),X8) | ~l1_waybel_0(X5,X6) | ~m1_subset_1(X7,u1_struct_0(X5)) | v2_struct_0(X6) | ~r2_waybel_0(X6,X5,k6_subset_1(X8,X9)) | ~l1_struct_0(X6) | v2_struct_0(X5)) )),
% 1.51/0.61    inference(resolution,[],[f106,f33])).
% 1.51/0.61  fof(f61,plain,(
% 1.51/0.61    m1_subset_1(o_2_2_yellow_6(sK0,sK1),u1_struct_0(sK1))),
% 1.51/0.61    inference(unit_resulting_resolution,[],[f21,f16,f18,f17,f19,f22,f31])).
% 1.51/0.61  fof(f31,plain,(
% 1.51/0.61    ( ! [X0,X1] : (m1_subset_1(o_2_2_yellow_6(X0,X1),u1_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | v2_struct_0(X0)) )),
% 1.51/0.61    inference(cnf_transformation,[],[f15])).
% 1.51/0.61  fof(f15,plain,(
% 1.51/0.61    ! [X0,X1] : (m1_subset_1(o_2_2_yellow_6(X0,X1),u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.51/0.61    inference(flattening,[],[f14])).
% 1.51/0.61  fof(f14,plain,(
% 1.51/0.61    ! [X0,X1] : (m1_subset_1(o_2_2_yellow_6(X0,X1),u1_struct_0(X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.51/0.61    inference(ennf_transformation,[],[f5])).
% 1.51/0.61  fof(f5,axiom,(
% 1.51/0.61    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => m1_subset_1(o_2_2_yellow_6(X0,X1),u1_struct_0(X1)))),
% 1.51/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_2_2_yellow_6)).
% 1.51/0.61  fof(f17,plain,(
% 1.51/0.61    v4_orders_2(sK1)),
% 1.51/0.61    inference(cnf_transformation,[],[f9])).
% 1.51/0.61  fof(f9,plain,(
% 1.51/0.61    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 1.51/0.61    inference(flattening,[],[f8])).
% 1.51/0.61  fof(f8,plain,(
% 1.51/0.61    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & (l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 1.51/0.61    inference(ennf_transformation,[],[f7])).
% 1.51/0.61  fof(f7,negated_conjecture,(
% 1.51/0.61    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 1.51/0.61    inference(negated_conjecture,[],[f6])).
% 1.51/0.61  fof(f6,conjecture,(
% 1.51/0.61    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 1.51/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_yellow_6)).
% 1.51/0.61  fof(f18,plain,(
% 1.51/0.61    v7_waybel_0(sK1)),
% 1.51/0.61    inference(cnf_transformation,[],[f9])).
% 1.51/0.61  fof(f19,plain,(
% 1.51/0.61    l1_waybel_0(sK1,sK0)),
% 1.51/0.61    inference(cnf_transformation,[],[f9])).
% 1.51/0.62  fof(f16,plain,(
% 1.51/0.62    ~v2_struct_0(sK1)),
% 1.51/0.62    inference(cnf_transformation,[],[f9])).
% 1.51/0.62  fof(f21,plain,(
% 1.51/0.62    ~v2_struct_0(sK0)),
% 1.51/0.62    inference(cnf_transformation,[],[f9])).
% 1.51/0.62  fof(f22,plain,(
% 1.51/0.62    l1_struct_0(sK0)),
% 1.51/0.62    inference(cnf_transformation,[],[f9])).
% 1.51/0.62  fof(f20,plain,(
% 1.51/0.62    ~r1_waybel_0(sK0,sK1,u1_struct_0(sK0))),
% 1.51/0.62    inference(cnf_transformation,[],[f9])).
% 1.51/0.62  % SZS output end Proof for theBenchmark
% 1.51/0.62  % (13999)------------------------------
% 1.51/0.62  % (13999)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.62  % (13999)Termination reason: Refutation
% 1.51/0.62  
% 1.51/0.62  % (13999)Memory used [KB]: 7036
% 1.51/0.62  % (13999)Time elapsed: 0.197 s
% 1.51/0.62  % (13999)------------------------------
% 1.51/0.62  % (13999)------------------------------
% 1.51/0.62  % (13974)Success in time 0.253 s
%------------------------------------------------------------------------------
