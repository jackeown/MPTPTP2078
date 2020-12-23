%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:04 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 384 expanded)
%              Number of leaves         :   13 ( 141 expanded)
%              Depth                    :   20
%              Number of atoms          :  318 (2184 expanded)
%              Number of equality atoms :   22 (  41 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f192,plain,(
    $false ),
    inference(subsumption_resolution,[],[f191,f167])).

fof(f167,plain,(
    ~ m1_subset_1(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f166,f119])).

fof(f119,plain,(
    ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f113,f37])).

fof(f37,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1))
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_waybel_0(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f25,f24,f23])).

fof(f23,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1))
                & m1_subset_1(X2,u1_struct_0(X1)) )
            & l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(u1_struct_0(k4_waybel_9(sK0,X1,X2)),u1_struct_0(X1))
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(u1_struct_0(k4_waybel_9(sK0,X1,X2)),u1_struct_0(X1))
            & m1_subset_1(X2,u1_struct_0(X1)) )
        & l1_waybel_0(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ~ r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,X2)),u1_struct_0(sK1))
          & m1_subset_1(X2,u1_struct_0(sK1)) )
      & l1_waybel_0(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X2] :
        ( ~ r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,X2)),u1_struct_0(sK1))
        & m1_subset_1(X2,u1_struct_0(sK1)) )
   => ( ~ r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1))
      & m1_subset_1(sK2,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1))
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1))
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X1))
               => r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_waybel_9)).

fof(f113,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f111,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f111,plain,(
    l1_struct_0(sK1) ),
    inference(resolution,[],[f110,f41])).

fof(f41,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f110,plain,(
    l1_orders_2(sK1) ),
    inference(subsumption_resolution,[],[f94,f36])).

fof(f36,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f94,plain,
    ( l1_orders_2(sK1)
    | ~ l1_struct_0(sK0) ),
    inference(resolution,[],[f38,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_0)).

fof(f38,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f166,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ m1_subset_1(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),u1_struct_0(sK1)) ),
    inference(resolution,[],[f155,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f155,plain,(
    ~ r2_hidden(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),u1_struct_0(sK1)) ),
    inference(resolution,[],[f153,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
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

fof(f153,plain,(
    ~ r1_tarski(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f152,f35])).

fof(f35,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f152,plain,
    ( ~ r1_tarski(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f151,f36])).

fof(f151,plain,
    ( ~ r1_tarski(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f150,f37])).

fof(f150,plain,
    ( ~ r1_tarski(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f149,f38])).

fof(f149,plain,
    ( ~ r1_tarski(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f148,f39])).

fof(f39,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f148,plain,
    ( ~ r1_tarski(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f40,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( u1_struct_0(k4_waybel_9(X0,X1,X2)) = a_3_0_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( u1_struct_0(k4_waybel_9(X0,X1,X2)) = a_3_0_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( u1_struct_0(k4_waybel_9(X0,X1,X2)) = a_3_0_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
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
              ( m1_subset_1(X2,u1_struct_0(X1))
             => u1_struct_0(k4_waybel_9(X0,X1,X2)) = a_3_0_waybel_9(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_waybel_9)).

fof(f40,plain,(
    ~ r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f191,plain,(
    m1_subset_1(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),u1_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f185,f190])).

fof(f190,plain,(
    sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)) = sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2) ),
    inference(subsumption_resolution,[],[f189,f35])).

fof(f189,plain,
    ( sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)) = sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f188,f36])).

fof(f188,plain,
    ( sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)) = sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f187,f37])).

fof(f187,plain,
    ( sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)) = sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f186,f38])).

fof(f186,plain,
    ( sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)) = sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2)
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f178,f39])).

fof(f178,plain,
    ( sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)) = sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f154,f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( sK4(X0,X2,X3) = X0
      | ~ r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))
          | ! [X4] :
              ( ~ r1_orders_2(X2,X3,X4)
              | X0 != X4
              | ~ m1_subset_1(X4,u1_struct_0(X2)) ) )
        & ( ( r1_orders_2(X2,X3,sK4(X0,X2,X3))
            & sK4(X0,X2,X3) = X0
            & m1_subset_1(sK4(X0,X2,X3),u1_struct_0(X2)) )
          | ~ r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) ) )
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f33])).

fof(f33,plain,(
    ! [X3,X2,X0] :
      ( ? [X5] :
          ( r1_orders_2(X2,X3,X5)
          & X0 = X5
          & m1_subset_1(X5,u1_struct_0(X2)) )
     => ( r1_orders_2(X2,X3,sK4(X0,X2,X3))
        & sK4(X0,X2,X3) = X0
        & m1_subset_1(sK4(X0,X2,X3),u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))
          | ! [X4] :
              ( ~ r1_orders_2(X2,X3,X4)
              | X0 != X4
              | ~ m1_subset_1(X4,u1_struct_0(X2)) ) )
        & ( ? [X5] :
              ( r1_orders_2(X2,X3,X5)
              & X0 = X5
              & m1_subset_1(X5,u1_struct_0(X2)) )
          | ~ r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) ) )
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))
          | ! [X4] :
              ( ~ r1_orders_2(X2,X3,X4)
              | X0 != X4
              | ~ m1_subset_1(X4,u1_struct_0(X2)) ) )
        & ( ? [X4] :
              ( r1_orders_2(X2,X3,X4)
              & X0 = X4
              & m1_subset_1(X4,u1_struct_0(X2)) )
          | ~ r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) ) )
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))
      <=> ? [X4] :
            ( r1_orders_2(X2,X3,X4)
            & X0 = X4
            & m1_subset_1(X4,u1_struct_0(X2)) ) )
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))
      <=> ? [X4] :
            ( r1_orders_2(X2,X3,X4)
            & X0 = X4
            & m1_subset_1(X4,u1_struct_0(X2)) ) )
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,u1_struct_0(X2))
        & l1_waybel_0(X2,X1)
        & ~ v2_struct_0(X2)
        & l1_struct_0(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))
      <=> ? [X4] :
            ( r1_orders_2(X2,X3,X4)
            & X0 = X4
            & m1_subset_1(X4,u1_struct_0(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_3_0_waybel_9)).

fof(f154,plain,(
    r2_hidden(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),a_3_0_waybel_9(sK0,sK1,sK2)) ),
    inference(resolution,[],[f153,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f185,plain,(
    m1_subset_1(sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f184,f35])).

fof(f184,plain,
    ( m1_subset_1(sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2),u1_struct_0(sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f183,f36])).

fof(f183,plain,
    ( m1_subset_1(sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2),u1_struct_0(sK1))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f182,f37])).

fof(f182,plain,
    ( m1_subset_1(sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f181,f38])).

fof(f181,plain,
    ( m1_subset_1(sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2),u1_struct_0(sK1))
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f177,f39])).

fof(f177,plain,
    ( m1_subset_1(sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f154,f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK4(X0,X2,X3),u1_struct_0(X2))
      | ~ r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:07:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.55  % (10376)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.56  % (10376)Refutation not found, incomplete strategy% (10376)------------------------------
% 0.21/0.56  % (10376)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (10398)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.57  % (10376)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (10376)Memory used [KB]: 1791
% 0.21/0.57  % (10376)Time elapsed: 0.124 s
% 0.21/0.57  % (10376)------------------------------
% 0.21/0.57  % (10376)------------------------------
% 0.21/0.57  % (10391)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.58  % (10384)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.58  % (10384)Refutation not found, incomplete strategy% (10384)------------------------------
% 0.21/0.58  % (10384)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (10384)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (10384)Memory used [KB]: 10746
% 0.21/0.58  % (10384)Time elapsed: 0.141 s
% 0.21/0.58  % (10384)------------------------------
% 0.21/0.58  % (10384)------------------------------
% 0.21/0.58  % (10398)Refutation not found, incomplete strategy% (10398)------------------------------
% 0.21/0.58  % (10398)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (10398)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (10398)Memory used [KB]: 10746
% 0.21/0.58  % (10398)Time elapsed: 0.145 s
% 0.21/0.58  % (10398)------------------------------
% 0.21/0.58  % (10398)------------------------------
% 0.21/0.58  % (10383)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.59  % (10399)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.59  % (10399)Refutation found. Thanks to Tanya!
% 0.21/0.59  % SZS status Theorem for theBenchmark
% 0.21/0.59  % SZS output start Proof for theBenchmark
% 0.21/0.59  fof(f192,plain,(
% 0.21/0.59    $false),
% 0.21/0.59    inference(subsumption_resolution,[],[f191,f167])).
% 0.21/0.59  fof(f167,plain,(
% 0.21/0.59    ~m1_subset_1(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),u1_struct_0(sK1))),
% 0.21/0.59    inference(subsumption_resolution,[],[f166,f119])).
% 0.21/0.59  fof(f119,plain,(
% 0.21/0.59    ~v1_xboole_0(u1_struct_0(sK1))),
% 0.21/0.59    inference(subsumption_resolution,[],[f113,f37])).
% 0.21/0.59  fof(f37,plain,(
% 0.21/0.59    ~v2_struct_0(sK1)),
% 0.21/0.59    inference(cnf_transformation,[],[f26])).
% 0.21/0.59  fof(f26,plain,(
% 0.21/0.59    ((~r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1)) & m1_subset_1(sK2,u1_struct_0(sK1))) & l1_waybel_0(sK1,sK0) & ~v2_struct_0(sK1)) & l1_struct_0(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f25,f24,f23])).
% 0.21/0.59  fof(f23,plain,(
% 0.21/0.59    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)) & m1_subset_1(X2,u1_struct_0(X1))) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r1_tarski(u1_struct_0(k4_waybel_9(sK0,X1,X2)),u1_struct_0(X1)) & m1_subset_1(X2,u1_struct_0(X1))) & l1_waybel_0(X1,sK0) & ~v2_struct_0(X1)) & l1_struct_0(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.59    introduced(choice_axiom,[])).
% 0.21/0.59  fof(f24,plain,(
% 0.21/0.59    ? [X1] : (? [X2] : (~r1_tarski(u1_struct_0(k4_waybel_9(sK0,X1,X2)),u1_struct_0(X1)) & m1_subset_1(X2,u1_struct_0(X1))) & l1_waybel_0(X1,sK0) & ~v2_struct_0(X1)) => (? [X2] : (~r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,X2)),u1_struct_0(sK1)) & m1_subset_1(X2,u1_struct_0(sK1))) & l1_waybel_0(sK1,sK0) & ~v2_struct_0(sK1))),
% 0.21/0.59    introduced(choice_axiom,[])).
% 0.21/0.59  fof(f25,plain,(
% 0.21/0.59    ? [X2] : (~r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,X2)),u1_struct_0(sK1)) & m1_subset_1(X2,u1_struct_0(sK1))) => (~r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1)) & m1_subset_1(sK2,u1_struct_0(sK1)))),
% 0.21/0.59    introduced(choice_axiom,[])).
% 0.21/0.59  fof(f11,plain,(
% 0.21/0.59    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)) & m1_subset_1(X2,u1_struct_0(X1))) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 0.21/0.59    inference(flattening,[],[f10])).
% 0.21/0.59  fof(f10,plain,(
% 0.21/0.59    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)) & m1_subset_1(X2,u1_struct_0(X1))) & (l1_waybel_0(X1,X0) & ~v2_struct_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 0.21/0.59    inference(ennf_transformation,[],[f9])).
% 0.21/0.59  fof(f9,negated_conjecture,(
% 0.21/0.59    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)))))),
% 0.21/0.59    inference(negated_conjecture,[],[f8])).
% 0.21/0.59  fof(f8,conjecture,(
% 0.21/0.59    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)))))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_waybel_9)).
% 0.21/0.59  fof(f113,plain,(
% 0.21/0.59    ~v1_xboole_0(u1_struct_0(sK1)) | v2_struct_0(sK1)),
% 0.21/0.59    inference(resolution,[],[f111,f43])).
% 0.21/0.59  fof(f43,plain,(
% 0.21/0.59    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f15])).
% 0.21/0.59  fof(f15,plain,(
% 0.21/0.59    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.59    inference(flattening,[],[f14])).
% 0.21/0.59  fof(f14,plain,(
% 0.21/0.59    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.59    inference(ennf_transformation,[],[f3])).
% 0.21/0.59  fof(f3,axiom,(
% 0.21/0.59    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.59  fof(f111,plain,(
% 0.21/0.59    l1_struct_0(sK1)),
% 0.21/0.59    inference(resolution,[],[f110,f41])).
% 0.21/0.59  fof(f41,plain,(
% 0.21/0.59    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f12])).
% 0.21/0.59  fof(f12,plain,(
% 0.21/0.59    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.21/0.59    inference(ennf_transformation,[],[f4])).
% 0.21/0.59  fof(f4,axiom,(
% 0.21/0.59    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.21/0.59  fof(f110,plain,(
% 0.21/0.59    l1_orders_2(sK1)),
% 0.21/0.59    inference(subsumption_resolution,[],[f94,f36])).
% 0.21/0.59  fof(f36,plain,(
% 0.21/0.59    l1_struct_0(sK0)),
% 0.21/0.59    inference(cnf_transformation,[],[f26])).
% 0.21/0.59  fof(f94,plain,(
% 0.21/0.59    l1_orders_2(sK1) | ~l1_struct_0(sK0)),
% 0.21/0.59    inference(resolution,[],[f38,f42])).
% 0.21/0.59  fof(f42,plain,(
% 0.21/0.59    ( ! [X0,X1] : (l1_orders_2(X1) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f13])).
% 0.21/0.59  fof(f13,plain,(
% 0.21/0.59    ! [X0] : (! [X1] : (l1_orders_2(X1) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 0.21/0.59    inference(ennf_transformation,[],[f5])).
% 0.21/0.59  fof(f5,axiom,(
% 0.21/0.59    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => l1_orders_2(X1)))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_0)).
% 0.21/0.59  fof(f38,plain,(
% 0.21/0.59    l1_waybel_0(sK1,sK0)),
% 0.21/0.59    inference(cnf_transformation,[],[f26])).
% 0.21/0.59  fof(f166,plain,(
% 0.21/0.59    v1_xboole_0(u1_struct_0(sK1)) | ~m1_subset_1(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),u1_struct_0(sK1))),
% 0.21/0.59    inference(resolution,[],[f155,f45])).
% 0.21/0.59  fof(f45,plain,(
% 0.21/0.59    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f19])).
% 0.21/0.59  fof(f19,plain,(
% 0.21/0.59    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.59    inference(flattening,[],[f18])).
% 0.21/0.59  fof(f18,plain,(
% 0.21/0.59    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.59    inference(ennf_transformation,[],[f2])).
% 0.21/0.59  fof(f2,axiom,(
% 0.21/0.59    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.59  fof(f155,plain,(
% 0.21/0.59    ~r2_hidden(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),u1_struct_0(sK1))),
% 0.21/0.59    inference(resolution,[],[f153,f48])).
% 0.21/0.59  fof(f48,plain,(
% 0.21/0.59    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK3(X0,X1),X1)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f30])).
% 0.21/0.59  fof(f30,plain,(
% 0.21/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f29])).
% 0.21/0.59  fof(f29,plain,(
% 0.21/0.59    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.21/0.59    introduced(choice_axiom,[])).
% 0.21/0.59  fof(f28,plain,(
% 0.21/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.59    inference(rectify,[],[f27])).
% 0.21/0.59  fof(f27,plain,(
% 0.21/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.59    inference(nnf_transformation,[],[f20])).
% 0.21/0.59  fof(f20,plain,(
% 0.21/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.59    inference(ennf_transformation,[],[f1])).
% 0.21/0.59  fof(f1,axiom,(
% 0.21/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.59  fof(f153,plain,(
% 0.21/0.59    ~r1_tarski(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1))),
% 0.21/0.59    inference(subsumption_resolution,[],[f152,f35])).
% 0.21/0.59  fof(f35,plain,(
% 0.21/0.59    ~v2_struct_0(sK0)),
% 0.21/0.59    inference(cnf_transformation,[],[f26])).
% 0.21/0.59  fof(f152,plain,(
% 0.21/0.59    ~r1_tarski(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)) | v2_struct_0(sK0)),
% 0.21/0.59    inference(subsumption_resolution,[],[f151,f36])).
% 0.21/0.59  fof(f151,plain,(
% 0.21/0.59    ~r1_tarski(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.59    inference(subsumption_resolution,[],[f150,f37])).
% 0.21/0.59  fof(f150,plain,(
% 0.21/0.59    ~r1_tarski(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)) | v2_struct_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.59    inference(subsumption_resolution,[],[f149,f38])).
% 0.21/0.59  fof(f149,plain,(
% 0.21/0.59    ~r1_tarski(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)) | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.59    inference(subsumption_resolution,[],[f148,f39])).
% 0.21/0.59  fof(f39,plain,(
% 0.21/0.59    m1_subset_1(sK2,u1_struct_0(sK1))),
% 0.21/0.59    inference(cnf_transformation,[],[f26])).
% 0.21/0.59  fof(f148,plain,(
% 0.21/0.59    ~r1_tarski(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK2,u1_struct_0(sK1)) | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.59    inference(superposition,[],[f40,f44])).
% 0.21/0.59  fof(f44,plain,(
% 0.21/0.59    ( ! [X2,X0,X1] : (u1_struct_0(k4_waybel_9(X0,X1,X2)) = a_3_0_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f17])).
% 0.21/0.59  fof(f17,plain,(
% 0.21/0.59    ! [X0] : (! [X1] : (! [X2] : (u1_struct_0(k4_waybel_9(X0,X1,X2)) = a_3_0_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.59    inference(flattening,[],[f16])).
% 0.21/0.59  fof(f16,plain,(
% 0.21/0.59    ! [X0] : (! [X1] : (! [X2] : (u1_struct_0(k4_waybel_9(X0,X1,X2)) = a_3_0_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.59    inference(ennf_transformation,[],[f7])).
% 0.21/0.59  fof(f7,axiom,(
% 0.21/0.59    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => u1_struct_0(k4_waybel_9(X0,X1,X2)) = a_3_0_waybel_9(X0,X1,X2))))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_waybel_9)).
% 0.21/0.59  fof(f40,plain,(
% 0.21/0.59    ~r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1))),
% 0.21/0.59    inference(cnf_transformation,[],[f26])).
% 0.21/0.59  fof(f191,plain,(
% 0.21/0.59    m1_subset_1(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),u1_struct_0(sK1))),
% 0.21/0.59    inference(backward_demodulation,[],[f185,f190])).
% 0.21/0.59  fof(f190,plain,(
% 0.21/0.59    sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)) = sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2)),
% 0.21/0.59    inference(subsumption_resolution,[],[f189,f35])).
% 0.21/0.59  fof(f189,plain,(
% 0.21/0.59    sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)) = sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2) | v2_struct_0(sK0)),
% 0.21/0.59    inference(subsumption_resolution,[],[f188,f36])).
% 0.21/0.59  fof(f188,plain,(
% 0.21/0.59    sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)) = sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.59    inference(subsumption_resolution,[],[f187,f37])).
% 0.21/0.59  fof(f187,plain,(
% 0.21/0.59    sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)) = sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2) | v2_struct_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.59    inference(subsumption_resolution,[],[f186,f38])).
% 0.21/0.59  fof(f186,plain,(
% 0.21/0.59    sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)) = sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2) | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.59    inference(subsumption_resolution,[],[f178,f39])).
% 0.21/0.59  fof(f178,plain,(
% 0.21/0.59    sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)) = sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2) | ~m1_subset_1(sK2,u1_struct_0(sK1)) | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.59    inference(resolution,[],[f154,f50])).
% 0.21/0.59  fof(f50,plain,(
% 0.21/0.59    ( ! [X2,X0,X3,X1] : (sK4(X0,X2,X3) = X0 | ~r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_waybel_0(X2,X1) | v2_struct_0(X2) | ~l1_struct_0(X1) | v2_struct_0(X1)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f34])).
% 0.21/0.59  fof(f34,plain,(
% 0.21/0.59    ! [X0,X1,X2,X3] : (((r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) | ! [X4] : (~r1_orders_2(X2,X3,X4) | X0 != X4 | ~m1_subset_1(X4,u1_struct_0(X2)))) & ((r1_orders_2(X2,X3,sK4(X0,X2,X3)) & sK4(X0,X2,X3) = X0 & m1_subset_1(sK4(X0,X2,X3),u1_struct_0(X2))) | ~r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)))) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_waybel_0(X2,X1) | v2_struct_0(X2) | ~l1_struct_0(X1) | v2_struct_0(X1))),
% 0.21/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f33])).
% 0.21/0.59  fof(f33,plain,(
% 0.21/0.59    ! [X3,X2,X0] : (? [X5] : (r1_orders_2(X2,X3,X5) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X2))) => (r1_orders_2(X2,X3,sK4(X0,X2,X3)) & sK4(X0,X2,X3) = X0 & m1_subset_1(sK4(X0,X2,X3),u1_struct_0(X2))))),
% 0.21/0.59    introduced(choice_axiom,[])).
% 0.21/0.59  fof(f32,plain,(
% 0.21/0.59    ! [X0,X1,X2,X3] : (((r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) | ! [X4] : (~r1_orders_2(X2,X3,X4) | X0 != X4 | ~m1_subset_1(X4,u1_struct_0(X2)))) & (? [X5] : (r1_orders_2(X2,X3,X5) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X2))) | ~r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)))) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_waybel_0(X2,X1) | v2_struct_0(X2) | ~l1_struct_0(X1) | v2_struct_0(X1))),
% 0.21/0.59    inference(rectify,[],[f31])).
% 0.21/0.59  fof(f31,plain,(
% 0.21/0.59    ! [X0,X1,X2,X3] : (((r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) | ! [X4] : (~r1_orders_2(X2,X3,X4) | X0 != X4 | ~m1_subset_1(X4,u1_struct_0(X2)))) & (? [X4] : (r1_orders_2(X2,X3,X4) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X2))) | ~r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)))) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_waybel_0(X2,X1) | v2_struct_0(X2) | ~l1_struct_0(X1) | v2_struct_0(X1))),
% 0.21/0.59    inference(nnf_transformation,[],[f22])).
% 0.21/0.59  fof(f22,plain,(
% 0.21/0.59    ! [X0,X1,X2,X3] : ((r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) <=> ? [X4] : (r1_orders_2(X2,X3,X4) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X2)))) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_waybel_0(X2,X1) | v2_struct_0(X2) | ~l1_struct_0(X1) | v2_struct_0(X1))),
% 0.21/0.59    inference(flattening,[],[f21])).
% 0.21/0.59  fof(f21,plain,(
% 0.21/0.59    ! [X0,X1,X2,X3] : ((r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) <=> ? [X4] : (r1_orders_2(X2,X3,X4) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X2)))) | (~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_waybel_0(X2,X1) | v2_struct_0(X2) | ~l1_struct_0(X1) | v2_struct_0(X1)))),
% 0.21/0.59    inference(ennf_transformation,[],[f6])).
% 0.21/0.59  fof(f6,axiom,(
% 0.21/0.59    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,u1_struct_0(X2)) & l1_waybel_0(X2,X1) & ~v2_struct_0(X2) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) <=> ? [X4] : (r1_orders_2(X2,X3,X4) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X2)))))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_3_0_waybel_9)).
% 0.21/0.59  fof(f154,plain,(
% 0.21/0.59    r2_hidden(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),a_3_0_waybel_9(sK0,sK1,sK2))),
% 0.21/0.59    inference(resolution,[],[f153,f47])).
% 0.21/0.59  fof(f47,plain,(
% 0.21/0.59    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f30])).
% 0.21/0.59  fof(f185,plain,(
% 0.21/0.59    m1_subset_1(sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2),u1_struct_0(sK1))),
% 0.21/0.59    inference(subsumption_resolution,[],[f184,f35])).
% 0.21/0.59  fof(f184,plain,(
% 0.21/0.59    m1_subset_1(sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2),u1_struct_0(sK1)) | v2_struct_0(sK0)),
% 0.21/0.59    inference(subsumption_resolution,[],[f183,f36])).
% 0.21/0.59  fof(f183,plain,(
% 0.21/0.59    m1_subset_1(sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2),u1_struct_0(sK1)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.59    inference(subsumption_resolution,[],[f182,f37])).
% 0.21/0.59  fof(f182,plain,(
% 0.21/0.59    m1_subset_1(sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2),u1_struct_0(sK1)) | v2_struct_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.59    inference(subsumption_resolution,[],[f181,f38])).
% 0.21/0.59  fof(f181,plain,(
% 0.21/0.59    m1_subset_1(sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2),u1_struct_0(sK1)) | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.59    inference(subsumption_resolution,[],[f177,f39])).
% 0.21/0.59  fof(f177,plain,(
% 0.21/0.59    m1_subset_1(sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK2,u1_struct_0(sK1)) | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.59    inference(resolution,[],[f154,f49])).
% 0.21/0.59  fof(f49,plain,(
% 0.21/0.59    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK4(X0,X2,X3),u1_struct_0(X2)) | ~r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_waybel_0(X2,X1) | v2_struct_0(X2) | ~l1_struct_0(X1) | v2_struct_0(X1)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f34])).
% 0.21/0.59  % SZS output end Proof for theBenchmark
% 0.21/0.59  % (10399)------------------------------
% 0.21/0.59  % (10399)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (10399)Termination reason: Refutation
% 0.21/0.59  
% 0.21/0.59  % (10399)Memory used [KB]: 1791
% 0.21/0.59  % (10399)Time elapsed: 0.096 s
% 0.21/0.59  % (10399)------------------------------
% 0.21/0.59  % (10399)------------------------------
% 0.21/0.59  % (10375)Success in time 0.228 s
%------------------------------------------------------------------------------
