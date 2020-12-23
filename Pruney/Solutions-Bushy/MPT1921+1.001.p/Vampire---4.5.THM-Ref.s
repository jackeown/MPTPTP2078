%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1921+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:55 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   34 (  89 expanded)
%              Number of leaves         :    5 (  19 expanded)
%              Depth                    :    9
%              Number of atoms          :  100 ( 284 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f38,plain,(
    $false ),
    inference(global_subsumption,[],[f28,f33,f37])).

fof(f37,plain,(
    m1_yellow_0(sK2,sK1) ),
    inference(subsumption_resolution,[],[f36,f16])).

fof(f16,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(u1_struct_0(X2),u1_struct_0(X1))
              & m1_yellow_6(X2,X0,X1) )
          & l1_waybel_0(X1,X0) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_waybel_0(X1,X0)
           => ! [X2] :
                ( m1_yellow_6(X2,X0,X1)
               => r1_tarski(u1_struct_0(X2),u1_struct_0(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => ! [X2] :
              ( m1_yellow_6(X2,X0,X1)
             => r1_tarski(u1_struct_0(X2),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_yellow_6)).

fof(f36,plain,
    ( m1_yellow_0(sK2,sK1)
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f35,f31])).

fof(f31,plain,(
    l1_waybel_0(sK2,sK0) ),
    inference(subsumption_resolution,[],[f30,f16])).

fof(f30,plain,
    ( ~ l1_struct_0(sK0)
    | l1_waybel_0(sK2,sK0) ),
    inference(subsumption_resolution,[],[f29,f15])).

fof(f15,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f29,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | ~ l1_struct_0(sK0)
    | l1_waybel_0(sK2,sK0) ),
    inference(resolution,[],[f24,f13])).

fof(f13,plain,(
    m1_yellow_6(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | l1_waybel_0(X2,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( l1_waybel_0(X2,X0)
          | ~ m1_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( l1_waybel_0(X2,X0)
          | ~ m1_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ! [X2] :
          ( m1_yellow_6(X2,X0,X1)
         => l1_waybel_0(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_yellow_6)).

fof(f35,plain,
    ( ~ l1_waybel_0(sK2,sK0)
    | m1_yellow_0(sK2,sK1)
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f34,f15])).

fof(f34,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | ~ l1_waybel_0(sK2,sK0)
    | m1_yellow_0(sK2,sK1)
    | ~ l1_struct_0(sK0) ),
    inference(resolution,[],[f21,f13])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_waybel_0(X2,X0)
      | m1_yellow_0(X2,X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_yellow_6(X2,X0,X1)
              <=> ( u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
                  & m1_yellow_0(X2,X1) ) )
              | ~ l1_waybel_0(X2,X0) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => ! [X2] :
              ( l1_waybel_0(X2,X0)
             => ( m1_yellow_6(X2,X0,X1)
              <=> ( u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
                  & m1_yellow_0(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_yellow_6)).

fof(f33,plain,(
    l1_orders_2(sK2) ),
    inference(subsumption_resolution,[],[f32,f16])).

fof(f32,plain,
    ( ~ l1_struct_0(sK0)
    | l1_orders_2(sK2) ),
    inference(resolution,[],[f31,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | l1_orders_2(X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_0)).

fof(f28,plain,
    ( ~ m1_yellow_0(sK2,sK1)
    | ~ l1_orders_2(sK2) ),
    inference(subsumption_resolution,[],[f27,f26])).

fof(f26,plain,(
    l1_orders_2(sK1) ),
    inference(subsumption_resolution,[],[f25,f16])).

fof(f25,plain,
    ( ~ l1_struct_0(sK0)
    | l1_orders_2(sK1) ),
    inference(resolution,[],[f20,f15])).

fof(f27,plain,
    ( ~ l1_orders_2(sK2)
    | ~ l1_orders_2(sK1)
    | ~ m1_yellow_0(sK2,sK1) ),
    inference(resolution,[],[f17,f14])).

fof(f14,plain,(
    ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0)
      | ~ m1_yellow_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_yellow_0(X1,X0)
          <=> ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( m1_yellow_0(X1,X0)
          <=> ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_yellow_0)).

%------------------------------------------------------------------------------
