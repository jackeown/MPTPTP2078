%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 217 expanded)
%              Number of leaves         :    8 (  39 expanded)
%              Depth                    :   21
%              Number of atoms          :  294 (1930 expanded)
%              Number of equality atoms :   19 ( 246 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f101,plain,(
    $false ),
    inference(subsumption_resolution,[],[f100,f29])).

fof(f29,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_orders_2(X2,X5,X6)
                              & r1_orders_2(X1,X3,X4)
                              & X4 = X6
                              & X3 = X5
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X2)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_yellow_6(X2,X0,X1)
              & v2_yellow_6(X2,X0,X1)
              & ~ v2_struct_0(X2) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_orders_2(X2,X5,X6)
                              & r1_orders_2(X1,X3,X4)
                              & X4 = X6
                              & X3 = X5
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X2)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_yellow_6(X2,X0,X1)
              & v2_yellow_6(X2,X0,X1)
              & ~ v2_struct_0(X2) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_yellow_6(X2,X0,X1)
                  & v2_yellow_6(X2,X0,X1)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X1))
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X2))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( ( r1_orders_2(X1,X3,X4)
                                    & X4 = X6
                                    & X3 = X5 )
                                 => r1_orders_2(X2,X5,X6) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_yellow_6(X2,X0,X1)
                & v2_yellow_6(X2,X0,X1)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X2))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X2))
                             => ( ( r1_orders_2(X1,X3,X4)
                                  & X4 = X6
                                  & X3 = X5 )
                               => r1_orders_2(X2,X5,X6) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_yellow_6)).

fof(f100,plain,(
    v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f98,f84])).

fof(f84,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f77,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f77,plain,(
    l1_orders_2(sK2) ),
    inference(subsumption_resolution,[],[f76,f54])).

fof(f54,plain,(
    l1_orders_2(sK1) ),
    inference(subsumption_resolution,[],[f53,f34])).

fof(f34,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f53,plain,
    ( ~ l1_struct_0(sK0)
    | l1_orders_2(sK1) ),
    inference(resolution,[],[f37,f33])).

fof(f33,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | l1_orders_2(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_0)).

fof(f76,plain,
    ( ~ l1_orders_2(sK1)
    | l1_orders_2(sK2) ),
    inference(resolution,[],[f71,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0)
      | l1_orders_2(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_yellow_0)).

fof(f71,plain,(
    m1_yellow_0(sK2,sK1) ),
    inference(subsumption_resolution,[],[f70,f34])).

fof(f70,plain,
    ( m1_yellow_0(sK2,sK1)
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f69,f31])).

fof(f31,plain,(
    m1_yellow_6(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f69,plain,
    ( ~ m1_yellow_6(sK2,sK0,sK1)
    | m1_yellow_0(sK2,sK1)
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f68,f33])).

fof(f68,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | ~ m1_yellow_6(sK2,sK0,sK1)
    | m1_yellow_0(sK2,sK1)
    | ~ l1_struct_0(sK0) ),
    inference(resolution,[],[f39,f30])).

fof(f30,plain,(
    v2_yellow_6(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_yellow_6(X2,X0,X1)
      | m1_yellow_0(X2,X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_yellow_6(X2,X0,X1)
              <=> ( m1_yellow_0(X2,X1)
                  & v4_yellow_0(X2,X1) ) )
              | ~ m1_yellow_6(X2,X0,X1) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => ! [X2] :
              ( m1_yellow_6(X2,X0,X1)
             => ( v2_yellow_6(X2,X0,X1)
              <=> ( m1_yellow_0(X2,X1)
                  & v4_yellow_0(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_yellow_6)).

fof(f98,plain,
    ( ~ l1_struct_0(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f93,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f93,plain,(
    v1_xboole_0(u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f62,f92])).

fof(f92,plain,(
    ~ r2_hidden(sK3,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f91,f50])).

fof(f50,plain,(
    ~ r1_orders_2(sK2,sK3,sK4) ),
    inference(backward_demodulation,[],[f49,f22])).

fof(f22,plain,(
    sK3 = sK5 ),
    inference(cnf_transformation,[],[f11])).

fof(f49,plain,(
    ~ r1_orders_2(sK2,sK5,sK4) ),
    inference(backward_demodulation,[],[f25,f23])).

fof(f23,plain,(
    sK4 = sK6 ),
    inference(cnf_transformation,[],[f11])).

fof(f25,plain,(
    ~ r1_orders_2(sK2,sK5,sK6) ),
    inference(cnf_transformation,[],[f11])).

fof(f91,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(sK2))
    | r1_orders_2(sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f90,f28])).

fof(f28,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f90,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ r2_hidden(sK3,u1_struct_0(sK2))
    | r1_orders_2(sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f89,f52])).

fof(f52,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f21,f23])).

fof(f21,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f89,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ r2_hidden(sK3,u1_struct_0(sK2))
    | r1_orders_2(sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f88,f51])).

fof(f51,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(backward_demodulation,[],[f26,f22])).

fof(f26,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f88,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ r2_hidden(sK3,u1_struct_0(sK2))
    | r1_orders_2(sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f87,f27])).

fof(f27,plain,(
    m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f87,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ r2_hidden(sK3,u1_struct_0(sK2))
    | r1_orders_2(sK2,sK3,sK4) ),
    inference(resolution,[],[f75,f24])).

fof(f24,plain,(
    r1_orders_2(sK1,sK3,sK4) ),
    inference(cnf_transformation,[],[f11])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK1,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ r2_hidden(X0,u1_struct_0(sK2))
      | r1_orders_2(sK2,X0,X1) ) ),
    inference(subsumption_resolution,[],[f74,f71])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_yellow_0(sK2,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ r1_orders_2(sK1,X0,X1)
      | ~ r2_hidden(X0,u1_struct_0(sK2))
      | r1_orders_2(sK2,X0,X1) ) ),
    inference(subsumption_resolution,[],[f73,f54])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(sK1)
      | ~ m1_yellow_0(sK2,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ r1_orders_2(sK1,X0,X1)
      | ~ r2_hidden(X0,u1_struct_0(sK2))
      | r1_orders_2(sK2,X0,X1) ) ),
    inference(resolution,[],[f67,f48])).

fof(f48,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ v4_yellow_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ m1_yellow_0(X1,X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ r1_orders_2(X0,X4,X5)
      | ~ r2_hidden(X4,u1_struct_0(X1))
      | r1_orders_2(X1,X4,X5) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X4,X0,X5,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v4_yellow_0(X1,X0)
      | ~ m1_yellow_0(X1,X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | X3 != X5
      | ~ r1_orders_2(X0,X4,X3)
      | ~ r2_hidden(X4,u1_struct_0(X1))
      | r1_orders_2(X1,X4,X5) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v4_yellow_0(X1,X0)
      | ~ m1_yellow_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | X2 != X4
      | X3 != X5
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r2_hidden(X4,u1_struct_0(X1))
      | r1_orders_2(X1,X4,X5) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_orders_2(X1,X4,X5)
                          | ~ r2_hidden(X4,u1_struct_0(X1))
                          | ~ r1_orders_2(X0,X2,X3)
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_yellow_0(X1,X0)
          | ~ v4_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_orders_2(X1,X4,X5)
                          | ~ r2_hidden(X4,u1_struct_0(X1))
                          | ~ r1_orders_2(X0,X2,X3)
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_yellow_0(X1,X0)
          | ~ v4_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ( ( r2_hidden(X4,u1_struct_0(X1))
                              & r1_orders_2(X0,X2,X3)
                              & X3 = X5
                              & X2 = X4 )
                           => r1_orders_2(X1,X4,X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_yellow_0)).

fof(f67,plain,(
    v4_yellow_0(sK2,sK1) ),
    inference(subsumption_resolution,[],[f66,f34])).

fof(f66,plain,
    ( v4_yellow_0(sK2,sK1)
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f65,f31])).

fof(f65,plain,
    ( ~ m1_yellow_6(sK2,sK0,sK1)
    | v4_yellow_0(sK2,sK1)
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f64,f33])).

fof(f64,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | ~ m1_yellow_6(sK2,sK0,sK1)
    | v4_yellow_0(sK2,sK1)
    | ~ l1_struct_0(sK0) ),
    inference(resolution,[],[f38,f30])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_yellow_6(X2,X0,X1)
      | v4_yellow_0(X2,X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f62,plain,
    ( r2_hidden(sK3,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(resolution,[],[f46,f51])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:30:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (2165)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.46  % (2170)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.46  % (2177)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.46  % (2177)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % (2162)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f101,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(subsumption_resolution,[],[f100,f29])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    ~v2_struct_0(sK2)),
% 0.21/0.46    inference(cnf_transformation,[],[f11])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X2,X5,X6) & r1_orders_2(X1,X3,X4) & X4 = X6 & X3 = X5 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_yellow_6(X2,X0,X1) & v2_yellow_6(X2,X0,X1) & ~v2_struct_0(X2)) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 0.21/0.46    inference(flattening,[],[f10])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_orders_2(X2,X5,X6) & (r1_orders_2(X1,X3,X4) & X4 = X6 & X3 = X5)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) & (m1_yellow_6(X2,X0,X1) & v2_yellow_6(X2,X0,X1) & ~v2_struct_0(X2))) & (l1_waybel_0(X1,X0) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,negated_conjecture,(
% 0.21/0.46    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_yellow_6(X2,X0,X1) & v2_yellow_6(X2,X0,X1) & ~v2_struct_0(X2)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_orders_2(X1,X3,X4) & X4 = X6 & X3 = X5) => r1_orders_2(X2,X5,X6)))))))))),
% 0.21/0.46    inference(negated_conjecture,[],[f8])).
% 0.21/0.46  fof(f8,conjecture,(
% 0.21/0.46    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_yellow_6(X2,X0,X1) & v2_yellow_6(X2,X0,X1) & ~v2_struct_0(X2)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_orders_2(X1,X3,X4) & X4 = X6 & X3 = X5) => r1_orders_2(X2,X5,X6)))))))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_yellow_6)).
% 0.21/0.46  fof(f100,plain,(
% 0.21/0.46    v2_struct_0(sK2)),
% 0.21/0.46    inference(subsumption_resolution,[],[f98,f84])).
% 0.21/0.46  fof(f84,plain,(
% 0.21/0.46    l1_struct_0(sK2)),
% 0.21/0.46    inference(resolution,[],[f77,f35])).
% 0.21/0.46  fof(f35,plain,(
% 0.21/0.46    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.21/0.46  fof(f77,plain,(
% 0.21/0.46    l1_orders_2(sK2)),
% 0.21/0.46    inference(subsumption_resolution,[],[f76,f54])).
% 0.21/0.46  fof(f54,plain,(
% 0.21/0.46    l1_orders_2(sK1)),
% 0.21/0.46    inference(subsumption_resolution,[],[f53,f34])).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    l1_struct_0(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f11])).
% 0.21/0.46  fof(f53,plain,(
% 0.21/0.46    ~l1_struct_0(sK0) | l1_orders_2(sK1)),
% 0.21/0.46    inference(resolution,[],[f37,f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    l1_waybel_0(sK1,sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0) | l1_orders_2(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (l1_orders_2(X1) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => l1_orders_2(X1)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_0)).
% 0.21/0.47  fof(f76,plain,(
% 0.21/0.47    ~l1_orders_2(sK1) | l1_orders_2(sK2)),
% 0.21/0.47    inference(resolution,[],[f71,f36])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_yellow_0(X1,X0) | ~l1_orders_2(X0) | l1_orders_2(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (l1_orders_2(X1) | ~m1_yellow_0(X1,X0)) | ~l1_orders_2(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_yellow_0(X1,X0) => l1_orders_2(X1)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_yellow_0)).
% 0.21/0.47  fof(f71,plain,(
% 0.21/0.47    m1_yellow_0(sK2,sK1)),
% 0.21/0.47    inference(subsumption_resolution,[],[f70,f34])).
% 0.21/0.47  fof(f70,plain,(
% 0.21/0.47    m1_yellow_0(sK2,sK1) | ~l1_struct_0(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f69,f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    m1_yellow_6(sK2,sK0,sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f69,plain,(
% 0.21/0.47    ~m1_yellow_6(sK2,sK0,sK1) | m1_yellow_0(sK2,sK1) | ~l1_struct_0(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f68,f33])).
% 0.21/0.47  fof(f68,plain,(
% 0.21/0.47    ~l1_waybel_0(sK1,sK0) | ~m1_yellow_6(sK2,sK0,sK1) | m1_yellow_0(sK2,sK1) | ~l1_struct_0(sK0)),
% 0.21/0.47    inference(resolution,[],[f39,f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    v2_yellow_6(sK2,sK0,sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~v2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~m1_yellow_6(X2,X0,X1) | m1_yellow_0(X2,X1) | ~l1_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : ((v2_yellow_6(X2,X0,X1) <=> (m1_yellow_0(X2,X1) & v4_yellow_0(X2,X1))) | ~m1_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => ! [X2] : (m1_yellow_6(X2,X0,X1) => (v2_yellow_6(X2,X0,X1) <=> (m1_yellow_0(X2,X1) & v4_yellow_0(X2,X1))))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_yellow_6)).
% 0.21/0.47  fof(f98,plain,(
% 0.21/0.47    ~l1_struct_0(sK2) | v2_struct_0(sK2)),
% 0.21/0.47    inference(resolution,[],[f93,f42])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.47  fof(f93,plain,(
% 0.21/0.47    v1_xboole_0(u1_struct_0(sK2))),
% 0.21/0.47    inference(subsumption_resolution,[],[f62,f92])).
% 0.21/0.47  fof(f92,plain,(
% 0.21/0.47    ~r2_hidden(sK3,u1_struct_0(sK2))),
% 0.21/0.47    inference(subsumption_resolution,[],[f91,f50])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    ~r1_orders_2(sK2,sK3,sK4)),
% 0.21/0.47    inference(backward_demodulation,[],[f49,f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    sK3 = sK5),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    ~r1_orders_2(sK2,sK5,sK4)),
% 0.21/0.47    inference(backward_demodulation,[],[f25,f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    sK4 = sK6),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ~r1_orders_2(sK2,sK5,sK6)),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f91,plain,(
% 0.21/0.47    ~r2_hidden(sK3,u1_struct_0(sK2)) | r1_orders_2(sK2,sK3,sK4)),
% 0.21/0.47    inference(subsumption_resolution,[],[f90,f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    m1_subset_1(sK3,u1_struct_0(sK1))),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f90,plain,(
% 0.21/0.47    ~m1_subset_1(sK3,u1_struct_0(sK1)) | ~r2_hidden(sK3,u1_struct_0(sK2)) | r1_orders_2(sK2,sK3,sK4)),
% 0.21/0.47    inference(subsumption_resolution,[],[f89,f52])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    m1_subset_1(sK4,u1_struct_0(sK2))),
% 0.21/0.47    inference(forward_demodulation,[],[f21,f23])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    m1_subset_1(sK6,u1_struct_0(sK2))),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f89,plain,(
% 0.21/0.47    ~m1_subset_1(sK4,u1_struct_0(sK2)) | ~m1_subset_1(sK3,u1_struct_0(sK1)) | ~r2_hidden(sK3,u1_struct_0(sK2)) | r1_orders_2(sK2,sK3,sK4)),
% 0.21/0.47    inference(subsumption_resolution,[],[f88,f51])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    m1_subset_1(sK3,u1_struct_0(sK2))),
% 0.21/0.47    inference(backward_demodulation,[],[f26,f22])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    m1_subset_1(sK5,u1_struct_0(sK2))),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f88,plain,(
% 0.21/0.47    ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~m1_subset_1(sK4,u1_struct_0(sK2)) | ~m1_subset_1(sK3,u1_struct_0(sK1)) | ~r2_hidden(sK3,u1_struct_0(sK2)) | r1_orders_2(sK2,sK3,sK4)),
% 0.21/0.47    inference(subsumption_resolution,[],[f87,f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    m1_subset_1(sK4,u1_struct_0(sK1))),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f87,plain,(
% 0.21/0.47    ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~m1_subset_1(sK4,u1_struct_0(sK2)) | ~m1_subset_1(sK3,u1_struct_0(sK1)) | ~r2_hidden(sK3,u1_struct_0(sK2)) | r1_orders_2(sK2,sK3,sK4)),
% 0.21/0.47    inference(resolution,[],[f75,f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    r1_orders_2(sK1,sK3,sK4)),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f75,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_orders_2(sK1,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~m1_subset_1(X1,u1_struct_0(sK2)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~r2_hidden(X0,u1_struct_0(sK2)) | r1_orders_2(sK2,X0,X1)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f74,f71])).
% 0.21/0.47  fof(f74,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_yellow_0(sK2,sK1) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~m1_subset_1(X1,u1_struct_0(sK2)) | ~r1_orders_2(sK1,X0,X1) | ~r2_hidden(X0,u1_struct_0(sK2)) | r1_orders_2(sK2,X0,X1)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f73,f54])).
% 0.21/0.47  fof(f73,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~l1_orders_2(sK1) | ~m1_yellow_0(sK2,sK1) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~m1_subset_1(X1,u1_struct_0(sK2)) | ~r1_orders_2(sK1,X0,X1) | ~r2_hidden(X0,u1_struct_0(sK2)) | r1_orders_2(sK2,X0,X1)) )),
% 0.21/0.47    inference(resolution,[],[f67,f48])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    ( ! [X4,X0,X5,X1] : (~v4_yellow_0(X1,X0) | ~l1_orders_2(X0) | ~m1_yellow_0(X1,X0) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,u1_struct_0(X1)) | r1_orders_2(X1,X4,X5)) )),
% 0.21/0.47    inference(equality_resolution,[],[f47])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    ( ! [X4,X0,X5,X3,X1] : (~l1_orders_2(X0) | ~v4_yellow_0(X1,X0) | ~m1_yellow_0(X1,X0) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X1)) | X3 != X5 | ~r1_orders_2(X0,X4,X3) | ~r2_hidden(X4,u1_struct_0(X1)) | r1_orders_2(X1,X4,X5)) )),
% 0.21/0.47    inference(equality_resolution,[],[f41])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X5,X3,X1] : (~l1_orders_2(X0) | ~v4_yellow_0(X1,X0) | ~m1_yellow_0(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X1)) | X2 != X4 | X3 != X5 | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X4,u1_struct_0(X1)) | r1_orders_2(X1,X4,X5)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_orders_2(X1,X4,X5) | ~r2_hidden(X4,u1_struct_0(X1)) | ~r1_orders_2(X0,X2,X3) | X3 != X5 | X2 != X4 | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_yellow_0(X1,X0) | ~v4_yellow_0(X1,X0)) | ~l1_orders_2(X0))),
% 0.21/0.47    inference(flattening,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_orders_2(X1,X4,X5) | (~r2_hidden(X4,u1_struct_0(X1)) | ~r1_orders_2(X0,X2,X3) | X3 != X5 | X2 != X4)) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~m1_yellow_0(X1,X0) | ~v4_yellow_0(X1,X0))) | ~l1_orders_2(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0] : (l1_orders_2(X0) => ! [X1] : ((m1_yellow_0(X1,X0) & v4_yellow_0(X1,X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ((r2_hidden(X4,u1_struct_0(X1)) & r1_orders_2(X0,X2,X3) & X3 = X5 & X2 = X4) => r1_orders_2(X1,X4,X5))))))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_yellow_0)).
% 0.21/0.47  fof(f67,plain,(
% 0.21/0.47    v4_yellow_0(sK2,sK1)),
% 0.21/0.47    inference(subsumption_resolution,[],[f66,f34])).
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    v4_yellow_0(sK2,sK1) | ~l1_struct_0(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f65,f31])).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    ~m1_yellow_6(sK2,sK0,sK1) | v4_yellow_0(sK2,sK1) | ~l1_struct_0(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f64,f33])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    ~l1_waybel_0(sK1,sK0) | ~m1_yellow_6(sK2,sK0,sK1) | v4_yellow_0(sK2,sK1) | ~l1_struct_0(sK0)),
% 0.21/0.47    inference(resolution,[],[f38,f30])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~v2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~m1_yellow_6(X2,X0,X1) | v4_yellow_0(X2,X1) | ~l1_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f62,plain,(
% 0.21/0.47    r2_hidden(sK3,u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK2))),
% 0.21/0.47    inference(resolution,[],[f46,f51])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (2177)------------------------------
% 0.21/0.47  % (2177)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (2177)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (2177)Memory used [KB]: 1663
% 0.21/0.47  % (2177)Time elapsed: 0.059 s
% 0.21/0.47  % (2177)------------------------------
% 0.21/0.47  % (2177)------------------------------
% 0.21/0.47  % (2159)Success in time 0.116 s
%------------------------------------------------------------------------------
