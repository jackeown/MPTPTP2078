%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 423 expanded)
%              Number of leaves         :   15 ( 225 expanded)
%              Depth                    :   16
%              Number of atoms          :  477 (5679 expanded)
%              Number of equality atoms :   49 (1040 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f229,plain,(
    $false ),
    inference(subsumption_resolution,[],[f227,f178])).

fof(f178,plain,(
    ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f173,f36])).

fof(f36,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ~ r1_orders_2(sK2,sK5,sK6)
    & r1_orders_2(sK1,sK3,sK4)
    & sK4 = sK6
    & sK3 = sK5
    & m1_subset_1(sK6,u1_struct_0(sK2))
    & m1_subset_1(sK5,u1_struct_0(sK2))
    & m1_subset_1(sK4,u1_struct_0(sK1))
    & m1_subset_1(sK3,u1_struct_0(sK1))
    & m1_yellow_6(sK2,sK0,sK1)
    & v2_yellow_6(sK2,sK0,sK1)
    & ~ v2_struct_0(sK2)
    & l1_waybel_0(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f11,f28,f27,f26,f25,f24,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
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
        & l1_struct_0(X0) )
   => ( ? [X1] :
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
              & m1_yellow_6(X2,sK0,X1)
              & v2_yellow_6(X2,sK0,X1)
              & ~ v2_struct_0(X2) )
          & l1_waybel_0(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
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
            & m1_yellow_6(X2,sK0,X1)
            & v2_yellow_6(X2,sK0,X1)
            & ~ v2_struct_0(X2) )
        & l1_waybel_0(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ~ r1_orders_2(X2,X5,X6)
                          & r1_orders_2(sK1,X3,X4)
                          & X4 = X6
                          & X3 = X5
                          & m1_subset_1(X6,u1_struct_0(X2)) )
                      & m1_subset_1(X5,u1_struct_0(X2)) )
                  & m1_subset_1(X4,u1_struct_0(sK1)) )
              & m1_subset_1(X3,u1_struct_0(sK1)) )
          & m1_yellow_6(X2,sK0,sK1)
          & v2_yellow_6(X2,sK0,sK1)
          & ~ v2_struct_0(X2) )
      & l1_waybel_0(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ~ r1_orders_2(X2,X5,X6)
                        & r1_orders_2(sK1,X3,X4)
                        & X4 = X6
                        & X3 = X5
                        & m1_subset_1(X6,u1_struct_0(X2)) )
                    & m1_subset_1(X5,u1_struct_0(X2)) )
                & m1_subset_1(X4,u1_struct_0(sK1)) )
            & m1_subset_1(X3,u1_struct_0(sK1)) )
        & m1_yellow_6(X2,sK0,sK1)
        & v2_yellow_6(X2,sK0,sK1)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ~ r1_orders_2(sK2,X5,X6)
                      & r1_orders_2(sK1,X3,X4)
                      & X4 = X6
                      & X3 = X5
                      & m1_subset_1(X6,u1_struct_0(sK2)) )
                  & m1_subset_1(X5,u1_struct_0(sK2)) )
              & m1_subset_1(X4,u1_struct_0(sK1)) )
          & m1_subset_1(X3,u1_struct_0(sK1)) )
      & m1_yellow_6(sK2,sK0,sK1)
      & v2_yellow_6(sK2,sK0,sK1)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ~ r1_orders_2(sK2,X5,X6)
                    & r1_orders_2(sK1,X3,X4)
                    & X4 = X6
                    & X3 = X5
                    & m1_subset_1(X6,u1_struct_0(sK2)) )
                & m1_subset_1(X5,u1_struct_0(sK2)) )
            & m1_subset_1(X4,u1_struct_0(sK1)) )
        & m1_subset_1(X3,u1_struct_0(sK1)) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ~ r1_orders_2(sK2,X5,X6)
                  & r1_orders_2(sK1,sK3,X4)
                  & X4 = X6
                  & sK3 = X5
                  & m1_subset_1(X6,u1_struct_0(sK2)) )
              & m1_subset_1(X5,u1_struct_0(sK2)) )
          & m1_subset_1(X4,u1_struct_0(sK1)) )
      & m1_subset_1(sK3,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ~ r1_orders_2(sK2,X5,X6)
                & r1_orders_2(sK1,sK3,X4)
                & X4 = X6
                & sK3 = X5
                & m1_subset_1(X6,u1_struct_0(sK2)) )
            & m1_subset_1(X5,u1_struct_0(sK2)) )
        & m1_subset_1(X4,u1_struct_0(sK1)) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ~ r1_orders_2(sK2,X5,X6)
              & r1_orders_2(sK1,sK3,sK4)
              & sK4 = X6
              & sK3 = X5
              & m1_subset_1(X6,u1_struct_0(sK2)) )
          & m1_subset_1(X5,u1_struct_0(sK2)) )
      & m1_subset_1(sK4,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ~ r1_orders_2(sK2,X5,X6)
            & r1_orders_2(sK1,sK3,sK4)
            & sK4 = X6
            & sK3 = X5
            & m1_subset_1(X6,u1_struct_0(sK2)) )
        & m1_subset_1(X5,u1_struct_0(sK2)) )
   => ( ? [X6] :
          ( ~ r1_orders_2(sK2,sK5,X6)
          & r1_orders_2(sK1,sK3,sK4)
          & sK4 = X6
          & sK3 = sK5
          & m1_subset_1(X6,u1_struct_0(sK2)) )
      & m1_subset_1(sK5,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X6] :
        ( ~ r1_orders_2(sK2,sK5,X6)
        & r1_orders_2(sK1,sK3,sK4)
        & sK4 = X6
        & sK3 = sK5
        & m1_subset_1(X6,u1_struct_0(sK2)) )
   => ( ~ r1_orders_2(sK2,sK5,sK6)
      & r1_orders_2(sK1,sK3,sK4)
      & sK4 = sK6
      & sK3 = sK5
      & m1_subset_1(sK6,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_yellow_6)).

fof(f173,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f167,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f167,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f159,f47])).

fof(f47,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f159,plain,(
    l1_orders_2(sK2) ),
    inference(subsumption_resolution,[],[f154,f33])).

fof(f33,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f154,plain,
    ( l1_orders_2(sK2)
    | ~ l1_struct_0(sK0) ),
    inference(resolution,[],[f98,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_0)).

fof(f98,plain,(
    l1_waybel_0(sK2,sK0) ),
    inference(subsumption_resolution,[],[f97,f33])).

fof(f97,plain,
    ( l1_waybel_0(sK2,sK0)
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f93,f35])).

fof(f35,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f93,plain,
    ( l1_waybel_0(sK2,sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ l1_struct_0(sK0) ),
    inference(resolution,[],[f38,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(X2,X0)
      | ~ m1_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( l1_waybel_0(X2,X0)
          | ~ m1_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( l1_waybel_0(X2,X0)
          | ~ m1_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ! [X2] :
          ( m1_yellow_6(X2,X0,X1)
         => l1_waybel_0(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_yellow_6)).

fof(f38,plain,(
    m1_yellow_6(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f227,plain,(
    v1_xboole_0(u1_struct_0(sK2)) ),
    inference(resolution,[],[f223,f146])).

fof(f146,plain,
    ( r2_hidden(sK3,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(resolution,[],[f64,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f64,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f41,f43])).

fof(f43,plain,(
    sK3 = sK5 ),
    inference(cnf_transformation,[],[f29])).

fof(f41,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f29])).

fof(f223,plain,(
    ~ r2_hidden(sK3,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f222,f89])).

fof(f89,plain,(
    v4_yellow_0(sK2,sK1) ),
    inference(subsumption_resolution,[],[f88,f33])).

fof(f88,plain,
    ( v4_yellow_0(sK2,sK1)
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f87,f35])).

fof(f87,plain,
    ( v4_yellow_0(sK2,sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f85,f38])).

fof(f85,plain,
    ( v4_yellow_0(sK2,sK1)
    | ~ m1_yellow_6(sK2,sK0,sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ l1_struct_0(sK0) ),
    inference(resolution,[],[f37,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v4_yellow_0(X2,X1)
      | ~ v2_yellow_6(X2,X0,X1)
      | ~ m1_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_yellow_6(X2,X0,X1)
                  | ~ m1_yellow_0(X2,X1)
                  | ~ v4_yellow_0(X2,X1) )
                & ( ( m1_yellow_0(X2,X1)
                    & v4_yellow_0(X2,X1) )
                  | ~ v2_yellow_6(X2,X0,X1) ) )
              | ~ m1_yellow_6(X2,X0,X1) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_yellow_6(X2,X0,X1)
                  | ~ m1_yellow_0(X2,X1)
                  | ~ v4_yellow_0(X2,X1) )
                & ( ( m1_yellow_0(X2,X1)
                    & v4_yellow_0(X2,X1) )
                  | ~ v2_yellow_6(X2,X0,X1) ) )
              | ~ m1_yellow_6(X2,X0,X1) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_yellow_6(X2,X0,X1)
              <=> ( m1_yellow_0(X2,X1)
                  & v4_yellow_0(X2,X1) ) )
              | ~ m1_yellow_6(X2,X0,X1) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => ! [X2] :
              ( m1_yellow_6(X2,X0,X1)
             => ( v2_yellow_6(X2,X0,X1)
              <=> ( m1_yellow_0(X2,X1)
                  & v4_yellow_0(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_yellow_6)).

fof(f37,plain,(
    v2_yellow_6(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f222,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(sK2))
    | ~ v4_yellow_0(sK2,sK1) ),
    inference(subsumption_resolution,[],[f221,f92])).

fof(f92,plain,(
    m1_yellow_0(sK2,sK1) ),
    inference(subsumption_resolution,[],[f91,f33])).

fof(f91,plain,
    ( m1_yellow_0(sK2,sK1)
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f90,f35])).

fof(f90,plain,
    ( m1_yellow_0(sK2,sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f86,f38])).

fof(f86,plain,
    ( m1_yellow_0(sK2,sK1)
    | ~ m1_yellow_6(sK2,sK0,sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ l1_struct_0(sK0) ),
    inference(resolution,[],[f37,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_yellow_0(X2,X1)
      | ~ v2_yellow_6(X2,X0,X1)
      | ~ m1_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f221,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(sK2))
    | ~ m1_yellow_0(sK2,sK1)
    | ~ v4_yellow_0(sK2,sK1) ),
    inference(subsumption_resolution,[],[f220,f64])).

fof(f220,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_yellow_0(sK2,sK1)
    | ~ v4_yellow_0(sK2,sK1) ),
    inference(subsumption_resolution,[],[f218,f63])).

fof(f63,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f42,f44])).

fof(f44,plain,(
    sK4 = sK6 ),
    inference(cnf_transformation,[],[f29])).

fof(f42,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f29])).

fof(f218,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_yellow_0(sK2,sK1)
    | ~ v4_yellow_0(sK2,sK1) ),
    inference(resolution,[],[f127,f62])).

fof(f62,plain,(
    ~ r1_orders_2(sK2,sK3,sK4) ),
    inference(backward_demodulation,[],[f61,f43])).

fof(f61,plain,(
    ~ r1_orders_2(sK2,sK5,sK4) ),
    inference(backward_demodulation,[],[f46,f44])).

fof(f46,plain,(
    ~ r1_orders_2(sK2,sK5,sK6) ),
    inference(cnf_transformation,[],[f29])).

fof(f127,plain,(
    ! [X0] :
      ( r1_orders_2(X0,sK3,sK4)
      | ~ r2_hidden(sK3,u1_struct_0(X0))
      | ~ m1_subset_1(sK4,u1_struct_0(X0))
      | ~ m1_subset_1(sK3,u1_struct_0(X0))
      | ~ m1_yellow_0(X0,sK1)
      | ~ v4_yellow_0(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f126,f82])).

fof(f82,plain,(
    l1_orders_2(sK1) ),
    inference(subsumption_resolution,[],[f77,f33])).

fof(f77,plain,
    ( l1_orders_2(sK1)
    | ~ l1_struct_0(sK0) ),
    inference(resolution,[],[f35,f49])).

fof(f126,plain,(
    ! [X0] :
      ( r1_orders_2(X0,sK3,sK4)
      | ~ r2_hidden(sK3,u1_struct_0(X0))
      | ~ m1_subset_1(sK4,u1_struct_0(X0))
      | ~ m1_subset_1(sK3,u1_struct_0(X0))
      | ~ m1_yellow_0(X0,sK1)
      | ~ v4_yellow_0(X0,sK1)
      | ~ l1_orders_2(sK1) ) ),
    inference(subsumption_resolution,[],[f125,f39])).

fof(f39,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f125,plain,(
    ! [X0] :
      ( r1_orders_2(X0,sK3,sK4)
      | ~ r2_hidden(sK3,u1_struct_0(X0))
      | ~ m1_subset_1(sK4,u1_struct_0(X0))
      | ~ m1_subset_1(sK3,u1_struct_0(X0))
      | ~ m1_subset_1(sK3,u1_struct_0(sK1))
      | ~ m1_yellow_0(X0,sK1)
      | ~ v4_yellow_0(X0,sK1)
      | ~ l1_orders_2(sK1) ) ),
    inference(subsumption_resolution,[],[f124,f40])).

fof(f40,plain,(
    m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f124,plain,(
    ! [X0] :
      ( r1_orders_2(X0,sK3,sK4)
      | ~ r2_hidden(sK3,u1_struct_0(X0))
      | ~ m1_subset_1(sK4,u1_struct_0(X0))
      | ~ m1_subset_1(sK3,u1_struct_0(X0))
      | ~ m1_subset_1(sK4,u1_struct_0(sK1))
      | ~ m1_subset_1(sK3,u1_struct_0(sK1))
      | ~ m1_yellow_0(X0,sK1)
      | ~ v4_yellow_0(X0,sK1)
      | ~ l1_orders_2(sK1) ) ),
    inference(resolution,[],[f45,f60])).

fof(f60,plain,(
    ! [X4,X0,X5,X1] :
      ( r1_orders_2(X1,X4,X5)
      | ~ r2_hidden(X4,u1_struct_0(X1))
      | ~ r1_orders_2(X0,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ v4_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( r1_orders_2(X1,X4,X5)
      | ~ r2_hidden(X4,u1_struct_0(X1))
      | ~ r1_orders_2(X0,X2,X5)
      | X2 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ v4_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_orders_2(X1,X4,X5)
      | ~ r2_hidden(X4,u1_struct_0(X1))
      | ~ r1_orders_2(X0,X2,X3)
      | X3 != X5
      | X2 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ v4_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_yellow_0)).

fof(f45,plain,(
    r1_orders_2(sK1,sK3,sK4) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:06:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (11892)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.47  % (11892)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (11901)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f229,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(subsumption_resolution,[],[f227,f178])).
% 0.21/0.49  fof(f178,plain,(
% 0.21/0.49    ~v1_xboole_0(u1_struct_0(sK2))),
% 0.21/0.49    inference(subsumption_resolution,[],[f173,f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ~v2_struct_0(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ((((((~r1_orders_2(sK2,sK5,sK6) & r1_orders_2(sK1,sK3,sK4) & sK4 = sK6 & sK3 = sK5 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK2))) & m1_subset_1(sK4,u1_struct_0(sK1))) & m1_subset_1(sK3,u1_struct_0(sK1))) & m1_yellow_6(sK2,sK0,sK1) & v2_yellow_6(sK2,sK0,sK1) & ~v2_struct_0(sK2)) & l1_waybel_0(sK1,sK0) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f11,f28,f27,f26,f25,f24,f23,f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X2,X5,X6) & r1_orders_2(X1,X3,X4) & X4 = X6 & X3 = X5 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_yellow_6(X2,X0,X1) & v2_yellow_6(X2,X0,X1) & ~v2_struct_0(X2)) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X2,X5,X6) & r1_orders_2(X1,X3,X4) & X4 = X6 & X3 = X5 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_yellow_6(X2,sK0,X1) & v2_yellow_6(X2,sK0,X1) & ~v2_struct_0(X2)) & l1_waybel_0(X1,sK0) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X2,X5,X6) & r1_orders_2(X1,X3,X4) & X4 = X6 & X3 = X5 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_yellow_6(X2,sK0,X1) & v2_yellow_6(X2,sK0,X1) & ~v2_struct_0(X2)) & l1_waybel_0(X1,sK0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X2,X5,X6) & r1_orders_2(sK1,X3,X4) & X4 = X6 & X3 = X5 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(sK1))) & m1_subset_1(X3,u1_struct_0(sK1))) & m1_yellow_6(X2,sK0,sK1) & v2_yellow_6(X2,sK0,sK1) & ~v2_struct_0(X2)) & l1_waybel_0(sK1,sK0) & ~v2_struct_0(sK1))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X2,X5,X6) & r1_orders_2(sK1,X3,X4) & X4 = X6 & X3 = X5 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(sK1))) & m1_subset_1(X3,u1_struct_0(sK1))) & m1_yellow_6(X2,sK0,sK1) & v2_yellow_6(X2,sK0,sK1) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(sK2,X5,X6) & r1_orders_2(sK1,X3,X4) & X4 = X6 & X3 = X5 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK2))) & m1_subset_1(X4,u1_struct_0(sK1))) & m1_subset_1(X3,u1_struct_0(sK1))) & m1_yellow_6(sK2,sK0,sK1) & v2_yellow_6(sK2,sK0,sK1) & ~v2_struct_0(sK2))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(sK2,X5,X6) & r1_orders_2(sK1,X3,X4) & X4 = X6 & X3 = X5 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK2))) & m1_subset_1(X4,u1_struct_0(sK1))) & m1_subset_1(X3,u1_struct_0(sK1))) => (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(sK2,X5,X6) & r1_orders_2(sK1,sK3,X4) & X4 = X6 & sK3 = X5 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK2))) & m1_subset_1(X4,u1_struct_0(sK1))) & m1_subset_1(sK3,u1_struct_0(sK1)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(sK2,X5,X6) & r1_orders_2(sK1,sK3,X4) & X4 = X6 & sK3 = X5 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK2))) & m1_subset_1(X4,u1_struct_0(sK1))) => (? [X5] : (? [X6] : (~r1_orders_2(sK2,X5,X6) & r1_orders_2(sK1,sK3,sK4) & sK4 = X6 & sK3 = X5 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK2))) & m1_subset_1(sK4,u1_struct_0(sK1)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ? [X5] : (? [X6] : (~r1_orders_2(sK2,X5,X6) & r1_orders_2(sK1,sK3,sK4) & sK4 = X6 & sK3 = X5 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK2))) => (? [X6] : (~r1_orders_2(sK2,sK5,X6) & r1_orders_2(sK1,sK3,sK4) & sK4 = X6 & sK3 = sK5 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK2)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ? [X6] : (~r1_orders_2(sK2,sK5,X6) & r1_orders_2(sK1,sK3,sK4) & sK4 = X6 & sK3 = sK5 & m1_subset_1(X6,u1_struct_0(sK2))) => (~r1_orders_2(sK2,sK5,sK6) & r1_orders_2(sK1,sK3,sK4) & sK4 = sK6 & sK3 = sK5 & m1_subset_1(sK6,u1_struct_0(sK2)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X2,X5,X6) & r1_orders_2(X1,X3,X4) & X4 = X6 & X3 = X5 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_yellow_6(X2,X0,X1) & v2_yellow_6(X2,X0,X1) & ~v2_struct_0(X2)) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_orders_2(X2,X5,X6) & (r1_orders_2(X1,X3,X4) & X4 = X6 & X3 = X5)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) & (m1_yellow_6(X2,X0,X1) & v2_yellow_6(X2,X0,X1) & ~v2_struct_0(X2))) & (l1_waybel_0(X1,X0) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,negated_conjecture,(
% 0.21/0.49    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_yellow_6(X2,X0,X1) & v2_yellow_6(X2,X0,X1) & ~v2_struct_0(X2)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_orders_2(X1,X3,X4) & X4 = X6 & X3 = X5) => r1_orders_2(X2,X5,X6)))))))))),
% 0.21/0.49    inference(negated_conjecture,[],[f8])).
% 0.21/0.49  fof(f8,conjecture,(
% 0.21/0.49    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_yellow_6(X2,X0,X1) & v2_yellow_6(X2,X0,X1) & ~v2_struct_0(X2)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_orders_2(X1,X3,X4) & X4 = X6 & X3 = X5) => r1_orders_2(X2,X5,X6)))))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_yellow_6)).
% 0.21/0.49  fof(f173,plain,(
% 0.21/0.49    ~v1_xboole_0(u1_struct_0(sK2)) | v2_struct_0(sK2)),
% 0.21/0.49    inference(resolution,[],[f167,f53])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.49  fof(f167,plain,(
% 0.21/0.49    l1_struct_0(sK2)),
% 0.21/0.49    inference(resolution,[],[f159,f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.21/0.49  fof(f159,plain,(
% 0.21/0.49    l1_orders_2(sK2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f154,f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    l1_struct_0(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f29])).
% 0.21/0.49  fof(f154,plain,(
% 0.21/0.49    l1_orders_2(sK2) | ~l1_struct_0(sK0)),
% 0.21/0.49    inference(resolution,[],[f98,f49])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ( ! [X0,X1] : (l1_orders_2(X1) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (l1_orders_2(X1) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => l1_orders_2(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_0)).
% 0.21/0.49  fof(f98,plain,(
% 0.21/0.49    l1_waybel_0(sK2,sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f97,f33])).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    l1_waybel_0(sK2,sK0) | ~l1_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f93,f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    l1_waybel_0(sK1,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f29])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    l1_waybel_0(sK2,sK0) | ~l1_waybel_0(sK1,sK0) | ~l1_struct_0(sK0)),
% 0.21/0.49    inference(resolution,[],[f38,f58])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (l1_waybel_0(X2,X0) | ~m1_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : (l1_waybel_0(X2,X0) | ~m1_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : (l1_waybel_0(X2,X0) | ~m1_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => ! [X2] : (m1_yellow_6(X2,X0,X1) => l1_waybel_0(X2,X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_yellow_6)).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    m1_yellow_6(sK2,sK0,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f29])).
% 0.21/0.49  fof(f227,plain,(
% 0.21/0.49    v1_xboole_0(u1_struct_0(sK2))),
% 0.21/0.49    inference(resolution,[],[f223,f146])).
% 0.21/0.49  fof(f146,plain,(
% 0.21/0.49    r2_hidden(sK3,u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK2))),
% 0.21/0.49    inference(resolution,[],[f64,f54])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.21/0.49    inference(nnf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    m1_subset_1(sK3,u1_struct_0(sK2))),
% 0.21/0.49    inference(forward_demodulation,[],[f41,f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    sK3 = sK5),
% 0.21/0.49    inference(cnf_transformation,[],[f29])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    m1_subset_1(sK5,u1_struct_0(sK2))),
% 0.21/0.49    inference(cnf_transformation,[],[f29])).
% 0.21/0.49  fof(f223,plain,(
% 0.21/0.49    ~r2_hidden(sK3,u1_struct_0(sK2))),
% 0.21/0.49    inference(subsumption_resolution,[],[f222,f89])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    v4_yellow_0(sK2,sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f88,f33])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    v4_yellow_0(sK2,sK1) | ~l1_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f87,f35])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    v4_yellow_0(sK2,sK1) | ~l1_waybel_0(sK1,sK0) | ~l1_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f85,f38])).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    v4_yellow_0(sK2,sK1) | ~m1_yellow_6(sK2,sK0,sK1) | ~l1_waybel_0(sK1,sK0) | ~l1_struct_0(sK0)),
% 0.21/0.49    inference(resolution,[],[f37,f50])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v4_yellow_0(X2,X1) | ~v2_yellow_6(X2,X0,X1) | ~m1_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (((v2_yellow_6(X2,X0,X1) | ~m1_yellow_0(X2,X1) | ~v4_yellow_0(X2,X1)) & ((m1_yellow_0(X2,X1) & v4_yellow_0(X2,X1)) | ~v2_yellow_6(X2,X0,X1))) | ~m1_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (((v2_yellow_6(X2,X0,X1) | (~m1_yellow_0(X2,X1) | ~v4_yellow_0(X2,X1))) & ((m1_yellow_0(X2,X1) & v4_yellow_0(X2,X1)) | ~v2_yellow_6(X2,X0,X1))) | ~m1_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((v2_yellow_6(X2,X0,X1) <=> (m1_yellow_0(X2,X1) & v4_yellow_0(X2,X1))) | ~m1_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => ! [X2] : (m1_yellow_6(X2,X0,X1) => (v2_yellow_6(X2,X0,X1) <=> (m1_yellow_0(X2,X1) & v4_yellow_0(X2,X1))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_yellow_6)).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    v2_yellow_6(sK2,sK0,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f29])).
% 0.21/0.49  fof(f222,plain,(
% 0.21/0.49    ~r2_hidden(sK3,u1_struct_0(sK2)) | ~v4_yellow_0(sK2,sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f221,f92])).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    m1_yellow_0(sK2,sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f91,f33])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    m1_yellow_0(sK2,sK1) | ~l1_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f90,f35])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    m1_yellow_0(sK2,sK1) | ~l1_waybel_0(sK1,sK0) | ~l1_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f86,f38])).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    m1_yellow_0(sK2,sK1) | ~m1_yellow_6(sK2,sK0,sK1) | ~l1_waybel_0(sK1,sK0) | ~l1_struct_0(sK0)),
% 0.21/0.49    inference(resolution,[],[f37,f51])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (m1_yellow_0(X2,X1) | ~v2_yellow_6(X2,X0,X1) | ~m1_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  fof(f221,plain,(
% 0.21/0.49    ~r2_hidden(sK3,u1_struct_0(sK2)) | ~m1_yellow_0(sK2,sK1) | ~v4_yellow_0(sK2,sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f220,f64])).
% 0.21/0.49  fof(f220,plain,(
% 0.21/0.49    ~r2_hidden(sK3,u1_struct_0(sK2)) | ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~m1_yellow_0(sK2,sK1) | ~v4_yellow_0(sK2,sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f218,f63])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    m1_subset_1(sK4,u1_struct_0(sK2))),
% 0.21/0.49    inference(forward_demodulation,[],[f42,f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    sK4 = sK6),
% 0.21/0.49    inference(cnf_transformation,[],[f29])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    m1_subset_1(sK6,u1_struct_0(sK2))),
% 0.21/0.49    inference(cnf_transformation,[],[f29])).
% 0.21/0.49  fof(f218,plain,(
% 0.21/0.49    ~r2_hidden(sK3,u1_struct_0(sK2)) | ~m1_subset_1(sK4,u1_struct_0(sK2)) | ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~m1_yellow_0(sK2,sK1) | ~v4_yellow_0(sK2,sK1)),
% 0.21/0.49    inference(resolution,[],[f127,f62])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    ~r1_orders_2(sK2,sK3,sK4)),
% 0.21/0.49    inference(backward_demodulation,[],[f61,f43])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    ~r1_orders_2(sK2,sK5,sK4)),
% 0.21/0.49    inference(backward_demodulation,[],[f46,f44])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ~r1_orders_2(sK2,sK5,sK6)),
% 0.21/0.49    inference(cnf_transformation,[],[f29])).
% 0.21/0.49  fof(f127,plain,(
% 0.21/0.49    ( ! [X0] : (r1_orders_2(X0,sK3,sK4) | ~r2_hidden(sK3,u1_struct_0(X0)) | ~m1_subset_1(sK4,u1_struct_0(X0)) | ~m1_subset_1(sK3,u1_struct_0(X0)) | ~m1_yellow_0(X0,sK1) | ~v4_yellow_0(X0,sK1)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f126,f82])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    l1_orders_2(sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f77,f33])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    l1_orders_2(sK1) | ~l1_struct_0(sK0)),
% 0.21/0.49    inference(resolution,[],[f35,f49])).
% 0.21/0.49  fof(f126,plain,(
% 0.21/0.49    ( ! [X0] : (r1_orders_2(X0,sK3,sK4) | ~r2_hidden(sK3,u1_struct_0(X0)) | ~m1_subset_1(sK4,u1_struct_0(X0)) | ~m1_subset_1(sK3,u1_struct_0(X0)) | ~m1_yellow_0(X0,sK1) | ~v4_yellow_0(X0,sK1) | ~l1_orders_2(sK1)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f125,f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    m1_subset_1(sK3,u1_struct_0(sK1))),
% 0.21/0.49    inference(cnf_transformation,[],[f29])).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    ( ! [X0] : (r1_orders_2(X0,sK3,sK4) | ~r2_hidden(sK3,u1_struct_0(X0)) | ~m1_subset_1(sK4,u1_struct_0(X0)) | ~m1_subset_1(sK3,u1_struct_0(X0)) | ~m1_subset_1(sK3,u1_struct_0(sK1)) | ~m1_yellow_0(X0,sK1) | ~v4_yellow_0(X0,sK1) | ~l1_orders_2(sK1)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f124,f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    m1_subset_1(sK4,u1_struct_0(sK1))),
% 0.21/0.49    inference(cnf_transformation,[],[f29])).
% 0.21/0.49  fof(f124,plain,(
% 0.21/0.49    ( ! [X0] : (r1_orders_2(X0,sK3,sK4) | ~r2_hidden(sK3,u1_struct_0(X0)) | ~m1_subset_1(sK4,u1_struct_0(X0)) | ~m1_subset_1(sK3,u1_struct_0(X0)) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK3,u1_struct_0(sK1)) | ~m1_yellow_0(X0,sK1) | ~v4_yellow_0(X0,sK1) | ~l1_orders_2(sK1)) )),
% 0.21/0.49    inference(resolution,[],[f45,f60])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    ( ! [X4,X0,X5,X1] : (r1_orders_2(X1,X4,X5) | ~r2_hidden(X4,u1_struct_0(X1)) | ~r1_orders_2(X0,X4,X5) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_yellow_0(X1,X0) | ~v4_yellow_0(X1,X0) | ~l1_orders_2(X0)) )),
% 0.21/0.49    inference(equality_resolution,[],[f59])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X5,X1] : (r1_orders_2(X1,X4,X5) | ~r2_hidden(X4,u1_struct_0(X1)) | ~r1_orders_2(X0,X2,X5) | X2 != X4 | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_yellow_0(X1,X0) | ~v4_yellow_0(X1,X0) | ~l1_orders_2(X0)) )),
% 0.21/0.49    inference(equality_resolution,[],[f48])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (r1_orders_2(X1,X4,X5) | ~r2_hidden(X4,u1_struct_0(X1)) | ~r1_orders_2(X0,X2,X3) | X3 != X5 | X2 != X4 | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_yellow_0(X1,X0) | ~v4_yellow_0(X1,X0) | ~l1_orders_2(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_orders_2(X1,X4,X5) | ~r2_hidden(X4,u1_struct_0(X1)) | ~r1_orders_2(X0,X2,X3) | X3 != X5 | X2 != X4 | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_yellow_0(X1,X0) | ~v4_yellow_0(X1,X0)) | ~l1_orders_2(X0))),
% 0.21/0.49    inference(flattening,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_orders_2(X1,X4,X5) | (~r2_hidden(X4,u1_struct_0(X1)) | ~r1_orders_2(X0,X2,X3) | X3 != X5 | X2 != X4)) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~m1_yellow_0(X1,X0) | ~v4_yellow_0(X1,X0))) | ~l1_orders_2(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : (l1_orders_2(X0) => ! [X1] : ((m1_yellow_0(X1,X0) & v4_yellow_0(X1,X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ((r2_hidden(X4,u1_struct_0(X1)) & r1_orders_2(X0,X2,X3) & X3 = X5 & X2 = X4) => r1_orders_2(X1,X4,X5))))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_yellow_0)).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    r1_orders_2(sK1,sK3,sK4)),
% 0.21/0.49    inference(cnf_transformation,[],[f29])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (11892)------------------------------
% 0.21/0.49  % (11892)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (11892)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (11892)Memory used [KB]: 1791
% 0.21/0.49  % (11892)Time elapsed: 0.067 s
% 0.21/0.49  % (11892)------------------------------
% 0.21/0.49  % (11892)------------------------------
% 0.21/0.50  % (11887)Success in time 0.139 s
%------------------------------------------------------------------------------
