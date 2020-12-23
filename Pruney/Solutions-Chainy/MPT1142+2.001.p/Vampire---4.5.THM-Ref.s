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
% DateTime   : Thu Dec  3 13:09:40 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   75 (1384 expanded)
%              Number of leaves         :    4 ( 241 expanded)
%              Depth                    :   35
%              Number of atoms          :  318 (10678 expanded)
%              Number of equality atoms :   67 ( 451 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f292,plain,(
    $false ),
    inference(subsumption_resolution,[],[f287,f277])).

fof(f277,plain,(
    r2_orders_2(sK0,sK1,sK1) ),
    inference(forward_demodulation,[],[f276,f239])).

fof(f239,plain,(
    sK1 = sK2 ),
    inference(subsumption_resolution,[],[f234,f114])).

fof(f114,plain,
    ( ~ r1_orders_2(sK0,sK2,sK1)
    | sK1 = sK2 ),
    inference(subsumption_resolution,[],[f113,f22])).

fof(f22,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_orders_2(X0,X1,X3)
                  & ( ( r2_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X2) )
                    | ( r1_orders_2(X0,X2,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_orders_2(X0,X1,X3)
                  & ( ( r2_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X2) )
                    | ( r1_orders_2(X0,X2,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( ( r2_orders_2(X0,X2,X3)
                          & r1_orders_2(X0,X1,X2) )
                        | ( r1_orders_2(X0,X2,X3)
                          & r2_orders_2(X0,X1,X2) ) )
                     => r2_orders_2(X0,X1,X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ( r2_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X2) )
                      | ( r1_orders_2(X0,X2,X3)
                        & r2_orders_2(X0,X1,X2) ) )
                   => r2_orders_2(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_orders_2)).

fof(f113,plain,
    ( sK1 = sK2
    | ~ v5_orders_2(sK0)
    | ~ r1_orders_2(sK0,sK2,sK1) ),
    inference(subsumption_resolution,[],[f112,f19])).

fof(f19,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f112,plain,
    ( sK1 = sK2
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ r1_orders_2(sK0,sK2,sK1) ),
    inference(subsumption_resolution,[],[f111,f20])).

fof(f20,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f111,plain,
    ( sK1 = sK2
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ r1_orders_2(sK0,sK2,sK1) ),
    inference(subsumption_resolution,[],[f109,f23])).

fof(f23,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f109,plain,
    ( sK1 = sK2
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ r1_orders_2(sK0,sK2,sK1) ),
    inference(duplicate_literal_removal,[],[f107])).

fof(f107,plain,
    ( sK1 = sK2
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ r1_orders_2(sK0,sK2,sK1)
    | sK1 = sK2 ),
    inference(resolution,[],[f78,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ r1_orders_2(X0,X2,X1)
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_orders_2(X0,X2,X1)
                  & r1_orders_2(X0,X1,X2) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_orders_2)).

fof(f78,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | sK1 = sK2 ),
    inference(subsumption_resolution,[],[f77,f23])).

fof(f77,plain,
    ( sK1 = sK2
    | r1_orders_2(sK0,sK1,sK2)
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f76,f19])).

fof(f76,plain,
    ( sK1 = sK2
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK2)
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f75,f20])).

fof(f75,plain,
    ( sK1 = sK2
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK2)
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f62,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).

fof(f62,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | sK1 = sK2 ),
    inference(subsumption_resolution,[],[f61,f23])).

fof(f61,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | ~ l1_orders_2(sK0)
    | sK1 = sK2 ),
    inference(subsumption_resolution,[],[f60,f19])).

fof(f60,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | sK1 = sK2 ),
    inference(subsumption_resolution,[],[f59,f20])).

fof(f59,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | sK1 = sK2 ),
    inference(duplicate_literal_removal,[],[f56])).

fof(f56,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | sK1 = sK2
    | r2_orders_2(sK0,sK1,sK2) ),
    inference(resolution,[],[f15,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | X1 = X2
      | r2_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f15,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | r2_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f234,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | sK1 = sK2 ),
    inference(duplicate_literal_removal,[],[f215])).

fof(f215,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | sK1 = sK2
    | sK1 = sK2 ),
    inference(superposition,[],[f70,f201])).

fof(f201,plain,
    ( sK1 = sK3
    | sK1 = sK2 ),
    inference(subsumption_resolution,[],[f183,f62])).

fof(f183,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | sK1 = sK2
    | sK1 = sK3 ),
    inference(superposition,[],[f18,f163])).

fof(f163,plain,
    ( sK2 = sK3
    | sK1 = sK2
    | sK1 = sK3 ),
    inference(subsumption_resolution,[],[f162,f18])).

fof(f162,plain,
    ( sK1 = sK2
    | sK2 = sK3
    | sK1 = sK3
    | r2_orders_2(sK0,sK1,sK3) ),
    inference(subsumption_resolution,[],[f161,f23])).

fof(f161,plain,
    ( sK1 = sK2
    | sK2 = sK3
    | ~ l1_orders_2(sK0)
    | sK1 = sK3
    | r2_orders_2(sK0,sK1,sK3) ),
    inference(subsumption_resolution,[],[f160,f17])).

fof(f17,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f160,plain,
    ( sK1 = sK2
    | sK2 = sK3
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | sK1 = sK3
    | r2_orders_2(sK0,sK1,sK3) ),
    inference(subsumption_resolution,[],[f157,f20])).

fof(f157,plain,
    ( sK1 = sK2
    | sK2 = sK3
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | sK1 = sK3
    | r2_orders_2(sK0,sK1,sK3) ),
    inference(resolution,[],[f155,f28])).

fof(f155,plain,
    ( r1_orders_2(sK0,sK1,sK3)
    | sK1 = sK2
    | sK2 = sK3 ),
    inference(subsumption_resolution,[],[f151,f17])).

fof(f151,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | sK1 = sK2
    | r1_orders_2(sK0,sK1,sK3)
    | sK2 = sK3 ),
    inference(resolution,[],[f118,f70])).

fof(f118,plain,(
    ! [X0] :
      ( ~ r1_orders_2(sK0,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | sK1 = sK2
      | r1_orders_2(sK0,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f117,f21])).

fof(f21,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f117,plain,(
    ! [X0] :
      ( sK1 = sK2
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v4_orders_2(sK0)
      | ~ r1_orders_2(sK0,sK2,X0)
      | r1_orders_2(sK0,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f116,f19])).

fof(f116,plain,(
    ! [X0] :
      ( sK1 = sK2
      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v4_orders_2(sK0)
      | ~ r1_orders_2(sK0,sK2,X0)
      | r1_orders_2(sK0,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f115,f20])).

fof(f115,plain,(
    ! [X0] :
      ( sK1 = sK2
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v4_orders_2(sK0)
      | ~ r1_orders_2(sK0,sK2,X0)
      | r1_orders_2(sK0,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f108,f23])).

fof(f108,plain,(
    ! [X0] :
      ( sK1 = sK2
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v4_orders_2(sK0)
      | ~ r1_orders_2(sK0,sK2,X0)
      | r1_orders_2(sK0,sK1,X0) ) ),
    inference(resolution,[],[f78,f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v4_orders_2(X0)
      | ~ r1_orders_2(X0,X2,X3)
      | r1_orders_2(X0,X1,X3) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X1,X3)
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X1,X3)
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X2) )
                   => r1_orders_2(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_orders_2)).

fof(f18,plain,(
    ~ r2_orders_2(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f7])).

fof(f70,plain,
    ( r1_orders_2(sK0,sK2,sK3)
    | sK2 = sK3 ),
    inference(subsumption_resolution,[],[f69,f23])).

fof(f69,plain,
    ( sK2 = sK3
    | r1_orders_2(sK0,sK2,sK3)
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f68,f17])).

fof(f68,plain,
    ( sK2 = sK3
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK2,sK3)
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f67,f19])).

fof(f67,plain,
    ( sK2 = sK3
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK2,sK3)
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f51,f26])).

fof(f51,plain,
    ( r2_orders_2(sK0,sK2,sK3)
    | sK2 = sK3 ),
    inference(subsumption_resolution,[],[f50,f23])).

fof(f50,plain,
    ( r2_orders_2(sK0,sK2,sK3)
    | ~ l1_orders_2(sK0)
    | sK2 = sK3 ),
    inference(subsumption_resolution,[],[f49,f17])).

fof(f49,plain,
    ( r2_orders_2(sK0,sK2,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | sK2 = sK3 ),
    inference(subsumption_resolution,[],[f48,f19])).

fof(f48,plain,
    ( r2_orders_2(sK0,sK2,sK3)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | sK2 = sK3 ),
    inference(duplicate_literal_removal,[],[f45])).

fof(f45,plain,
    ( r2_orders_2(sK0,sK2,sK3)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | sK2 = sK3
    | r2_orders_2(sK0,sK2,sK3) ),
    inference(resolution,[],[f14,f28])).

fof(f14,plain,
    ( r1_orders_2(sK0,sK2,sK3)
    | r2_orders_2(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f7])).

fof(f276,plain,(
    r2_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f243,f18])).

fof(f243,plain,
    ( r2_orders_2(sK0,sK1,sK3)
    | r2_orders_2(sK0,sK1,sK2) ),
    inference(backward_demodulation,[],[f16,f239])).

fof(f16,plain,
    ( r2_orders_2(sK0,sK2,sK3)
    | r2_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f287,plain,(
    ~ r2_orders_2(sK0,sK1,sK1) ),
    inference(backward_demodulation,[],[f18,f285])).

fof(f285,plain,(
    sK1 = sK3 ),
    inference(forward_demodulation,[],[f284,f239])).

fof(f284,plain,(
    sK2 = sK3 ),
    inference(subsumption_resolution,[],[f248,f18])).

fof(f248,plain,
    ( r2_orders_2(sK0,sK1,sK3)
    | sK2 = sK3 ),
    inference(backward_demodulation,[],[f51,f239])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:21:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (32513)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (32513)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % (32509)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (32531)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.50  % (32523)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.51  % (32526)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.51  % (32508)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (32520)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f292,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(subsumption_resolution,[],[f287,f277])).
% 0.21/0.51  fof(f277,plain,(
% 0.21/0.51    r2_orders_2(sK0,sK1,sK1)),
% 0.21/0.51    inference(forward_demodulation,[],[f276,f239])).
% 0.21/0.51  fof(f239,plain,(
% 0.21/0.51    sK1 = sK2),
% 0.21/0.51    inference(subsumption_resolution,[],[f234,f114])).
% 0.21/0.51  fof(f114,plain,(
% 0.21/0.51    ~r1_orders_2(sK0,sK2,sK1) | sK1 = sK2),
% 0.21/0.51    inference(subsumption_resolution,[],[f113,f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    v5_orders_2(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r2_orders_2(X0,X1,X3) & ((r2_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X2)) | (r1_orders_2(X0,X2,X3) & r2_orders_2(X0,X1,X2))) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0))),
% 0.21/0.51    inference(flattening,[],[f6])).
% 0.21/0.51  fof(f6,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r2_orders_2(X0,X1,X3) & ((r2_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X2)) | (r1_orders_2(X0,X2,X3) & r2_orders_2(X0,X1,X2)))) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,negated_conjecture,(
% 0.21/0.51    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (((r2_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X2)) | (r1_orders_2(X0,X2,X3) & r2_orders_2(X0,X1,X2))) => r2_orders_2(X0,X1,X3))))))),
% 0.21/0.51    inference(negated_conjecture,[],[f4])).
% 0.21/0.51  fof(f4,conjecture,(
% 0.21/0.51    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (((r2_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X2)) | (r1_orders_2(X0,X2,X3) & r2_orders_2(X0,X1,X2))) => r2_orders_2(X0,X1,X3))))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_orders_2)).
% 0.21/0.51  fof(f113,plain,(
% 0.21/0.51    sK1 = sK2 | ~v5_orders_2(sK0) | ~r1_orders_2(sK0,sK2,sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f112,f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f112,plain,(
% 0.21/0.51    sK1 = sK2 | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~r1_orders_2(sK0,sK2,sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f111,f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f111,plain,(
% 0.21/0.51    sK1 = sK2 | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~r1_orders_2(sK0,sK2,sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f109,f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    l1_orders_2(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f109,plain,(
% 0.21/0.51    sK1 = sK2 | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~r1_orders_2(sK0,sK2,sK1)),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f107])).
% 0.21/0.51  fof(f107,plain,(
% 0.21/0.51    sK1 = sK2 | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~r1_orders_2(sK0,sK2,sK1) | sK1 = sK2),
% 0.21/0.51    inference(resolution,[],[f78,f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r1_orders_2(X0,X1,X2) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~r1_orders_2(X0,X2,X1) | X1 = X2) )),
% 0.21/0.51    inference(cnf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (X1 = X2 | ~r1_orders_2(X0,X2,X1) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.21/0.51    inference(flattening,[],[f10])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((X1 = X2 | (~r1_orders_2(X0,X2,X1) | ~r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X1) & r1_orders_2(X0,X1,X2)) => X1 = X2))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_orders_2)).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    r1_orders_2(sK0,sK1,sK2) | sK1 = sK2),
% 0.21/0.51    inference(subsumption_resolution,[],[f77,f23])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    sK1 = sK2 | r1_orders_2(sK0,sK1,sK2) | ~l1_orders_2(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f76,f19])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    sK1 = sK2 | ~m1_subset_1(sK2,u1_struct_0(sK0)) | r1_orders_2(sK0,sK1,sK2) | ~l1_orders_2(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f75,f20])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    sK1 = sK2 | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | r1_orders_2(sK0,sK1,sK2) | ~l1_orders_2(sK0)),
% 0.21/0.51    inference(resolution,[],[f62,f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_orders_2(X0,X1,X2) | ~l1_orders_2(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    r2_orders_2(sK0,sK1,sK2) | sK1 = sK2),
% 0.21/0.51    inference(subsumption_resolution,[],[f61,f23])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    r2_orders_2(sK0,sK1,sK2) | ~l1_orders_2(sK0) | sK1 = sK2),
% 0.21/0.51    inference(subsumption_resolution,[],[f60,f19])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    r2_orders_2(sK0,sK1,sK2) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | sK1 = sK2),
% 0.21/0.51    inference(subsumption_resolution,[],[f59,f20])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    r2_orders_2(sK0,sK1,sK2) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | sK1 = sK2),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f56])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    r2_orders_2(sK0,sK1,sK2) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | sK1 = sK2 | r2_orders_2(sK0,sK1,sK2)),
% 0.21/0.51    inference(resolution,[],[f15,f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | X1 = X2 | r2_orders_2(X0,X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    r1_orders_2(sK0,sK1,sK2) | r2_orders_2(sK0,sK1,sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f234,plain,(
% 0.21/0.51    r1_orders_2(sK0,sK2,sK1) | sK1 = sK2),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f215])).
% 0.21/0.51  fof(f215,plain,(
% 0.21/0.51    r1_orders_2(sK0,sK2,sK1) | sK1 = sK2 | sK1 = sK2),
% 0.21/0.51    inference(superposition,[],[f70,f201])).
% 0.21/0.51  fof(f201,plain,(
% 0.21/0.51    sK1 = sK3 | sK1 = sK2),
% 0.21/0.51    inference(subsumption_resolution,[],[f183,f62])).
% 0.21/0.51  fof(f183,plain,(
% 0.21/0.51    ~r2_orders_2(sK0,sK1,sK2) | sK1 = sK2 | sK1 = sK3),
% 0.21/0.51    inference(superposition,[],[f18,f163])).
% 0.21/0.51  fof(f163,plain,(
% 0.21/0.51    sK2 = sK3 | sK1 = sK2 | sK1 = sK3),
% 0.21/0.51    inference(subsumption_resolution,[],[f162,f18])).
% 0.21/0.51  fof(f162,plain,(
% 0.21/0.51    sK1 = sK2 | sK2 = sK3 | sK1 = sK3 | r2_orders_2(sK0,sK1,sK3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f161,f23])).
% 0.21/0.51  fof(f161,plain,(
% 0.21/0.51    sK1 = sK2 | sK2 = sK3 | ~l1_orders_2(sK0) | sK1 = sK3 | r2_orders_2(sK0,sK1,sK3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f160,f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    m1_subset_1(sK3,u1_struct_0(sK0))),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f160,plain,(
% 0.21/0.51    sK1 = sK2 | sK2 = sK3 | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | sK1 = sK3 | r2_orders_2(sK0,sK1,sK3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f157,f20])).
% 0.21/0.51  fof(f157,plain,(
% 0.21/0.51    sK1 = sK2 | sK2 = sK3 | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | sK1 = sK3 | r2_orders_2(sK0,sK1,sK3)),
% 0.21/0.51    inference(resolution,[],[f155,f28])).
% 0.21/0.51  fof(f155,plain,(
% 0.21/0.51    r1_orders_2(sK0,sK1,sK3) | sK1 = sK2 | sK2 = sK3),
% 0.21/0.51    inference(subsumption_resolution,[],[f151,f17])).
% 0.21/0.51  fof(f151,plain,(
% 0.21/0.51    ~m1_subset_1(sK3,u1_struct_0(sK0)) | sK1 = sK2 | r1_orders_2(sK0,sK1,sK3) | sK2 = sK3),
% 0.21/0.51    inference(resolution,[],[f118,f70])).
% 0.21/0.51  fof(f118,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_orders_2(sK0,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | sK1 = sK2 | r1_orders_2(sK0,sK1,X0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f117,f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    v4_orders_2(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f117,plain,(
% 0.21/0.51    ( ! [X0] : (sK1 = sK2 | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v4_orders_2(sK0) | ~r1_orders_2(sK0,sK2,X0) | r1_orders_2(sK0,sK1,X0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f116,f19])).
% 0.21/0.51  fof(f116,plain,(
% 0.21/0.51    ( ! [X0] : (sK1 = sK2 | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v4_orders_2(sK0) | ~r1_orders_2(sK0,sK2,X0) | r1_orders_2(sK0,sK1,X0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f115,f20])).
% 0.21/0.51  fof(f115,plain,(
% 0.21/0.51    ( ! [X0] : (sK1 = sK2 | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v4_orders_2(sK0) | ~r1_orders_2(sK0,sK2,X0) | r1_orders_2(sK0,sK1,X0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f108,f23])).
% 0.21/0.51  fof(f108,plain,(
% 0.21/0.51    ( ! [X0] : (sK1 = sK2 | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v4_orders_2(sK0) | ~r1_orders_2(sK0,sK2,X0) | r1_orders_2(sK0,sK1,X0)) )),
% 0.21/0.51    inference(resolution,[],[f78,f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~r1_orders_2(X0,X1,X2) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v4_orders_2(X0) | ~r1_orders_2(X0,X2,X3) | r1_orders_2(X0,X1,X3)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_orders_2(X0,X1,X3) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v4_orders_2(X0))),
% 0.21/0.51    inference(flattening,[],[f8])).
% 0.21/0.51  fof(f8,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r1_orders_2(X0,X1,X3) | (~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v4_orders_2(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X2)) => r1_orders_2(X0,X1,X3))))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_orders_2)).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ~r2_orders_2(sK0,sK1,sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    r1_orders_2(sK0,sK2,sK3) | sK2 = sK3),
% 0.21/0.51    inference(subsumption_resolution,[],[f69,f23])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    sK2 = sK3 | r1_orders_2(sK0,sK2,sK3) | ~l1_orders_2(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f68,f17])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    sK2 = sK3 | ~m1_subset_1(sK3,u1_struct_0(sK0)) | r1_orders_2(sK0,sK2,sK3) | ~l1_orders_2(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f67,f19])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    sK2 = sK3 | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | r1_orders_2(sK0,sK2,sK3) | ~l1_orders_2(sK0)),
% 0.21/0.51    inference(resolution,[],[f51,f26])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    r2_orders_2(sK0,sK2,sK3) | sK2 = sK3),
% 0.21/0.51    inference(subsumption_resolution,[],[f50,f23])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    r2_orders_2(sK0,sK2,sK3) | ~l1_orders_2(sK0) | sK2 = sK3),
% 0.21/0.51    inference(subsumption_resolution,[],[f49,f17])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    r2_orders_2(sK0,sK2,sK3) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | sK2 = sK3),
% 0.21/0.51    inference(subsumption_resolution,[],[f48,f19])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    r2_orders_2(sK0,sK2,sK3) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | sK2 = sK3),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    r2_orders_2(sK0,sK2,sK3) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | sK2 = sK3 | r2_orders_2(sK0,sK2,sK3)),
% 0.21/0.51    inference(resolution,[],[f14,f28])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    r1_orders_2(sK0,sK2,sK3) | r2_orders_2(sK0,sK2,sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f276,plain,(
% 0.21/0.51    r2_orders_2(sK0,sK1,sK2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f243,f18])).
% 0.21/0.51  fof(f243,plain,(
% 0.21/0.51    r2_orders_2(sK0,sK1,sK3) | r2_orders_2(sK0,sK1,sK2)),
% 0.21/0.51    inference(backward_demodulation,[],[f16,f239])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    r2_orders_2(sK0,sK2,sK3) | r2_orders_2(sK0,sK1,sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f287,plain,(
% 0.21/0.51    ~r2_orders_2(sK0,sK1,sK1)),
% 0.21/0.51    inference(backward_demodulation,[],[f18,f285])).
% 0.21/0.51  fof(f285,plain,(
% 0.21/0.51    sK1 = sK3),
% 0.21/0.51    inference(forward_demodulation,[],[f284,f239])).
% 0.21/0.51  fof(f284,plain,(
% 0.21/0.51    sK2 = sK3),
% 0.21/0.51    inference(subsumption_resolution,[],[f248,f18])).
% 0.21/0.51  fof(f248,plain,(
% 0.21/0.51    r2_orders_2(sK0,sK1,sK3) | sK2 = sK3),
% 0.21/0.51    inference(backward_demodulation,[],[f51,f239])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (32513)------------------------------
% 0.21/0.51  % (32513)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (32513)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (32513)Memory used [KB]: 6140
% 0.21/0.51  % (32513)Time elapsed: 0.099 s
% 0.21/0.51  % (32513)------------------------------
% 0.21/0.51  % (32513)------------------------------
% 0.21/0.51  % (32507)Success in time 0.154 s
%------------------------------------------------------------------------------
