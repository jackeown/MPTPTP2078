%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 497 expanded)
%              Number of leaves         :   12 ( 124 expanded)
%              Depth                    :   50
%              Number of atoms          :  476 (1700 expanded)
%              Number of equality atoms :   19 ( 177 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f195,plain,(
    $false ),
    inference(subsumption_resolution,[],[f194,f64])).

fof(f64,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(forward_demodulation,[],[f28,f39])).

fof(f39,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

fof(f28,plain,(
    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & v2_lattice3(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & v2_lattice3(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ( v2_lattice3(k2_yellow_1(X0))
         => ! [X1] :
              ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
                 => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v2_lattice3(k2_yellow_1(X0))
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
               => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_yellow_1)).

fof(f194,plain,(
    ~ m1_subset_1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f192,f63])).

fof(f63,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(forward_demodulation,[],[f30,f39])).

fof(f30,plain,(
    m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f192,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | ~ m1_subset_1(sK2,sK0) ),
    inference(resolution,[],[f191,f141])).

fof(f141,plain,(
    ! [X19,X18] :
      ( r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X18,X19),X18)
      | ~ m1_subset_1(X18,sK0)
      | ~ m1_subset_1(X19,sK0) ) ),
    inference(subsumption_resolution,[],[f119,f105])).

fof(f105,plain,(
    ! [X12,X13] :
      ( m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X12,X13),sK0)
      | ~ m1_subset_1(X13,sK0)
      | ~ m1_subset_1(X12,sK0) ) ),
    inference(forward_demodulation,[],[f104,f39])).

fof(f104,plain,(
    ! [X12,X13] :
      ( ~ m1_subset_1(X13,sK0)
      | ~ m1_subset_1(X12,sK0)
      | m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X12,X13),u1_struct_0(k2_yellow_1(sK0))) ) ),
    inference(forward_demodulation,[],[f103,f39])).

fof(f103,plain,(
    ! [X12,X13] :
      ( ~ m1_subset_1(X12,sK0)
      | ~ m1_subset_1(X13,u1_struct_0(k2_yellow_1(sK0)))
      | m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X12,X13),u1_struct_0(k2_yellow_1(sK0))) ) ),
    inference(forward_demodulation,[],[f102,f39])).

fof(f102,plain,(
    ! [X12,X13] :
      ( ~ m1_subset_1(X12,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(X13,u1_struct_0(k2_yellow_1(sK0)))
      | m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X12,X13),u1_struct_0(k2_yellow_1(sK0))) ) ),
    inference(subsumption_resolution,[],[f101,f38])).

fof(f38,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(f101,plain,(
    ! [X12,X13] :
      ( ~ l1_orders_2(k2_yellow_1(sK0))
      | ~ m1_subset_1(X12,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(X13,u1_struct_0(k2_yellow_1(sK0)))
      | m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X12,X13),u1_struct_0(k2_yellow_1(sK0))) ) ),
    inference(subsumption_resolution,[],[f75,f36])).

fof(f36,plain,(
    ! [X0] : v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v4_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).

fof(f75,plain,(
    ! [X12,X13] :
      ( ~ v5_orders_2(k2_yellow_1(sK0))
      | ~ l1_orders_2(k2_yellow_1(sK0))
      | ~ m1_subset_1(X12,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(X13,u1_struct_0(k2_yellow_1(sK0)))
      | m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X12,X13),u1_struct_0(k2_yellow_1(sK0))) ) ),
    inference(resolution,[],[f32,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k12_lattice3)).

fof(f32,plain,(
    v2_lattice3(k2_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f119,plain,(
    ! [X19,X18] :
      ( ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X18,X19),sK0)
      | ~ m1_subset_1(X19,sK0)
      | ~ m1_subset_1(X18,sK0)
      | r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X18,X19),X18) ) ),
    inference(forward_demodulation,[],[f118,f39])).

fof(f118,plain,(
    ! [X19,X18] :
      ( ~ m1_subset_1(X19,sK0)
      | ~ m1_subset_1(X18,sK0)
      | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X18,X19),u1_struct_0(k2_yellow_1(sK0)))
      | r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X18,X19),X18) ) ),
    inference(forward_demodulation,[],[f117,f39])).

fof(f117,plain,(
    ! [X19,X18] :
      ( ~ m1_subset_1(X18,sK0)
      | ~ m1_subset_1(X19,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X18,X19),u1_struct_0(k2_yellow_1(sK0)))
      | r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X18,X19),X18) ) ),
    inference(forward_demodulation,[],[f116,f39])).

fof(f116,plain,(
    ! [X19,X18] :
      ( ~ m1_subset_1(X18,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(X19,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X18,X19),u1_struct_0(k2_yellow_1(sK0)))
      | r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X18,X19),X18) ) ),
    inference(subsumption_resolution,[],[f115,f38])).

fof(f115,plain,(
    ! [X19,X18] :
      ( ~ l1_orders_2(k2_yellow_1(sK0))
      | ~ m1_subset_1(X18,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(X19,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X18,X19),u1_struct_0(k2_yellow_1(sK0)))
      | r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X18,X19),X18) ) ),
    inference(subsumption_resolution,[],[f78,f36])).

fof(f78,plain,(
    ! [X19,X18] :
      ( ~ v5_orders_2(k2_yellow_1(sK0))
      | ~ l1_orders_2(k2_yellow_1(sK0))
      | ~ m1_subset_1(X18,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(X19,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X18,X19),u1_struct_0(k2_yellow_1(sK0)))
      | r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X18,X19),X18) ) ),
    inference(resolution,[],[f32,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | r1_orders_2(X0,k12_lattice3(X0,X1,X2),X1) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_orders_2(X0,X3,X1)
      | k12_lattice3(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k12_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k12_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( k12_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X4,X2)
                              & r1_orders_2(X0,X4,X1) )
                           => r1_orders_2(X0,X4,X3) ) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_yellow_0)).

fof(f191,plain,(
    ~ r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) ),
    inference(subsumption_resolution,[],[f190,f31])).

fof(f31,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f190,plain,
    ( ~ r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f189,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v1_orders_2(k2_yellow_1(X0))
        & ~ v2_struct_0(k2_yellow_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_orders_2(k2_yellow_1(X0))
        & ~ v2_struct_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_yellow_1)).

fof(f189,plain,
    ( v2_struct_0(k2_yellow_1(sK0))
    | ~ r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) ),
    inference(subsumption_resolution,[],[f188,f63])).

fof(f188,plain,
    ( ~ r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | v2_struct_0(k2_yellow_1(sK0))
    | ~ m1_subset_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f187,f64])).

fof(f187,plain,
    ( ~ r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | v2_struct_0(k2_yellow_1(sK0))
    | ~ m1_subset_1(sK2,sK0)
    | ~ m1_subset_1(sK1,sK0) ),
    inference(resolution,[],[f181,f105])).

fof(f181,plain,
    ( ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0)
    | ~ r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | v2_struct_0(k2_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f180,f63])).

fof(f180,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0)
    | ~ r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | v2_struct_0(k2_yellow_1(sK0)) ),
    inference(forward_demodulation,[],[f179,f39])).

fof(f179,plain,
    ( ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | v2_struct_0(k2_yellow_1(sK0)) ),
    inference(forward_demodulation,[],[f178,f39])).

fof(f178,plain,
    ( ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | v2_struct_0(k2_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f177,f38])).

fof(f177,plain,
    ( ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | v2_struct_0(k2_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f175,f34])).

fof(f34,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f175,plain,
    ( ~ v3_orders_2(k2_yellow_1(sK0))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | v2_struct_0(k2_yellow_1(sK0)) ),
    inference(resolution,[],[f173,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X2)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f173,plain,(
    ~ r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) ),
    inference(subsumption_resolution,[],[f172,f64])).

fof(f172,plain,
    ( ~ r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | ~ m1_subset_1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f170,f63])).

fof(f170,plain,
    ( ~ r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | ~ m1_subset_1(sK1,sK0)
    | ~ m1_subset_1(sK2,sK0) ),
    inference(resolution,[],[f169,f140])).

fof(f140,plain,(
    ! [X17,X16] :
      ( r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X16,X17),X17)
      | ~ m1_subset_1(X16,sK0)
      | ~ m1_subset_1(X17,sK0) ) ),
    inference(subsumption_resolution,[],[f114,f105])).

fof(f114,plain,(
    ! [X17,X16] :
      ( ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X16,X17),sK0)
      | ~ m1_subset_1(X17,sK0)
      | ~ m1_subset_1(X16,sK0)
      | r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X16,X17),X17) ) ),
    inference(forward_demodulation,[],[f113,f39])).

fof(f113,plain,(
    ! [X17,X16] :
      ( ~ m1_subset_1(X17,sK0)
      | ~ m1_subset_1(X16,sK0)
      | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X16,X17),u1_struct_0(k2_yellow_1(sK0)))
      | r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X16,X17),X17) ) ),
    inference(forward_demodulation,[],[f112,f39])).

fof(f112,plain,(
    ! [X17,X16] :
      ( ~ m1_subset_1(X16,sK0)
      | ~ m1_subset_1(X17,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X16,X17),u1_struct_0(k2_yellow_1(sK0)))
      | r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X16,X17),X17) ) ),
    inference(forward_demodulation,[],[f111,f39])).

fof(f111,plain,(
    ! [X17,X16] :
      ( ~ m1_subset_1(X16,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(X17,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X16,X17),u1_struct_0(k2_yellow_1(sK0)))
      | r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X16,X17),X17) ) ),
    inference(subsumption_resolution,[],[f110,f38])).

fof(f110,plain,(
    ! [X17,X16] :
      ( ~ l1_orders_2(k2_yellow_1(sK0))
      | ~ m1_subset_1(X16,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(X17,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X16,X17),u1_struct_0(k2_yellow_1(sK0)))
      | r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X16,X17),X17) ) ),
    inference(subsumption_resolution,[],[f77,f36])).

fof(f77,plain,(
    ! [X17,X16] :
      ( ~ v5_orders_2(k2_yellow_1(sK0))
      | ~ l1_orders_2(k2_yellow_1(sK0))
      | ~ m1_subset_1(X16,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(X17,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X16,X17),u1_struct_0(k2_yellow_1(sK0)))
      | r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X16,X17),X17) ) ),
    inference(resolution,[],[f32,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | r1_orders_2(X0,k12_lattice3(X0,X1,X2),X2) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_orders_2(X0,X3,X2)
      | k12_lattice3(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f169,plain,
    ( ~ r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | ~ r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) ),
    inference(subsumption_resolution,[],[f168,f31])).

fof(f168,plain,
    ( ~ r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | ~ r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f167,f41])).

fof(f167,plain,
    ( v2_struct_0(k2_yellow_1(sK0))
    | ~ r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | ~ r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) ),
    inference(subsumption_resolution,[],[f166,f63])).

fof(f166,plain,
    ( ~ r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | ~ r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | v2_struct_0(k2_yellow_1(sK0))
    | ~ m1_subset_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f165,f64])).

fof(f165,plain,
    ( ~ r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | ~ r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | v2_struct_0(k2_yellow_1(sK0))
    | ~ m1_subset_1(sK2,sK0)
    | ~ m1_subset_1(sK1,sK0) ),
    inference(resolution,[],[f160,f105])).

fof(f160,plain,
    ( ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0)
    | ~ r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | ~ r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | v2_struct_0(k2_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f159,f64])).

fof(f159,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0)
    | ~ r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | ~ r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | v2_struct_0(k2_yellow_1(sK0)) ),
    inference(forward_demodulation,[],[f158,f39])).

fof(f158,plain,
    ( ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0)
    | ~ r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | v2_struct_0(k2_yellow_1(sK0)) ),
    inference(forward_demodulation,[],[f157,f39])).

fof(f157,plain,
    ( ~ r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | v2_struct_0(k2_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f156,f38])).

fof(f156,plain,
    ( ~ r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | v2_struct_0(k2_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f154,f34])).

fof(f154,plain,
    ( ~ r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | ~ v3_orders_2(k2_yellow_1(sK0))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | v2_struct_0(k2_yellow_1(sK0)) ),
    inference(resolution,[],[f152,f53])).

fof(f152,plain,
    ( ~ r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | ~ r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) ),
    inference(subsumption_resolution,[],[f151,f63])).

fof(f151,plain,
    ( ~ r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | ~ r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | ~ m1_subset_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f150,f64])).

fof(f150,plain,
    ( ~ r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | ~ r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | ~ m1_subset_1(sK2,sK0)
    | ~ m1_subset_1(sK1,sK0) ),
    inference(resolution,[],[f149,f105])).

fof(f149,plain,
    ( ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0)
    | ~ r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | ~ r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) ),
    inference(subsumption_resolution,[],[f148,f63])).

fof(f148,plain,
    ( ~ r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0)
    | ~ m1_subset_1(sK1,sK0)
    | ~ r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) ),
    inference(resolution,[],[f147,f70])).

fof(f70,plain,(
    ! [X2,X3] :
      ( r1_tarski(X2,X3)
      | ~ m1_subset_1(X2,sK0)
      | ~ m1_subset_1(X3,sK0)
      | ~ r3_orders_2(k2_yellow_1(sK0),X2,X3) ) ),
    inference(forward_demodulation,[],[f69,f39])).

fof(f69,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,sK0)
      | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK0)))
      | r1_tarski(X2,X3)
      | ~ r3_orders_2(k2_yellow_1(sK0),X2,X3) ) ),
    inference(forward_demodulation,[],[f66,f39])).

fof(f66,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK0)))
      | r1_tarski(X2,X3)
      | ~ r3_orders_2(k2_yellow_1(sK0),X2,X3) ) ),
    inference(resolution,[],[f31,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | r1_tarski(X1,X2)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow_1)).

fof(f147,plain,
    ( ~ r1_tarski(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | ~ r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) ),
    inference(subsumption_resolution,[],[f146,f63])).

fof(f146,plain,
    ( ~ r1_tarski(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | ~ r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | ~ m1_subset_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f145,f64])).

fof(f145,plain,
    ( ~ r1_tarski(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | ~ r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | ~ m1_subset_1(sK2,sK0)
    | ~ m1_subset_1(sK1,sK0) ),
    inference(resolution,[],[f139,f105])).

fof(f139,plain,
    ( ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0)
    | ~ r1_tarski(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | ~ r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) ),
    inference(subsumption_resolution,[],[f138,f64])).

fof(f138,plain,
    ( ~ r1_tarski(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0)
    | ~ m1_subset_1(sK2,sK0)
    | ~ r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) ),
    inference(resolution,[],[f133,f70])).

fof(f133,plain,
    ( ~ r1_tarski(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | ~ r1_tarski(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) ),
    inference(subsumption_resolution,[],[f132,f64])).

fof(f132,plain,
    ( ~ r1_tarski(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | ~ r1_tarski(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | ~ m1_subset_1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f130,f63])).

fof(f130,plain,
    ( ~ r1_tarski(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | ~ r1_tarski(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | ~ m1_subset_1(sK1,sK0)
    | ~ m1_subset_1(sK2,sK0) ),
    inference(superposition,[],[f126,f109])).

fof(f109,plain,(
    ! [X14,X15] :
      ( k12_lattice3(k2_yellow_1(sK0),X14,X15) = k11_lattice3(k2_yellow_1(sK0),X14,X15)
      | ~ m1_subset_1(X14,sK0)
      | ~ m1_subset_1(X15,sK0) ) ),
    inference(forward_demodulation,[],[f108,f39])).

fof(f108,plain,(
    ! [X14,X15] :
      ( ~ m1_subset_1(X14,sK0)
      | ~ m1_subset_1(X15,u1_struct_0(k2_yellow_1(sK0)))
      | k12_lattice3(k2_yellow_1(sK0),X14,X15) = k11_lattice3(k2_yellow_1(sK0),X14,X15) ) ),
    inference(forward_demodulation,[],[f107,f39])).

fof(f107,plain,(
    ! [X14,X15] :
      ( ~ m1_subset_1(X14,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(X15,u1_struct_0(k2_yellow_1(sK0)))
      | k12_lattice3(k2_yellow_1(sK0),X14,X15) = k11_lattice3(k2_yellow_1(sK0),X14,X15) ) ),
    inference(subsumption_resolution,[],[f106,f38])).

fof(f106,plain,(
    ! [X14,X15] :
      ( ~ l1_orders_2(k2_yellow_1(sK0))
      | ~ m1_subset_1(X14,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(X15,u1_struct_0(k2_yellow_1(sK0)))
      | k12_lattice3(k2_yellow_1(sK0),X14,X15) = k11_lattice3(k2_yellow_1(sK0),X14,X15) ) ),
    inference(subsumption_resolution,[],[f76,f36])).

fof(f76,plain,(
    ! [X14,X15] :
      ( ~ v5_orders_2(k2_yellow_1(sK0))
      | ~ l1_orders_2(k2_yellow_1(sK0))
      | ~ m1_subset_1(X14,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(X15,u1_struct_0(k2_yellow_1(sK0)))
      | k12_lattice3(k2_yellow_1(sK0),X14,X15) = k11_lattice3(k2_yellow_1(sK0),X14,X15) ) ),
    inference(resolution,[],[f32,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

fof(f126,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) ),
    inference(resolution,[],[f58,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f57,f52])).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f58,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f29,f52])).

fof(f29,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:09:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (27996)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.50  % (28003)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.50  % (28024)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.50  % (27996)Refutation not found, incomplete strategy% (27996)------------------------------
% 0.21/0.50  % (27996)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (27996)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (27996)Memory used [KB]: 1663
% 0.21/0.50  % (27996)Time elapsed: 0.091 s
% 0.21/0.50  % (27996)------------------------------
% 0.21/0.50  % (27996)------------------------------
% 0.21/0.50  % (28020)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.51  % (28008)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (28018)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (28012)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.51  % (28006)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (28007)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (28010)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (28006)Refutation not found, incomplete strategy% (28006)------------------------------
% 0.21/0.52  % (28006)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (28006)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (28006)Memory used [KB]: 10618
% 0.21/0.52  % (28006)Time elapsed: 0.107 s
% 0.21/0.52  % (28006)------------------------------
% 0.21/0.52  % (28006)------------------------------
% 0.21/0.52  % (28007)Refutation not found, incomplete strategy% (28007)------------------------------
% 0.21/0.52  % (28007)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (28007)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (28007)Memory used [KB]: 10618
% 0.21/0.52  % (28007)Time elapsed: 0.106 s
% 0.21/0.52  % (28007)------------------------------
% 0.21/0.52  % (28007)------------------------------
% 0.21/0.52  % (27997)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (28023)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (28015)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (27998)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (28002)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (27999)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (28001)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (28018)Refutation not found, incomplete strategy% (28018)------------------------------
% 0.21/0.53  % (28018)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (28018)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (28018)Memory used [KB]: 10746
% 0.21/0.53  % (28018)Time elapsed: 0.097 s
% 0.21/0.53  % (28018)------------------------------
% 0.21/0.53  % (28018)------------------------------
% 0.21/0.53  % (27998)Refutation not found, incomplete strategy% (27998)------------------------------
% 0.21/0.53  % (27998)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (27998)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (27998)Memory used [KB]: 10746
% 0.21/0.53  % (27998)Time elapsed: 0.126 s
% 0.21/0.53  % (27998)------------------------------
% 0.21/0.53  % (27998)------------------------------
% 0.21/0.53  % (28000)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (28025)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (28013)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (28013)Refutation not found, incomplete strategy% (28013)------------------------------
% 0.21/0.54  % (28013)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (28013)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (28013)Memory used [KB]: 10618
% 0.21/0.54  % (28013)Time elapsed: 0.127 s
% 0.21/0.54  % (28013)------------------------------
% 0.21/0.54  % (28013)------------------------------
% 0.21/0.54  % (28019)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (28016)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (28022)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (28017)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (28021)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (28022)Refutation not found, incomplete strategy% (28022)------------------------------
% 0.21/0.54  % (28022)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (28022)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (28022)Memory used [KB]: 10746
% 0.21/0.54  % (28022)Time elapsed: 0.138 s
% 0.21/0.54  % (28022)------------------------------
% 0.21/0.54  % (28022)------------------------------
% 0.21/0.54  % (28021)Refutation not found, incomplete strategy% (28021)------------------------------
% 0.21/0.54  % (28021)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (28021)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (28021)Memory used [KB]: 6268
% 0.21/0.54  % (28021)Time elapsed: 0.140 s
% 0.21/0.54  % (28021)------------------------------
% 0.21/0.54  % (28021)------------------------------
% 0.21/0.54  % (28017)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f195,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(subsumption_resolution,[],[f194,f64])).
% 0.21/0.54  fof(f64,plain,(
% 0.21/0.54    m1_subset_1(sK2,sK0)),
% 0.21/0.54    inference(forward_demodulation,[],[f28,f39])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,axiom,(
% 0.21/0.54    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v2_lattice3(k2_yellow_1(X0)) & ~v1_xboole_0(X0))),
% 0.21/0.54    inference(flattening,[],[f14])).
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    ? [X0] : ((? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v2_lattice3(k2_yellow_1(X0))) & ~v1_xboole_0(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,negated_conjecture,(
% 0.21/0.54    ~! [X0] : (~v1_xboole_0(X0) => (v2_lattice3(k2_yellow_1(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))))))),
% 0.21/0.54    inference(negated_conjecture,[],[f12])).
% 0.21/0.54  fof(f12,conjecture,(
% 0.21/0.54    ! [X0] : (~v1_xboole_0(X0) => (v2_lattice3(k2_yellow_1(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_yellow_1)).
% 0.21/0.54  fof(f194,plain,(
% 0.21/0.54    ~m1_subset_1(sK2,sK0)),
% 0.21/0.54    inference(subsumption_resolution,[],[f192,f63])).
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    m1_subset_1(sK1,sK0)),
% 0.21/0.54    inference(forward_demodulation,[],[f30,f39])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f192,plain,(
% 0.21/0.54    ~m1_subset_1(sK1,sK0) | ~m1_subset_1(sK2,sK0)),
% 0.21/0.54    inference(resolution,[],[f191,f141])).
% 0.21/0.54  fof(f141,plain,(
% 0.21/0.54    ( ! [X19,X18] : (r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X18,X19),X18) | ~m1_subset_1(X18,sK0) | ~m1_subset_1(X19,sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f119,f105])).
% 0.21/0.54  fof(f105,plain,(
% 0.21/0.54    ( ! [X12,X13] : (m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X12,X13),sK0) | ~m1_subset_1(X13,sK0) | ~m1_subset_1(X12,sK0)) )),
% 0.21/0.54    inference(forward_demodulation,[],[f104,f39])).
% 0.21/0.54  fof(f104,plain,(
% 0.21/0.54    ( ! [X12,X13] : (~m1_subset_1(X13,sK0) | ~m1_subset_1(X12,sK0) | m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X12,X13),u1_struct_0(k2_yellow_1(sK0)))) )),
% 0.21/0.54    inference(forward_demodulation,[],[f103,f39])).
% 0.21/0.54  fof(f103,plain,(
% 0.21/0.54    ( ! [X12,X13] : (~m1_subset_1(X12,sK0) | ~m1_subset_1(X13,u1_struct_0(k2_yellow_1(sK0))) | m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X12,X13),u1_struct_0(k2_yellow_1(sK0)))) )),
% 0.21/0.54    inference(forward_demodulation,[],[f102,f39])).
% 0.21/0.54  fof(f102,plain,(
% 0.21/0.54    ( ! [X12,X13] : (~m1_subset_1(X12,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X13,u1_struct_0(k2_yellow_1(sK0))) | m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X12,X13),u1_struct_0(k2_yellow_1(sK0)))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f101,f38])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).
% 0.21/0.54  fof(f101,plain,(
% 0.21/0.54    ( ! [X12,X13] : (~l1_orders_2(k2_yellow_1(sK0)) | ~m1_subset_1(X12,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X13,u1_struct_0(k2_yellow_1(sK0))) | m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X12,X13),u1_struct_0(k2_yellow_1(sK0)))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f75,f36])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ( ! [X0] : (v5_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).
% 0.21/0.54  fof(f75,plain,(
% 0.21/0.54    ( ! [X12,X13] : (~v5_orders_2(k2_yellow_1(sK0)) | ~l1_orders_2(k2_yellow_1(sK0)) | ~m1_subset_1(X12,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X13,u1_struct_0(k2_yellow_1(sK0))) | m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X12,X13),u1_struct_0(k2_yellow_1(sK0)))) )),
% 0.21/0.54    inference(resolution,[],[f32,f55])).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~v2_lattice3(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 0.21/0.54    inference(flattening,[],[f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k12_lattice3)).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    v2_lattice3(k2_yellow_1(sK0))),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f119,plain,(
% 0.21/0.54    ( ! [X19,X18] : (~m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X18,X19),sK0) | ~m1_subset_1(X19,sK0) | ~m1_subset_1(X18,sK0) | r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X18,X19),X18)) )),
% 0.21/0.54    inference(forward_demodulation,[],[f118,f39])).
% 0.21/0.54  fof(f118,plain,(
% 0.21/0.54    ( ! [X19,X18] : (~m1_subset_1(X19,sK0) | ~m1_subset_1(X18,sK0) | ~m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X18,X19),u1_struct_0(k2_yellow_1(sK0))) | r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X18,X19),X18)) )),
% 0.21/0.54    inference(forward_demodulation,[],[f117,f39])).
% 0.21/0.54  fof(f117,plain,(
% 0.21/0.54    ( ! [X19,X18] : (~m1_subset_1(X18,sK0) | ~m1_subset_1(X19,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X18,X19),u1_struct_0(k2_yellow_1(sK0))) | r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X18,X19),X18)) )),
% 0.21/0.54    inference(forward_demodulation,[],[f116,f39])).
% 0.21/0.54  fof(f116,plain,(
% 0.21/0.54    ( ! [X19,X18] : (~m1_subset_1(X18,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X19,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X18,X19),u1_struct_0(k2_yellow_1(sK0))) | r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X18,X19),X18)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f115,f38])).
% 0.21/0.54  fof(f115,plain,(
% 0.21/0.54    ( ! [X19,X18] : (~l1_orders_2(k2_yellow_1(sK0)) | ~m1_subset_1(X18,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X19,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X18,X19),u1_struct_0(k2_yellow_1(sK0))) | r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X18,X19),X18)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f78,f36])).
% 0.21/0.54  fof(f78,plain,(
% 0.21/0.54    ( ! [X19,X18] : (~v5_orders_2(k2_yellow_1(sK0)) | ~l1_orders_2(k2_yellow_1(sK0)) | ~m1_subset_1(X18,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X19,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X18,X19),u1_struct_0(k2_yellow_1(sK0))) | r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X18,X19),X18)) )),
% 0.21/0.54    inference(resolution,[],[f32,f61])).
% 0.21/0.54  fof(f61,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~v2_lattice3(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) | r1_orders_2(X0,k12_lattice3(X0,X1,X2),X1)) )),
% 0.21/0.54    inference(equality_resolution,[],[f50])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~v5_orders_2(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | r1_orders_2(X0,X3,X1) | k12_lattice3(X0,X1,X2) != X3) )),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k12_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 0.21/0.54    inference(flattening,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k12_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X4,X3) | (~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k12_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1)) => r1_orders_2(X0,X4,X3))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)))))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_yellow_0)).
% 0.21/0.54  fof(f191,plain,(
% 0.21/0.54    ~r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)),
% 0.21/0.54    inference(subsumption_resolution,[],[f190,f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ~v1_xboole_0(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f190,plain,(
% 0.21/0.54    ~r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | v1_xboole_0(sK0)),
% 0.21/0.54    inference(resolution,[],[f189,f41])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    ( ! [X0] : (~v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f16])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ! [X0] : ((v1_orders_2(k2_yellow_1(X0)) & ~v2_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0] : (~v1_xboole_0(X0) => (v1_orders_2(k2_yellow_1(X0)) & ~v2_struct_0(k2_yellow_1(X0))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_yellow_1)).
% 0.21/0.54  fof(f189,plain,(
% 0.21/0.54    v2_struct_0(k2_yellow_1(sK0)) | ~r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)),
% 0.21/0.54    inference(subsumption_resolution,[],[f188,f63])).
% 0.21/0.54  fof(f188,plain,(
% 0.21/0.54    ~r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | v2_struct_0(k2_yellow_1(sK0)) | ~m1_subset_1(sK1,sK0)),
% 0.21/0.54    inference(subsumption_resolution,[],[f187,f64])).
% 0.21/0.54  fof(f187,plain,(
% 0.21/0.54    ~r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | v2_struct_0(k2_yellow_1(sK0)) | ~m1_subset_1(sK2,sK0) | ~m1_subset_1(sK1,sK0)),
% 0.21/0.54    inference(resolution,[],[f181,f105])).
% 0.21/0.54  fof(f181,plain,(
% 0.21/0.54    ~m1_subset_1(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0) | ~r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | v2_struct_0(k2_yellow_1(sK0))),
% 0.21/0.54    inference(subsumption_resolution,[],[f180,f63])).
% 0.21/0.54  fof(f180,plain,(
% 0.21/0.54    ~m1_subset_1(sK1,sK0) | ~m1_subset_1(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0) | ~r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | v2_struct_0(k2_yellow_1(sK0))),
% 0.21/0.54    inference(forward_demodulation,[],[f179,f39])).
% 0.21/0.54  fof(f179,plain,(
% 0.21/0.54    ~m1_subset_1(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | v2_struct_0(k2_yellow_1(sK0))),
% 0.21/0.54    inference(forward_demodulation,[],[f178,f39])).
% 0.21/0.54  fof(f178,plain,(
% 0.21/0.54    ~m1_subset_1(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | v2_struct_0(k2_yellow_1(sK0))),
% 0.21/0.54    inference(subsumption_resolution,[],[f177,f38])).
% 0.21/0.54  fof(f177,plain,(
% 0.21/0.54    ~l1_orders_2(k2_yellow_1(sK0)) | ~m1_subset_1(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | v2_struct_0(k2_yellow_1(sK0))),
% 0.21/0.54    inference(subsumption_resolution,[],[f175,f34])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f8])).
% 0.21/0.54  fof(f175,plain,(
% 0.21/0.54    ~v3_orders_2(k2_yellow_1(sK0)) | ~l1_orders_2(k2_yellow_1(sK0)) | ~m1_subset_1(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | v2_struct_0(k2_yellow_1(sK0))),
% 0.21/0.54    inference(resolution,[],[f173,f53])).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r3_orders_2(X0,X1,X2) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X2) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 0.21/0.54  fof(f173,plain,(
% 0.21/0.54    ~r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)),
% 0.21/0.54    inference(subsumption_resolution,[],[f172,f64])).
% 0.21/0.54  fof(f172,plain,(
% 0.21/0.54    ~r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | ~m1_subset_1(sK2,sK0)),
% 0.21/0.54    inference(subsumption_resolution,[],[f170,f63])).
% 0.21/0.54  fof(f170,plain,(
% 0.21/0.54    ~r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | ~m1_subset_1(sK1,sK0) | ~m1_subset_1(sK2,sK0)),
% 0.21/0.54    inference(resolution,[],[f169,f140])).
% 0.21/0.54  fof(f140,plain,(
% 0.21/0.54    ( ! [X17,X16] : (r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X16,X17),X17) | ~m1_subset_1(X16,sK0) | ~m1_subset_1(X17,sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f114,f105])).
% 0.21/0.54  fof(f114,plain,(
% 0.21/0.54    ( ! [X17,X16] : (~m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X16,X17),sK0) | ~m1_subset_1(X17,sK0) | ~m1_subset_1(X16,sK0) | r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X16,X17),X17)) )),
% 0.21/0.54    inference(forward_demodulation,[],[f113,f39])).
% 0.21/0.54  fof(f113,plain,(
% 0.21/0.54    ( ! [X17,X16] : (~m1_subset_1(X17,sK0) | ~m1_subset_1(X16,sK0) | ~m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X16,X17),u1_struct_0(k2_yellow_1(sK0))) | r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X16,X17),X17)) )),
% 0.21/0.54    inference(forward_demodulation,[],[f112,f39])).
% 0.21/0.54  fof(f112,plain,(
% 0.21/0.54    ( ! [X17,X16] : (~m1_subset_1(X16,sK0) | ~m1_subset_1(X17,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X16,X17),u1_struct_0(k2_yellow_1(sK0))) | r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X16,X17),X17)) )),
% 0.21/0.54    inference(forward_demodulation,[],[f111,f39])).
% 0.21/0.54  fof(f111,plain,(
% 0.21/0.54    ( ! [X17,X16] : (~m1_subset_1(X16,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X17,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X16,X17),u1_struct_0(k2_yellow_1(sK0))) | r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X16,X17),X17)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f110,f38])).
% 0.21/0.54  fof(f110,plain,(
% 0.21/0.54    ( ! [X17,X16] : (~l1_orders_2(k2_yellow_1(sK0)) | ~m1_subset_1(X16,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X17,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X16,X17),u1_struct_0(k2_yellow_1(sK0))) | r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X16,X17),X17)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f77,f36])).
% 0.21/0.54  fof(f77,plain,(
% 0.21/0.54    ( ! [X17,X16] : (~v5_orders_2(k2_yellow_1(sK0)) | ~l1_orders_2(k2_yellow_1(sK0)) | ~m1_subset_1(X16,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X17,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X16,X17),u1_struct_0(k2_yellow_1(sK0))) | r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X16,X17),X17)) )),
% 0.21/0.54    inference(resolution,[],[f32,f60])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~v2_lattice3(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) | r1_orders_2(X0,k12_lattice3(X0,X1,X2),X2)) )),
% 0.21/0.54    inference(equality_resolution,[],[f51])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~v5_orders_2(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | r1_orders_2(X0,X3,X2) | k12_lattice3(X0,X1,X2) != X3) )),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  fof(f169,plain,(
% 0.21/0.54    ~r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | ~r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)),
% 0.21/0.54    inference(subsumption_resolution,[],[f168,f31])).
% 0.21/0.54  fof(f168,plain,(
% 0.21/0.54    ~r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | ~r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | v1_xboole_0(sK0)),
% 0.21/0.54    inference(resolution,[],[f167,f41])).
% 0.21/0.54  fof(f167,plain,(
% 0.21/0.54    v2_struct_0(k2_yellow_1(sK0)) | ~r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | ~r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)),
% 0.21/0.54    inference(subsumption_resolution,[],[f166,f63])).
% 0.21/0.54  fof(f166,plain,(
% 0.21/0.54    ~r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | ~r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | v2_struct_0(k2_yellow_1(sK0)) | ~m1_subset_1(sK1,sK0)),
% 0.21/0.54    inference(subsumption_resolution,[],[f165,f64])).
% 0.21/0.54  fof(f165,plain,(
% 0.21/0.54    ~r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | ~r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | v2_struct_0(k2_yellow_1(sK0)) | ~m1_subset_1(sK2,sK0) | ~m1_subset_1(sK1,sK0)),
% 0.21/0.54    inference(resolution,[],[f160,f105])).
% 0.21/0.54  fof(f160,plain,(
% 0.21/0.54    ~m1_subset_1(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0) | ~r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | ~r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | v2_struct_0(k2_yellow_1(sK0))),
% 0.21/0.54    inference(subsumption_resolution,[],[f159,f64])).
% 0.21/0.54  fof(f159,plain,(
% 0.21/0.54    ~m1_subset_1(sK2,sK0) | ~m1_subset_1(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0) | ~r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | ~r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | v2_struct_0(k2_yellow_1(sK0))),
% 0.21/0.54    inference(forward_demodulation,[],[f158,f39])).
% 0.21/0.54  fof(f158,plain,(
% 0.21/0.54    ~m1_subset_1(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0) | ~r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | v2_struct_0(k2_yellow_1(sK0))),
% 0.21/0.54    inference(forward_demodulation,[],[f157,f39])).
% 0.21/0.54  fof(f157,plain,(
% 0.21/0.54    ~r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | ~m1_subset_1(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | v2_struct_0(k2_yellow_1(sK0))),
% 0.21/0.54    inference(subsumption_resolution,[],[f156,f38])).
% 0.21/0.54  fof(f156,plain,(
% 0.21/0.54    ~r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | ~l1_orders_2(k2_yellow_1(sK0)) | ~m1_subset_1(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | v2_struct_0(k2_yellow_1(sK0))),
% 0.21/0.54    inference(subsumption_resolution,[],[f154,f34])).
% 0.21/0.54  fof(f154,plain,(
% 0.21/0.54    ~r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | ~v3_orders_2(k2_yellow_1(sK0)) | ~l1_orders_2(k2_yellow_1(sK0)) | ~m1_subset_1(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | v2_struct_0(k2_yellow_1(sK0))),
% 0.21/0.54    inference(resolution,[],[f152,f53])).
% 0.21/0.54  fof(f152,plain,(
% 0.21/0.54    ~r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | ~r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)),
% 0.21/0.54    inference(subsumption_resolution,[],[f151,f63])).
% 0.21/0.54  fof(f151,plain,(
% 0.21/0.54    ~r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | ~r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | ~m1_subset_1(sK1,sK0)),
% 0.21/0.54    inference(subsumption_resolution,[],[f150,f64])).
% 0.21/0.54  fof(f150,plain,(
% 0.21/0.54    ~r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | ~r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | ~m1_subset_1(sK2,sK0) | ~m1_subset_1(sK1,sK0)),
% 0.21/0.54    inference(resolution,[],[f149,f105])).
% 0.21/0.54  fof(f149,plain,(
% 0.21/0.54    ~m1_subset_1(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0) | ~r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | ~r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)),
% 0.21/0.54    inference(subsumption_resolution,[],[f148,f63])).
% 0.21/0.54  fof(f148,plain,(
% 0.21/0.54    ~r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | ~m1_subset_1(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0) | ~m1_subset_1(sK1,sK0) | ~r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)),
% 0.21/0.54    inference(resolution,[],[f147,f70])).
% 0.21/0.54  fof(f70,plain,(
% 0.21/0.54    ( ! [X2,X3] : (r1_tarski(X2,X3) | ~m1_subset_1(X2,sK0) | ~m1_subset_1(X3,sK0) | ~r3_orders_2(k2_yellow_1(sK0),X2,X3)) )),
% 0.21/0.54    inference(forward_demodulation,[],[f69,f39])).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    ( ! [X2,X3] : (~m1_subset_1(X2,sK0) | ~m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK0))) | r1_tarski(X2,X3) | ~r3_orders_2(k2_yellow_1(sK0),X2,X3)) )),
% 0.21/0.54    inference(forward_demodulation,[],[f66,f39])).
% 0.21/0.54  fof(f66,plain,(
% 0.21/0.54    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK0))) | r1_tarski(X2,X3) | ~r3_orders_2(k2_yellow_1(sK0),X2,X3)) )),
% 0.21/0.54    inference(resolution,[],[f31,f44])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : ((r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,axiom,(
% 0.21/0.54    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow_1)).
% 0.21/0.54  fof(f147,plain,(
% 0.21/0.54    ~r1_tarski(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | ~r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)),
% 0.21/0.54    inference(subsumption_resolution,[],[f146,f63])).
% 0.21/0.54  fof(f146,plain,(
% 0.21/0.54    ~r1_tarski(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | ~r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | ~m1_subset_1(sK1,sK0)),
% 0.21/0.54    inference(subsumption_resolution,[],[f145,f64])).
% 0.21/0.54  fof(f145,plain,(
% 0.21/0.54    ~r1_tarski(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | ~r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | ~m1_subset_1(sK2,sK0) | ~m1_subset_1(sK1,sK0)),
% 0.21/0.54    inference(resolution,[],[f139,f105])).
% 0.21/0.54  fof(f139,plain,(
% 0.21/0.54    ~m1_subset_1(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0) | ~r1_tarski(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | ~r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)),
% 0.21/0.54    inference(subsumption_resolution,[],[f138,f64])).
% 0.21/0.54  fof(f138,plain,(
% 0.21/0.54    ~r1_tarski(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | ~m1_subset_1(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0) | ~m1_subset_1(sK2,sK0) | ~r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)),
% 0.21/0.54    inference(resolution,[],[f133,f70])).
% 0.21/0.54  fof(f133,plain,(
% 0.21/0.54    ~r1_tarski(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | ~r1_tarski(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)),
% 0.21/0.54    inference(subsumption_resolution,[],[f132,f64])).
% 0.21/0.54  fof(f132,plain,(
% 0.21/0.54    ~r1_tarski(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | ~r1_tarski(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | ~m1_subset_1(sK2,sK0)),
% 0.21/0.54    inference(subsumption_resolution,[],[f130,f63])).
% 0.21/0.54  fof(f130,plain,(
% 0.21/0.54    ~r1_tarski(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | ~r1_tarski(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | ~m1_subset_1(sK1,sK0) | ~m1_subset_1(sK2,sK0)),
% 0.21/0.54    inference(superposition,[],[f126,f109])).
% 0.21/0.54  fof(f109,plain,(
% 0.21/0.54    ( ! [X14,X15] : (k12_lattice3(k2_yellow_1(sK0),X14,X15) = k11_lattice3(k2_yellow_1(sK0),X14,X15) | ~m1_subset_1(X14,sK0) | ~m1_subset_1(X15,sK0)) )),
% 0.21/0.54    inference(forward_demodulation,[],[f108,f39])).
% 0.21/0.54  fof(f108,plain,(
% 0.21/0.54    ( ! [X14,X15] : (~m1_subset_1(X14,sK0) | ~m1_subset_1(X15,u1_struct_0(k2_yellow_1(sK0))) | k12_lattice3(k2_yellow_1(sK0),X14,X15) = k11_lattice3(k2_yellow_1(sK0),X14,X15)) )),
% 0.21/0.54    inference(forward_demodulation,[],[f107,f39])).
% 0.21/0.54  fof(f107,plain,(
% 0.21/0.54    ( ! [X14,X15] : (~m1_subset_1(X14,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X15,u1_struct_0(k2_yellow_1(sK0))) | k12_lattice3(k2_yellow_1(sK0),X14,X15) = k11_lattice3(k2_yellow_1(sK0),X14,X15)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f106,f38])).
% 0.21/0.54  fof(f106,plain,(
% 0.21/0.54    ( ! [X14,X15] : (~l1_orders_2(k2_yellow_1(sK0)) | ~m1_subset_1(X14,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X15,u1_struct_0(k2_yellow_1(sK0))) | k12_lattice3(k2_yellow_1(sK0),X14,X15) = k11_lattice3(k2_yellow_1(sK0),X14,X15)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f76,f36])).
% 0.21/0.54  fof(f76,plain,(
% 0.21/0.54    ( ! [X14,X15] : (~v5_orders_2(k2_yellow_1(sK0)) | ~l1_orders_2(k2_yellow_1(sK0)) | ~m1_subset_1(X14,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X15,u1_struct_0(k2_yellow_1(sK0))) | k12_lattice3(k2_yellow_1(sK0),X14,X15) = k11_lattice3(k2_yellow_1(sK0),X14,X15)) )),
% 0.21/0.54    inference(resolution,[],[f32,f56])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~v2_lattice3(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 0.21/0.54    inference(flattening,[],[f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k12_lattice3)).
% 0.21/0.54  fof(f126,plain,(
% 0.21/0.54    ~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | ~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)),
% 0.21/0.54    inference(resolution,[],[f58,f59])).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f57,f52])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X0,X2) | r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.54    inference(flattening,[],[f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    ~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 0.21/0.54    inference(definition_unfolding,[],[f29,f52])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2))),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (28017)------------------------------
% 0.21/0.54  % (28017)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (28017)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (28017)Memory used [KB]: 1791
% 0.21/0.54  % (28017)Time elapsed: 0.142 s
% 0.21/0.54  % (28017)------------------------------
% 0.21/0.54  % (28017)------------------------------
% 0.21/0.55  % (27995)Success in time 0.184 s
%------------------------------------------------------------------------------
