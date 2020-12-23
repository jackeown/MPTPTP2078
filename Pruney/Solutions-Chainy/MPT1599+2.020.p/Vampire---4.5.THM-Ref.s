%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 614 expanded)
%              Number of leaves         :   12 ( 152 expanded)
%              Depth                    :   27
%              Number of atoms          :  460 (2038 expanded)
%              Number of equality atoms :   31 ( 246 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1388,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1387,f457])).

fof(f457,plain,(
    r1_tarski(k12_lattice3(k2_yellow_1(sK0),sK2,sK1),sK1) ),
    inference(subsumption_resolution,[],[f456,f63])).

fof(f63,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(forward_demodulation,[],[f32,f41])).

fof(f41,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

fof(f32,plain,(
    m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_yellow_1)).

fof(f456,plain,
    ( r1_tarski(k12_lattice3(k2_yellow_1(sK0),sK2,sK1),sK1)
    | ~ m1_subset_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f451,f144])).

fof(f144,plain,(
    m1_subset_1(k12_lattice3(k2_yellow_1(sK0),sK2,sK1),sK0) ),
    inference(resolution,[],[f141,f64])).

fof(f64,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(forward_demodulation,[],[f30,f41])).

fof(f30,plain,(
    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f141,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK0)
      | m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X0,sK1),sK0) ) ),
    inference(resolution,[],[f112,f63])).

fof(f112,plain,(
    ! [X14,X15] :
      ( ~ m1_subset_1(X15,sK0)
      | m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X14,X15),sK0)
      | ~ m1_subset_1(X14,sK0) ) ),
    inference(forward_demodulation,[],[f111,f41])).

fof(f111,plain,(
    ! [X14,X15] :
      ( ~ m1_subset_1(X15,sK0)
      | ~ m1_subset_1(X14,sK0)
      | m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X14,X15),u1_struct_0(k2_yellow_1(sK0))) ) ),
    inference(forward_demodulation,[],[f110,f41])).

fof(f110,plain,(
    ! [X14,X15] :
      ( ~ m1_subset_1(X14,sK0)
      | ~ m1_subset_1(X15,u1_struct_0(k2_yellow_1(sK0)))
      | m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X14,X15),u1_struct_0(k2_yellow_1(sK0))) ) ),
    inference(forward_demodulation,[],[f109,f41])).

fof(f109,plain,(
    ! [X14,X15] :
      ( ~ m1_subset_1(X14,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(X15,u1_struct_0(k2_yellow_1(sK0)))
      | m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X14,X15),u1_struct_0(k2_yellow_1(sK0))) ) ),
    inference(subsumption_resolution,[],[f108,f40])).

fof(f40,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(f108,plain,(
    ! [X14,X15] :
      ( ~ l1_orders_2(k2_yellow_1(sK0))
      | ~ m1_subset_1(X14,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(X15,u1_struct_0(k2_yellow_1(sK0)))
      | m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X14,X15),u1_struct_0(k2_yellow_1(sK0))) ) ),
    inference(subsumption_resolution,[],[f78,f38])).

fof(f38,plain,(
    ! [X0] : v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v4_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).

fof(f78,plain,(
    ! [X14,X15] :
      ( ~ v5_orders_2(k2_yellow_1(sK0))
      | ~ l1_orders_2(k2_yellow_1(sK0))
      | ~ m1_subset_1(X14,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(X15,u1_struct_0(k2_yellow_1(sK0)))
      | m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X14,X15),u1_struct_0(k2_yellow_1(sK0))) ) ),
    inference(resolution,[],[f34,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k12_lattice3)).

fof(f34,plain,(
    v2_lattice3(k2_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f451,plain,
    ( ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK0),sK2,sK1),sK0)
    | r1_tarski(k12_lattice3(k2_yellow_1(sK0),sK2,sK1),sK1)
    | ~ m1_subset_1(sK1,sK0) ),
    inference(resolution,[],[f432,f72])).

fof(f72,plain,(
    ! [X2,X3] :
      ( ~ r3_orders_2(k2_yellow_1(sK0),X2,X3)
      | ~ m1_subset_1(X2,sK0)
      | r1_tarski(X2,X3)
      | ~ m1_subset_1(X3,sK0) ) ),
    inference(forward_demodulation,[],[f71,f41])).

fof(f71,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,sK0)
      | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK0)))
      | r1_tarski(X2,X3)
      | ~ r3_orders_2(k2_yellow_1(sK0),X2,X3) ) ),
    inference(forward_demodulation,[],[f66,f41])).

fof(f66,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK0)))
      | r1_tarski(X2,X3)
      | ~ r3_orders_2(k2_yellow_1(sK0),X2,X3) ) ),
    inference(resolution,[],[f33,f46])).

fof(f46,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).

fof(f33,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f432,plain,(
    r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK2,sK1),sK1) ),
    inference(subsumption_resolution,[],[f431,f63])).

fof(f431,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK2,sK1),sK1) ),
    inference(forward_demodulation,[],[f430,f41])).

fof(f430,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK2,sK1),sK1) ),
    inference(subsumption_resolution,[],[f429,f144])).

fof(f429,plain,
    ( ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK0),sK2,sK1),sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK2,sK1),sK1) ),
    inference(forward_demodulation,[],[f428,f41])).

fof(f428,plain,
    ( ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK0),sK2,sK1),u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK2,sK1),sK1) ),
    inference(subsumption_resolution,[],[f427,f40])).

fof(f427,plain,
    ( ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK0),sK2,sK1),u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK2,sK1),sK1) ),
    inference(subsumption_resolution,[],[f426,f36])).

fof(f36,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f426,plain,
    ( ~ v3_orders_2(k2_yellow_1(sK0))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK0),sK2,sK1),u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK2,sK1),sK1) ),
    inference(subsumption_resolution,[],[f419,f67])).

fof(f67,plain,(
    ~ v2_struct_0(k2_yellow_1(sK0)) ),
    inference(resolution,[],[f33,f43])).

fof(f43,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ v2_struct_0(k2_yellow_1(X0)) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_yellow_1)).

fof(f419,plain,
    ( v2_struct_0(k2_yellow_1(sK0))
    | ~ v3_orders_2(k2_yellow_1(sK0))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK0),sK2,sK1),u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK2,sK1),sK1) ),
    inference(resolution,[],[f374,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | r3_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f374,plain,(
    r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK2,sK1),sK1) ),
    inference(resolution,[],[f357,f64])).

fof(f357,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK0)
      | r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X0,sK1),sK1) ) ),
    inference(resolution,[],[f122,f63])).

fof(f122,plain,(
    ! [X19,X18] :
      ( ~ m1_subset_1(X19,sK0)
      | ~ m1_subset_1(X18,sK0)
      | r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X18,X19),X19) ) ),
    inference(subsumption_resolution,[],[f121,f112])).

fof(f121,plain,(
    ! [X19,X18] :
      ( ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X18,X19),sK0)
      | ~ m1_subset_1(X19,sK0)
      | ~ m1_subset_1(X18,sK0)
      | r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X18,X19),X19) ) ),
    inference(forward_demodulation,[],[f120,f41])).

fof(f120,plain,(
    ! [X19,X18] :
      ( ~ m1_subset_1(X19,sK0)
      | ~ m1_subset_1(X18,sK0)
      | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X18,X19),u1_struct_0(k2_yellow_1(sK0)))
      | r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X18,X19),X19) ) ),
    inference(forward_demodulation,[],[f119,f41])).

fof(f119,plain,(
    ! [X19,X18] :
      ( ~ m1_subset_1(X18,sK0)
      | ~ m1_subset_1(X19,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X18,X19),u1_struct_0(k2_yellow_1(sK0)))
      | r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X18,X19),X19) ) ),
    inference(forward_demodulation,[],[f118,f41])).

fof(f118,plain,(
    ! [X19,X18] :
      ( ~ m1_subset_1(X18,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(X19,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X18,X19),u1_struct_0(k2_yellow_1(sK0)))
      | r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X18,X19),X19) ) ),
    inference(subsumption_resolution,[],[f117,f40])).

fof(f117,plain,(
    ! [X19,X18] :
      ( ~ l1_orders_2(k2_yellow_1(sK0))
      | ~ m1_subset_1(X18,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(X19,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X18,X19),u1_struct_0(k2_yellow_1(sK0)))
      | r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X18,X19),X19) ) ),
    inference(subsumption_resolution,[],[f80,f38])).

fof(f80,plain,(
    ! [X19,X18] :
      ( ~ v5_orders_2(k2_yellow_1(sK0))
      | ~ l1_orders_2(k2_yellow_1(sK0))
      | ~ m1_subset_1(X18,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(X19,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X18,X19),u1_struct_0(k2_yellow_1(sK0)))
      | r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X18,X19),X19) ) ),
    inference(resolution,[],[f34,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | r1_orders_2(X0,k12_lattice3(X0,X1,X2),X2) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_orders_2(X0,X3,X2)
      | k12_lattice3(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_yellow_0)).

fof(f1387,plain,(
    ~ r1_tarski(k12_lattice3(k2_yellow_1(sK0),sK2,sK1),sK1) ),
    inference(forward_demodulation,[],[f1386,f1383])).

fof(f1383,plain,(
    k11_lattice3(k2_yellow_1(sK0),sK1,sK2) = k12_lattice3(k2_yellow_1(sK0),sK2,sK1) ),
    inference(backward_demodulation,[],[f1279,f1368])).

fof(f1368,plain,(
    k11_lattice3(k2_yellow_1(sK0),sK2,sK1) = k12_lattice3(k2_yellow_1(sK0),sK2,sK1) ),
    inference(resolution,[],[f690,f64])).

fof(f690,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK0)
      | k12_lattice3(k2_yellow_1(sK0),X0,sK1) = k11_lattice3(k2_yellow_1(sK0),X0,sK1) ) ),
    inference(resolution,[],[f116,f63])).

fof(f116,plain,(
    ! [X17,X16] :
      ( ~ m1_subset_1(X17,sK0)
      | ~ m1_subset_1(X16,sK0)
      | k12_lattice3(k2_yellow_1(sK0),X16,X17) = k11_lattice3(k2_yellow_1(sK0),X16,X17) ) ),
    inference(forward_demodulation,[],[f115,f41])).

fof(f115,plain,(
    ! [X17,X16] :
      ( ~ m1_subset_1(X16,sK0)
      | ~ m1_subset_1(X17,u1_struct_0(k2_yellow_1(sK0)))
      | k12_lattice3(k2_yellow_1(sK0),X16,X17) = k11_lattice3(k2_yellow_1(sK0),X16,X17) ) ),
    inference(forward_demodulation,[],[f114,f41])).

fof(f114,plain,(
    ! [X17,X16] :
      ( ~ m1_subset_1(X16,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(X17,u1_struct_0(k2_yellow_1(sK0)))
      | k12_lattice3(k2_yellow_1(sK0),X16,X17) = k11_lattice3(k2_yellow_1(sK0),X16,X17) ) ),
    inference(subsumption_resolution,[],[f113,f40])).

fof(f113,plain,(
    ! [X17,X16] :
      ( ~ l1_orders_2(k2_yellow_1(sK0))
      | ~ m1_subset_1(X16,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(X17,u1_struct_0(k2_yellow_1(sK0)))
      | k12_lattice3(k2_yellow_1(sK0),X16,X17) = k11_lattice3(k2_yellow_1(sK0),X16,X17) ) ),
    inference(subsumption_resolution,[],[f79,f38])).

fof(f79,plain,(
    ! [X17,X16] :
      ( ~ v5_orders_2(k2_yellow_1(sK0))
      | ~ l1_orders_2(k2_yellow_1(sK0))
      | ~ m1_subset_1(X16,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(X17,u1_struct_0(k2_yellow_1(sK0)))
      | k12_lattice3(k2_yellow_1(sK0),X16,X17) = k11_lattice3(k2_yellow_1(sK0),X16,X17) ) ),
    inference(resolution,[],[f34,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
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
     => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

fof(f1279,plain,(
    k11_lattice3(k2_yellow_1(sK0),sK1,sK2) = k11_lattice3(k2_yellow_1(sK0),sK2,sK1) ),
    inference(resolution,[],[f573,f64])).

fof(f573,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK0)
      | k11_lattice3(k2_yellow_1(sK0),X0,sK1) = k11_lattice3(k2_yellow_1(sK0),sK1,X0) ) ),
    inference(resolution,[],[f86,f63])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,sK0)
      | ~ m1_subset_1(X0,sK0)
      | k11_lattice3(k2_yellow_1(sK0),X0,X1) = k11_lattice3(k2_yellow_1(sK0),X1,X0) ) ),
    inference(forward_demodulation,[],[f85,f41])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
      | k11_lattice3(k2_yellow_1(sK0),X0,X1) = k11_lattice3(k2_yellow_1(sK0),X1,X0) ) ),
    inference(forward_demodulation,[],[f84,f41])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
      | k11_lattice3(k2_yellow_1(sK0),X0,X1) = k11_lattice3(k2_yellow_1(sK0),X1,X0) ) ),
    inference(subsumption_resolution,[],[f83,f40])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(k2_yellow_1(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
      | k11_lattice3(k2_yellow_1(sK0),X0,X1) = k11_lattice3(k2_yellow_1(sK0),X1,X0) ) ),
    inference(subsumption_resolution,[],[f73,f38])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(k2_yellow_1(sK0))
      | ~ l1_orders_2(k2_yellow_1(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
      | k11_lattice3(k2_yellow_1(sK0),X0,X1) = k11_lattice3(k2_yellow_1(sK0),X1,X0) ) ),
    inference(resolution,[],[f34,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1)
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
              ( k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_lattice3)).

fof(f1386,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) ),
    inference(subsumption_resolution,[],[f1384,f635])).

fof(f635,plain,(
    r1_tarski(k12_lattice3(k2_yellow_1(sK0),sK2,sK1),sK2) ),
    inference(subsumption_resolution,[],[f634,f64])).

fof(f634,plain,
    ( r1_tarski(k12_lattice3(k2_yellow_1(sK0),sK2,sK1),sK2)
    | ~ m1_subset_1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f629,f144])).

fof(f629,plain,
    ( ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK0),sK2,sK1),sK0)
    | r1_tarski(k12_lattice3(k2_yellow_1(sK0),sK2,sK1),sK2)
    | ~ m1_subset_1(sK2,sK0) ),
    inference(resolution,[],[f626,f72])).

fof(f626,plain,(
    r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK2,sK1),sK2) ),
    inference(subsumption_resolution,[],[f625,f64])).

fof(f625,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK2,sK1),sK2) ),
    inference(forward_demodulation,[],[f624,f41])).

fof(f624,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK2,sK1),sK2) ),
    inference(subsumption_resolution,[],[f623,f144])).

fof(f623,plain,
    ( ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK0),sK2,sK1),sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK2,sK1),sK2) ),
    inference(forward_demodulation,[],[f622,f41])).

fof(f622,plain,
    ( ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK0),sK2,sK1),u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK2,sK1),sK2) ),
    inference(subsumption_resolution,[],[f621,f40])).

fof(f621,plain,
    ( ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK0),sK2,sK1),u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK2,sK1),sK2) ),
    inference(subsumption_resolution,[],[f620,f36])).

fof(f620,plain,
    ( ~ v3_orders_2(k2_yellow_1(sK0))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK0),sK2,sK1),u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK2,sK1),sK2) ),
    inference(subsumption_resolution,[],[f613,f67])).

fof(f613,plain,
    ( v2_struct_0(k2_yellow_1(sK0))
    | ~ v3_orders_2(k2_yellow_1(sK0))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK0),sK2,sK1),u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK2,sK1),sK2) ),
    inference(resolution,[],[f590,f55])).

fof(f590,plain,(
    r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK2,sK1),sK2) ),
    inference(resolution,[],[f465,f64])).

fof(f465,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK0)
      | r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X0,sK1),X0) ) ),
    inference(resolution,[],[f128,f63])).

fof(f128,plain,(
    ! [X21,X20] :
      ( ~ m1_subset_1(X21,sK0)
      | ~ m1_subset_1(X20,sK0)
      | r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X20,X21),X20) ) ),
    inference(subsumption_resolution,[],[f127,f112])).

fof(f127,plain,(
    ! [X21,X20] :
      ( ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X20,X21),sK0)
      | ~ m1_subset_1(X21,sK0)
      | ~ m1_subset_1(X20,sK0)
      | r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X20,X21),X20) ) ),
    inference(forward_demodulation,[],[f126,f41])).

fof(f126,plain,(
    ! [X21,X20] :
      ( ~ m1_subset_1(X21,sK0)
      | ~ m1_subset_1(X20,sK0)
      | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X20,X21),u1_struct_0(k2_yellow_1(sK0)))
      | r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X20,X21),X20) ) ),
    inference(forward_demodulation,[],[f125,f41])).

fof(f125,plain,(
    ! [X21,X20] :
      ( ~ m1_subset_1(X20,sK0)
      | ~ m1_subset_1(X21,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X20,X21),u1_struct_0(k2_yellow_1(sK0)))
      | r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X20,X21),X20) ) ),
    inference(forward_demodulation,[],[f124,f41])).

fof(f124,plain,(
    ! [X21,X20] :
      ( ~ m1_subset_1(X20,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(X21,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X20,X21),u1_struct_0(k2_yellow_1(sK0)))
      | r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X20,X21),X20) ) ),
    inference(subsumption_resolution,[],[f123,f40])).

fof(f123,plain,(
    ! [X21,X20] :
      ( ~ l1_orders_2(k2_yellow_1(sK0))
      | ~ m1_subset_1(X20,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(X21,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X20,X21),u1_struct_0(k2_yellow_1(sK0)))
      | r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X20,X21),X20) ) ),
    inference(subsumption_resolution,[],[f81,f38])).

fof(f81,plain,(
    ! [X21,X20] :
      ( ~ v5_orders_2(k2_yellow_1(sK0))
      | ~ l1_orders_2(k2_yellow_1(sK0))
      | ~ m1_subset_1(X20,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(X21,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X20,X21),u1_struct_0(k2_yellow_1(sK0)))
      | r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X20,X21),X20) ) ),
    inference(resolution,[],[f34,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | r1_orders_2(X0,k12_lattice3(X0,X1,X2),X1) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_orders_2(X0,X3,X1)
      | k12_lattice3(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1384,plain,
    ( ~ r1_tarski(k12_lattice3(k2_yellow_1(sK0),sK2,sK1),sK2)
    | ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) ),
    inference(backward_demodulation,[],[f138,f1383])).

fof(f138,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) ),
    inference(resolution,[],[f31,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f31,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:24:44 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.42  % (7109)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.44  % (7109)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f1388,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(subsumption_resolution,[],[f1387,f457])).
% 0.21/0.44  fof(f457,plain,(
% 0.21/0.44    r1_tarski(k12_lattice3(k2_yellow_1(sK0),sK2,sK1),sK1)),
% 0.21/0.44    inference(subsumption_resolution,[],[f456,f63])).
% 0.21/0.44  fof(f63,plain,(
% 0.21/0.44    m1_subset_1(sK1,sK0)),
% 0.21/0.44    inference(forward_demodulation,[],[f32,f41])).
% 0.21/0.44  fof(f41,plain,(
% 0.21/0.44    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 0.21/0.44    inference(cnf_transformation,[],[f10])).
% 0.21/0.44  fof(f10,axiom,(
% 0.21/0.44    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).
% 0.21/0.44  fof(f32,plain,(
% 0.21/0.44    m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))),
% 0.21/0.44    inference(cnf_transformation,[],[f15])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v2_lattice3(k2_yellow_1(X0)) & ~v1_xboole_0(X0))),
% 0.21/0.44    inference(flattening,[],[f14])).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    ? [X0] : ((? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v2_lattice3(k2_yellow_1(X0))) & ~v1_xboole_0(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f13])).
% 0.21/0.45  fof(f13,negated_conjecture,(
% 0.21/0.45    ~! [X0] : (~v1_xboole_0(X0) => (v2_lattice3(k2_yellow_1(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))))))),
% 0.21/0.45    inference(negated_conjecture,[],[f12])).
% 0.21/0.45  fof(f12,conjecture,(
% 0.21/0.45    ! [X0] : (~v1_xboole_0(X0) => (v2_lattice3(k2_yellow_1(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_yellow_1)).
% 0.21/0.45  fof(f456,plain,(
% 0.21/0.45    r1_tarski(k12_lattice3(k2_yellow_1(sK0),sK2,sK1),sK1) | ~m1_subset_1(sK1,sK0)),
% 0.21/0.45    inference(subsumption_resolution,[],[f451,f144])).
% 0.21/0.45  fof(f144,plain,(
% 0.21/0.45    m1_subset_1(k12_lattice3(k2_yellow_1(sK0),sK2,sK1),sK0)),
% 0.21/0.45    inference(resolution,[],[f141,f64])).
% 0.21/0.45  fof(f64,plain,(
% 0.21/0.45    m1_subset_1(sK2,sK0)),
% 0.21/0.45    inference(forward_demodulation,[],[f30,f41])).
% 0.21/0.45  fof(f30,plain,(
% 0.21/0.45    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))),
% 0.21/0.45    inference(cnf_transformation,[],[f15])).
% 0.21/0.45  fof(f141,plain,(
% 0.21/0.45    ( ! [X0] : (~m1_subset_1(X0,sK0) | m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X0,sK1),sK0)) )),
% 0.21/0.45    inference(resolution,[],[f112,f63])).
% 0.21/0.45  fof(f112,plain,(
% 0.21/0.45    ( ! [X14,X15] : (~m1_subset_1(X15,sK0) | m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X14,X15),sK0) | ~m1_subset_1(X14,sK0)) )),
% 0.21/0.45    inference(forward_demodulation,[],[f111,f41])).
% 0.21/0.45  fof(f111,plain,(
% 0.21/0.45    ( ! [X14,X15] : (~m1_subset_1(X15,sK0) | ~m1_subset_1(X14,sK0) | m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X14,X15),u1_struct_0(k2_yellow_1(sK0)))) )),
% 0.21/0.45    inference(forward_demodulation,[],[f110,f41])).
% 0.21/0.45  fof(f110,plain,(
% 0.21/0.45    ( ! [X14,X15] : (~m1_subset_1(X14,sK0) | ~m1_subset_1(X15,u1_struct_0(k2_yellow_1(sK0))) | m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X14,X15),u1_struct_0(k2_yellow_1(sK0)))) )),
% 0.21/0.45    inference(forward_demodulation,[],[f109,f41])).
% 0.21/0.45  fof(f109,plain,(
% 0.21/0.45    ( ! [X14,X15] : (~m1_subset_1(X14,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X15,u1_struct_0(k2_yellow_1(sK0))) | m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X14,X15),u1_struct_0(k2_yellow_1(sK0)))) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f108,f40])).
% 0.21/0.45  fof(f40,plain,(
% 0.21/0.45    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f7])).
% 0.21/0.45  fof(f7,axiom,(
% 0.21/0.45    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).
% 0.21/0.45  fof(f108,plain,(
% 0.21/0.45    ( ! [X14,X15] : (~l1_orders_2(k2_yellow_1(sK0)) | ~m1_subset_1(X14,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X15,u1_struct_0(k2_yellow_1(sK0))) | m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X14,X15),u1_struct_0(k2_yellow_1(sK0)))) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f78,f38])).
% 0.21/0.45  fof(f38,plain,(
% 0.21/0.45    ( ! [X0] : (v5_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f8])).
% 0.21/0.45  fof(f8,axiom,(
% 0.21/0.45    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).
% 0.21/0.45  fof(f78,plain,(
% 0.21/0.45    ( ! [X14,X15] : (~v5_orders_2(k2_yellow_1(sK0)) | ~l1_orders_2(k2_yellow_1(sK0)) | ~m1_subset_1(X14,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X15,u1_struct_0(k2_yellow_1(sK0))) | m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X14,X15),u1_struct_0(k2_yellow_1(sK0)))) )),
% 0.21/0.45    inference(resolution,[],[f34,f57])).
% 0.21/0.45  fof(f57,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~v5_orders_2(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f25])).
% 0.21/0.45  fof(f25,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 0.21/0.45    inference(flattening,[],[f24])).
% 0.21/0.45  fof(f24,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k12_lattice3)).
% 0.21/0.45  fof(f34,plain,(
% 0.21/0.45    v2_lattice3(k2_yellow_1(sK0))),
% 0.21/0.45    inference(cnf_transformation,[],[f15])).
% 0.21/0.45  fof(f451,plain,(
% 0.21/0.45    ~m1_subset_1(k12_lattice3(k2_yellow_1(sK0),sK2,sK1),sK0) | r1_tarski(k12_lattice3(k2_yellow_1(sK0),sK2,sK1),sK1) | ~m1_subset_1(sK1,sK0)),
% 0.21/0.45    inference(resolution,[],[f432,f72])).
% 0.21/0.45  fof(f72,plain,(
% 0.21/0.45    ( ! [X2,X3] : (~r3_orders_2(k2_yellow_1(sK0),X2,X3) | ~m1_subset_1(X2,sK0) | r1_tarski(X2,X3) | ~m1_subset_1(X3,sK0)) )),
% 0.21/0.45    inference(forward_demodulation,[],[f71,f41])).
% 0.21/0.45  fof(f71,plain,(
% 0.21/0.45    ( ! [X2,X3] : (~m1_subset_1(X2,sK0) | ~m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK0))) | r1_tarski(X2,X3) | ~r3_orders_2(k2_yellow_1(sK0),X2,X3)) )),
% 0.21/0.45    inference(forward_demodulation,[],[f66,f41])).
% 0.21/0.45  fof(f66,plain,(
% 0.21/0.45    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK0))) | r1_tarski(X2,X3) | ~r3_orders_2(k2_yellow_1(sK0),X2,X3)) )),
% 0.21/0.45    inference(resolution,[],[f33,f46])).
% 0.21/0.45  fof(f46,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f17])).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : ((r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f11])).
% 0.21/0.45  fof(f11,axiom,(
% 0.21/0.45    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).
% 0.21/0.45  fof(f33,plain,(
% 0.21/0.45    ~v1_xboole_0(sK0)),
% 0.21/0.45    inference(cnf_transformation,[],[f15])).
% 0.21/0.45  fof(f432,plain,(
% 0.21/0.45    r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK2,sK1),sK1)),
% 0.21/0.45    inference(subsumption_resolution,[],[f431,f63])).
% 0.21/0.45  fof(f431,plain,(
% 0.21/0.45    ~m1_subset_1(sK1,sK0) | r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK2,sK1),sK1)),
% 0.21/0.45    inference(forward_demodulation,[],[f430,f41])).
% 0.21/0.45  fof(f430,plain,(
% 0.21/0.45    ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK2,sK1),sK1)),
% 0.21/0.45    inference(subsumption_resolution,[],[f429,f144])).
% 0.21/0.45  fof(f429,plain,(
% 0.21/0.45    ~m1_subset_1(k12_lattice3(k2_yellow_1(sK0),sK2,sK1),sK0) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK2,sK1),sK1)),
% 0.21/0.45    inference(forward_demodulation,[],[f428,f41])).
% 0.21/0.45  fof(f428,plain,(
% 0.21/0.45    ~m1_subset_1(k12_lattice3(k2_yellow_1(sK0),sK2,sK1),u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK2,sK1),sK1)),
% 0.21/0.45    inference(subsumption_resolution,[],[f427,f40])).
% 0.21/0.45  fof(f427,plain,(
% 0.21/0.45    ~l1_orders_2(k2_yellow_1(sK0)) | ~m1_subset_1(k12_lattice3(k2_yellow_1(sK0),sK2,sK1),u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK2,sK1),sK1)),
% 0.21/0.45    inference(subsumption_resolution,[],[f426,f36])).
% 0.21/0.45  fof(f36,plain,(
% 0.21/0.45    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f8])).
% 0.21/0.45  fof(f426,plain,(
% 0.21/0.45    ~v3_orders_2(k2_yellow_1(sK0)) | ~l1_orders_2(k2_yellow_1(sK0)) | ~m1_subset_1(k12_lattice3(k2_yellow_1(sK0),sK2,sK1),u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK2,sK1),sK1)),
% 0.21/0.45    inference(subsumption_resolution,[],[f419,f67])).
% 0.21/0.45  fof(f67,plain,(
% 0.21/0.45    ~v2_struct_0(k2_yellow_1(sK0))),
% 0.21/0.45    inference(resolution,[],[f33,f43])).
% 0.21/0.45  fof(f43,plain,(
% 0.21/0.45    ( ! [X0] : (v1_xboole_0(X0) | ~v2_struct_0(k2_yellow_1(X0))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f16])).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    ! [X0] : ((v1_orders_2(k2_yellow_1(X0)) & ~v2_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f9])).
% 0.21/0.45  fof(f9,axiom,(
% 0.21/0.45    ! [X0] : (~v1_xboole_0(X0) => (v1_orders_2(k2_yellow_1(X0)) & ~v2_struct_0(k2_yellow_1(X0))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_yellow_1)).
% 0.21/0.45  fof(f419,plain,(
% 0.21/0.45    v2_struct_0(k2_yellow_1(sK0)) | ~v3_orders_2(k2_yellow_1(sK0)) | ~l1_orders_2(k2_yellow_1(sK0)) | ~m1_subset_1(k12_lattice3(k2_yellow_1(sK0),sK2,sK1),u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK2,sK1),sK1)),
% 0.21/0.45    inference(resolution,[],[f374,f55])).
% 0.21/0.45  fof(f55,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X2) | r3_orders_2(X0,X1,X2)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f23])).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.45    inference(flattening,[],[f22])).
% 0.21/0.45  fof(f22,plain,(
% 0.21/0.45    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 0.21/0.45  fof(f374,plain,(
% 0.21/0.45    r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK2,sK1),sK1)),
% 0.21/0.45    inference(resolution,[],[f357,f64])).
% 0.21/0.45  fof(f357,plain,(
% 0.21/0.45    ( ! [X0] : (~m1_subset_1(X0,sK0) | r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X0,sK1),sK1)) )),
% 0.21/0.45    inference(resolution,[],[f122,f63])).
% 0.21/0.45  fof(f122,plain,(
% 0.21/0.45    ( ! [X19,X18] : (~m1_subset_1(X19,sK0) | ~m1_subset_1(X18,sK0) | r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X18,X19),X19)) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f121,f112])).
% 0.21/0.45  fof(f121,plain,(
% 0.21/0.45    ( ! [X19,X18] : (~m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X18,X19),sK0) | ~m1_subset_1(X19,sK0) | ~m1_subset_1(X18,sK0) | r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X18,X19),X19)) )),
% 0.21/0.45    inference(forward_demodulation,[],[f120,f41])).
% 0.21/0.45  fof(f120,plain,(
% 0.21/0.45    ( ! [X19,X18] : (~m1_subset_1(X19,sK0) | ~m1_subset_1(X18,sK0) | ~m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X18,X19),u1_struct_0(k2_yellow_1(sK0))) | r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X18,X19),X19)) )),
% 0.21/0.45    inference(forward_demodulation,[],[f119,f41])).
% 0.21/0.45  fof(f119,plain,(
% 0.21/0.45    ( ! [X19,X18] : (~m1_subset_1(X18,sK0) | ~m1_subset_1(X19,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X18,X19),u1_struct_0(k2_yellow_1(sK0))) | r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X18,X19),X19)) )),
% 0.21/0.45    inference(forward_demodulation,[],[f118,f41])).
% 0.21/0.45  fof(f118,plain,(
% 0.21/0.45    ( ! [X19,X18] : (~m1_subset_1(X18,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X19,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X18,X19),u1_struct_0(k2_yellow_1(sK0))) | r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X18,X19),X19)) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f117,f40])).
% 0.21/0.45  fof(f117,plain,(
% 0.21/0.45    ( ! [X19,X18] : (~l1_orders_2(k2_yellow_1(sK0)) | ~m1_subset_1(X18,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X19,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X18,X19),u1_struct_0(k2_yellow_1(sK0))) | r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X18,X19),X19)) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f80,f38])).
% 0.21/0.45  fof(f80,plain,(
% 0.21/0.45    ( ! [X19,X18] : (~v5_orders_2(k2_yellow_1(sK0)) | ~l1_orders_2(k2_yellow_1(sK0)) | ~m1_subset_1(X18,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X19,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X18,X19),u1_struct_0(k2_yellow_1(sK0))) | r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X18,X19),X19)) )),
% 0.21/0.45    inference(resolution,[],[f34,f60])).
% 0.21/0.45  fof(f60,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~v5_orders_2(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) | r1_orders_2(X0,k12_lattice3(X0,X1,X2),X2)) )),
% 0.21/0.45    inference(equality_resolution,[],[f54])).
% 0.21/0.45  fof(f54,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (~v5_orders_2(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | r1_orders_2(X0,X3,X2) | k12_lattice3(X0,X1,X2) != X3) )),
% 0.21/0.45    inference(cnf_transformation,[],[f21])).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k12_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 0.21/0.45    inference(flattening,[],[f20])).
% 0.21/0.45  fof(f20,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k12_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X4,X3) | (~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f6])).
% 0.21/0.45  fof(f6,axiom,(
% 0.21/0.45    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k12_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1)) => r1_orders_2(X0,X4,X3))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)))))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_yellow_0)).
% 0.21/0.45  fof(f1387,plain,(
% 0.21/0.45    ~r1_tarski(k12_lattice3(k2_yellow_1(sK0),sK2,sK1),sK1)),
% 0.21/0.45    inference(forward_demodulation,[],[f1386,f1383])).
% 0.21/0.45  fof(f1383,plain,(
% 0.21/0.45    k11_lattice3(k2_yellow_1(sK0),sK1,sK2) = k12_lattice3(k2_yellow_1(sK0),sK2,sK1)),
% 0.21/0.45    inference(backward_demodulation,[],[f1279,f1368])).
% 0.21/0.45  fof(f1368,plain,(
% 0.21/0.45    k11_lattice3(k2_yellow_1(sK0),sK2,sK1) = k12_lattice3(k2_yellow_1(sK0),sK2,sK1)),
% 0.21/0.45    inference(resolution,[],[f690,f64])).
% 0.21/0.45  fof(f690,plain,(
% 0.21/0.45    ( ! [X0] : (~m1_subset_1(X0,sK0) | k12_lattice3(k2_yellow_1(sK0),X0,sK1) = k11_lattice3(k2_yellow_1(sK0),X0,sK1)) )),
% 0.21/0.45    inference(resolution,[],[f116,f63])).
% 0.21/0.45  fof(f116,plain,(
% 0.21/0.45    ( ! [X17,X16] : (~m1_subset_1(X17,sK0) | ~m1_subset_1(X16,sK0) | k12_lattice3(k2_yellow_1(sK0),X16,X17) = k11_lattice3(k2_yellow_1(sK0),X16,X17)) )),
% 0.21/0.45    inference(forward_demodulation,[],[f115,f41])).
% 0.21/0.45  fof(f115,plain,(
% 0.21/0.45    ( ! [X17,X16] : (~m1_subset_1(X16,sK0) | ~m1_subset_1(X17,u1_struct_0(k2_yellow_1(sK0))) | k12_lattice3(k2_yellow_1(sK0),X16,X17) = k11_lattice3(k2_yellow_1(sK0),X16,X17)) )),
% 0.21/0.45    inference(forward_demodulation,[],[f114,f41])).
% 0.21/0.45  fof(f114,plain,(
% 0.21/0.45    ( ! [X17,X16] : (~m1_subset_1(X16,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X17,u1_struct_0(k2_yellow_1(sK0))) | k12_lattice3(k2_yellow_1(sK0),X16,X17) = k11_lattice3(k2_yellow_1(sK0),X16,X17)) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f113,f40])).
% 0.21/0.45  fof(f113,plain,(
% 0.21/0.45    ( ! [X17,X16] : (~l1_orders_2(k2_yellow_1(sK0)) | ~m1_subset_1(X16,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X17,u1_struct_0(k2_yellow_1(sK0))) | k12_lattice3(k2_yellow_1(sK0),X16,X17) = k11_lattice3(k2_yellow_1(sK0),X16,X17)) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f79,f38])).
% 0.21/0.45  fof(f79,plain,(
% 0.21/0.45    ( ! [X17,X16] : (~v5_orders_2(k2_yellow_1(sK0)) | ~l1_orders_2(k2_yellow_1(sK0)) | ~m1_subset_1(X16,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X17,u1_struct_0(k2_yellow_1(sK0))) | k12_lattice3(k2_yellow_1(sK0),X16,X17) = k11_lattice3(k2_yellow_1(sK0),X16,X17)) )),
% 0.21/0.45    inference(resolution,[],[f34,f58])).
% 0.21/0.45  fof(f58,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~v5_orders_2(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f27])).
% 0.21/0.45  fof(f27,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 0.21/0.45    inference(flattening,[],[f26])).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f4])).
% 0.21/0.45  fof(f4,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).
% 0.21/0.45  fof(f1279,plain,(
% 0.21/0.45    k11_lattice3(k2_yellow_1(sK0),sK1,sK2) = k11_lattice3(k2_yellow_1(sK0),sK2,sK1)),
% 0.21/0.45    inference(resolution,[],[f573,f64])).
% 0.21/0.45  fof(f573,plain,(
% 0.21/0.45    ( ! [X0] : (~m1_subset_1(X0,sK0) | k11_lattice3(k2_yellow_1(sK0),X0,sK1) = k11_lattice3(k2_yellow_1(sK0),sK1,X0)) )),
% 0.21/0.45    inference(resolution,[],[f86,f63])).
% 0.21/0.45  fof(f86,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~m1_subset_1(X1,sK0) | ~m1_subset_1(X0,sK0) | k11_lattice3(k2_yellow_1(sK0),X0,X1) = k11_lattice3(k2_yellow_1(sK0),X1,X0)) )),
% 0.21/0.45    inference(forward_demodulation,[],[f85,f41])).
% 0.21/0.45  fof(f85,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~m1_subset_1(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | k11_lattice3(k2_yellow_1(sK0),X0,X1) = k11_lattice3(k2_yellow_1(sK0),X1,X0)) )),
% 0.21/0.45    inference(forward_demodulation,[],[f84,f41])).
% 0.21/0.45  fof(f84,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | k11_lattice3(k2_yellow_1(sK0),X0,X1) = k11_lattice3(k2_yellow_1(sK0),X1,X0)) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f83,f40])).
% 0.21/0.45  fof(f83,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~l1_orders_2(k2_yellow_1(sK0)) | ~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | k11_lattice3(k2_yellow_1(sK0),X0,X1) = k11_lattice3(k2_yellow_1(sK0),X1,X0)) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f73,f38])).
% 0.21/0.45  fof(f73,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~v5_orders_2(k2_yellow_1(sK0)) | ~l1_orders_2(k2_yellow_1(sK0)) | ~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | k11_lattice3(k2_yellow_1(sK0),X0,X1) = k11_lattice3(k2_yellow_1(sK0),X1,X0)) )),
% 0.21/0.45    inference(resolution,[],[f34,f47])).
% 0.21/0.45  fof(f47,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~v5_orders_2(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f19])).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : (k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 0.21/0.45    inference(flattening,[],[f18])).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : (k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f5])).
% 0.21/0.45  fof(f5,axiom,(
% 0.21/0.45    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_lattice3)).
% 0.21/0.45  fof(f1386,plain,(
% 0.21/0.45    ~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)),
% 0.21/0.45    inference(subsumption_resolution,[],[f1384,f635])).
% 0.21/0.45  fof(f635,plain,(
% 0.21/0.45    r1_tarski(k12_lattice3(k2_yellow_1(sK0),sK2,sK1),sK2)),
% 0.21/0.45    inference(subsumption_resolution,[],[f634,f64])).
% 0.21/0.45  fof(f634,plain,(
% 0.21/0.45    r1_tarski(k12_lattice3(k2_yellow_1(sK0),sK2,sK1),sK2) | ~m1_subset_1(sK2,sK0)),
% 0.21/0.45    inference(subsumption_resolution,[],[f629,f144])).
% 0.21/0.45  fof(f629,plain,(
% 0.21/0.45    ~m1_subset_1(k12_lattice3(k2_yellow_1(sK0),sK2,sK1),sK0) | r1_tarski(k12_lattice3(k2_yellow_1(sK0),sK2,sK1),sK2) | ~m1_subset_1(sK2,sK0)),
% 0.21/0.45    inference(resolution,[],[f626,f72])).
% 0.21/0.45  fof(f626,plain,(
% 0.21/0.45    r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK2,sK1),sK2)),
% 0.21/0.45    inference(subsumption_resolution,[],[f625,f64])).
% 0.21/0.45  fof(f625,plain,(
% 0.21/0.45    ~m1_subset_1(sK2,sK0) | r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK2,sK1),sK2)),
% 0.21/0.45    inference(forward_demodulation,[],[f624,f41])).
% 0.21/0.45  fof(f624,plain,(
% 0.21/0.45    ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK2,sK1),sK2)),
% 0.21/0.45    inference(subsumption_resolution,[],[f623,f144])).
% 0.21/0.45  fof(f623,plain,(
% 0.21/0.45    ~m1_subset_1(k12_lattice3(k2_yellow_1(sK0),sK2,sK1),sK0) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK2,sK1),sK2)),
% 0.21/0.45    inference(forward_demodulation,[],[f622,f41])).
% 0.21/0.45  fof(f622,plain,(
% 0.21/0.45    ~m1_subset_1(k12_lattice3(k2_yellow_1(sK0),sK2,sK1),u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK2,sK1),sK2)),
% 0.21/0.45    inference(subsumption_resolution,[],[f621,f40])).
% 0.21/0.45  fof(f621,plain,(
% 0.21/0.45    ~l1_orders_2(k2_yellow_1(sK0)) | ~m1_subset_1(k12_lattice3(k2_yellow_1(sK0),sK2,sK1),u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK2,sK1),sK2)),
% 0.21/0.45    inference(subsumption_resolution,[],[f620,f36])).
% 0.21/0.45  fof(f620,plain,(
% 0.21/0.45    ~v3_orders_2(k2_yellow_1(sK0)) | ~l1_orders_2(k2_yellow_1(sK0)) | ~m1_subset_1(k12_lattice3(k2_yellow_1(sK0),sK2,sK1),u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK2,sK1),sK2)),
% 0.21/0.45    inference(subsumption_resolution,[],[f613,f67])).
% 0.21/0.45  fof(f613,plain,(
% 0.21/0.45    v2_struct_0(k2_yellow_1(sK0)) | ~v3_orders_2(k2_yellow_1(sK0)) | ~l1_orders_2(k2_yellow_1(sK0)) | ~m1_subset_1(k12_lattice3(k2_yellow_1(sK0),sK2,sK1),u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK2,sK1),sK2)),
% 0.21/0.45    inference(resolution,[],[f590,f55])).
% 0.21/0.45  fof(f590,plain,(
% 0.21/0.45    r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK2,sK1),sK2)),
% 0.21/0.45    inference(resolution,[],[f465,f64])).
% 0.21/0.45  fof(f465,plain,(
% 0.21/0.45    ( ! [X0] : (~m1_subset_1(X0,sK0) | r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X0,sK1),X0)) )),
% 0.21/0.45    inference(resolution,[],[f128,f63])).
% 0.21/0.45  fof(f128,plain,(
% 0.21/0.45    ( ! [X21,X20] : (~m1_subset_1(X21,sK0) | ~m1_subset_1(X20,sK0) | r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X20,X21),X20)) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f127,f112])).
% 0.21/0.45  fof(f127,plain,(
% 0.21/0.45    ( ! [X21,X20] : (~m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X20,X21),sK0) | ~m1_subset_1(X21,sK0) | ~m1_subset_1(X20,sK0) | r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X20,X21),X20)) )),
% 0.21/0.45    inference(forward_demodulation,[],[f126,f41])).
% 0.21/0.45  fof(f126,plain,(
% 0.21/0.45    ( ! [X21,X20] : (~m1_subset_1(X21,sK0) | ~m1_subset_1(X20,sK0) | ~m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X20,X21),u1_struct_0(k2_yellow_1(sK0))) | r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X20,X21),X20)) )),
% 0.21/0.45    inference(forward_demodulation,[],[f125,f41])).
% 0.21/0.45  fof(f125,plain,(
% 0.21/0.45    ( ! [X21,X20] : (~m1_subset_1(X20,sK0) | ~m1_subset_1(X21,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X20,X21),u1_struct_0(k2_yellow_1(sK0))) | r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X20,X21),X20)) )),
% 0.21/0.45    inference(forward_demodulation,[],[f124,f41])).
% 0.21/0.45  fof(f124,plain,(
% 0.21/0.45    ( ! [X21,X20] : (~m1_subset_1(X20,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X21,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X20,X21),u1_struct_0(k2_yellow_1(sK0))) | r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X20,X21),X20)) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f123,f40])).
% 0.21/0.45  fof(f123,plain,(
% 0.21/0.45    ( ! [X21,X20] : (~l1_orders_2(k2_yellow_1(sK0)) | ~m1_subset_1(X20,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X21,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X20,X21),u1_struct_0(k2_yellow_1(sK0))) | r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X20,X21),X20)) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f81,f38])).
% 0.21/0.45  fof(f81,plain,(
% 0.21/0.45    ( ! [X21,X20] : (~v5_orders_2(k2_yellow_1(sK0)) | ~l1_orders_2(k2_yellow_1(sK0)) | ~m1_subset_1(X20,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X21,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X20,X21),u1_struct_0(k2_yellow_1(sK0))) | r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X20,X21),X20)) )),
% 0.21/0.45    inference(resolution,[],[f34,f61])).
% 0.21/0.45  fof(f61,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~v5_orders_2(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) | r1_orders_2(X0,k12_lattice3(X0,X1,X2),X1)) )),
% 0.21/0.45    inference(equality_resolution,[],[f53])).
% 0.21/0.45  fof(f53,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (~v5_orders_2(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | r1_orders_2(X0,X3,X1) | k12_lattice3(X0,X1,X2) != X3) )),
% 0.21/0.45    inference(cnf_transformation,[],[f21])).
% 0.21/0.45  fof(f1384,plain,(
% 0.21/0.45    ~r1_tarski(k12_lattice3(k2_yellow_1(sK0),sK2,sK1),sK2) | ~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)),
% 0.21/0.45    inference(backward_demodulation,[],[f138,f1383])).
% 0.21/0.45  fof(f138,plain,(
% 0.21/0.45    ~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | ~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)),
% 0.21/0.45    inference(resolution,[],[f31,f59])).
% 0.21/0.45  fof(f59,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X0,X2) | r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f29])).
% 0.21/0.45  fof(f29,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.45    inference(flattening,[],[f28])).
% 0.21/0.45  fof(f28,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.45    inference(ennf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.21/0.45  fof(f31,plain,(
% 0.21/0.45    ~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2))),
% 0.21/0.45    inference(cnf_transformation,[],[f15])).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (7109)------------------------------
% 0.21/0.45  % (7109)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (7109)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (7109)Memory used [KB]: 2174
% 0.21/0.45  % (7109)Time elapsed: 0.031 s
% 0.21/0.45  % (7109)------------------------------
% 0.21/0.45  % (7109)------------------------------
% 0.21/0.45  % (7095)Success in time 0.093 s
%------------------------------------------------------------------------------
