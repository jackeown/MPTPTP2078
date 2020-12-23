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
% DateTime   : Thu Dec  3 13:22:48 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 347 expanded)
%              Number of leaves         :    9 ( 107 expanded)
%              Depth                    :   19
%              Number of atoms          :  274 (2729 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f73,plain,(
    $false ),
    inference(subsumption_resolution,[],[f72,f44])).

fof(f44,plain,(
    ~ v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f43,f32])).

fof(f32,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ( ~ r1_orders_2(sK0,k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,sK1))
      | ~ r3_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2)) )
    & r1_tarski(sK1,sK2)
    & l1_orders_2(sK0)
    & v3_lattice3(sK0)
    & v2_lattice3(sK0)
    & v1_lattice3(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( ( ~ r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
              | ~ r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) )
            & r1_tarski(X1,X2) )
        & l1_orders_2(X0)
        & v3_lattice3(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X2,X1] :
          ( ( ~ r1_orders_2(sK0,k2_yellow_0(sK0,X2),k2_yellow_0(sK0,X1))
            | ~ r3_orders_2(sK0,k1_yellow_0(sK0,X1),k1_yellow_0(sK0,X2)) )
          & r1_tarski(X1,X2) )
      & l1_orders_2(sK0)
      & v3_lattice3(sK0)
      & v2_lattice3(sK0)
      & v1_lattice3(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X2,X1] :
        ( ( ~ r1_orders_2(sK0,k2_yellow_0(sK0,X2),k2_yellow_0(sK0,X1))
          | ~ r3_orders_2(sK0,k1_yellow_0(sK0,X1),k1_yellow_0(sK0,X2)) )
        & r1_tarski(X1,X2) )
   => ( ( ~ r1_orders_2(sK0,k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,sK1))
        | ~ r3_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2)) )
      & r1_tarski(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( ~ r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
            | ~ r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) )
          & r1_tarski(X1,X2) )
      & l1_orders_2(X0)
      & v3_lattice3(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( ~ r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
            | ~ r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) )
          & r1_tarski(X1,X2) )
      & l1_orders_2(X0)
      & v3_lattice3(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_lattice3(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1,X2] :
            ( r1_tarski(X1,X2)
           => ( r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
              & r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_lattice3(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => ( r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
            & r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_waybel_7)).

fof(f43,plain,
    ( ~ v2_struct_0(sK0)
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f35,f30])).

fof(f30,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v2_lattice3(X0)
      | ~ v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_lattice3)).

fof(f72,plain,(
    v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f71,f26])).

fof(f26,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f71,plain,
    ( ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f70,f32])).

fof(f70,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f69,f45])).

fof(f45,plain,(
    ! [X0] : m1_subset_1(k1_yellow_0(sK0,X0),u1_struct_0(sK0)) ),
    inference(resolution,[],[f40,f32])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_0)).

fof(f69,plain,
    ( ~ m1_subset_1(k1_yellow_0(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f68,f45])).

fof(f68,plain,
    ( ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(k1_yellow_0(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f67,f59])).

fof(f59,plain,(
    ~ r3_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f34,f58])).

fof(f58,plain,(
    r1_orders_2(sK0,k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f57,f32])).

fof(f57,plain,
    ( r1_orders_2(sK0,k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,sK1))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f56,f53])).

fof(f53,plain,(
    ! [X0] : r2_yellow_0(sK0,X0) ),
    inference(subsumption_resolution,[],[f52,f44])).

fof(f52,plain,(
    ! [X0] :
      ( r2_yellow_0(sK0,X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f51,f28])).

fof(f28,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f51,plain,(
    ! [X0] :
      ( r2_yellow_0(sK0,X0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f50,f32])).

fof(f50,plain,(
    ! [X0] :
      ( ~ l1_orders_2(sK0)
      | r2_yellow_0(sK0,X0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f39,f31])).

fof(f31,plain,(
    v3_lattice3(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v3_lattice3(X0)
      | ~ l1_orders_2(X0)
      | r2_yellow_0(X0,X1)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
          & r1_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
          & r1_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_lattice3(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( r2_yellow_0(X0,X1)
          & r1_yellow_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_yellow_0)).

fof(f56,plain,
    ( ~ r2_yellow_0(sK0,sK1)
    | r1_orders_2(sK0,k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,sK1))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f54,f53])).

fof(f54,plain,(
    ! [X0] :
      ( ~ r2_yellow_0(X0,sK2)
      | ~ r2_yellow_0(X0,sK1)
      | r1_orders_2(X0,k2_yellow_0(X0,sK2),k2_yellow_0(X0,sK1))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f36,f33])).

fof(f33,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ r2_yellow_0(X0,X2)
      | ~ r2_yellow_0(X0,X1)
      | r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
          | ~ r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
          | ~ r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( ( r2_yellow_0(X0,X2)
            & r2_yellow_0(X0,X1)
            & r1_tarski(X1,X2) )
         => r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_yellow_0)).

fof(f34,plain,
    ( ~ r1_orders_2(sK0,k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,sK1))
    | ~ r3_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f24])).

fof(f67,plain,
    ( r3_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2))
    | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(k1_yellow_0(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f62,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_orders_2(X0,X1,X2)
          | ~ r1_orders_2(X0,X1,X2) )
        & ( r1_orders_2(X0,X1,X2)
          | ~ r3_orders_2(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f21])).

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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f62,plain,(
    r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f61,f32])).

fof(f61,plain,
    ( r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f60,f49])).

fof(f49,plain,(
    ! [X0] : r1_yellow_0(sK0,X0) ),
    inference(subsumption_resolution,[],[f48,f44])).

fof(f48,plain,(
    ! [X0] :
      ( r1_yellow_0(sK0,X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f47,f28])).

fof(f47,plain,(
    ! [X0] :
      ( r1_yellow_0(sK0,X0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f46,f32])).

fof(f46,plain,(
    ! [X0] :
      ( ~ l1_orders_2(sK0)
      | r1_yellow_0(sK0,X0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f38,f31])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v3_lattice3(X0)
      | ~ l1_orders_2(X0)
      | r1_yellow_0(X0,X1)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f60,plain,
    ( ~ r1_yellow_0(sK0,sK1)
    | r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f55,f49])).

fof(f55,plain,(
    ! [X0] :
      ( ~ r1_yellow_0(X0,sK2)
      | ~ r1_yellow_0(X0,sK1)
      | r1_orders_2(X0,k1_yellow_0(X0,sK1),k1_yellow_0(X0,sK2))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f37,f33])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ r1_yellow_0(X0,X2)
      | ~ r1_yellow_0(X0,X1)
      | r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
          | ~ r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
          | ~ r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( ( r1_yellow_0(X0,X2)
            & r1_yellow_0(X0,X1)
            & r1_tarski(X1,X2) )
         => r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_yellow_0)).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 19:22:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.44  % (26638)WARNING: option uwaf not known.
% 0.20/0.45  % (26638)lrs+10_4:1_av=off:bd=off:bsr=on:cond=on:fde=unused:inw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=5:stl=90:sp=reverse_arity:thi=strong:uwa=ground:updr=off:uwaf=on_73 on theBenchmark
% 0.20/0.45  % (26638)Refutation found. Thanks to Tanya!
% 0.20/0.45  % SZS status Theorem for theBenchmark
% 0.20/0.45  % SZS output start Proof for theBenchmark
% 0.20/0.45  fof(f73,plain,(
% 0.20/0.45    $false),
% 0.20/0.45    inference(subsumption_resolution,[],[f72,f44])).
% 0.20/0.45  fof(f44,plain,(
% 0.20/0.45    ~v2_struct_0(sK0)),
% 0.20/0.45    inference(subsumption_resolution,[],[f43,f32])).
% 0.20/0.45  fof(f32,plain,(
% 0.20/0.45    l1_orders_2(sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f24])).
% 0.20/0.45  fof(f24,plain,(
% 0.20/0.45    ((~r1_orders_2(sK0,k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,sK1)) | ~r3_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2))) & r1_tarski(sK1,sK2)) & l1_orders_2(sK0) & v3_lattice3(sK0) & v2_lattice3(sK0) & v1_lattice3(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0)),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f23,f22])).
% 0.20/0.45  fof(f22,plain,(
% 0.20/0.45    ? [X0] : (? [X1,X2] : ((~r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) | ~r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))) & r1_tarski(X1,X2)) & l1_orders_2(X0) & v3_lattice3(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => (? [X2,X1] : ((~r1_orders_2(sK0,k2_yellow_0(sK0,X2),k2_yellow_0(sK0,X1)) | ~r3_orders_2(sK0,k1_yellow_0(sK0,X1),k1_yellow_0(sK0,X2))) & r1_tarski(X1,X2)) & l1_orders_2(sK0) & v3_lattice3(sK0) & v2_lattice3(sK0) & v1_lattice3(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f23,plain,(
% 0.20/0.45    ? [X2,X1] : ((~r1_orders_2(sK0,k2_yellow_0(sK0,X2),k2_yellow_0(sK0,X1)) | ~r3_orders_2(sK0,k1_yellow_0(sK0,X1),k1_yellow_0(sK0,X2))) & r1_tarski(X1,X2)) => ((~r1_orders_2(sK0,k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,sK1)) | ~r3_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2))) & r1_tarski(sK1,sK2))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f10,plain,(
% 0.20/0.45    ? [X0] : (? [X1,X2] : ((~r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) | ~r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))) & r1_tarski(X1,X2)) & l1_orders_2(X0) & v3_lattice3(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0))),
% 0.20/0.45    inference(flattening,[],[f9])).
% 0.20/0.45  fof(f9,plain,(
% 0.20/0.45    ? [X0] : (? [X1,X2] : ((~r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) | ~r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))) & r1_tarski(X1,X2)) & (l1_orders_2(X0) & v3_lattice3(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f8])).
% 0.20/0.45  fof(f8,negated_conjecture,(
% 0.20/0.45    ~! [X0] : ((l1_orders_2(X0) & v3_lattice3(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => ! [X1,X2] : (r1_tarski(X1,X2) => (r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) & r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)))))),
% 0.20/0.45    inference(negated_conjecture,[],[f7])).
% 0.20/0.45  fof(f7,conjecture,(
% 0.20/0.45    ! [X0] : ((l1_orders_2(X0) & v3_lattice3(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => ! [X1,X2] : (r1_tarski(X1,X2) => (r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) & r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)))))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_waybel_7)).
% 0.20/0.45  fof(f43,plain,(
% 0.20/0.45    ~v2_struct_0(sK0) | ~l1_orders_2(sK0)),
% 0.20/0.45    inference(resolution,[],[f35,f30])).
% 0.20/0.45  fof(f30,plain,(
% 0.20/0.45    v2_lattice3(sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f24])).
% 0.20/0.45  fof(f35,plain,(
% 0.20/0.45    ( ! [X0] : (~v2_lattice3(X0) | ~v2_struct_0(X0) | ~l1_orders_2(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f12])).
% 0.20/0.45  fof(f12,plain,(
% 0.20/0.45    ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0))),
% 0.20/0.45    inference(flattening,[],[f11])).
% 0.20/0.45  fof(f11,plain,(
% 0.20/0.45    ! [X0] : ((~v2_struct_0(X0) | ~v2_lattice3(X0)) | ~l1_orders_2(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f2])).
% 0.20/0.45  fof(f2,axiom,(
% 0.20/0.45    ! [X0] : (l1_orders_2(X0) => (v2_lattice3(X0) => ~v2_struct_0(X0)))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_lattice3)).
% 0.20/0.45  fof(f72,plain,(
% 0.20/0.45    v2_struct_0(sK0)),
% 0.20/0.45    inference(subsumption_resolution,[],[f71,f26])).
% 0.20/0.45  fof(f26,plain,(
% 0.20/0.45    v3_orders_2(sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f24])).
% 0.20/0.45  fof(f71,plain,(
% 0.20/0.45    ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.20/0.45    inference(subsumption_resolution,[],[f70,f32])).
% 0.20/0.45  fof(f70,plain,(
% 0.20/0.45    ~l1_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.20/0.45    inference(subsumption_resolution,[],[f69,f45])).
% 0.20/0.45  fof(f45,plain,(
% 0.20/0.45    ( ! [X0] : (m1_subset_1(k1_yellow_0(sK0,X0),u1_struct_0(sK0))) )),
% 0.20/0.45    inference(resolution,[],[f40,f32])).
% 0.20/0.45  fof(f40,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~l1_orders_2(X0) | m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f19])).
% 0.20/0.45  fof(f19,plain,(
% 0.20/0.45    ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f3])).
% 0.20/0.45  fof(f3,axiom,(
% 0.20/0.45    ! [X0,X1] : (l1_orders_2(X0) => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_0)).
% 0.20/0.45  fof(f69,plain,(
% 0.20/0.45    ~m1_subset_1(k1_yellow_0(sK0,sK1),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.20/0.45    inference(subsumption_resolution,[],[f68,f45])).
% 0.20/0.45  fof(f68,plain,(
% 0.20/0.45    ~m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0)) | ~m1_subset_1(k1_yellow_0(sK0,sK1),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.20/0.45    inference(subsumption_resolution,[],[f67,f59])).
% 0.20/0.45  fof(f59,plain,(
% 0.20/0.45    ~r3_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2))),
% 0.20/0.45    inference(subsumption_resolution,[],[f34,f58])).
% 0.20/0.45  fof(f58,plain,(
% 0.20/0.45    r1_orders_2(sK0,k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,sK1))),
% 0.20/0.45    inference(subsumption_resolution,[],[f57,f32])).
% 0.20/0.45  fof(f57,plain,(
% 0.20/0.45    r1_orders_2(sK0,k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,sK1)) | ~l1_orders_2(sK0)),
% 0.20/0.45    inference(subsumption_resolution,[],[f56,f53])).
% 0.20/0.45  fof(f53,plain,(
% 0.20/0.45    ( ! [X0] : (r2_yellow_0(sK0,X0)) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f52,f44])).
% 0.20/0.45  fof(f52,plain,(
% 0.20/0.45    ( ! [X0] : (r2_yellow_0(sK0,X0) | v2_struct_0(sK0)) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f51,f28])).
% 0.20/0.45  fof(f28,plain,(
% 0.20/0.45    v5_orders_2(sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f24])).
% 0.20/0.45  fof(f51,plain,(
% 0.20/0.45    ( ! [X0] : (r2_yellow_0(sK0,X0) | ~v5_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f50,f32])).
% 0.20/0.45  fof(f50,plain,(
% 0.20/0.45    ( ! [X0] : (~l1_orders_2(sK0) | r2_yellow_0(sK0,X0) | ~v5_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.45    inference(resolution,[],[f39,f31])).
% 0.20/0.45  fof(f31,plain,(
% 0.20/0.45    v3_lattice3(sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f24])).
% 0.20/0.45  fof(f39,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~v3_lattice3(X0) | ~l1_orders_2(X0) | r2_yellow_0(X0,X1) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f18])).
% 0.20/0.45  fof(f18,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (r2_yellow_0(X0,X1) & r1_yellow_0(X0,X1)) | ~l1_orders_2(X0) | ~v3_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.45    inference(flattening,[],[f17])).
% 0.20/0.45  fof(f17,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (r2_yellow_0(X0,X1) & r1_yellow_0(X0,X1)) | (~l1_orders_2(X0) | ~v3_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f4])).
% 0.20/0.45  fof(f4,axiom,(
% 0.20/0.45    ! [X0] : ((l1_orders_2(X0) & v3_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (r2_yellow_0(X0,X1) & r1_yellow_0(X0,X1)))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_yellow_0)).
% 0.20/0.45  fof(f56,plain,(
% 0.20/0.45    ~r2_yellow_0(sK0,sK1) | r1_orders_2(sK0,k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,sK1)) | ~l1_orders_2(sK0)),
% 0.20/0.45    inference(resolution,[],[f54,f53])).
% 0.20/0.45  fof(f54,plain,(
% 0.20/0.45    ( ! [X0] : (~r2_yellow_0(X0,sK2) | ~r2_yellow_0(X0,sK1) | r1_orders_2(X0,k2_yellow_0(X0,sK2),k2_yellow_0(X0,sK1)) | ~l1_orders_2(X0)) )),
% 0.20/0.45    inference(resolution,[],[f36,f33])).
% 0.20/0.45  fof(f33,plain,(
% 0.20/0.45    r1_tarski(sK1,sK2)),
% 0.20/0.45    inference(cnf_transformation,[],[f24])).
% 0.20/0.45  fof(f36,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | ~r2_yellow_0(X0,X2) | ~r2_yellow_0(X0,X1) | r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) | ~l1_orders_2(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f14])).
% 0.20/0.45  fof(f14,plain,(
% 0.20/0.45    ! [X0] : (! [X1,X2] : (r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) | ~r2_yellow_0(X0,X2) | ~r2_yellow_0(X0,X1) | ~r1_tarski(X1,X2)) | ~l1_orders_2(X0))),
% 0.20/0.45    inference(flattening,[],[f13])).
% 0.20/0.45  fof(f13,plain,(
% 0.20/0.45    ! [X0] : (! [X1,X2] : (r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) | (~r2_yellow_0(X0,X2) | ~r2_yellow_0(X0,X1) | ~r1_tarski(X1,X2))) | ~l1_orders_2(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f6])).
% 0.20/0.45  fof(f6,axiom,(
% 0.20/0.45    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : ((r2_yellow_0(X0,X2) & r2_yellow_0(X0,X1) & r1_tarski(X1,X2)) => r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_yellow_0)).
% 0.20/0.45  fof(f34,plain,(
% 0.20/0.45    ~r1_orders_2(sK0,k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,sK1)) | ~r3_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2))),
% 0.20/0.45    inference(cnf_transformation,[],[f24])).
% 0.20/0.45  fof(f67,plain,(
% 0.20/0.45    r3_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2)) | ~m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0)) | ~m1_subset_1(k1_yellow_0(sK0,sK1),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.20/0.45    inference(resolution,[],[f62,f42])).
% 0.20/0.45  fof(f42,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~r1_orders_2(X0,X1,X2) | r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f25])).
% 0.20/0.45  fof(f25,plain,(
% 0.20/0.45    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.45    inference(nnf_transformation,[],[f21])).
% 0.20/0.45  fof(f21,plain,(
% 0.20/0.45    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.45    inference(flattening,[],[f20])).
% 0.20/0.45  fof(f20,plain,(
% 0.20/0.45    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f1])).
% 0.20/0.45  fof(f1,axiom,(
% 0.20/0.45    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 0.20/0.45  fof(f62,plain,(
% 0.20/0.45    r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2))),
% 0.20/0.45    inference(subsumption_resolution,[],[f61,f32])).
% 0.20/0.45  fof(f61,plain,(
% 0.20/0.45    r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2)) | ~l1_orders_2(sK0)),
% 0.20/0.45    inference(subsumption_resolution,[],[f60,f49])).
% 0.20/0.45  fof(f49,plain,(
% 0.20/0.45    ( ! [X0] : (r1_yellow_0(sK0,X0)) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f48,f44])).
% 0.20/0.45  fof(f48,plain,(
% 0.20/0.45    ( ! [X0] : (r1_yellow_0(sK0,X0) | v2_struct_0(sK0)) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f47,f28])).
% 0.20/0.45  fof(f47,plain,(
% 0.20/0.45    ( ! [X0] : (r1_yellow_0(sK0,X0) | ~v5_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f46,f32])).
% 0.20/0.45  fof(f46,plain,(
% 0.20/0.45    ( ! [X0] : (~l1_orders_2(sK0) | r1_yellow_0(sK0,X0) | ~v5_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.45    inference(resolution,[],[f38,f31])).
% 0.20/0.45  fof(f38,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~v3_lattice3(X0) | ~l1_orders_2(X0) | r1_yellow_0(X0,X1) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f18])).
% 0.20/0.45  fof(f60,plain,(
% 0.20/0.45    ~r1_yellow_0(sK0,sK1) | r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2)) | ~l1_orders_2(sK0)),
% 0.20/0.45    inference(resolution,[],[f55,f49])).
% 0.20/0.45  fof(f55,plain,(
% 0.20/0.45    ( ! [X0] : (~r1_yellow_0(X0,sK2) | ~r1_yellow_0(X0,sK1) | r1_orders_2(X0,k1_yellow_0(X0,sK1),k1_yellow_0(X0,sK2)) | ~l1_orders_2(X0)) )),
% 0.20/0.45    inference(resolution,[],[f37,f33])).
% 0.20/0.45  fof(f37,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | ~r1_yellow_0(X0,X2) | ~r1_yellow_0(X0,X1) | r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) | ~l1_orders_2(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f16])).
% 0.20/0.45  fof(f16,plain,(
% 0.20/0.45    ! [X0] : (! [X1,X2] : (r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) | ~r1_yellow_0(X0,X2) | ~r1_yellow_0(X0,X1) | ~r1_tarski(X1,X2)) | ~l1_orders_2(X0))),
% 0.20/0.45    inference(flattening,[],[f15])).
% 0.20/0.45  fof(f15,plain,(
% 0.20/0.45    ! [X0] : (! [X1,X2] : (r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) | (~r1_yellow_0(X0,X2) | ~r1_yellow_0(X0,X1) | ~r1_tarski(X1,X2))) | ~l1_orders_2(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f5])).
% 0.20/0.45  fof(f5,axiom,(
% 0.20/0.45    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : ((r1_yellow_0(X0,X2) & r1_yellow_0(X0,X1) & r1_tarski(X1,X2)) => r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_yellow_0)).
% 0.20/0.45  % SZS output end Proof for theBenchmark
% 0.20/0.45  % (26638)------------------------------
% 0.20/0.45  % (26638)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (26638)Termination reason: Refutation
% 0.20/0.45  
% 0.20/0.45  % (26638)Memory used [KB]: 895
% 0.20/0.45  % (26638)Time elapsed: 0.006 s
% 0.20/0.45  % (26638)------------------------------
% 0.20/0.45  % (26638)------------------------------
% 0.20/0.45  % (26624)Success in time 0.094 s
%------------------------------------------------------------------------------
