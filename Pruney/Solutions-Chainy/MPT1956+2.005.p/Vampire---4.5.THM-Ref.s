%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:48 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 353 expanded)
%              Number of leaves         :   11 ( 111 expanded)
%              Depth                    :   17
%              Number of atoms          :  294 (2748 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f85,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f71,f80,f84])).

fof(f84,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f83])).

fof(f83,plain,
    ( $false
    | spl3_2 ),
    inference(subsumption_resolution,[],[f81,f33])).

fof(f33,plain,(
    r1_tarski(sK1,sK2) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_waybel_7)).

fof(f81,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl3_2 ),
    inference(resolution,[],[f70,f62])).

fof(f62,plain,(
    ! [X6,X7] :
      ( r1_orders_2(sK0,k2_yellow_0(sK0,X6),k2_yellow_0(sK0,X7))
      | ~ r1_tarski(X7,X6) ) ),
    inference(global_subsumption,[],[f50,f61])).

fof(f61,plain,(
    ! [X6,X7] :
      ( ~ r2_yellow_0(sK0,X7)
      | ~ r1_tarski(X7,X6)
      | r1_orders_2(sK0,k2_yellow_0(sK0,X6),k2_yellow_0(sK0,X7)) ) ),
    inference(global_subsumption,[],[f50,f54])).

fof(f54,plain,(
    ! [X6,X7] :
      ( ~ r2_yellow_0(sK0,X6)
      | ~ r2_yellow_0(sK0,X7)
      | ~ r1_tarski(X7,X6)
      | r1_orders_2(sK0,k2_yellow_0(sK0,X6),k2_yellow_0(sK0,X7)) ) ),
    inference(resolution,[],[f32,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_yellow_0(X0,X2)
      | ~ r2_yellow_0(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_yellow_0)).

fof(f32,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f50,plain,(
    ! [X1] : r2_yellow_0(sK0,X1) ),
    inference(global_subsumption,[],[f32,f44,f49])).

fof(f49,plain,(
    ! [X1] :
      ( ~ l1_orders_2(sK0)
      | r2_yellow_0(sK0,X1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f46,f28])).

fof(f28,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f46,plain,(
    ! [X1] :
      ( ~ l1_orders_2(sK0)
      | r2_yellow_0(sK0,X1)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f31,f39])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_yellow_0)).

fof(f31,plain,(
    v3_lattice3(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f44,plain,(
    ~ v2_struct_0(sK0) ),
    inference(global_subsumption,[],[f32,f43])).

fof(f43,plain,
    ( ~ v2_struct_0(sK0)
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f29,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_lattice3(X0)
      | ~ v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).

fof(f29,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f70,plain,
    ( ~ r1_orders_2(sK0,k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,sK1))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl3_2
  <=> r1_orders_2(sK0,k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f80,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f79])).

fof(f79,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f78,f33])).

fof(f78,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl3_1 ),
    inference(resolution,[],[f76,f66])).

fof(f66,plain,
    ( ~ r3_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl3_1
  <=> r3_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r3_orders_2(sK0,k1_yellow_0(sK0,X0),k1_yellow_0(sK0,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f75,f60])).

fof(f60,plain,(
    ! [X4,X5] :
      ( r1_orders_2(sK0,k1_yellow_0(sK0,X5),k1_yellow_0(sK0,X4))
      | ~ r1_tarski(X5,X4) ) ),
    inference(global_subsumption,[],[f48,f59])).

fof(f59,plain,(
    ! [X4,X5] :
      ( ~ r1_yellow_0(sK0,X5)
      | ~ r1_tarski(X5,X4)
      | r1_orders_2(sK0,k1_yellow_0(sK0,X5),k1_yellow_0(sK0,X4)) ) ),
    inference(global_subsumption,[],[f48,f53])).

fof(f53,plain,(
    ! [X4,X5] :
      ( ~ r1_yellow_0(sK0,X4)
      | ~ r1_yellow_0(sK0,X5)
      | ~ r1_tarski(X5,X4)
      | r1_orders_2(sK0,k1_yellow_0(sK0,X5),k1_yellow_0(sK0,X4)) ) ),
    inference(resolution,[],[f32,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_yellow_0)).

fof(f48,plain,(
    ! [X0] : r1_yellow_0(sK0,X0) ),
    inference(global_subsumption,[],[f32,f44,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ l1_orders_2(sK0)
      | r1_yellow_0(sK0,X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f45,f28])).

fof(f45,plain,(
    ! [X0] :
      ( ~ l1_orders_2(sK0)
      | r1_yellow_0(sK0,X0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f31,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v3_lattice3(X0)
      | ~ l1_orders_2(X0)
      | r1_yellow_0(X0,X1)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK0,k1_yellow_0(sK0,X0),k1_yellow_0(sK0,X1))
      | r3_orders_2(sK0,k1_yellow_0(sK0,X0),k1_yellow_0(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f74,f32])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK0,k1_yellow_0(sK0,X0),k1_yellow_0(sK0,X1))
      | r3_orders_2(sK0,k1_yellow_0(sK0,X0),k1_yellow_0(sK0,X1))
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f73,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,k1_yellow_0(sK0,X1),X0)
      | r3_orders_2(sK0,k1_yellow_0(sK0,X1),X0) ) ),
    inference(subsumption_resolution,[],[f72,f32])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,k1_yellow_0(sK0,X1),X0)
      | r3_orders_2(sK0,k1_yellow_0(sK0,X1),X0)
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f58,f40])).

fof(f58,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X2,X3)
      | r3_orders_2(sK0,X2,X3) ) ),
    inference(global_subsumption,[],[f44,f57])).

fof(f57,plain,(
    ! [X2,X3] :
      ( ~ r1_orders_2(sK0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r3_orders_2(sK0,X2,X3)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f52,f26])).

fof(f26,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f52,plain,(
    ! [X2,X3] :
      ( ~ r1_orders_2(sK0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r3_orders_2(sK0,X2,X3)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f32,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r3_orders_2(X0,X1,X2)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f71,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f34,f68,f64])).

fof(f34,plain,
    ( ~ r1_orders_2(sK0,k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,sK1))
    | ~ r3_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:39:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (8921)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.22/0.47  % (8921)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % (8913)dis+1002_8:1_awrs=converge:awrsf=256:anc=all_dependent:br=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:irw=on:nm=64:nwc=1:sas=z3:s2a=on:sp=frequency:thf=on:uwa=interpreted_only:urr=on_7 on theBenchmark
% 0.22/0.48  % (8928)dis+1011_4_awrs=decay:awrsf=32:afp=40000:afq=1.0:amm=off:anc=all:bs=on:cond=on:fsr=off:gsp=input_only:lma=on:nm=16:nwc=1:nicw=on:sac=on:sp=frequency:thi=all:updr=off:uhcvi=on_670 on theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f85,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f71,f80,f84])).
% 0.22/0.48  fof(f84,plain,(
% 0.22/0.48    spl3_2),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f83])).
% 0.22/0.48  fof(f83,plain,(
% 0.22/0.48    $false | spl3_2),
% 0.22/0.48    inference(subsumption_resolution,[],[f81,f33])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    r1_tarski(sK1,sK2)),
% 0.22/0.48    inference(cnf_transformation,[],[f24])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ((~r1_orders_2(sK0,k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,sK1)) | ~r3_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2))) & r1_tarski(sK1,sK2)) & l1_orders_2(sK0) & v3_lattice3(sK0) & v2_lattice3(sK0) & v1_lattice3(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0)),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f23,f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ? [X0] : (? [X1,X2] : ((~r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) | ~r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))) & r1_tarski(X1,X2)) & l1_orders_2(X0) & v3_lattice3(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => (? [X2,X1] : ((~r1_orders_2(sK0,k2_yellow_0(sK0,X2),k2_yellow_0(sK0,X1)) | ~r3_orders_2(sK0,k1_yellow_0(sK0,X1),k1_yellow_0(sK0,X2))) & r1_tarski(X1,X2)) & l1_orders_2(sK0) & v3_lattice3(sK0) & v2_lattice3(sK0) & v1_lattice3(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ? [X2,X1] : ((~r1_orders_2(sK0,k2_yellow_0(sK0,X2),k2_yellow_0(sK0,X1)) | ~r3_orders_2(sK0,k1_yellow_0(sK0,X1),k1_yellow_0(sK0,X2))) & r1_tarski(X1,X2)) => ((~r1_orders_2(sK0,k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,sK1)) | ~r3_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2))) & r1_tarski(sK1,sK2))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    ? [X0] : (? [X1,X2] : ((~r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) | ~r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))) & r1_tarski(X1,X2)) & l1_orders_2(X0) & v3_lattice3(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0))),
% 0.22/0.48    inference(flattening,[],[f9])).
% 0.22/0.48  fof(f9,plain,(
% 0.22/0.48    ? [X0] : (? [X1,X2] : ((~r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) | ~r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))) & r1_tarski(X1,X2)) & (l1_orders_2(X0) & v3_lattice3(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,negated_conjecture,(
% 0.22/0.48    ~! [X0] : ((l1_orders_2(X0) & v3_lattice3(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => ! [X1,X2] : (r1_tarski(X1,X2) => (r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) & r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)))))),
% 0.22/0.48    inference(negated_conjecture,[],[f7])).
% 0.22/0.48  fof(f7,conjecture,(
% 0.22/0.48    ! [X0] : ((l1_orders_2(X0) & v3_lattice3(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => ! [X1,X2] : (r1_tarski(X1,X2) => (r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) & r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_waybel_7)).
% 0.22/0.48  fof(f81,plain,(
% 0.22/0.48    ~r1_tarski(sK1,sK2) | spl3_2),
% 0.22/0.48    inference(resolution,[],[f70,f62])).
% 0.22/0.48  fof(f62,plain,(
% 0.22/0.48    ( ! [X6,X7] : (r1_orders_2(sK0,k2_yellow_0(sK0,X6),k2_yellow_0(sK0,X7)) | ~r1_tarski(X7,X6)) )),
% 0.22/0.48    inference(global_subsumption,[],[f50,f61])).
% 0.22/0.48  fof(f61,plain,(
% 0.22/0.48    ( ! [X6,X7] : (~r2_yellow_0(sK0,X7) | ~r1_tarski(X7,X6) | r1_orders_2(sK0,k2_yellow_0(sK0,X6),k2_yellow_0(sK0,X7))) )),
% 0.22/0.48    inference(global_subsumption,[],[f50,f54])).
% 0.22/0.48  fof(f54,plain,(
% 0.22/0.48    ( ! [X6,X7] : (~r2_yellow_0(sK0,X6) | ~r2_yellow_0(sK0,X7) | ~r1_tarski(X7,X6) | r1_orders_2(sK0,k2_yellow_0(sK0,X6),k2_yellow_0(sK0,X7))) )),
% 0.22/0.48    inference(resolution,[],[f32,f36])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~r2_yellow_0(X0,X2) | ~r2_yellow_0(X0,X1) | ~r1_tarski(X1,X2) | r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ! [X0] : (! [X1,X2] : (r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) | ~r2_yellow_0(X0,X2) | ~r2_yellow_0(X0,X1) | ~r1_tarski(X1,X2)) | ~l1_orders_2(X0))),
% 0.22/0.48    inference(flattening,[],[f13])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ! [X0] : (! [X1,X2] : (r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) | (~r2_yellow_0(X0,X2) | ~r2_yellow_0(X0,X1) | ~r1_tarski(X1,X2))) | ~l1_orders_2(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : ((r2_yellow_0(X0,X2) & r2_yellow_0(X0,X1) & r1_tarski(X1,X2)) => r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_yellow_0)).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    l1_orders_2(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f24])).
% 0.22/0.48  fof(f50,plain,(
% 0.22/0.48    ( ! [X1] : (r2_yellow_0(sK0,X1)) )),
% 0.22/0.48    inference(global_subsumption,[],[f32,f44,f49])).
% 0.22/0.48  fof(f49,plain,(
% 0.22/0.48    ( ! [X1] : (~l1_orders_2(sK0) | r2_yellow_0(sK0,X1) | v2_struct_0(sK0)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f46,f28])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    v5_orders_2(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f24])).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    ( ! [X1] : (~l1_orders_2(sK0) | r2_yellow_0(sK0,X1) | ~v5_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.48    inference(resolution,[],[f31,f39])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v3_lattice3(X0) | ~l1_orders_2(X0) | r2_yellow_0(X0,X1) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (r2_yellow_0(X0,X1) & r1_yellow_0(X0,X1)) | ~l1_orders_2(X0) | ~v3_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (r2_yellow_0(X0,X1) & r1_yellow_0(X0,X1)) | (~l1_orders_2(X0) | ~v3_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0] : ((l1_orders_2(X0) & v3_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (r2_yellow_0(X0,X1) & r1_yellow_0(X0,X1)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_yellow_0)).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    v3_lattice3(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f24])).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    ~v2_struct_0(sK0)),
% 0.22/0.48    inference(global_subsumption,[],[f32,f43])).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    ~v2_struct_0(sK0) | ~l1_orders_2(sK0)),
% 0.22/0.48    inference(resolution,[],[f29,f35])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    ( ! [X0] : (~v1_lattice3(X0) | ~v2_struct_0(X0) | ~l1_orders_2(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 0.22/0.48    inference(flattening,[],[f11])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    v1_lattice3(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f24])).
% 0.22/0.48  fof(f70,plain,(
% 0.22/0.48    ~r1_orders_2(sK0,k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,sK1)) | spl3_2),
% 0.22/0.48    inference(avatar_component_clause,[],[f68])).
% 0.22/0.48  fof(f68,plain,(
% 0.22/0.48    spl3_2 <=> r1_orders_2(sK0,k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,sK1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.48  fof(f80,plain,(
% 0.22/0.48    spl3_1),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f79])).
% 0.22/0.48  fof(f79,plain,(
% 0.22/0.48    $false | spl3_1),
% 0.22/0.48    inference(subsumption_resolution,[],[f78,f33])).
% 0.22/0.48  fof(f78,plain,(
% 0.22/0.48    ~r1_tarski(sK1,sK2) | spl3_1),
% 0.22/0.48    inference(resolution,[],[f76,f66])).
% 0.22/0.48  fof(f66,plain,(
% 0.22/0.48    ~r3_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2)) | spl3_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f64])).
% 0.22/0.48  fof(f64,plain,(
% 0.22/0.48    spl3_1 <=> r3_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.48  fof(f76,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r3_orders_2(sK0,k1_yellow_0(sK0,X0),k1_yellow_0(sK0,X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.48    inference(resolution,[],[f75,f60])).
% 0.22/0.48  fof(f60,plain,(
% 0.22/0.48    ( ! [X4,X5] : (r1_orders_2(sK0,k1_yellow_0(sK0,X5),k1_yellow_0(sK0,X4)) | ~r1_tarski(X5,X4)) )),
% 0.22/0.48    inference(global_subsumption,[],[f48,f59])).
% 0.22/0.48  fof(f59,plain,(
% 0.22/0.48    ( ! [X4,X5] : (~r1_yellow_0(sK0,X5) | ~r1_tarski(X5,X4) | r1_orders_2(sK0,k1_yellow_0(sK0,X5),k1_yellow_0(sK0,X4))) )),
% 0.22/0.48    inference(global_subsumption,[],[f48,f53])).
% 0.22/0.48  fof(f53,plain,(
% 0.22/0.48    ( ! [X4,X5] : (~r1_yellow_0(sK0,X4) | ~r1_yellow_0(sK0,X5) | ~r1_tarski(X5,X4) | r1_orders_2(sK0,k1_yellow_0(sK0,X5),k1_yellow_0(sK0,X4))) )),
% 0.22/0.48    inference(resolution,[],[f32,f37])).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~r1_yellow_0(X0,X2) | ~r1_yellow_0(X0,X1) | ~r1_tarski(X1,X2) | r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ! [X0] : (! [X1,X2] : (r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) | ~r1_yellow_0(X0,X2) | ~r1_yellow_0(X0,X1) | ~r1_tarski(X1,X2)) | ~l1_orders_2(X0))),
% 0.22/0.48    inference(flattening,[],[f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ! [X0] : (! [X1,X2] : (r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) | (~r1_yellow_0(X0,X2) | ~r1_yellow_0(X0,X1) | ~r1_tarski(X1,X2))) | ~l1_orders_2(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : ((r1_yellow_0(X0,X2) & r1_yellow_0(X0,X1) & r1_tarski(X1,X2)) => r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_yellow_0)).
% 0.22/0.48  fof(f48,plain,(
% 0.22/0.48    ( ! [X0] : (r1_yellow_0(sK0,X0)) )),
% 0.22/0.48    inference(global_subsumption,[],[f32,f44,f47])).
% 0.22/0.48  fof(f47,plain,(
% 0.22/0.48    ( ! [X0] : (~l1_orders_2(sK0) | r1_yellow_0(sK0,X0) | v2_struct_0(sK0)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f45,f28])).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    ( ! [X0] : (~l1_orders_2(sK0) | r1_yellow_0(sK0,X0) | ~v5_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.48    inference(resolution,[],[f31,f38])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v3_lattice3(X0) | ~l1_orders_2(X0) | r1_yellow_0(X0,X1) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f75,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r1_orders_2(sK0,k1_yellow_0(sK0,X0),k1_yellow_0(sK0,X1)) | r3_orders_2(sK0,k1_yellow_0(sK0,X0),k1_yellow_0(sK0,X1))) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f74,f32])).
% 0.22/0.48  fof(f74,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r1_orders_2(sK0,k1_yellow_0(sK0,X0),k1_yellow_0(sK0,X1)) | r3_orders_2(sK0,k1_yellow_0(sK0,X0),k1_yellow_0(sK0,X1)) | ~l1_orders_2(sK0)) )),
% 0.22/0.48    inference(resolution,[],[f73,f40])).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    ( ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f19])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1] : (l1_orders_2(X0) => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).
% 0.22/0.48  fof(f73,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,k1_yellow_0(sK0,X1),X0) | r3_orders_2(sK0,k1_yellow_0(sK0,X1),X0)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f72,f32])).
% 0.22/0.48  fof(f72,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,k1_yellow_0(sK0,X1),X0) | r3_orders_2(sK0,k1_yellow_0(sK0,X1),X0) | ~l1_orders_2(sK0)) )),
% 0.22/0.48    inference(resolution,[],[f58,f40])).
% 0.22/0.48  fof(f58,plain,(
% 0.22/0.48    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X2,X3) | r3_orders_2(sK0,X2,X3)) )),
% 0.22/0.48    inference(global_subsumption,[],[f44,f57])).
% 0.22/0.48  fof(f57,plain,(
% 0.22/0.48    ( ! [X2,X3] : (~r1_orders_2(sK0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r3_orders_2(sK0,X2,X3) | v2_struct_0(sK0)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f52,f26])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    v3_orders_2(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f24])).
% 0.22/0.48  fof(f52,plain,(
% 0.22/0.48    ( ! [X2,X3] : (~r1_orders_2(sK0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r3_orders_2(sK0,X2,X3) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.48    inference(resolution,[],[f32,f42])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r3_orders_2(X0,X1,X2) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f25])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(nnf_transformation,[],[f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 0.22/0.48  fof(f71,plain,(
% 0.22/0.48    ~spl3_1 | ~spl3_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f34,f68,f64])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    ~r1_orders_2(sK0,k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,sK1)) | ~r3_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2))),
% 0.22/0.48    inference(cnf_transformation,[],[f24])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (8921)------------------------------
% 0.22/0.48  % (8921)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (8921)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (8921)Memory used [KB]: 9850
% 0.22/0.48  % (8921)Time elapsed: 0.056 s
% 0.22/0.48  % (8921)------------------------------
% 0.22/0.48  % (8921)------------------------------
% 0.22/0.48  % (8911)Success in time 0.119 s
%------------------------------------------------------------------------------
