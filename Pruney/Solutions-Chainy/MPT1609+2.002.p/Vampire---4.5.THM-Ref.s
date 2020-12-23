%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:36 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 283 expanded)
%              Number of leaves         :   18 (  81 expanded)
%              Depth                    :   24
%              Number of atoms          :  413 ( 777 expanded)
%              Number of equality atoms :   74 ( 254 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f148,plain,(
    $false ),
    inference(subsumption_resolution,[],[f147,f76])).

fof(f76,plain,(
    m1_subset_1(sK1,k9_setfam_1(sK0)) ),
    inference(backward_demodulation,[],[f46,f73])).

fof(f73,plain,(
    ! [X0] : u1_struct_0(k3_yellow_1(X0)) = k9_setfam_1(X0) ),
    inference(superposition,[],[f56,f50])).

fof(f50,plain,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).

fof(f56,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

fof(f46,plain,(
    m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( ( k3_xboole_0(sK1,sK2) != k12_lattice3(k3_yellow_1(sK0),sK1,sK2)
      | k2_xboole_0(sK1,sK2) != k13_lattice3(k3_yellow_1(sK0),sK1,sK2) )
    & m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK0)))
    & m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f44,f43])).

fof(f43,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( k3_xboole_0(X1,X2) != k12_lattice3(k3_yellow_1(X0),X1,X2)
              | k2_xboole_0(X1,X2) != k13_lattice3(k3_yellow_1(X0),X1,X2) )
            & m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) )
        & m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) )
   => ( ? [X2] :
          ( ( k3_xboole_0(sK1,X2) != k12_lattice3(k3_yellow_1(sK0),sK1,X2)
            | k2_xboole_0(sK1,X2) != k13_lattice3(k3_yellow_1(sK0),sK1,X2) )
          & m1_subset_1(X2,u1_struct_0(k3_yellow_1(sK0))) )
      & m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X2] :
        ( ( k3_xboole_0(sK1,X2) != k12_lattice3(k3_yellow_1(sK0),sK1,X2)
          | k2_xboole_0(sK1,X2) != k13_lattice3(k3_yellow_1(sK0),sK1,X2) )
        & m1_subset_1(X2,u1_struct_0(k3_yellow_1(sK0))) )
   => ( ( k3_xboole_0(sK1,sK2) != k12_lattice3(k3_yellow_1(sK0),sK1,sK2)
        | k2_xboole_0(sK1,sK2) != k13_lattice3(k3_yellow_1(sK0),sK1,sK2) )
      & m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( k3_xboole_0(X1,X2) != k12_lattice3(k3_yellow_1(X0),X1,X2)
            | k2_xboole_0(X1,X2) != k13_lattice3(k3_yellow_1(X0),X1,X2) )
          & m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) )
      & m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
           => ( k3_xboole_0(X1,X2) = k12_lattice3(k3_yellow_1(X0),X1,X2)
              & k2_xboole_0(X1,X2) = k13_lattice3(k3_yellow_1(X0),X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
         => ( k3_xboole_0(X1,X2) = k12_lattice3(k3_yellow_1(X0),X1,X2)
            & k2_xboole_0(X1,X2) = k13_lattice3(k3_yellow_1(X0),X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_yellow_1)).

fof(f147,plain,(
    ~ m1_subset_1(sK1,k9_setfam_1(sK0)) ),
    inference(subsumption_resolution,[],[f146,f77])).

fof(f77,plain,(
    m1_subset_1(sK2,k9_setfam_1(sK0)) ),
    inference(backward_demodulation,[],[f47,f73])).

fof(f47,plain,(
    m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f45])).

fof(f146,plain,
    ( ~ m1_subset_1(sK2,k9_setfam_1(sK0))
    | ~ m1_subset_1(sK1,k9_setfam_1(sK0)) ),
    inference(trivial_inequality_removal,[],[f145])).

fof(f145,plain,
    ( k3_xboole_0(sK1,sK2) != k3_xboole_0(sK1,sK2)
    | ~ m1_subset_1(sK2,k9_setfam_1(sK0))
    | ~ m1_subset_1(sK1,k9_setfam_1(sK0)) ),
    inference(superposition,[],[f142,f138])).

fof(f138,plain,(
    ! [X4,X5,X3] :
      ( k3_xboole_0(X4,X5) = k12_lattice3(k3_yellow_1(X3),X4,X5)
      | ~ m1_subset_1(X5,k9_setfam_1(X3))
      | ~ m1_subset_1(X4,k9_setfam_1(X3)) ) ),
    inference(duplicate_literal_removal,[],[f137])).

fof(f137,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X4,k9_setfam_1(X3))
      | ~ m1_subset_1(X5,k9_setfam_1(X3))
      | k3_xboole_0(X4,X5) = k12_lattice3(k3_yellow_1(X3),X4,X5)
      | ~ m1_subset_1(X4,k9_setfam_1(X3)) ) ),
    inference(forward_demodulation,[],[f136,f73])).

fof(f136,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k9_setfam_1(X3))
      | k3_xboole_0(X4,X5) = k12_lattice3(k3_yellow_1(X3),X4,X5)
      | ~ m1_subset_1(X4,u1_struct_0(k3_yellow_1(X3)))
      | ~ m1_subset_1(X4,k9_setfam_1(X3)) ) ),
    inference(duplicate_literal_removal,[],[f135])).

fof(f135,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k9_setfam_1(X3))
      | k3_xboole_0(X4,X5) = k12_lattice3(k3_yellow_1(X3),X4,X5)
      | ~ m1_subset_1(X4,u1_struct_0(k3_yellow_1(X3)))
      | ~ m1_subset_1(X5,k9_setfam_1(X3))
      | ~ m1_subset_1(X4,k9_setfam_1(X3)) ) ),
    inference(forward_demodulation,[],[f134,f73])).

fof(f134,plain,(
    ! [X4,X5,X3] :
      ( k3_xboole_0(X4,X5) = k12_lattice3(k3_yellow_1(X3),X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(k3_yellow_1(X3)))
      | ~ m1_subset_1(X4,u1_struct_0(k3_yellow_1(X3)))
      | ~ m1_subset_1(X5,k9_setfam_1(X3))
      | ~ m1_subset_1(X4,k9_setfam_1(X3)) ) ),
    inference(subsumption_resolution,[],[f133,f74])).

fof(f74,plain,(
    ! [X1] : v5_orders_2(k3_yellow_1(X1)) ),
    inference(superposition,[],[f55,f50])).

fof(f55,plain,(
    ! [X0] : v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] : v5_orders_2(k2_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v4_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).

fof(f133,plain,(
    ! [X4,X5,X3] :
      ( k3_xboole_0(X4,X5) = k12_lattice3(k3_yellow_1(X3),X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(k3_yellow_1(X3)))
      | ~ m1_subset_1(X4,u1_struct_0(k3_yellow_1(X3)))
      | ~ v5_orders_2(k3_yellow_1(X3))
      | ~ m1_subset_1(X5,k9_setfam_1(X3))
      | ~ m1_subset_1(X4,k9_setfam_1(X3)) ) ),
    inference(subsumption_resolution,[],[f132,f90])).

fof(f90,plain,(
    ! [X0] : v2_lattice3(k3_yellow_1(X0)) ),
    inference(subsumption_resolution,[],[f89,f51])).

fof(f51,plain,(
    ! [X0] : ~ v2_struct_0(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] : ~ v2_struct_0(k1_lattice3(X0)) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v3_lattices(k1_lattice3(X0))
      & ~ v2_struct_0(k1_lattice3(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_lattice3)).

fof(f89,plain,(
    ! [X0] :
      ( v2_lattice3(k3_yellow_1(X0))
      | v2_struct_0(k1_lattice3(X0)) ) ),
    inference(subsumption_resolution,[],[f88,f53])).

fof(f53,plain,(
    ! [X0] : v10_lattices(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] : v10_lattices(k1_lattice3(X0)) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v10_lattices(k1_lattice3(X0))
      & v3_lattices(k1_lattice3(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_lattice3)).

fof(f88,plain,(
    ! [X0] :
      ( v2_lattice3(k3_yellow_1(X0))
      | ~ v10_lattices(k1_lattice3(X0))
      | v2_struct_0(k1_lattice3(X0)) ) ),
    inference(subsumption_resolution,[],[f87,f52])).

fof(f52,plain,(
    ! [X0] : l3_lattices(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] : l3_lattices(k1_lattice3(X0)) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l3_lattices(k1_lattice3(X0))
      & v3_lattices(k1_lattice3(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_lattice3)).

fof(f87,plain,(
    ! [X0] :
      ( v2_lattice3(k3_yellow_1(X0))
      | ~ l3_lattices(k1_lattice3(X0))
      | ~ v10_lattices(k1_lattice3(X0))
      | v2_struct_0(k1_lattice3(X0)) ) ),
    inference(superposition,[],[f62,f49])).

fof(f49,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_yellow_1)).

fof(f62,plain,(
    ! [X0] :
      ( v2_lattice3(k3_lattice3(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( v2_lattice3(k3_lattice3(X0))
        & v1_lattice3(k3_lattice3(X0))
        & v5_orders_2(k3_lattice3(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v2_lattice3(k3_lattice3(X0))
        & v1_lattice3(k3_lattice3(X0))
        & v5_orders_2(k3_lattice3(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_lattice3(k3_lattice3(X0))
        & v1_lattice3(k3_lattice3(X0))
        & v5_orders_2(k3_lattice3(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_lattice3(k3_lattice3(X0))
        & v1_lattice3(k3_lattice3(X0))
        & v5_orders_2(k3_lattice3(X0))
        & v1_orders_2(k3_lattice3(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_lattice3(k3_lattice3(X0))
        & v1_lattice3(k3_lattice3(X0))
        & v5_orders_2(k3_lattice3(X0))
        & v3_orders_2(k3_lattice3(X0))
        & v1_orders_2(k3_lattice3(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_lattice3(k3_lattice3(X0))
        & v1_lattice3(k3_lattice3(X0))
        & v5_orders_2(k3_lattice3(X0))
        & v4_orders_2(k3_lattice3(X0))
        & v3_orders_2(k3_lattice3(X0))
        & v1_orders_2(k3_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_yellow_1)).

fof(f132,plain,(
    ! [X4,X5,X3] :
      ( k3_xboole_0(X4,X5) = k12_lattice3(k3_yellow_1(X3),X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(k3_yellow_1(X3)))
      | ~ m1_subset_1(X4,u1_struct_0(k3_yellow_1(X3)))
      | ~ v2_lattice3(k3_yellow_1(X3))
      | ~ v5_orders_2(k3_yellow_1(X3))
      | ~ m1_subset_1(X5,k9_setfam_1(X3))
      | ~ m1_subset_1(X4,k9_setfam_1(X3)) ) ),
    inference(subsumption_resolution,[],[f122,f75])).

fof(f75,plain,(
    ! [X2] : l1_orders_2(k3_yellow_1(X2)) ),
    inference(superposition,[],[f54,f50])).

fof(f54,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(f122,plain,(
    ! [X4,X5,X3] :
      ( k3_xboole_0(X4,X5) = k12_lattice3(k3_yellow_1(X3),X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(k3_yellow_1(X3)))
      | ~ m1_subset_1(X4,u1_struct_0(k3_yellow_1(X3)))
      | ~ l1_orders_2(k3_yellow_1(X3))
      | ~ v2_lattice3(k3_yellow_1(X3))
      | ~ v5_orders_2(k3_yellow_1(X3))
      | ~ m1_subset_1(X5,k9_setfam_1(X3))
      | ~ m1_subset_1(X4,k9_setfam_1(X3)) ) ),
    inference(superposition,[],[f68,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k11_lattice3(k3_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,k9_setfam_1(X0))
      | ~ m1_subset_1(X1,k9_setfam_1(X0)) ) ),
    inference(subsumption_resolution,[],[f101,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k9_setfam_1(X1))
      | ~ m1_subset_1(X0,k9_setfam_1(X1))
      | ~ v1_xboole_0(k9_setfam_1(X1)) ) ),
    inference(resolution,[],[f80,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X0))
      | ~ m1_subset_1(X1,k9_setfam_1(X0))
      | ~ m1_subset_1(X2,k9_setfam_1(X0)) ) ),
    inference(forward_demodulation,[],[f78,f73])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k9_setfam_1(X0))
      | r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X0))
      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(backward_demodulation,[],[f65,f73])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X0))
      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0))
            & r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X0)) )
          | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) )
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
         => ( r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0))
            & r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l19_yellow_1)).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k11_lattice3(k3_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,k9_setfam_1(X0))
      | ~ m1_subset_1(X1,k9_setfam_1(X0))
      | v1_xboole_0(k9_setfam_1(X0)) ) ),
    inference(subsumption_resolution,[],[f100,f80])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k11_lattice3(k3_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,k9_setfam_1(X0))
      | ~ m1_subset_1(X1,k9_setfam_1(X0))
      | ~ r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X0))
      | v1_xboole_0(k9_setfam_1(X0)) ) ),
    inference(superposition,[],[f72,f50])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k11_lattice3(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ r2_hidden(k3_xboole_0(X1,X2),X0)
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f71,f56])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | k3_xboole_0(X1,X2) = k11_lattice3(k2_yellow_1(X0),X1,X2)
      | ~ r2_hidden(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f59,f56])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k11_lattice3(k2_yellow_1(X0),X1,X2)
      | ~ r2_hidden(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k3_xboole_0(X1,X2) = k11_lattice3(k2_yellow_1(X0),X1,X2)
              | ~ r2_hidden(k3_xboole_0(X1,X2),X0)
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k3_xboole_0(X1,X2) = k11_lattice3(k2_yellow_1(X0),X1,X2)
              | ~ r2_hidden(k3_xboole_0(X1,X2),X0)
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r2_hidden(k3_xboole_0(X1,X2),X0)
               => k3_xboole_0(X1,X2) = k11_lattice3(k2_yellow_1(X0),X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_yellow_1)).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

fof(f142,plain,(
    k3_xboole_0(sK1,sK2) != k12_lattice3(k3_yellow_1(sK0),sK1,sK2) ),
    inference(subsumption_resolution,[],[f141,f76])).

fof(f141,plain,
    ( k3_xboole_0(sK1,sK2) != k12_lattice3(k3_yellow_1(sK0),sK1,sK2)
    | ~ m1_subset_1(sK1,k9_setfam_1(sK0)) ),
    inference(subsumption_resolution,[],[f140,f77])).

fof(f140,plain,
    ( k3_xboole_0(sK1,sK2) != k12_lattice3(k3_yellow_1(sK0),sK1,sK2)
    | ~ m1_subset_1(sK2,k9_setfam_1(sK0))
    | ~ m1_subset_1(sK1,k9_setfam_1(sK0)) ),
    inference(trivial_inequality_removal,[],[f139])).

fof(f139,plain,
    ( k2_xboole_0(sK1,sK2) != k2_xboole_0(sK1,sK2)
    | k3_xboole_0(sK1,sK2) != k12_lattice3(k3_yellow_1(sK0),sK1,sK2)
    | ~ m1_subset_1(sK2,k9_setfam_1(sK0))
    | ~ m1_subset_1(sK1,k9_setfam_1(sK0)) ),
    inference(superposition,[],[f48,f120])).

fof(f120,plain,(
    ! [X4,X5,X3] :
      ( k2_xboole_0(X4,X5) = k13_lattice3(k3_yellow_1(X3),X4,X5)
      | ~ m1_subset_1(X5,k9_setfam_1(X3))
      | ~ m1_subset_1(X4,k9_setfam_1(X3)) ) ),
    inference(duplicate_literal_removal,[],[f119])).

fof(f119,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X4,k9_setfam_1(X3))
      | ~ m1_subset_1(X5,k9_setfam_1(X3))
      | k2_xboole_0(X4,X5) = k13_lattice3(k3_yellow_1(X3),X4,X5)
      | ~ m1_subset_1(X4,k9_setfam_1(X3)) ) ),
    inference(forward_demodulation,[],[f118,f73])).

fof(f118,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k9_setfam_1(X3))
      | k2_xboole_0(X4,X5) = k13_lattice3(k3_yellow_1(X3),X4,X5)
      | ~ m1_subset_1(X4,u1_struct_0(k3_yellow_1(X3)))
      | ~ m1_subset_1(X4,k9_setfam_1(X3)) ) ),
    inference(duplicate_literal_removal,[],[f117])).

fof(f117,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k9_setfam_1(X3))
      | k2_xboole_0(X4,X5) = k13_lattice3(k3_yellow_1(X3),X4,X5)
      | ~ m1_subset_1(X4,u1_struct_0(k3_yellow_1(X3)))
      | ~ m1_subset_1(X5,k9_setfam_1(X3))
      | ~ m1_subset_1(X4,k9_setfam_1(X3)) ) ),
    inference(forward_demodulation,[],[f116,f73])).

fof(f116,plain,(
    ! [X4,X5,X3] :
      ( k2_xboole_0(X4,X5) = k13_lattice3(k3_yellow_1(X3),X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(k3_yellow_1(X3)))
      | ~ m1_subset_1(X4,u1_struct_0(k3_yellow_1(X3)))
      | ~ m1_subset_1(X5,k9_setfam_1(X3))
      | ~ m1_subset_1(X4,k9_setfam_1(X3)) ) ),
    inference(subsumption_resolution,[],[f115,f74])).

fof(f115,plain,(
    ! [X4,X5,X3] :
      ( k2_xboole_0(X4,X5) = k13_lattice3(k3_yellow_1(X3),X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(k3_yellow_1(X3)))
      | ~ m1_subset_1(X4,u1_struct_0(k3_yellow_1(X3)))
      | ~ v5_orders_2(k3_yellow_1(X3))
      | ~ m1_subset_1(X5,k9_setfam_1(X3))
      | ~ m1_subset_1(X4,k9_setfam_1(X3)) ) ),
    inference(subsumption_resolution,[],[f114,f86])).

fof(f86,plain,(
    ! [X0] : v1_lattice3(k3_yellow_1(X0)) ),
    inference(subsumption_resolution,[],[f85,f51])).

fof(f85,plain,(
    ! [X0] :
      ( v1_lattice3(k3_yellow_1(X0))
      | v2_struct_0(k1_lattice3(X0)) ) ),
    inference(subsumption_resolution,[],[f84,f53])).

fof(f84,plain,(
    ! [X0] :
      ( v1_lattice3(k3_yellow_1(X0))
      | ~ v10_lattices(k1_lattice3(X0))
      | v2_struct_0(k1_lattice3(X0)) ) ),
    inference(subsumption_resolution,[],[f83,f52])).

fof(f83,plain,(
    ! [X0] :
      ( v1_lattice3(k3_yellow_1(X0))
      | ~ l3_lattices(k1_lattice3(X0))
      | ~ v10_lattices(k1_lattice3(X0))
      | v2_struct_0(k1_lattice3(X0)) ) ),
    inference(superposition,[],[f61,f49])).

fof(f61,plain,(
    ! [X0] :
      ( v1_lattice3(k3_lattice3(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f114,plain,(
    ! [X4,X5,X3] :
      ( k2_xboole_0(X4,X5) = k13_lattice3(k3_yellow_1(X3),X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(k3_yellow_1(X3)))
      | ~ m1_subset_1(X4,u1_struct_0(k3_yellow_1(X3)))
      | ~ v1_lattice3(k3_yellow_1(X3))
      | ~ v5_orders_2(k3_yellow_1(X3))
      | ~ m1_subset_1(X5,k9_setfam_1(X3))
      | ~ m1_subset_1(X4,k9_setfam_1(X3)) ) ),
    inference(subsumption_resolution,[],[f104,f75])).

fof(f104,plain,(
    ! [X4,X5,X3] :
      ( k2_xboole_0(X4,X5) = k13_lattice3(k3_yellow_1(X3),X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(k3_yellow_1(X3)))
      | ~ m1_subset_1(X4,u1_struct_0(k3_yellow_1(X3)))
      | ~ l1_orders_2(k3_yellow_1(X3))
      | ~ v1_lattice3(k3_yellow_1(X3))
      | ~ v5_orders_2(k3_yellow_1(X3))
      | ~ m1_subset_1(X5,k9_setfam_1(X3))
      | ~ m1_subset_1(X4,k9_setfam_1(X3)) ) ),
    inference(superposition,[],[f67,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k10_lattice3(k3_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,k9_setfam_1(X0))
      | ~ m1_subset_1(X1,k9_setfam_1(X0)) ) ),
    inference(subsumption_resolution,[],[f98,f91])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k10_lattice3(k3_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,k9_setfam_1(X0))
      | ~ m1_subset_1(X1,k9_setfam_1(X0))
      | v1_xboole_0(k9_setfam_1(X0)) ) ),
    inference(subsumption_resolution,[],[f97,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0))
      | ~ m1_subset_1(X1,k9_setfam_1(X0))
      | ~ m1_subset_1(X2,k9_setfam_1(X0)) ) ),
    inference(forward_demodulation,[],[f79,f73])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k9_setfam_1(X0))
      | r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0))
      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(backward_demodulation,[],[f66,f73])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0))
      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k10_lattice3(k3_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,k9_setfam_1(X0))
      | ~ m1_subset_1(X1,k9_setfam_1(X0))
      | ~ r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0))
      | v1_xboole_0(k9_setfam_1(X0)) ) ),
    inference(superposition,[],[f70,f50])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k10_lattice3(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ r2_hidden(k2_xboole_0(X1,X2),X0)
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f69,f56])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | k2_xboole_0(X1,X2) = k10_lattice3(k2_yellow_1(X0),X1,X2)
      | ~ r2_hidden(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f58,f56])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k10_lattice3(k2_yellow_1(X0),X1,X2)
      | ~ r2_hidden(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_xboole_0(X1,X2) = k10_lattice3(k2_yellow_1(X0),X1,X2)
              | ~ r2_hidden(k2_xboole_0(X1,X2),X0)
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_xboole_0(X1,X2) = k10_lattice3(k2_yellow_1(X0),X1,X2)
              | ~ r2_hidden(k2_xboole_0(X1,X2),X0)
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r2_hidden(k2_xboole_0(X1,X2),X0)
               => k2_xboole_0(X1,X2) = k10_lattice3(k2_yellow_1(X0),X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_yellow_1)).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

fof(f48,plain,
    ( k2_xboole_0(sK1,sK2) != k13_lattice3(k3_yellow_1(sK0),sK1,sK2)
    | k3_xboole_0(sK1,sK2) != k12_lattice3(k3_yellow_1(sK0),sK1,sK2) ),
    inference(cnf_transformation,[],[f45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:17:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (25271)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.47  % (25285)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.47  % (25272)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.47  % (25273)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.47  % (25273)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % (25284)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.48  % (25280)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.48  % (25281)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.48  % (25279)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.48  % (25278)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.48  % (25276)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.48  % (25281)Refutation not found, incomplete strategy% (25281)------------------------------
% 0.22/0.48  % (25281)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f148,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(subsumption_resolution,[],[f147,f76])).
% 0.22/0.48  fof(f76,plain,(
% 0.22/0.48    m1_subset_1(sK1,k9_setfam_1(sK0))),
% 0.22/0.48    inference(backward_demodulation,[],[f46,f73])).
% 0.22/0.48  fof(f73,plain,(
% 0.22/0.48    ( ! [X0] : (u1_struct_0(k3_yellow_1(X0)) = k9_setfam_1(X0)) )),
% 0.22/0.48    inference(superposition,[],[f56,f50])).
% 0.22/0.48  fof(f50,plain,(
% 0.22/0.48    ( ! [X0] : (k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f14])).
% 0.22/0.48  fof(f14,axiom,(
% 0.22/0.48    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).
% 0.22/0.48  fof(f56,plain,(
% 0.22/0.48    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f13])).
% 0.22/0.48  fof(f13,axiom,(
% 0.22/0.48    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0)))),
% 0.22/0.48    inference(cnf_transformation,[],[f45])).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    ((k3_xboole_0(sK1,sK2) != k12_lattice3(k3_yellow_1(sK0),sK1,sK2) | k2_xboole_0(sK1,sK2) != k13_lattice3(k3_yellow_1(sK0),sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK0)))) & m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0)))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f44,f43])).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    ? [X0,X1] : (? [X2] : ((k3_xboole_0(X1,X2) != k12_lattice3(k3_yellow_1(X0),X1,X2) | k2_xboole_0(X1,X2) != k13_lattice3(k3_yellow_1(X0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))) => (? [X2] : ((k3_xboole_0(sK1,X2) != k12_lattice3(k3_yellow_1(sK0),sK1,X2) | k2_xboole_0(sK1,X2) != k13_lattice3(k3_yellow_1(sK0),sK1,X2)) & m1_subset_1(X2,u1_struct_0(k3_yellow_1(sK0)))) & m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0))))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    ? [X2] : ((k3_xboole_0(sK1,X2) != k12_lattice3(k3_yellow_1(sK0),sK1,X2) | k2_xboole_0(sK1,X2) != k13_lattice3(k3_yellow_1(sK0),sK1,X2)) & m1_subset_1(X2,u1_struct_0(k3_yellow_1(sK0)))) => ((k3_xboole_0(sK1,sK2) != k12_lattice3(k3_yellow_1(sK0),sK1,sK2) | k2_xboole_0(sK1,sK2) != k13_lattice3(k3_yellow_1(sK0),sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK0))))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    ? [X0,X1] : (? [X2] : ((k3_xboole_0(X1,X2) != k12_lattice3(k3_yellow_1(X0),X1,X2) | k2_xboole_0(X1,X2) != k13_lattice3(k3_yellow_1(X0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))))),
% 0.22/0.48    inference(ennf_transformation,[],[f18])).
% 0.22/0.48  fof(f18,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1] : (m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) => (k3_xboole_0(X1,X2) = k12_lattice3(k3_yellow_1(X0),X1,X2) & k2_xboole_0(X1,X2) = k13_lattice3(k3_yellow_1(X0),X1,X2))))),
% 0.22/0.48    inference(negated_conjecture,[],[f17])).
% 0.22/0.48  fof(f17,conjecture,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) => (k3_xboole_0(X1,X2) = k12_lattice3(k3_yellow_1(X0),X1,X2) & k2_xboole_0(X1,X2) = k13_lattice3(k3_yellow_1(X0),X1,X2))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_yellow_1)).
% 0.22/0.48  fof(f147,plain,(
% 0.22/0.48    ~m1_subset_1(sK1,k9_setfam_1(sK0))),
% 0.22/0.48    inference(subsumption_resolution,[],[f146,f77])).
% 0.22/0.48  fof(f77,plain,(
% 0.22/0.48    m1_subset_1(sK2,k9_setfam_1(sK0))),
% 0.22/0.48    inference(backward_demodulation,[],[f47,f73])).
% 0.22/0.48  fof(f47,plain,(
% 0.22/0.48    m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK0)))),
% 0.22/0.48    inference(cnf_transformation,[],[f45])).
% 0.22/0.48  fof(f146,plain,(
% 0.22/0.48    ~m1_subset_1(sK2,k9_setfam_1(sK0)) | ~m1_subset_1(sK1,k9_setfam_1(sK0))),
% 0.22/0.48    inference(trivial_inequality_removal,[],[f145])).
% 0.22/0.48  fof(f145,plain,(
% 0.22/0.48    k3_xboole_0(sK1,sK2) != k3_xboole_0(sK1,sK2) | ~m1_subset_1(sK2,k9_setfam_1(sK0)) | ~m1_subset_1(sK1,k9_setfam_1(sK0))),
% 0.22/0.48    inference(superposition,[],[f142,f138])).
% 0.22/0.48  fof(f138,plain,(
% 0.22/0.48    ( ! [X4,X5,X3] : (k3_xboole_0(X4,X5) = k12_lattice3(k3_yellow_1(X3),X4,X5) | ~m1_subset_1(X5,k9_setfam_1(X3)) | ~m1_subset_1(X4,k9_setfam_1(X3))) )),
% 0.22/0.48    inference(duplicate_literal_removal,[],[f137])).
% 0.22/0.48  fof(f137,plain,(
% 0.22/0.48    ( ! [X4,X5,X3] : (~m1_subset_1(X4,k9_setfam_1(X3)) | ~m1_subset_1(X5,k9_setfam_1(X3)) | k3_xboole_0(X4,X5) = k12_lattice3(k3_yellow_1(X3),X4,X5) | ~m1_subset_1(X4,k9_setfam_1(X3))) )),
% 0.22/0.48    inference(forward_demodulation,[],[f136,f73])).
% 0.22/0.48  fof(f136,plain,(
% 0.22/0.48    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k9_setfam_1(X3)) | k3_xboole_0(X4,X5) = k12_lattice3(k3_yellow_1(X3),X4,X5) | ~m1_subset_1(X4,u1_struct_0(k3_yellow_1(X3))) | ~m1_subset_1(X4,k9_setfam_1(X3))) )),
% 0.22/0.48    inference(duplicate_literal_removal,[],[f135])).
% 0.22/0.48  fof(f135,plain,(
% 0.22/0.48    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k9_setfam_1(X3)) | k3_xboole_0(X4,X5) = k12_lattice3(k3_yellow_1(X3),X4,X5) | ~m1_subset_1(X4,u1_struct_0(k3_yellow_1(X3))) | ~m1_subset_1(X5,k9_setfam_1(X3)) | ~m1_subset_1(X4,k9_setfam_1(X3))) )),
% 0.22/0.48    inference(forward_demodulation,[],[f134,f73])).
% 0.22/0.48  fof(f134,plain,(
% 0.22/0.48    ( ! [X4,X5,X3] : (k3_xboole_0(X4,X5) = k12_lattice3(k3_yellow_1(X3),X4,X5) | ~m1_subset_1(X5,u1_struct_0(k3_yellow_1(X3))) | ~m1_subset_1(X4,u1_struct_0(k3_yellow_1(X3))) | ~m1_subset_1(X5,k9_setfam_1(X3)) | ~m1_subset_1(X4,k9_setfam_1(X3))) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f133,f74])).
% 0.22/0.48  fof(f74,plain,(
% 0.22/0.48    ( ! [X1] : (v5_orders_2(k3_yellow_1(X1))) )),
% 0.22/0.48    inference(superposition,[],[f55,f50])).
% 0.22/0.48  fof(f55,plain,(
% 0.22/0.48    ( ! [X0] : (v5_orders_2(k2_yellow_1(X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f26])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ! [X0] : v5_orders_2(k2_yellow_1(X0))),
% 0.22/0.48    inference(pure_predicate_removal,[],[f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.22/0.48    inference(pure_predicate_removal,[],[f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.22/0.48    inference(pure_predicate_removal,[],[f11])).
% 0.22/0.48  fof(f11,axiom,(
% 0.22/0.48    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).
% 0.22/0.48  fof(f133,plain,(
% 0.22/0.48    ( ! [X4,X5,X3] : (k3_xboole_0(X4,X5) = k12_lattice3(k3_yellow_1(X3),X4,X5) | ~m1_subset_1(X5,u1_struct_0(k3_yellow_1(X3))) | ~m1_subset_1(X4,u1_struct_0(k3_yellow_1(X3))) | ~v5_orders_2(k3_yellow_1(X3)) | ~m1_subset_1(X5,k9_setfam_1(X3)) | ~m1_subset_1(X4,k9_setfam_1(X3))) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f132,f90])).
% 0.22/0.48  fof(f90,plain,(
% 0.22/0.48    ( ! [X0] : (v2_lattice3(k3_yellow_1(X0))) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f89,f51])).
% 0.22/0.48  fof(f51,plain,(
% 0.22/0.48    ( ! [X0] : (~v2_struct_0(k1_lattice3(X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f27])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ! [X0] : ~v2_struct_0(k1_lattice3(X0))),
% 0.22/0.48    inference(pure_predicate_removal,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0] : (v3_lattices(k1_lattice3(X0)) & ~v2_struct_0(k1_lattice3(X0)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_lattice3)).
% 0.22/0.48  fof(f89,plain,(
% 0.22/0.48    ( ! [X0] : (v2_lattice3(k3_yellow_1(X0)) | v2_struct_0(k1_lattice3(X0))) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f88,f53])).
% 0.22/0.48  fof(f53,plain,(
% 0.22/0.48    ( ! [X0] : (v10_lattices(k1_lattice3(X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f28])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ! [X0] : v10_lattices(k1_lattice3(X0))),
% 0.22/0.48    inference(pure_predicate_removal,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0] : (v10_lattices(k1_lattice3(X0)) & v3_lattices(k1_lattice3(X0)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_lattice3)).
% 0.22/0.48  fof(f88,plain,(
% 0.22/0.48    ( ! [X0] : (v2_lattice3(k3_yellow_1(X0)) | ~v10_lattices(k1_lattice3(X0)) | v2_struct_0(k1_lattice3(X0))) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f87,f52])).
% 0.22/0.48  fof(f52,plain,(
% 0.22/0.48    ( ! [X0] : (l3_lattices(k1_lattice3(X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f29])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    ! [X0] : l3_lattices(k1_lattice3(X0))),
% 0.22/0.48    inference(pure_predicate_removal,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0] : (l3_lattices(k1_lattice3(X0)) & v3_lattices(k1_lattice3(X0)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_lattice3)).
% 0.22/0.48  fof(f87,plain,(
% 0.22/0.48    ( ! [X0] : (v2_lattice3(k3_yellow_1(X0)) | ~l3_lattices(k1_lattice3(X0)) | ~v10_lattices(k1_lattice3(X0)) | v2_struct_0(k1_lattice3(X0))) )),
% 0.22/0.48    inference(superposition,[],[f62,f49])).
% 0.22/0.48  fof(f49,plain,(
% 0.22/0.48    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,axiom,(
% 0.22/0.48    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_yellow_1)).
% 0.22/0.48  fof(f62,plain,(
% 0.22/0.48    ( ! [X0] : (v2_lattice3(k3_lattice3(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f36])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    ! [X0] : ((v2_lattice3(k3_lattice3(X0)) & v1_lattice3(k3_lattice3(X0)) & v5_orders_2(k3_lattice3(X0))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f35])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    ! [X0] : ((v2_lattice3(k3_lattice3(X0)) & v1_lattice3(k3_lattice3(X0)) & v5_orders_2(k3_lattice3(X0))) | (~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f24])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (v2_lattice3(k3_lattice3(X0)) & v1_lattice3(k3_lattice3(X0)) & v5_orders_2(k3_lattice3(X0))))),
% 0.22/0.48    inference(pure_predicate_removal,[],[f23])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (v2_lattice3(k3_lattice3(X0)) & v1_lattice3(k3_lattice3(X0)) & v5_orders_2(k3_lattice3(X0)) & v1_orders_2(k3_lattice3(X0))))),
% 0.22/0.48    inference(pure_predicate_removal,[],[f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (v2_lattice3(k3_lattice3(X0)) & v1_lattice3(k3_lattice3(X0)) & v5_orders_2(k3_lattice3(X0)) & v3_orders_2(k3_lattice3(X0)) & v1_orders_2(k3_lattice3(X0))))),
% 0.22/0.48    inference(pure_predicate_removal,[],[f10])).
% 0.22/0.48  fof(f10,axiom,(
% 0.22/0.48    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (v2_lattice3(k3_lattice3(X0)) & v1_lattice3(k3_lattice3(X0)) & v5_orders_2(k3_lattice3(X0)) & v4_orders_2(k3_lattice3(X0)) & v3_orders_2(k3_lattice3(X0)) & v1_orders_2(k3_lattice3(X0))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_yellow_1)).
% 0.22/0.48  fof(f132,plain,(
% 0.22/0.48    ( ! [X4,X5,X3] : (k3_xboole_0(X4,X5) = k12_lattice3(k3_yellow_1(X3),X4,X5) | ~m1_subset_1(X5,u1_struct_0(k3_yellow_1(X3))) | ~m1_subset_1(X4,u1_struct_0(k3_yellow_1(X3))) | ~v2_lattice3(k3_yellow_1(X3)) | ~v5_orders_2(k3_yellow_1(X3)) | ~m1_subset_1(X5,k9_setfam_1(X3)) | ~m1_subset_1(X4,k9_setfam_1(X3))) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f122,f75])).
% 0.22/0.48  fof(f75,plain,(
% 0.22/0.48    ( ! [X2] : (l1_orders_2(k3_yellow_1(X2))) )),
% 0.22/0.48    inference(superposition,[],[f54,f50])).
% 0.22/0.48  fof(f54,plain,(
% 0.22/0.48    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f25])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ! [X0] : l1_orders_2(k2_yellow_1(X0))),
% 0.22/0.48    inference(pure_predicate_removal,[],[f9])).
% 0.22/0.48  fof(f9,axiom,(
% 0.22/0.48    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).
% 0.22/0.48  fof(f122,plain,(
% 0.22/0.48    ( ! [X4,X5,X3] : (k3_xboole_0(X4,X5) = k12_lattice3(k3_yellow_1(X3),X4,X5) | ~m1_subset_1(X5,u1_struct_0(k3_yellow_1(X3))) | ~m1_subset_1(X4,u1_struct_0(k3_yellow_1(X3))) | ~l1_orders_2(k3_yellow_1(X3)) | ~v2_lattice3(k3_yellow_1(X3)) | ~v5_orders_2(k3_yellow_1(X3)) | ~m1_subset_1(X5,k9_setfam_1(X3)) | ~m1_subset_1(X4,k9_setfam_1(X3))) )),
% 0.22/0.48    inference(superposition,[],[f68,f102])).
% 0.22/0.48  fof(f102,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k11_lattice3(k3_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,k9_setfam_1(X0)) | ~m1_subset_1(X1,k9_setfam_1(X0))) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f101,f91])).
% 0.22/0.48  fof(f91,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k9_setfam_1(X1)) | ~m1_subset_1(X0,k9_setfam_1(X1)) | ~v1_xboole_0(k9_setfam_1(X1))) )),
% 0.22/0.48    inference(resolution,[],[f80,f63])).
% 0.22/0.48  fof(f63,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f37])).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f19])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.48    inference(unused_predicate_definition_removal,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.48  fof(f80,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X0)) | ~m1_subset_1(X1,k9_setfam_1(X0)) | ~m1_subset_1(X2,k9_setfam_1(X0))) )),
% 0.22/0.48    inference(forward_demodulation,[],[f78,f73])).
% 0.22/0.48  fof(f78,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k9_setfam_1(X0)) | r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X0)) | ~m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))) )),
% 0.22/0.48    inference(backward_demodulation,[],[f65,f73])).
% 0.22/0.48  fof(f65,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X0)) | ~m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f38])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    ! [X0,X1] : (! [X2] : ((r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0)) & r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X0))) | ~m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))))),
% 0.22/0.48    inference(ennf_transformation,[],[f12])).
% 0.22/0.48  fof(f12,axiom,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) => (r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0)) & r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X0)))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l19_yellow_1)).
% 0.22/0.48  fof(f101,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k11_lattice3(k3_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,k9_setfam_1(X0)) | ~m1_subset_1(X1,k9_setfam_1(X0)) | v1_xboole_0(k9_setfam_1(X0))) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f100,f80])).
% 0.22/0.48  fof(f100,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k11_lattice3(k3_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,k9_setfam_1(X0)) | ~m1_subset_1(X1,k9_setfam_1(X0)) | ~r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X0)) | v1_xboole_0(k9_setfam_1(X0))) )),
% 0.22/0.48    inference(superposition,[],[f72,f50])).
% 0.22/0.48  fof(f72,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k11_lattice3(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | ~r2_hidden(k3_xboole_0(X1,X2),X0) | v1_xboole_0(X0)) )),
% 0.22/0.48    inference(forward_demodulation,[],[f71,f56])).
% 0.22/0.48  fof(f71,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | k3_xboole_0(X1,X2) = k11_lattice3(k2_yellow_1(X0),X1,X2) | ~r2_hidden(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.22/0.48    inference(forward_demodulation,[],[f59,f56])).
% 0.22/0.48  fof(f59,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k11_lattice3(k2_yellow_1(X0),X1,X2) | ~r2_hidden(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f34])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : (k3_xboole_0(X1,X2) = k11_lattice3(k2_yellow_1(X0),X1,X2) | ~r2_hidden(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.22/0.48    inference(flattening,[],[f33])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : ((k3_xboole_0(X1,X2) = k11_lattice3(k2_yellow_1(X0),X1,X2) | ~r2_hidden(k3_xboole_0(X1,X2),X0)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f16])).
% 0.22/0.48  fof(f16,axiom,(
% 0.22/0.48    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r2_hidden(k3_xboole_0(X1,X2),X0) => k3_xboole_0(X1,X2) = k11_lattice3(k2_yellow_1(X0),X1,X2)))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_yellow_1)).
% 0.22/0.48  fof(f68,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f42])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 0.22/0.48    inference(flattening,[],[f41])).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k12_lattice3)).
% 0.22/0.48  fof(f142,plain,(
% 0.22/0.48    k3_xboole_0(sK1,sK2) != k12_lattice3(k3_yellow_1(sK0),sK1,sK2)),
% 0.22/0.48    inference(subsumption_resolution,[],[f141,f76])).
% 0.22/0.48  fof(f141,plain,(
% 0.22/0.48    k3_xboole_0(sK1,sK2) != k12_lattice3(k3_yellow_1(sK0),sK1,sK2) | ~m1_subset_1(sK1,k9_setfam_1(sK0))),
% 0.22/0.48    inference(subsumption_resolution,[],[f140,f77])).
% 0.22/0.48  fof(f140,plain,(
% 0.22/0.48    k3_xboole_0(sK1,sK2) != k12_lattice3(k3_yellow_1(sK0),sK1,sK2) | ~m1_subset_1(sK2,k9_setfam_1(sK0)) | ~m1_subset_1(sK1,k9_setfam_1(sK0))),
% 0.22/0.48    inference(trivial_inequality_removal,[],[f139])).
% 0.22/0.48  fof(f139,plain,(
% 0.22/0.48    k2_xboole_0(sK1,sK2) != k2_xboole_0(sK1,sK2) | k3_xboole_0(sK1,sK2) != k12_lattice3(k3_yellow_1(sK0),sK1,sK2) | ~m1_subset_1(sK2,k9_setfam_1(sK0)) | ~m1_subset_1(sK1,k9_setfam_1(sK0))),
% 0.22/0.48    inference(superposition,[],[f48,f120])).
% 0.22/0.48  fof(f120,plain,(
% 0.22/0.48    ( ! [X4,X5,X3] : (k2_xboole_0(X4,X5) = k13_lattice3(k3_yellow_1(X3),X4,X5) | ~m1_subset_1(X5,k9_setfam_1(X3)) | ~m1_subset_1(X4,k9_setfam_1(X3))) )),
% 0.22/0.48    inference(duplicate_literal_removal,[],[f119])).
% 0.22/0.48  fof(f119,plain,(
% 0.22/0.48    ( ! [X4,X5,X3] : (~m1_subset_1(X4,k9_setfam_1(X3)) | ~m1_subset_1(X5,k9_setfam_1(X3)) | k2_xboole_0(X4,X5) = k13_lattice3(k3_yellow_1(X3),X4,X5) | ~m1_subset_1(X4,k9_setfam_1(X3))) )),
% 0.22/0.48    inference(forward_demodulation,[],[f118,f73])).
% 0.22/0.48  fof(f118,plain,(
% 0.22/0.48    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k9_setfam_1(X3)) | k2_xboole_0(X4,X5) = k13_lattice3(k3_yellow_1(X3),X4,X5) | ~m1_subset_1(X4,u1_struct_0(k3_yellow_1(X3))) | ~m1_subset_1(X4,k9_setfam_1(X3))) )),
% 0.22/0.48    inference(duplicate_literal_removal,[],[f117])).
% 0.22/0.48  fof(f117,plain,(
% 0.22/0.48    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k9_setfam_1(X3)) | k2_xboole_0(X4,X5) = k13_lattice3(k3_yellow_1(X3),X4,X5) | ~m1_subset_1(X4,u1_struct_0(k3_yellow_1(X3))) | ~m1_subset_1(X5,k9_setfam_1(X3)) | ~m1_subset_1(X4,k9_setfam_1(X3))) )),
% 0.22/0.48    inference(forward_demodulation,[],[f116,f73])).
% 0.22/0.48  fof(f116,plain,(
% 0.22/0.48    ( ! [X4,X5,X3] : (k2_xboole_0(X4,X5) = k13_lattice3(k3_yellow_1(X3),X4,X5) | ~m1_subset_1(X5,u1_struct_0(k3_yellow_1(X3))) | ~m1_subset_1(X4,u1_struct_0(k3_yellow_1(X3))) | ~m1_subset_1(X5,k9_setfam_1(X3)) | ~m1_subset_1(X4,k9_setfam_1(X3))) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f115,f74])).
% 0.22/0.48  fof(f115,plain,(
% 0.22/0.48    ( ! [X4,X5,X3] : (k2_xboole_0(X4,X5) = k13_lattice3(k3_yellow_1(X3),X4,X5) | ~m1_subset_1(X5,u1_struct_0(k3_yellow_1(X3))) | ~m1_subset_1(X4,u1_struct_0(k3_yellow_1(X3))) | ~v5_orders_2(k3_yellow_1(X3)) | ~m1_subset_1(X5,k9_setfam_1(X3)) | ~m1_subset_1(X4,k9_setfam_1(X3))) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f114,f86])).
% 0.22/0.48  fof(f86,plain,(
% 0.22/0.48    ( ! [X0] : (v1_lattice3(k3_yellow_1(X0))) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f85,f51])).
% 0.22/0.48  fof(f85,plain,(
% 0.22/0.48    ( ! [X0] : (v1_lattice3(k3_yellow_1(X0)) | v2_struct_0(k1_lattice3(X0))) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f84,f53])).
% 0.22/0.48  fof(f84,plain,(
% 0.22/0.48    ( ! [X0] : (v1_lattice3(k3_yellow_1(X0)) | ~v10_lattices(k1_lattice3(X0)) | v2_struct_0(k1_lattice3(X0))) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f83,f52])).
% 0.22/0.48  fof(f83,plain,(
% 0.22/0.48    ( ! [X0] : (v1_lattice3(k3_yellow_1(X0)) | ~l3_lattices(k1_lattice3(X0)) | ~v10_lattices(k1_lattice3(X0)) | v2_struct_0(k1_lattice3(X0))) )),
% 0.22/0.48    inference(superposition,[],[f61,f49])).
% 0.22/0.48  fof(f61,plain,(
% 0.22/0.48    ( ! [X0] : (v1_lattice3(k3_lattice3(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f36])).
% 0.22/0.48  fof(f114,plain,(
% 0.22/0.48    ( ! [X4,X5,X3] : (k2_xboole_0(X4,X5) = k13_lattice3(k3_yellow_1(X3),X4,X5) | ~m1_subset_1(X5,u1_struct_0(k3_yellow_1(X3))) | ~m1_subset_1(X4,u1_struct_0(k3_yellow_1(X3))) | ~v1_lattice3(k3_yellow_1(X3)) | ~v5_orders_2(k3_yellow_1(X3)) | ~m1_subset_1(X5,k9_setfam_1(X3)) | ~m1_subset_1(X4,k9_setfam_1(X3))) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f104,f75])).
% 0.22/0.48  fof(f104,plain,(
% 0.22/0.48    ( ! [X4,X5,X3] : (k2_xboole_0(X4,X5) = k13_lattice3(k3_yellow_1(X3),X4,X5) | ~m1_subset_1(X5,u1_struct_0(k3_yellow_1(X3))) | ~m1_subset_1(X4,u1_struct_0(k3_yellow_1(X3))) | ~l1_orders_2(k3_yellow_1(X3)) | ~v1_lattice3(k3_yellow_1(X3)) | ~v5_orders_2(k3_yellow_1(X3)) | ~m1_subset_1(X5,k9_setfam_1(X3)) | ~m1_subset_1(X4,k9_setfam_1(X3))) )),
% 0.22/0.48    inference(superposition,[],[f67,f99])).
% 0.22/0.48  fof(f99,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k10_lattice3(k3_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,k9_setfam_1(X0)) | ~m1_subset_1(X1,k9_setfam_1(X0))) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f98,f91])).
% 0.22/0.48  fof(f98,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k10_lattice3(k3_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,k9_setfam_1(X0)) | ~m1_subset_1(X1,k9_setfam_1(X0)) | v1_xboole_0(k9_setfam_1(X0))) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f97,f81])).
% 0.22/0.48  fof(f81,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0)) | ~m1_subset_1(X1,k9_setfam_1(X0)) | ~m1_subset_1(X2,k9_setfam_1(X0))) )),
% 0.22/0.48    inference(forward_demodulation,[],[f79,f73])).
% 0.22/0.48  fof(f79,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k9_setfam_1(X0)) | r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0)) | ~m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))) )),
% 0.22/0.48    inference(backward_demodulation,[],[f66,f73])).
% 0.22/0.48  fof(f66,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0)) | ~m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f38])).
% 0.22/0.48  fof(f97,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k10_lattice3(k3_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,k9_setfam_1(X0)) | ~m1_subset_1(X1,k9_setfam_1(X0)) | ~r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0)) | v1_xboole_0(k9_setfam_1(X0))) )),
% 0.22/0.48    inference(superposition,[],[f70,f50])).
% 0.22/0.48  fof(f70,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k10_lattice3(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | ~r2_hidden(k2_xboole_0(X1,X2),X0) | v1_xboole_0(X0)) )),
% 0.22/0.48    inference(forward_demodulation,[],[f69,f56])).
% 0.22/0.48  fof(f69,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | k2_xboole_0(X1,X2) = k10_lattice3(k2_yellow_1(X0),X1,X2) | ~r2_hidden(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.22/0.48    inference(forward_demodulation,[],[f58,f56])).
% 0.22/0.48  fof(f58,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k10_lattice3(k2_yellow_1(X0),X1,X2) | ~r2_hidden(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f32])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : (k2_xboole_0(X1,X2) = k10_lattice3(k2_yellow_1(X0),X1,X2) | ~r2_hidden(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.22/0.48    inference(flattening,[],[f31])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : ((k2_xboole_0(X1,X2) = k10_lattice3(k2_yellow_1(X0),X1,X2) | ~r2_hidden(k2_xboole_0(X1,X2),X0)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f15])).
% 0.22/0.48  fof(f15,axiom,(
% 0.22/0.48    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r2_hidden(k2_xboole_0(X1,X2),X0) => k2_xboole_0(X1,X2) = k10_lattice3(k2_yellow_1(X0),X1,X2)))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_yellow_1)).
% 0.22/0.48  fof(f67,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f40])).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 0.22/0.48    inference(flattening,[],[f39])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k13_lattice3)).
% 0.22/0.48  fof(f48,plain,(
% 0.22/0.48    k2_xboole_0(sK1,sK2) != k13_lattice3(k3_yellow_1(sK0),sK1,sK2) | k3_xboole_0(sK1,sK2) != k12_lattice3(k3_yellow_1(sK0),sK1,sK2)),
% 0.22/0.48    inference(cnf_transformation,[],[f45])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (25273)------------------------------
% 0.22/0.48  % (25273)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (25273)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (25273)Memory used [KB]: 1663
% 0.22/0.48  % (25273)Time elapsed: 0.063 s
% 0.22/0.48  % (25273)------------------------------
% 0.22/0.48  % (25273)------------------------------
% 0.22/0.49  % (25266)Success in time 0.126 s
%------------------------------------------------------------------------------
