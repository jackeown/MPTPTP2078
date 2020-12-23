%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1960+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:58 EST 2020

% Result     : Theorem 0.14s
% Output     : Refutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 399 expanded)
%              Number of leaves         :   23 ( 110 expanded)
%              Depth                    :   34
%              Number of atoms          :  530 (1165 expanded)
%              Number of equality atoms :  128 ( 266 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f250,plain,(
    $false ),
    inference(subsumption_resolution,[],[f249,f55])).

fof(f55,plain,(
    k6_subset_1(sK1,sK2) != k7_waybel_1(k3_yellow_1(sK1),sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,
    ( k6_subset_1(sK1,sK2) != k7_waybel_1(k3_yellow_1(sK1),sK2)
    & m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f30,f47])).

fof(f47,plain,
    ( ? [X0,X1] :
        ( k6_subset_1(X0,X1) != k7_waybel_1(k3_yellow_1(X0),X1)
        & m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) )
   => ( k6_subset_1(sK1,sK2) != k7_waybel_1(k3_yellow_1(sK1),sK2)
      & m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ? [X0,X1] :
      ( k6_subset_1(X0,X1) != k7_waybel_1(k3_yellow_1(X0),X1)
      & m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
       => k6_subset_1(X0,X1) = k7_waybel_1(k3_yellow_1(X0),X1) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
     => k6_subset_1(X0,X1) = k7_waybel_1(k3_yellow_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_waybel_7)).

fof(f249,plain,(
    k6_subset_1(sK1,sK2) = k7_waybel_1(k3_yellow_1(sK1),sK2) ),
    inference(subsumption_resolution,[],[f248,f112])).

fof(f112,plain,(
    ! [X2,X3] : k1_xboole_0 = k3_xboole_0(X2,k6_subset_1(X3,X2)) ),
    inference(resolution,[],[f85,f99])).

fof(f99,plain,(
    ! [X0,X1] : r1_xboole_0(X0,k6_subset_1(X1,X0)) ),
    inference(resolution,[],[f82,f93])).

fof(f93,plain,(
    ! [X0,X1] : r1_xboole_0(k6_subset_1(X0,X1),X1) ),
    inference(backward_demodulation,[],[f78,f80])).

fof(f80,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f78,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f248,plain,
    ( k1_xboole_0 != k3_xboole_0(sK2,k6_subset_1(sK1,sK2))
    | k6_subset_1(sK1,sK2) = k7_waybel_1(k3_yellow_1(sK1),sK2) ),
    inference(trivial_inequality_removal,[],[f247])).

fof(f247,plain,
    ( sK1 != sK1
    | k1_xboole_0 != k3_xboole_0(sK2,k6_subset_1(sK1,sK2))
    | k6_subset_1(sK1,sK2) = k7_waybel_1(k3_yellow_1(sK1),sK2) ),
    inference(superposition,[],[f245,f117])).

fof(f117,plain,(
    sK1 = k2_xboole_0(sK2,k6_subset_1(sK1,sK2)) ),
    inference(resolution,[],[f94,f101])).

fof(f101,plain,(
    r1_tarski(sK2,sK1) ),
    inference(resolution,[],[f87,f92])).

fof(f92,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(backward_demodulation,[],[f54,f91])).

fof(f91,plain,(
    ! [X0] : k1_zfmisc_1(X0) = u1_struct_0(k3_yellow_1(X0)) ),
    inference(forward_demodulation,[],[f59,f57])).

fof(f57,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(f59,plain,(
    ! [X0] : k9_setfam_1(X0) = u1_struct_0(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : k9_setfam_1(X0) = u1_struct_0(k3_yellow_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_waybel_7)).

fof(f54,plain,(
    m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK1))) ),
    inference(cnf_transformation,[],[f48])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,k6_subset_1(X1,X0)) = X1 ) ),
    inference(forward_demodulation,[],[f81,f80])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

fof(f245,plain,(
    ! [X0] :
      ( sK1 != k2_xboole_0(sK2,k6_subset_1(sK1,X0))
      | k1_xboole_0 != k3_xboole_0(sK2,k6_subset_1(sK1,X0))
      | k7_waybel_1(k3_yellow_1(sK1),sK2) = k6_subset_1(sK1,X0) ) ),
    inference(resolution,[],[f243,f193])).

fof(f193,plain,(
    ! [X0] :
      ( r6_waybel_1(k3_yellow_1(sK1),sK2,k6_subset_1(sK1,X0))
      | k1_xboole_0 != k3_xboole_0(sK2,k6_subset_1(sK1,X0))
      | sK1 != k2_xboole_0(sK2,k6_subset_1(sK1,X0)) ) ),
    inference(subsumption_resolution,[],[f192,f92])).

fof(f192,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
      | sK1 != k2_xboole_0(sK2,k6_subset_1(sK1,X0))
      | k1_xboole_0 != k3_xboole_0(sK2,k6_subset_1(sK1,X0))
      | r6_waybel_1(k3_yellow_1(sK1),sK2,k6_subset_1(sK1,X0)) ) ),
    inference(forward_demodulation,[],[f191,f91])).

fof(f191,plain,(
    ! [X0] :
      ( sK1 != k2_xboole_0(sK2,k6_subset_1(sK1,X0))
      | k1_xboole_0 != k3_xboole_0(sK2,k6_subset_1(sK1,X0))
      | r6_waybel_1(k3_yellow_1(sK1),sK2,k6_subset_1(sK1,X0))
      | ~ m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK1))) ) ),
    inference(subsumption_resolution,[],[f190,f79])).

fof(f79,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(f190,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k6_subset_1(sK1,X0),k1_zfmisc_1(sK1))
      | sK1 != k2_xboole_0(sK2,k6_subset_1(sK1,X0))
      | k1_xboole_0 != k3_xboole_0(sK2,k6_subset_1(sK1,X0))
      | r6_waybel_1(k3_yellow_1(sK1),sK2,k6_subset_1(sK1,X0))
      | ~ m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK1))) ) ),
    inference(forward_demodulation,[],[f189,f91])).

fof(f189,plain,(
    ! [X0] :
      ( sK1 != k2_xboole_0(sK2,k6_subset_1(sK1,X0))
      | k1_xboole_0 != k3_xboole_0(sK2,k6_subset_1(sK1,X0))
      | r6_waybel_1(k3_yellow_1(sK1),sK2,k6_subset_1(sK1,X0))
      | ~ m1_subset_1(k6_subset_1(sK1,X0),u1_struct_0(k3_yellow_1(sK1)))
      | ~ m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK1))) ) ),
    inference(forward_demodulation,[],[f188,f148])).

fof(f148,plain,(
    ! [X0] : k2_xboole_0(sK2,k6_subset_1(sK1,X0)) = k10_lattice3(k3_yellow_1(sK1),sK2,k6_subset_1(sK1,X0)) ),
    inference(forward_demodulation,[],[f146,f133])).

fof(f133,plain,(
    ! [X0] : k13_lattice3(k3_yellow_1(sK1),sK2,k6_subset_1(sK1,X0)) = k2_xboole_0(sK2,k6_subset_1(sK1,X0)) ),
    inference(resolution,[],[f128,f92])).

fof(f128,plain,(
    ! [X2,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | k13_lattice3(k3_yellow_1(X2),X1,k6_subset_1(X2,X3)) = k2_xboole_0(X1,k6_subset_1(X2,X3)) ) ),
    inference(resolution,[],[f98,f79])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k13_lattice3(k3_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X2) ) ),
    inference(forward_demodulation,[],[f97,f91])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k13_lattice3(k3_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(forward_demodulation,[],[f83,f91])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k13_lattice3(k3_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k12_lattice3(k3_yellow_1(X0),X1,X2) = k3_xboole_0(X1,X2)
            & k13_lattice3(k3_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X2) )
          | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) )
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
         => ( k12_lattice3(k3_yellow_1(X0),X1,X2) = k3_xboole_0(X1,X2)
            & k13_lattice3(k3_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_yellow_1)).

fof(f146,plain,(
    ! [X0] : k13_lattice3(k3_yellow_1(sK1),sK2,k6_subset_1(sK1,X0)) = k10_lattice3(k3_yellow_1(sK1),sK2,k6_subset_1(sK1,X0)) ),
    inference(resolution,[],[f141,f92])).

fof(f141,plain,(
    ! [X2,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | k13_lattice3(k3_yellow_1(X2),X1,k6_subset_1(X2,X3)) = k10_lattice3(k3_yellow_1(X2),X1,k6_subset_1(X2,X3)) ) ),
    inference(resolution,[],[f139,f79])).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | k10_lattice3(k3_yellow_1(X1),X2,X0) = k13_lattice3(k3_yellow_1(X1),X2,X0) ) ),
    inference(forward_demodulation,[],[f138,f91])).

fof(f138,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | k10_lattice3(k3_yellow_1(X1),X2,X0) = k13_lattice3(k3_yellow_1(X1),X2,X0) ) ),
    inference(forward_demodulation,[],[f137,f91])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | k10_lattice3(k3_yellow_1(X1),X2,X0) = k13_lattice3(k3_yellow_1(X1),X2,X0) ) ),
    inference(subsumption_resolution,[],[f136,f63])).

fof(f63,plain,(
    ! [X0] : v5_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( v5_orders_2(k3_yellow_1(X0))
      & v4_orders_2(k3_yellow_1(X0))
      & v3_orders_2(k3_yellow_1(X0))
      & ~ v2_struct_0(k3_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v5_orders_2(k3_yellow_1(X0))
      & v4_orders_2(k3_yellow_1(X0))
      & v3_orders_2(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0))
      & ~ v2_struct_0(k3_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_yellow_1)).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | k10_lattice3(k3_yellow_1(X1),X2,X0) = k13_lattice3(k3_yellow_1(X1),X2,X0)
      | ~ v5_orders_2(k3_yellow_1(X1)) ) ),
    inference(subsumption_resolution,[],[f135,f65])).

fof(f65,plain,(
    ! [X0] : l1_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] : l1_orders_2(k3_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow_1)).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | ~ l1_orders_2(k3_yellow_1(X1))
      | k10_lattice3(k3_yellow_1(X1),X2,X0) = k13_lattice3(k3_yellow_1(X1),X2,X0)
      | ~ v5_orders_2(k3_yellow_1(X1)) ) ),
    inference(resolution,[],[f88,f107])).

fof(f107,plain,(
    ! [X1] : v1_lattice3(k3_yellow_1(X1)) ),
    inference(resolution,[],[f105,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v1_lattice3(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ( v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ sP0(X0) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ sP0(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f105,plain,(
    ! [X0] : sP0(k3_yellow_1(X0)) ),
    inference(subsumption_resolution,[],[f104,f65])).

fof(f104,plain,(
    ! [X0] :
      ( sP0(k3_yellow_1(X0))
      | ~ l1_orders_2(k3_yellow_1(X0)) ) ),
    inference(subsumption_resolution,[],[f103,f60])).

fof(f60,plain,(
    ! [X0] : ~ v2_struct_0(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f103,plain,(
    ! [X0] :
      ( sP0(k3_yellow_1(X0))
      | v2_struct_0(k3_yellow_1(X0))
      | ~ l1_orders_2(k3_yellow_1(X0)) ) ),
    inference(resolution,[],[f72,f64])).

fof(f64,plain,(
    ! [X0] : v11_waybel_1(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] : v11_waybel_1(k3_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v11_waybel_1(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_waybel_7)).

fof(f72,plain,(
    ! [X0] :
      ( ~ v11_waybel_1(X0)
      | sP0(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f32,f45])).

fof(f32,plain,(
    ! [X0] :
      ( ( v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v11_waybel_1(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v11_waybel_1(X0)
          & ~ v2_struct_0(X0) )
       => ( v3_yellow_0(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v11_waybel_1(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_waybel_1(X0)
          & v3_yellow_0(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v11_waybel_1(X0)
          & ~ v2_struct_0(X0) )
       => ( v10_waybel_1(X0)
          & v2_waybel_1(X0)
          & v3_yellow_0(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc8_waybel_1)).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_lattice3(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

fof(f188,plain,(
    ! [X0] :
      ( sK1 != k10_lattice3(k3_yellow_1(sK1),sK2,k6_subset_1(sK1,X0))
      | k1_xboole_0 != k3_xboole_0(sK2,k6_subset_1(sK1,X0))
      | r6_waybel_1(k3_yellow_1(sK1),sK2,k6_subset_1(sK1,X0))
      | ~ m1_subset_1(k6_subset_1(sK1,X0),u1_struct_0(k3_yellow_1(sK1)))
      | ~ m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK1))) ) ),
    inference(forward_demodulation,[],[f187,f58])).

fof(f58,plain,(
    ! [X0] : k4_yellow_0(k3_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k4_yellow_0(k3_yellow_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_yellow_1)).

fof(f187,plain,(
    ! [X0] :
      ( k1_xboole_0 != k3_xboole_0(sK2,k6_subset_1(sK1,X0))
      | r6_waybel_1(k3_yellow_1(sK1),sK2,k6_subset_1(sK1,X0))
      | k10_lattice3(k3_yellow_1(sK1),sK2,k6_subset_1(sK1,X0)) != k4_yellow_0(k3_yellow_1(sK1))
      | ~ m1_subset_1(k6_subset_1(sK1,X0),u1_struct_0(k3_yellow_1(sK1)))
      | ~ m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK1))) ) ),
    inference(forward_demodulation,[],[f186,f56])).

fof(f56,plain,(
    ! [X0] : k1_xboole_0 = k3_yellow_0(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k1_xboole_0 = k3_yellow_0(k3_yellow_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_yellow_1)).

fof(f186,plain,(
    ! [X0] :
      ( k3_xboole_0(sK2,k6_subset_1(sK1,X0)) != k3_yellow_0(k3_yellow_1(sK1))
      | r6_waybel_1(k3_yellow_1(sK1),sK2,k6_subset_1(sK1,X0))
      | k10_lattice3(k3_yellow_1(sK1),sK2,k6_subset_1(sK1,X0)) != k4_yellow_0(k3_yellow_1(sK1))
      | ~ m1_subset_1(k6_subset_1(sK1,X0),u1_struct_0(k3_yellow_1(sK1)))
      | ~ m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK1))) ) ),
    inference(subsumption_resolution,[],[f185,f60])).

fof(f185,plain,(
    ! [X0] :
      ( k3_xboole_0(sK2,k6_subset_1(sK1,X0)) != k3_yellow_0(k3_yellow_1(sK1))
      | r6_waybel_1(k3_yellow_1(sK1),sK2,k6_subset_1(sK1,X0))
      | k10_lattice3(k3_yellow_1(sK1),sK2,k6_subset_1(sK1,X0)) != k4_yellow_0(k3_yellow_1(sK1))
      | ~ m1_subset_1(k6_subset_1(sK1,X0),u1_struct_0(k3_yellow_1(sK1)))
      | ~ m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK1)))
      | v2_struct_0(k3_yellow_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f184,f65])).

fof(f184,plain,(
    ! [X0] :
      ( k3_xboole_0(sK2,k6_subset_1(sK1,X0)) != k3_yellow_0(k3_yellow_1(sK1))
      | r6_waybel_1(k3_yellow_1(sK1),sK2,k6_subset_1(sK1,X0))
      | k10_lattice3(k3_yellow_1(sK1),sK2,k6_subset_1(sK1,X0)) != k4_yellow_0(k3_yellow_1(sK1))
      | ~ m1_subset_1(k6_subset_1(sK1,X0),u1_struct_0(k3_yellow_1(sK1)))
      | ~ m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK1)))
      | ~ l1_orders_2(k3_yellow_1(sK1))
      | v2_struct_0(k3_yellow_1(sK1)) ) ),
    inference(superposition,[],[f75,f182])).

fof(f182,plain,(
    ! [X0] : k3_xboole_0(sK2,k6_subset_1(sK1,X0)) = k11_lattice3(k3_yellow_1(sK1),sK2,k6_subset_1(sK1,X0)) ),
    inference(forward_demodulation,[],[f180,f131])).

fof(f131,plain,(
    ! [X0] : k12_lattice3(k3_yellow_1(sK1),sK2,k6_subset_1(sK1,X0)) = k3_xboole_0(sK2,k6_subset_1(sK1,X0)) ),
    inference(resolution,[],[f124,f92])).

fof(f124,plain,(
    ! [X2,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | k12_lattice3(k3_yellow_1(X2),X1,k6_subset_1(X2,X3)) = k3_xboole_0(X1,k6_subset_1(X2,X3)) ) ),
    inference(resolution,[],[f96,f79])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k12_lattice3(k3_yellow_1(X0),X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(forward_demodulation,[],[f95,f91])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k12_lattice3(k3_yellow_1(X0),X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(forward_demodulation,[],[f84,f91])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k12_lattice3(k3_yellow_1(X0),X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f180,plain,(
    ! [X0] : k12_lattice3(k3_yellow_1(sK1),sK2,k6_subset_1(sK1,X0)) = k11_lattice3(k3_yellow_1(sK1),sK2,k6_subset_1(sK1,X0)) ),
    inference(resolution,[],[f156,f92])).

fof(f156,plain,(
    ! [X2,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | k12_lattice3(k3_yellow_1(X2),X1,k6_subset_1(X2,X3)) = k11_lattice3(k3_yellow_1(X2),X1,k6_subset_1(X2,X3)) ) ),
    inference(resolution,[],[f154,f79])).

fof(f154,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | k11_lattice3(k3_yellow_1(X1),X2,X0) = k12_lattice3(k3_yellow_1(X1),X2,X0) ) ),
    inference(forward_demodulation,[],[f153,f91])).

fof(f153,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | k11_lattice3(k3_yellow_1(X1),X2,X0) = k12_lattice3(k3_yellow_1(X1),X2,X0) ) ),
    inference(forward_demodulation,[],[f152,f91])).

fof(f152,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | k11_lattice3(k3_yellow_1(X1),X2,X0) = k12_lattice3(k3_yellow_1(X1),X2,X0) ) ),
    inference(subsumption_resolution,[],[f151,f63])).

fof(f151,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | k11_lattice3(k3_yellow_1(X1),X2,X0) = k12_lattice3(k3_yellow_1(X1),X2,X0)
      | ~ v5_orders_2(k3_yellow_1(X1)) ) ),
    inference(subsumption_resolution,[],[f150,f65])).

fof(f150,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | ~ l1_orders_2(k3_yellow_1(X1))
      | k11_lattice3(k3_yellow_1(X1),X2,X0) = k12_lattice3(k3_yellow_1(X1),X2,X0)
      | ~ v5_orders_2(k3_yellow_1(X1)) ) ),
    inference(resolution,[],[f89,f106])).

fof(f106,plain,(
    ! [X0] : v2_lattice3(k3_yellow_1(X0)) ),
    inference(resolution,[],[f105,f71])).

fof(f71,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v2_lattice3(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_lattice3(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k11_lattice3(X0,X1,X2) != k3_yellow_0(X0)
      | r6_waybel_1(X0,X1,X2)
      | k10_lattice3(X0,X1,X2) != k4_yellow_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r6_waybel_1(X0,X1,X2)
                  | k11_lattice3(X0,X1,X2) != k3_yellow_0(X0)
                  | k10_lattice3(X0,X1,X2) != k4_yellow_0(X0) )
                & ( ( k11_lattice3(X0,X1,X2) = k3_yellow_0(X0)
                    & k10_lattice3(X0,X1,X2) = k4_yellow_0(X0) )
                  | ~ r6_waybel_1(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r6_waybel_1(X0,X1,X2)
                  | k11_lattice3(X0,X1,X2) != k3_yellow_0(X0)
                  | k10_lattice3(X0,X1,X2) != k4_yellow_0(X0) )
                & ( ( k11_lattice3(X0,X1,X2) = k3_yellow_0(X0)
                    & k10_lattice3(X0,X1,X2) = k4_yellow_0(X0) )
                  | ~ r6_waybel_1(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r6_waybel_1(X0,X1,X2)
              <=> ( k11_lattice3(X0,X1,X2) = k3_yellow_0(X0)
                  & k10_lattice3(X0,X1,X2) = k4_yellow_0(X0) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r6_waybel_1(X0,X1,X2)
              <=> ( k11_lattice3(X0,X1,X2) = k3_yellow_0(X0)
                  & k10_lattice3(X0,X1,X2) = k4_yellow_0(X0) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r6_waybel_1(X0,X1,X2)
              <=> ( k11_lattice3(X0,X1,X2) = k3_yellow_0(X0)
                  & k10_lattice3(X0,X1,X2) = k4_yellow_0(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d23_waybel_1)).

fof(f243,plain,(
    ! [X0] :
      ( ~ r6_waybel_1(k3_yellow_1(sK1),sK2,k6_subset_1(sK1,X0))
      | k7_waybel_1(k3_yellow_1(sK1),sK2) = k6_subset_1(sK1,X0) ) ),
    inference(resolution,[],[f242,f92])).

fof(f242,plain,(
    ! [X2,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r6_waybel_1(k3_yellow_1(X2),X1,k6_subset_1(X2,X3))
      | k6_subset_1(X2,X3) = k7_waybel_1(k3_yellow_1(X2),X1) ) ),
    inference(resolution,[],[f240,f79])).

fof(f240,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r6_waybel_1(k3_yellow_1(X0),X1,X2)
      | k7_waybel_1(k3_yellow_1(X0),X1) = X2 ) ),
    inference(forward_demodulation,[],[f239,f91])).

fof(f239,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ r6_waybel_1(k3_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
      | k7_waybel_1(k3_yellow_1(X0),X1) = X2 ) ),
    inference(forward_demodulation,[],[f238,f91])).

fof(f238,plain,(
    ! [X2,X0,X1] :
      ( ~ r6_waybel_1(k3_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
      | k7_waybel_1(k3_yellow_1(X0),X1) = X2 ) ),
    inference(subsumption_resolution,[],[f237,f61])).

fof(f61,plain,(
    ! [X0] : v3_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f237,plain,(
    ! [X2,X0,X1] :
      ( ~ r6_waybel_1(k3_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
      | k7_waybel_1(k3_yellow_1(X0),X1) = X2
      | ~ v3_orders_2(k3_yellow_1(X0)) ) ),
    inference(subsumption_resolution,[],[f236,f62])).

fof(f62,plain,(
    ! [X0] : v4_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f236,plain,(
    ! [X2,X0,X1] :
      ( ~ r6_waybel_1(k3_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
      | k7_waybel_1(k3_yellow_1(X0),X1) = X2
      | ~ v4_orders_2(k3_yellow_1(X0))
      | ~ v3_orders_2(k3_yellow_1(X0)) ) ),
    inference(subsumption_resolution,[],[f235,f63])).

fof(f235,plain,(
    ! [X2,X0,X1] :
      ( ~ r6_waybel_1(k3_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
      | k7_waybel_1(k3_yellow_1(X0),X1) = X2
      | ~ v5_orders_2(k3_yellow_1(X0))
      | ~ v4_orders_2(k3_yellow_1(X0))
      | ~ v3_orders_2(k3_yellow_1(X0)) ) ),
    inference(subsumption_resolution,[],[f234,f107])).

fof(f234,plain,(
    ! [X2,X0,X1] :
      ( ~ r6_waybel_1(k3_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
      | k7_waybel_1(k3_yellow_1(X0),X1) = X2
      | ~ v1_lattice3(k3_yellow_1(X0))
      | ~ v5_orders_2(k3_yellow_1(X0))
      | ~ v4_orders_2(k3_yellow_1(X0))
      | ~ v3_orders_2(k3_yellow_1(X0)) ) ),
    inference(subsumption_resolution,[],[f233,f64])).

fof(f233,plain,(
    ! [X2,X0,X1] :
      ( ~ r6_waybel_1(k3_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
      | ~ v11_waybel_1(k3_yellow_1(X0))
      | k7_waybel_1(k3_yellow_1(X0),X1) = X2
      | ~ v1_lattice3(k3_yellow_1(X0))
      | ~ v5_orders_2(k3_yellow_1(X0))
      | ~ v4_orders_2(k3_yellow_1(X0))
      | ~ v3_orders_2(k3_yellow_1(X0)) ) ),
    inference(subsumption_resolution,[],[f232,f65])).

fof(f232,plain,(
    ! [X2,X0,X1] :
      ( ~ r6_waybel_1(k3_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
      | ~ l1_orders_2(k3_yellow_1(X0))
      | ~ v11_waybel_1(k3_yellow_1(X0))
      | k7_waybel_1(k3_yellow_1(X0),X1) = X2
      | ~ v1_lattice3(k3_yellow_1(X0))
      | ~ v5_orders_2(k3_yellow_1(X0))
      | ~ v4_orders_2(k3_yellow_1(X0))
      | ~ v3_orders_2(k3_yellow_1(X0)) ) ),
    inference(resolution,[],[f76,f106])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_lattice3(X0)
      | ~ r6_waybel_1(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v11_waybel_1(X0)
      | k7_waybel_1(X0,X1) = X2
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r6_waybel_1(X0,X1,X2)
                  | k7_waybel_1(X0,X1) != X2 )
                & ( k7_waybel_1(X0,X1) = X2
                  | ~ r6_waybel_1(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v11_waybel_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r6_waybel_1(X0,X1,X2)
              <=> k7_waybel_1(X0,X1) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v11_waybel_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r6_waybel_1(X0,X1,X2)
              <=> k7_waybel_1(X0,X1) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v11_waybel_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

% (21779)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
fof(f13,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v11_waybel_1(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r6_waybel_1(X0,X1,X2)
              <=> k7_waybel_1(X0,X1) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_yellow_5)).

%------------------------------------------------------------------------------
