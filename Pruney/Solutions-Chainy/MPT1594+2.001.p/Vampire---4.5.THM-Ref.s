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
% DateTime   : Thu Dec  3 13:16:26 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  153 (3768 expanded)
%              Number of leaves         :   15 ( 810 expanded)
%              Depth                    :   72
%              Number of atoms          :  573 (9974 expanded)
%              Number of equality atoms :   39 (1110 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f194,plain,(
    $false ),
    inference(global_subsumption,[],[f72,f163,f193])).

fof(f193,plain,(
    r3_orders_2(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) ),
    inference(forward_demodulation,[],[f192,f104])).

% (12858)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
fof(f104,plain,(
    sK1 = k4_lattice3(k1_lattice3(sK0),sK1) ),
    inference(resolution,[],[f101,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))
      | k4_lattice3(k1_lattice3(X0),X1) = X1 ) ),
    inference(subsumption_resolution,[],[f86,f52])).

fof(f52,plain,(
    ! [X0] : l3_lattices(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] : l3_lattices(k1_lattice3(X0)) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l3_lattices(k1_lattice3(X0))
      & v3_lattices(k1_lattice3(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_lattice3)).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ l3_lattices(k1_lattice3(X0))
      | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))
      | k4_lattice3(k1_lattice3(X0),X1) = X1 ) ),
    inference(subsumption_resolution,[],[f85,f50])).

fof(f50,plain,(
    ! [X0] : ~ v2_struct_0(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] : ~ v2_struct_0(k1_lattice3(X0)) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v3_lattices(k1_lattice3(X0))
      & ~ v2_struct_0(k1_lattice3(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_lattice3)).

fof(f85,plain,(
    ! [X0,X1] :
      ( v2_struct_0(k1_lattice3(X0))
      | ~ l3_lattices(k1_lattice3(X0))
      | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))
      | k4_lattice3(k1_lattice3(X0),X1) = X1 ) ),
    inference(resolution,[],[f59,f51])).

fof(f51,plain,(
    ! [X0] : v10_lattices(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] : v10_lattices(k1_lattice3(X0)) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v10_lattices(k1_lattice3(X0))
      & v3_lattices(k1_lattice3(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_lattice3)).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k4_lattice3(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattice3(X0,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattice3(X0,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k4_lattice3(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_lattice3)).

fof(f101,plain,(
    m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0))) ),
    inference(backward_demodulation,[],[f70,f99])).

fof(f99,plain,(
    ! [X0] : u1_struct_0(k1_lattice3(X0)) = u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
    ! [X2,X3] :
      ( k3_lattice3(k1_lattice3(X2)) != k3_lattice3(k1_lattice3(X3))
      | u1_struct_0(k3_lattice3(k1_lattice3(X2))) = u1_struct_0(k1_lattice3(X3)) ) ),
    inference(superposition,[],[f92,f89])).

fof(f89,plain,(
    ! [X0] : k3_lattice3(k1_lattice3(X0)) = g1_orders_2(u1_struct_0(k3_lattice3(k1_lattice3(X0))),u1_orders_2(k3_lattice3(k1_lattice3(X0)))) ),
    inference(subsumption_resolution,[],[f88,f83])).

fof(f83,plain,(
    ! [X0] : l1_orders_2(k3_lattice3(k1_lattice3(X0))) ),
    inference(forward_demodulation,[],[f81,f77])).

fof(f77,plain,(
    ! [X0] : k3_lattice3(k1_lattice3(X0)) = g1_orders_2(u1_struct_0(k1_lattice3(X0)),k2_lattice3(k1_lattice3(X0))) ),
    inference(subsumption_resolution,[],[f76,f52])).

fof(f76,plain,(
    ! [X0] :
      ( ~ l3_lattices(k1_lattice3(X0))
      | k3_lattice3(k1_lattice3(X0)) = g1_orders_2(u1_struct_0(k1_lattice3(X0)),k2_lattice3(k1_lattice3(X0))) ) ),
    inference(subsumption_resolution,[],[f75,f50])).

fof(f75,plain,(
    ! [X0] :
      ( v2_struct_0(k1_lattice3(X0))
      | ~ l3_lattices(k1_lattice3(X0))
      | k3_lattice3(k1_lattice3(X0)) = g1_orders_2(u1_struct_0(k1_lattice3(X0)),k2_lattice3(k1_lattice3(X0))) ) ),
    inference(resolution,[],[f57,f51])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | k3_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k2_lattice3(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( k3_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k2_lattice3(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( k3_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k2_lattice3(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k2_lattice3(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_lattice3)).

fof(f81,plain,(
    ! [X0] : l1_orders_2(g1_orders_2(u1_struct_0(k1_lattice3(X0)),k2_lattice3(k1_lattice3(X0)))) ),
    inference(resolution,[],[f80,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | l1_orders_2(g1_orders_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( l1_orders_2(g1_orders_2(X0,X1))
        & v1_orders_2(g1_orders_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ( l1_orders_2(g1_orders_2(X0,X1))
        & v1_orders_2(g1_orders_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_orders_2)).

fof(f80,plain,(
    ! [X0] : m1_subset_1(k2_lattice3(k1_lattice3(X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_lattice3(X0)),u1_struct_0(k1_lattice3(X0))))) ),
    inference(subsumption_resolution,[],[f79,f52])).

fof(f79,plain,(
    ! [X0] :
      ( ~ l3_lattices(k1_lattice3(X0))
      | m1_subset_1(k2_lattice3(k1_lattice3(X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_lattice3(X0)),u1_struct_0(k1_lattice3(X0))))) ) ),
    inference(subsumption_resolution,[],[f78,f50])).

fof(f78,plain,(
    ! [X0] :
      ( v2_struct_0(k1_lattice3(X0))
      | ~ l3_lattices(k1_lattice3(X0))
      | m1_subset_1(k2_lattice3(k1_lattice3(X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_lattice3(X0)),u1_struct_0(k1_lattice3(X0))))) ) ),
    inference(resolution,[],[f58,f51])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_partfun1(k2_lattice3(X0),u1_struct_0(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_relat_2(k2_lattice3(X0))
        & v1_partfun1(k2_lattice3(X0),u1_struct_0(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f17])).

% (12847)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
fof(f17,plain,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v4_relat_2(k2_lattice3(X0))
        & v1_relat_2(k2_lattice3(X0))
        & v1_partfun1(k2_lattice3(X0),u1_struct_0(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v8_relat_2(k2_lattice3(X0))
        & v4_relat_2(k2_lattice3(X0))
        & v1_relat_2(k2_lattice3(X0))
        & v1_partfun1(k2_lattice3(X0),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_lattice3)).

fof(f88,plain,(
    ! [X0] :
      ( ~ l1_orders_2(k3_lattice3(k1_lattice3(X0)))
      | k3_lattice3(k1_lattice3(X0)) = g1_orders_2(u1_struct_0(k3_lattice3(k1_lattice3(X0))),u1_orders_2(k3_lattice3(k1_lattice3(X0)))) ) ),
    inference(resolution,[],[f84,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_orders_2(X0)
       => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_orders_2)).

fof(f84,plain,(
    ! [X1] : v1_orders_2(k3_lattice3(k1_lattice3(X1))) ),
    inference(forward_demodulation,[],[f82,f77])).

fof(f82,plain,(
    ! [X1] : v1_orders_2(g1_orders_2(u1_struct_0(k1_lattice3(X1)),k2_lattice3(k1_lattice3(X1)))) ),
    inference(resolution,[],[f80,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | v1_orders_2(g1_orders_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( k3_lattice3(k1_lattice3(X0)) != g1_orders_2(X1,X2)
      | u1_struct_0(k1_lattice3(X0)) = X1 ) ),
    inference(superposition,[],[f90,f77])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( g1_orders_2(u1_struct_0(k1_lattice3(X0)),k2_lattice3(k1_lattice3(X0))) != g1_orders_2(X1,X2)
      | u1_struct_0(k1_lattice3(X0)) = X1 ) ),
    inference(resolution,[],[f66,f80])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(f70,plain,(
    m1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) ),
    inference(definition_unfolding,[],[f48,f49])).

fof(f49,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_yellow_1)).

fof(f48,plain,(
    m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r3_orders_2(k3_yellow_1(X0),X1,X2)
          <~> r1_tarski(X1,X2) )
          & m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) )
      & m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
           => ( r3_orders_2(k3_yellow_1(X0),X1,X2)
            <=> r1_tarski(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
         => ( r3_orders_2(k3_yellow_1(X0),X1,X2)
          <=> r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_yellow_1)).

fof(f192,plain,(
    r3_orders_2(k3_lattice3(k1_lattice3(sK0)),k4_lattice3(k1_lattice3(sK0),sK1),sK2) ),
    inference(forward_demodulation,[],[f191,f103])).

fof(f103,plain,(
    sK2 = k4_lattice3(k1_lattice3(sK0),sK2) ),
    inference(resolution,[],[f100,f87])).

fof(f100,plain,(
    m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0))) ),
    inference(backward_demodulation,[],[f71,f99])).

fof(f71,plain,(
    m1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) ),
    inference(definition_unfolding,[],[f47,f49])).

fof(f47,plain,(
    m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f191,plain,(
    r3_orders_2(k3_lattice3(k1_lattice3(sK0)),k4_lattice3(k1_lattice3(sK0),sK1),k4_lattice3(k1_lattice3(sK0),sK2)) ),
    inference(subsumption_resolution,[],[f190,f50])).

fof(f190,plain,
    ( r3_orders_2(k3_lattice3(k1_lattice3(sK0)),k4_lattice3(k1_lattice3(sK0),sK1),k4_lattice3(k1_lattice3(sK0),sK2))
    | v2_struct_0(k1_lattice3(sK0)) ),
    inference(subsumption_resolution,[],[f189,f100])).

fof(f189,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0)))
    | r3_orders_2(k3_lattice3(k1_lattice3(sK0)),k4_lattice3(k1_lattice3(sK0),sK1),k4_lattice3(k1_lattice3(sK0),sK2))
    | v2_struct_0(k1_lattice3(sK0)) ),
    inference(subsumption_resolution,[],[f188,f101])).

fof(f188,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0)))
    | r3_orders_2(k3_lattice3(k1_lattice3(sK0)),k4_lattice3(k1_lattice3(sK0),sK1),k4_lattice3(k1_lattice3(sK0),sK2))
    | v2_struct_0(k1_lattice3(sK0)) ),
    inference(subsumption_resolution,[],[f187,f52])).

fof(f187,plain,
    ( ~ l3_lattices(k1_lattice3(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0)))
    | r3_orders_2(k3_lattice3(k1_lattice3(sK0)),k4_lattice3(k1_lattice3(sK0),sK1),k4_lattice3(k1_lattice3(sK0),sK2))
    | v2_struct_0(k1_lattice3(sK0)) ),
    inference(subsumption_resolution,[],[f185,f51])).

fof(f185,plain,
    ( ~ v10_lattices(k1_lattice3(sK0))
    | ~ l3_lattices(k1_lattice3(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0)))
    | r3_orders_2(k3_lattice3(k1_lattice3(sK0)),k4_lattice3(k1_lattice3(sK0),sK1),k4_lattice3(k1_lattice3(sK0),sK2))
    | v2_struct_0(k1_lattice3(sK0)) ),
    inference(resolution,[],[f184,f61])).

% (12865)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_lattices(X0,X1,X2)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattices(X0,X1,X2)
              <=> r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattices(X0,X1,X2)
              <=> r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r3_lattices(X0,X1,X2)
              <=> r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_lattice3)).

fof(f184,plain,(
    r3_lattices(k1_lattice3(sK0),sK1,sK2) ),
    inference(subsumption_resolution,[],[f183,f52])).

fof(f183,plain,
    ( r3_lattices(k1_lattice3(sK0),sK1,sK2)
    | ~ l3_lattices(k1_lattice3(sK0)) ),
    inference(subsumption_resolution,[],[f182,f51])).

fof(f182,plain,
    ( r3_lattices(k1_lattice3(sK0),sK1,sK2)
    | ~ v10_lattices(k1_lattice3(sK0))
    | ~ l3_lattices(k1_lattice3(sK0)) ),
    inference(subsumption_resolution,[],[f181,f50])).

fof(f181,plain,
    ( r3_lattices(k1_lattice3(sK0),sK1,sK2)
    | v2_struct_0(k1_lattice3(sK0))
    | ~ v10_lattices(k1_lattice3(sK0))
    | ~ l3_lattices(k1_lattice3(sK0)) ),
    inference(resolution,[],[f180,f54])).

fof(f54,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v7_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).

fof(f180,plain,
    ( ~ v6_lattices(k1_lattice3(sK0))
    | r3_lattices(k1_lattice3(sK0),sK1,sK2) ),
    inference(subsumption_resolution,[],[f179,f52])).

fof(f179,plain,
    ( ~ v6_lattices(k1_lattice3(sK0))
    | r3_lattices(k1_lattice3(sK0),sK1,sK2)
    | ~ l3_lattices(k1_lattice3(sK0)) ),
    inference(subsumption_resolution,[],[f178,f51])).

fof(f178,plain,
    ( ~ v6_lattices(k1_lattice3(sK0))
    | r3_lattices(k1_lattice3(sK0),sK1,sK2)
    | ~ v10_lattices(k1_lattice3(sK0))
    | ~ l3_lattices(k1_lattice3(sK0)) ),
    inference(subsumption_resolution,[],[f177,f50])).

fof(f177,plain,
    ( ~ v6_lattices(k1_lattice3(sK0))
    | r3_lattices(k1_lattice3(sK0),sK1,sK2)
    | v2_struct_0(k1_lattice3(sK0))
    | ~ v10_lattices(k1_lattice3(sK0))
    | ~ l3_lattices(k1_lattice3(sK0)) ),
    inference(resolution,[],[f176,f55])).

fof(f55,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f176,plain,
    ( ~ v8_lattices(k1_lattice3(sK0))
    | ~ v6_lattices(k1_lattice3(sK0))
    | r3_lattices(k1_lattice3(sK0),sK1,sK2) ),
    inference(subsumption_resolution,[],[f175,f52])).

fof(f175,plain,
    ( ~ v8_lattices(k1_lattice3(sK0))
    | ~ v6_lattices(k1_lattice3(sK0))
    | r3_lattices(k1_lattice3(sK0),sK1,sK2)
    | ~ l3_lattices(k1_lattice3(sK0)) ),
    inference(subsumption_resolution,[],[f174,f51])).

fof(f174,plain,
    ( ~ v8_lattices(k1_lattice3(sK0))
    | ~ v6_lattices(k1_lattice3(sK0))
    | r3_lattices(k1_lattice3(sK0),sK1,sK2)
    | ~ v10_lattices(k1_lattice3(sK0))
    | ~ l3_lattices(k1_lattice3(sK0)) ),
    inference(subsumption_resolution,[],[f173,f50])).

fof(f173,plain,
    ( ~ v8_lattices(k1_lattice3(sK0))
    | ~ v6_lattices(k1_lattice3(sK0))
    | r3_lattices(k1_lattice3(sK0),sK1,sK2)
    | v2_struct_0(k1_lattice3(sK0))
    | ~ v10_lattices(k1_lattice3(sK0))
    | ~ l3_lattices(k1_lattice3(sK0)) ),
    inference(resolution,[],[f172,f56])).

fof(f56,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f172,plain,
    ( ~ v9_lattices(k1_lattice3(sK0))
    | ~ v8_lattices(k1_lattice3(sK0))
    | ~ v6_lattices(k1_lattice3(sK0))
    | r3_lattices(k1_lattice3(sK0),sK1,sK2) ),
    inference(subsumption_resolution,[],[f171,f50])).

fof(f171,plain,
    ( ~ v6_lattices(k1_lattice3(sK0))
    | ~ v8_lattices(k1_lattice3(sK0))
    | ~ v9_lattices(k1_lattice3(sK0))
    | v2_struct_0(k1_lattice3(sK0))
    | r3_lattices(k1_lattice3(sK0),sK1,sK2) ),
    inference(subsumption_resolution,[],[f170,f100])).

fof(f170,plain,
    ( ~ v6_lattices(k1_lattice3(sK0))
    | ~ v8_lattices(k1_lattice3(sK0))
    | ~ v9_lattices(k1_lattice3(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0)))
    | v2_struct_0(k1_lattice3(sK0))
    | r3_lattices(k1_lattice3(sK0),sK1,sK2) ),
    inference(subsumption_resolution,[],[f169,f101])).

fof(f169,plain,
    ( ~ v6_lattices(k1_lattice3(sK0))
    | ~ v8_lattices(k1_lattice3(sK0))
    | ~ v9_lattices(k1_lattice3(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0)))
    | v2_struct_0(k1_lattice3(sK0))
    | r3_lattices(k1_lattice3(sK0),sK1,sK2) ),
    inference(subsumption_resolution,[],[f168,f52])).

fof(f168,plain,
    ( ~ v6_lattices(k1_lattice3(sK0))
    | ~ v8_lattices(k1_lattice3(sK0))
    | ~ v9_lattices(k1_lattice3(sK0))
    | ~ l3_lattices(k1_lattice3(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0)))
    | v2_struct_0(k1_lattice3(sK0))
    | r3_lattices(k1_lattice3(sK0),sK1,sK2) ),
    inference(resolution,[],[f166,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X1,X2)
      | ~ v6_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r3_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).

fof(f166,plain,(
    r1_lattices(k1_lattice3(sK0),sK1,sK2) ),
    inference(subsumption_resolution,[],[f165,f101])).

fof(f165,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0)))
    | r1_lattices(k1_lattice3(sK0),sK1,sK2) ),
    inference(resolution,[],[f164,f100])).

fof(f164,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,u1_struct_0(k1_lattice3(X0)))
      | ~ m1_subset_1(sK1,u1_struct_0(k1_lattice3(X0)))
      | r1_lattices(k1_lattice3(X0),sK1,sK2) ) ),
    inference(resolution,[],[f163,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))
      | r1_lattices(k1_lattice3(X0),X1,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_lattices(k1_lattice3(X0),X1,X2)
          <=> r1_tarski(X1,X2) )
          | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) )
      | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))
         => ( r1_lattices(k1_lattice3(X0),X1,X2)
          <=> r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_lattice3)).

fof(f163,plain,(
    r1_tarski(sK1,sK2) ),
    inference(subsumption_resolution,[],[f162,f101])).

fof(f162,plain,
    ( r1_tarski(sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0))) ),
    inference(subsumption_resolution,[],[f161,f100])).

fof(f161,plain,
    ( r1_tarski(sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0))) ),
    inference(duplicate_literal_removal,[],[f159])).

fof(f159,plain,
    ( r1_tarski(sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0)))
    | r1_tarski(sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0))) ),
    inference(resolution,[],[f158,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(k1_lattice3(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f158,plain,
    ( r1_lattices(k1_lattice3(sK0),sK1,sK2)
    | r1_tarski(sK1,sK2) ),
    inference(subsumption_resolution,[],[f157,f52])).

fof(f157,plain,
    ( r1_tarski(sK1,sK2)
    | r1_lattices(k1_lattice3(sK0),sK1,sK2)
    | ~ l3_lattices(k1_lattice3(sK0)) ),
    inference(subsumption_resolution,[],[f156,f51])).

fof(f156,plain,
    ( r1_tarski(sK1,sK2)
    | r1_lattices(k1_lattice3(sK0),sK1,sK2)
    | ~ v10_lattices(k1_lattice3(sK0))
    | ~ l3_lattices(k1_lattice3(sK0)) ),
    inference(subsumption_resolution,[],[f155,f50])).

fof(f155,plain,
    ( r1_tarski(sK1,sK2)
    | r1_lattices(k1_lattice3(sK0),sK1,sK2)
    | v2_struct_0(k1_lattice3(sK0))
    | ~ v10_lattices(k1_lattice3(sK0))
    | ~ l3_lattices(k1_lattice3(sK0)) ),
    inference(resolution,[],[f154,f54])).

fof(f154,plain,
    ( ~ v6_lattices(k1_lattice3(sK0))
    | r1_tarski(sK1,sK2)
    | r1_lattices(k1_lattice3(sK0),sK1,sK2) ),
    inference(subsumption_resolution,[],[f153,f52])).

fof(f153,plain,
    ( ~ v6_lattices(k1_lattice3(sK0))
    | r1_tarski(sK1,sK2)
    | r1_lattices(k1_lattice3(sK0),sK1,sK2)
    | ~ l3_lattices(k1_lattice3(sK0)) ),
    inference(subsumption_resolution,[],[f152,f51])).

fof(f152,plain,
    ( ~ v6_lattices(k1_lattice3(sK0))
    | r1_tarski(sK1,sK2)
    | r1_lattices(k1_lattice3(sK0),sK1,sK2)
    | ~ v10_lattices(k1_lattice3(sK0))
    | ~ l3_lattices(k1_lattice3(sK0)) ),
    inference(subsumption_resolution,[],[f151,f50])).

fof(f151,plain,
    ( ~ v6_lattices(k1_lattice3(sK0))
    | r1_tarski(sK1,sK2)
    | r1_lattices(k1_lattice3(sK0),sK1,sK2)
    | v2_struct_0(k1_lattice3(sK0))
    | ~ v10_lattices(k1_lattice3(sK0))
    | ~ l3_lattices(k1_lattice3(sK0)) ),
    inference(resolution,[],[f150,f55])).

fof(f150,plain,
    ( ~ v8_lattices(k1_lattice3(sK0))
    | ~ v6_lattices(k1_lattice3(sK0))
    | r1_tarski(sK1,sK2)
    | r1_lattices(k1_lattice3(sK0),sK1,sK2) ),
    inference(subsumption_resolution,[],[f149,f52])).

fof(f149,plain,
    ( ~ v6_lattices(k1_lattice3(sK0))
    | ~ v8_lattices(k1_lattice3(sK0))
    | r1_tarski(sK1,sK2)
    | r1_lattices(k1_lattice3(sK0),sK1,sK2)
    | ~ l3_lattices(k1_lattice3(sK0)) ),
    inference(subsumption_resolution,[],[f148,f51])).

fof(f148,plain,
    ( ~ v6_lattices(k1_lattice3(sK0))
    | ~ v8_lattices(k1_lattice3(sK0))
    | r1_tarski(sK1,sK2)
    | r1_lattices(k1_lattice3(sK0),sK1,sK2)
    | ~ v10_lattices(k1_lattice3(sK0))
    | ~ l3_lattices(k1_lattice3(sK0)) ),
    inference(subsumption_resolution,[],[f147,f50])).

fof(f147,plain,
    ( ~ v6_lattices(k1_lattice3(sK0))
    | ~ v8_lattices(k1_lattice3(sK0))
    | r1_tarski(sK1,sK2)
    | r1_lattices(k1_lattice3(sK0),sK1,sK2)
    | v2_struct_0(k1_lattice3(sK0))
    | ~ v10_lattices(k1_lattice3(sK0))
    | ~ l3_lattices(k1_lattice3(sK0)) ),
    inference(resolution,[],[f142,f56])).

fof(f142,plain,
    ( ~ v9_lattices(k1_lattice3(sK0))
    | ~ v6_lattices(k1_lattice3(sK0))
    | ~ v8_lattices(k1_lattice3(sK0))
    | r1_tarski(sK1,sK2)
    | r1_lattices(k1_lattice3(sK0),sK1,sK2) ),
    inference(subsumption_resolution,[],[f141,f50])).

fof(f141,plain,
    ( r1_tarski(sK1,sK2)
    | ~ v6_lattices(k1_lattice3(sK0))
    | ~ v8_lattices(k1_lattice3(sK0))
    | ~ v9_lattices(k1_lattice3(sK0))
    | r1_lattices(k1_lattice3(sK0),sK1,sK2)
    | v2_struct_0(k1_lattice3(sK0)) ),
    inference(subsumption_resolution,[],[f140,f100])).

fof(f140,plain,
    ( r1_tarski(sK1,sK2)
    | ~ v6_lattices(k1_lattice3(sK0))
    | ~ v8_lattices(k1_lattice3(sK0))
    | ~ v9_lattices(k1_lattice3(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0)))
    | r1_lattices(k1_lattice3(sK0),sK1,sK2)
    | v2_struct_0(k1_lattice3(sK0)) ),
    inference(subsumption_resolution,[],[f139,f101])).

fof(f139,plain,
    ( r1_tarski(sK1,sK2)
    | ~ v6_lattices(k1_lattice3(sK0))
    | ~ v8_lattices(k1_lattice3(sK0))
    | ~ v9_lattices(k1_lattice3(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0)))
    | r1_lattices(k1_lattice3(sK0),sK1,sK2)
    | v2_struct_0(k1_lattice3(sK0)) ),
    inference(subsumption_resolution,[],[f131,f52])).

fof(f131,plain,
    ( r1_tarski(sK1,sK2)
    | ~ v6_lattices(k1_lattice3(sK0))
    | ~ v8_lattices(k1_lattice3(sK0))
    | ~ v9_lattices(k1_lattice3(sK0))
    | ~ l3_lattices(k1_lattice3(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0)))
    | r1_lattices(k1_lattice3(sK0),sK1,sK2)
    | v2_struct_0(k1_lattice3(sK0)) ),
    inference(resolution,[],[f129,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_lattices(X0,X1,X2)
      | ~ v6_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_lattices(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f129,plain,
    ( r3_lattices(k1_lattice3(sK0),sK1,sK2)
    | r1_tarski(sK1,sK2) ),
    inference(resolution,[],[f128,f73])).

fof(f73,plain,
    ( r3_orders_2(k3_lattice3(k1_lattice3(sK0)),sK1,sK2)
    | r1_tarski(sK1,sK2) ),
    inference(definition_unfolding,[],[f45,f49])).

fof(f45,plain,
    ( r1_tarski(sK1,sK2)
    | r3_orders_2(k3_yellow_1(sK0),sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f128,plain,
    ( ~ r3_orders_2(k3_lattice3(k1_lattice3(sK0)),sK1,sK2)
    | r3_lattices(k1_lattice3(sK0),sK1,sK2) ),
    inference(subsumption_resolution,[],[f126,f101])).

fof(f126,plain,
    ( ~ r3_orders_2(k3_lattice3(k1_lattice3(sK0)),sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0)))
    | r3_lattices(k1_lattice3(sK0),sK1,sK2) ),
    inference(superposition,[],[f123,f104])).

fof(f123,plain,(
    ! [X0] :
      ( ~ r3_orders_2(k3_lattice3(k1_lattice3(sK0)),k4_lattice3(k1_lattice3(sK0),X0),sK2)
      | ~ m1_subset_1(X0,u1_struct_0(k1_lattice3(sK0)))
      | r3_lattices(k1_lattice3(sK0),X0,sK2) ) ),
    inference(forward_demodulation,[],[f121,f103])).

fof(f121,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(k1_lattice3(sK0)))
      | ~ r3_orders_2(k3_lattice3(k1_lattice3(sK0)),k4_lattice3(k1_lattice3(sK0),X0),k4_lattice3(k1_lattice3(sK0),sK2))
      | r3_lattices(k1_lattice3(sK0),X0,sK2) ) ),
    inference(resolution,[],[f120,f100])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))
      | ~ r3_orders_2(k3_lattice3(k1_lattice3(X0)),k4_lattice3(k1_lattice3(X0),X1),k4_lattice3(k1_lattice3(X0),X2))
      | r3_lattices(k1_lattice3(X0),X1,X2) ) ),
    inference(subsumption_resolution,[],[f119,f52])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( ~ l3_lattices(k1_lattice3(X0))
      | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))
      | ~ r3_orders_2(k3_lattice3(k1_lattice3(X0)),k4_lattice3(k1_lattice3(X0),X1),k4_lattice3(k1_lattice3(X0),X2))
      | r3_lattices(k1_lattice3(X0),X1,X2) ) ),
    inference(subsumption_resolution,[],[f118,f50])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(k1_lattice3(X0))
      | ~ l3_lattices(k1_lattice3(X0))
      | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))
      | ~ r3_orders_2(k3_lattice3(k1_lattice3(X0)),k4_lattice3(k1_lattice3(X0),X1),k4_lattice3(k1_lattice3(X0),X2))
      | r3_lattices(k1_lattice3(X0),X1,X2) ) ),
    inference(resolution,[],[f60,f51])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))
      | r3_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f72,plain,
    ( ~ r3_orders_2(k3_lattice3(k1_lattice3(sK0)),sK1,sK2)
    | ~ r1_tarski(sK1,sK2) ),
    inference(definition_unfolding,[],[f46,f49])).

fof(f46,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ r3_orders_2(k3_yellow_1(sK0),sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:17:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.49  % (12856)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.49  % (12848)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.49  % (12848)Refutation not found, incomplete strategy% (12848)------------------------------
% 0.22/0.49  % (12848)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (12848)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (12848)Memory used [KB]: 10618
% 0.22/0.49  % (12848)Time elapsed: 0.085 s
% 0.22/0.49  % (12848)------------------------------
% 0.22/0.49  % (12848)------------------------------
% 0.22/0.52  % (12842)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (12864)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.52  % (12842)Refutation not found, incomplete strategy% (12842)------------------------------
% 0.22/0.52  % (12842)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (12842)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (12842)Memory used [KB]: 6268
% 0.22/0.52  % (12842)Time elapsed: 0.115 s
% 0.22/0.52  % (12842)------------------------------
% 0.22/0.52  % (12842)------------------------------
% 0.22/0.53  % (12840)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (12860)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.53  % (12867)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.53  % (12844)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (12844)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f194,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(global_subsumption,[],[f72,f163,f193])).
% 0.22/0.54  fof(f193,plain,(
% 0.22/0.54    r3_orders_2(k3_lattice3(k1_lattice3(sK0)),sK1,sK2)),
% 0.22/0.54    inference(forward_demodulation,[],[f192,f104])).
% 0.22/0.54  % (12858)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.54  fof(f104,plain,(
% 0.22/0.54    sK1 = k4_lattice3(k1_lattice3(sK0),sK1)),
% 0.22/0.54    inference(resolution,[],[f101,f87])).
% 0.22/0.54  fof(f87,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) | k4_lattice3(k1_lattice3(X0),X1) = X1) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f86,f52])).
% 0.22/0.54  fof(f52,plain,(
% 0.22/0.54    ( ! [X0] : (l3_lattices(k1_lattice3(X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ! [X0] : l3_lattices(k1_lattice3(X0))),
% 0.22/0.54    inference(pure_predicate_removal,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0] : (l3_lattices(k1_lattice3(X0)) & v3_lattices(k1_lattice3(X0)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_lattice3)).
% 0.22/0.54  fof(f86,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~l3_lattices(k1_lattice3(X0)) | ~m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) | k4_lattice3(k1_lattice3(X0),X1) = X1) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f85,f50])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    ( ! [X0] : (~v2_struct_0(k1_lattice3(X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ! [X0] : ~v2_struct_0(k1_lattice3(X0))),
% 0.22/0.54    inference(pure_predicate_removal,[],[f10])).
% 0.22/0.54  fof(f10,axiom,(
% 0.22/0.54    ! [X0] : (v3_lattices(k1_lattice3(X0)) & ~v2_struct_0(k1_lattice3(X0)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_lattice3)).
% 0.22/0.54  fof(f85,plain,(
% 0.22/0.54    ( ! [X0,X1] : (v2_struct_0(k1_lattice3(X0)) | ~l3_lattices(k1_lattice3(X0)) | ~m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) | k4_lattice3(k1_lattice3(X0),X1) = X1) )),
% 0.22/0.54    inference(resolution,[],[f59,f51])).
% 0.22/0.54  fof(f51,plain,(
% 0.22/0.54    ( ! [X0] : (v10_lattices(k1_lattice3(X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ! [X0] : v10_lattices(k1_lattice3(X0))),
% 0.22/0.54    inference(pure_predicate_removal,[],[f11])).
% 0.22/0.54  fof(f11,axiom,(
% 0.22/0.54    ! [X0] : (v10_lattices(k1_lattice3(X0)) & v3_lattices(k1_lattice3(X0)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_lattice3)).
% 0.22/0.54  fof(f59,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | k4_lattice3(X0,X1) = X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f37])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (k4_lattice3(X0,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f36])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (k4_lattice3(X0,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k4_lattice3(X0,X1) = X1))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_lattice3)).
% 0.22/0.54  fof(f101,plain,(
% 0.22/0.54    m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0)))),
% 0.22/0.54    inference(backward_demodulation,[],[f70,f99])).
% 0.22/0.54  fof(f99,plain,(
% 0.22/0.54    ( ! [X0] : (u1_struct_0(k1_lattice3(X0)) = u1_struct_0(k3_lattice3(k1_lattice3(X0)))) )),
% 0.22/0.54    inference(equality_resolution,[],[f97])).
% 0.22/0.54  fof(f97,plain,(
% 0.22/0.54    ( ! [X2,X3] : (k3_lattice3(k1_lattice3(X2)) != k3_lattice3(k1_lattice3(X3)) | u1_struct_0(k3_lattice3(k1_lattice3(X2))) = u1_struct_0(k1_lattice3(X3))) )),
% 0.22/0.54    inference(superposition,[],[f92,f89])).
% 0.22/0.54  fof(f89,plain,(
% 0.22/0.54    ( ! [X0] : (k3_lattice3(k1_lattice3(X0)) = g1_orders_2(u1_struct_0(k3_lattice3(k1_lattice3(X0))),u1_orders_2(k3_lattice3(k1_lattice3(X0))))) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f88,f83])).
% 0.22/0.54  fof(f83,plain,(
% 0.22/0.54    ( ! [X0] : (l1_orders_2(k3_lattice3(k1_lattice3(X0)))) )),
% 0.22/0.54    inference(forward_demodulation,[],[f81,f77])).
% 0.22/0.54  fof(f77,plain,(
% 0.22/0.54    ( ! [X0] : (k3_lattice3(k1_lattice3(X0)) = g1_orders_2(u1_struct_0(k1_lattice3(X0)),k2_lattice3(k1_lattice3(X0)))) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f76,f52])).
% 0.22/0.54  fof(f76,plain,(
% 0.22/0.54    ( ! [X0] : (~l3_lattices(k1_lattice3(X0)) | k3_lattice3(k1_lattice3(X0)) = g1_orders_2(u1_struct_0(k1_lattice3(X0)),k2_lattice3(k1_lattice3(X0)))) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f75,f50])).
% 0.22/0.54  fof(f75,plain,(
% 0.22/0.54    ( ! [X0] : (v2_struct_0(k1_lattice3(X0)) | ~l3_lattices(k1_lattice3(X0)) | k3_lattice3(k1_lattice3(X0)) = g1_orders_2(u1_struct_0(k1_lattice3(X0)),k2_lattice3(k1_lattice3(X0)))) )),
% 0.22/0.54    inference(resolution,[],[f57,f51])).
% 0.22/0.54  fof(f57,plain,(
% 0.22/0.54    ( ! [X0] : (~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | k3_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k2_lattice3(X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f33])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ! [X0] : (k3_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k2_lattice3(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f32])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ! [X0] : (k3_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k2_lattice3(X0)) | (~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => k3_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k2_lattice3(X0)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_lattice3)).
% 0.22/0.54  fof(f81,plain,(
% 0.22/0.54    ( ! [X0] : (l1_orders_2(g1_orders_2(u1_struct_0(k1_lattice3(X0)),k2_lattice3(k1_lattice3(X0))))) )),
% 0.22/0.54    inference(resolution,[],[f80,f65])).
% 0.22/0.54  fof(f65,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | l1_orders_2(g1_orders_2(X0,X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f41])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    ! [X0,X1] : ((l1_orders_2(g1_orders_2(X0,X1)) & v1_orders_2(g1_orders_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 0.22/0.54    inference(ennf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => (l1_orders_2(g1_orders_2(X0,X1)) & v1_orders_2(g1_orders_2(X0,X1))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_orders_2)).
% 0.22/0.54  fof(f80,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(k2_lattice3(k1_lattice3(X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_lattice3(X0)),u1_struct_0(k1_lattice3(X0)))))) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f79,f52])).
% 0.22/0.54  fof(f79,plain,(
% 0.22/0.54    ( ! [X0] : (~l3_lattices(k1_lattice3(X0)) | m1_subset_1(k2_lattice3(k1_lattice3(X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_lattice3(X0)),u1_struct_0(k1_lattice3(X0)))))) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f78,f50])).
% 0.22/0.54  fof(f78,plain,(
% 0.22/0.54    ( ! [X0] : (v2_struct_0(k1_lattice3(X0)) | ~l3_lattices(k1_lattice3(X0)) | m1_subset_1(k2_lattice3(k1_lattice3(X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_lattice3(X0)),u1_struct_0(k1_lattice3(X0)))))) )),
% 0.22/0.54    inference(resolution,[],[f58,f51])).
% 0.22/0.54  fof(f58,plain,(
% 0.22/0.54    ( ! [X0] : (~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f35])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ! [X0] : (m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ! [X0] : (m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | (~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f20])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))))),
% 0.22/0.54    inference(pure_predicate_removal,[],[f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_partfun1(k2_lattice3(X0),u1_struct_0(X0))))),
% 0.22/0.54    inference(pure_predicate_removal,[],[f18])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_relat_2(k2_lattice3(X0)) & v1_partfun1(k2_lattice3(X0),u1_struct_0(X0))))),
% 0.22/0.54    inference(pure_predicate_removal,[],[f17])).
% 0.22/0.54  % (12847)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v4_relat_2(k2_lattice3(X0)) & v1_relat_2(k2_lattice3(X0)) & v1_partfun1(k2_lattice3(X0),u1_struct_0(X0))))),
% 0.22/0.54    inference(pure_predicate_removal,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v8_relat_2(k2_lattice3(X0)) & v4_relat_2(k2_lattice3(X0)) & v1_relat_2(k2_lattice3(X0)) & v1_partfun1(k2_lattice3(X0),u1_struct_0(X0))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_lattice3)).
% 0.22/0.54  fof(f88,plain,(
% 0.22/0.54    ( ! [X0] : (~l1_orders_2(k3_lattice3(k1_lattice3(X0))) | k3_lattice3(k1_lattice3(X0)) = g1_orders_2(u1_struct_0(k3_lattice3(k1_lattice3(X0))),u1_orders_2(k3_lattice3(k1_lattice3(X0))))) )),
% 0.22/0.54    inference(resolution,[],[f84,f53])).
% 0.22/0.54  fof(f53,plain,(
% 0.22/0.54    ( ! [X0] : (~v1_orders_2(X0) | ~l1_orders_2(X0) | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ! [X0] : (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 | ~v1_orders_2(X0) | ~l1_orders_2(X0))),
% 0.22/0.54    inference(flattening,[],[f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ! [X0] : ((g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 | ~v1_orders_2(X0)) | ~l1_orders_2(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0] : (l1_orders_2(X0) => (v1_orders_2(X0) => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_orders_2)).
% 0.22/0.54  fof(f84,plain,(
% 0.22/0.54    ( ! [X1] : (v1_orders_2(k3_lattice3(k1_lattice3(X1)))) )),
% 0.22/0.54    inference(forward_demodulation,[],[f82,f77])).
% 0.22/0.54  fof(f82,plain,(
% 0.22/0.54    ( ! [X1] : (v1_orders_2(g1_orders_2(u1_struct_0(k1_lattice3(X1)),k2_lattice3(k1_lattice3(X1))))) )),
% 0.22/0.54    inference(resolution,[],[f80,f64])).
% 0.22/0.54  fof(f64,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | v1_orders_2(g1_orders_2(X0,X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f41])).
% 0.22/0.54  fof(f92,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k3_lattice3(k1_lattice3(X0)) != g1_orders_2(X1,X2) | u1_struct_0(k1_lattice3(X0)) = X1) )),
% 0.22/0.54    inference(superposition,[],[f90,f77])).
% 0.22/0.54  fof(f90,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (g1_orders_2(u1_struct_0(k1_lattice3(X0)),k2_lattice3(k1_lattice3(X0))) != g1_orders_2(X1,X2) | u1_struct_0(k1_lattice3(X0)) = X1) )),
% 0.22/0.54    inference(resolution,[],[f66,f80])).
% 0.22/0.54  fof(f66,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | X0 = X2) )),
% 0.22/0.54    inference(cnf_transformation,[],[f42])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 0.22/0.54    inference(ennf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ! [X2,X3] : (g1_orders_2(X0,X1) = g1_orders_2(X2,X3) => (X1 = X3 & X0 = X2)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_orders_2)).
% 0.22/0.54  fof(f70,plain,(
% 0.22/0.54    m1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(sK0))))),
% 0.22/0.54    inference(definition_unfolding,[],[f48,f49])).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f14])).
% 0.22/0.54  fof(f14,axiom,(
% 0.22/0.54    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_yellow_1)).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0)))),
% 0.22/0.54    inference(cnf_transformation,[],[f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ? [X0,X1] : (? [X2] : ((r3_orders_2(k3_yellow_1(X0),X1,X2) <~> r1_tarski(X1,X2)) & m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))))),
% 0.22/0.54    inference(ennf_transformation,[],[f16])).
% 0.22/0.54  fof(f16,negated_conjecture,(
% 0.22/0.54    ~! [X0,X1] : (m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) => (r3_orders_2(k3_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2))))),
% 0.22/0.54    inference(negated_conjecture,[],[f15])).
% 0.22/0.54  fof(f15,conjecture,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) => (r3_orders_2(k3_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_yellow_1)).
% 0.22/0.54  fof(f192,plain,(
% 0.22/0.54    r3_orders_2(k3_lattice3(k1_lattice3(sK0)),k4_lattice3(k1_lattice3(sK0),sK1),sK2)),
% 0.22/0.54    inference(forward_demodulation,[],[f191,f103])).
% 0.22/0.54  fof(f103,plain,(
% 0.22/0.54    sK2 = k4_lattice3(k1_lattice3(sK0),sK2)),
% 0.22/0.54    inference(resolution,[],[f100,f87])).
% 0.22/0.54  fof(f100,plain,(
% 0.22/0.54    m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0)))),
% 0.22/0.54    inference(backward_demodulation,[],[f71,f99])).
% 0.22/0.54  fof(f71,plain,(
% 0.22/0.54    m1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(sK0))))),
% 0.22/0.54    inference(definition_unfolding,[],[f47,f49])).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK0)))),
% 0.22/0.54    inference(cnf_transformation,[],[f27])).
% 0.22/0.54  fof(f191,plain,(
% 0.22/0.54    r3_orders_2(k3_lattice3(k1_lattice3(sK0)),k4_lattice3(k1_lattice3(sK0),sK1),k4_lattice3(k1_lattice3(sK0),sK2))),
% 0.22/0.54    inference(subsumption_resolution,[],[f190,f50])).
% 0.22/0.54  fof(f190,plain,(
% 0.22/0.54    r3_orders_2(k3_lattice3(k1_lattice3(sK0)),k4_lattice3(k1_lattice3(sK0),sK1),k4_lattice3(k1_lattice3(sK0),sK2)) | v2_struct_0(k1_lattice3(sK0))),
% 0.22/0.54    inference(subsumption_resolution,[],[f189,f100])).
% 0.22/0.54  fof(f189,plain,(
% 0.22/0.54    ~m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0))) | r3_orders_2(k3_lattice3(k1_lattice3(sK0)),k4_lattice3(k1_lattice3(sK0),sK1),k4_lattice3(k1_lattice3(sK0),sK2)) | v2_struct_0(k1_lattice3(sK0))),
% 0.22/0.54    inference(subsumption_resolution,[],[f188,f101])).
% 0.22/0.54  fof(f188,plain,(
% 0.22/0.54    ~m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0))) | ~m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0))) | r3_orders_2(k3_lattice3(k1_lattice3(sK0)),k4_lattice3(k1_lattice3(sK0),sK1),k4_lattice3(k1_lattice3(sK0),sK2)) | v2_struct_0(k1_lattice3(sK0))),
% 0.22/0.54    inference(subsumption_resolution,[],[f187,f52])).
% 0.22/0.54  fof(f187,plain,(
% 0.22/0.54    ~l3_lattices(k1_lattice3(sK0)) | ~m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0))) | ~m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0))) | r3_orders_2(k3_lattice3(k1_lattice3(sK0)),k4_lattice3(k1_lattice3(sK0),sK1),k4_lattice3(k1_lattice3(sK0),sK2)) | v2_struct_0(k1_lattice3(sK0))),
% 0.22/0.54    inference(subsumption_resolution,[],[f185,f51])).
% 0.22/0.54  fof(f185,plain,(
% 0.22/0.54    ~v10_lattices(k1_lattice3(sK0)) | ~l3_lattices(k1_lattice3(sK0)) | ~m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0))) | ~m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0))) | r3_orders_2(k3_lattice3(k1_lattice3(sK0)),k4_lattice3(k1_lattice3(sK0),sK1),k4_lattice3(k1_lattice3(sK0),sK2)) | v2_struct_0(k1_lattice3(sK0))),
% 0.22/0.54    inference(resolution,[],[f184,f61])).
% 0.22/0.54  % (12865)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  fof(f61,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r3_lattices(X0,X1,X2) | ~v10_lattices(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2)) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f39])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : ((r3_lattices(X0,X1,X2) <=> r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f38])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : ((r3_lattices(X0,X1,X2) <=> r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f13])).
% 0.22/0.54  fof(f13,axiom,(
% 0.22/0.54    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_lattice3)).
% 0.22/0.54  fof(f184,plain,(
% 0.22/0.54    r3_lattices(k1_lattice3(sK0),sK1,sK2)),
% 0.22/0.54    inference(subsumption_resolution,[],[f183,f52])).
% 0.22/0.54  fof(f183,plain,(
% 0.22/0.54    r3_lattices(k1_lattice3(sK0),sK1,sK2) | ~l3_lattices(k1_lattice3(sK0))),
% 0.22/0.54    inference(subsumption_resolution,[],[f182,f51])).
% 0.22/0.54  fof(f182,plain,(
% 0.22/0.54    r3_lattices(k1_lattice3(sK0),sK1,sK2) | ~v10_lattices(k1_lattice3(sK0)) | ~l3_lattices(k1_lattice3(sK0))),
% 0.22/0.54    inference(subsumption_resolution,[],[f181,f50])).
% 0.22/0.54  fof(f181,plain,(
% 0.22/0.54    r3_lattices(k1_lattice3(sK0),sK1,sK2) | v2_struct_0(k1_lattice3(sK0)) | ~v10_lattices(k1_lattice3(sK0)) | ~l3_lattices(k1_lattice3(sK0))),
% 0.22/0.54    inference(resolution,[],[f180,f54])).
% 0.22/0.54  fof(f54,plain,(
% 0.22/0.54    ( ! [X0] : (v6_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | ~l3_lattices(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f31])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.22/0.54    inference(flattening,[],[f30])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0))))),
% 0.22/0.54    inference(pure_predicate_removal,[],[f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.22/0.54    inference(pure_predicate_removal,[],[f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.22/0.54    inference(pure_predicate_removal,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).
% 0.22/0.54  fof(f180,plain,(
% 0.22/0.54    ~v6_lattices(k1_lattice3(sK0)) | r3_lattices(k1_lattice3(sK0),sK1,sK2)),
% 0.22/0.54    inference(subsumption_resolution,[],[f179,f52])).
% 0.22/0.54  fof(f179,plain,(
% 0.22/0.54    ~v6_lattices(k1_lattice3(sK0)) | r3_lattices(k1_lattice3(sK0),sK1,sK2) | ~l3_lattices(k1_lattice3(sK0))),
% 0.22/0.54    inference(subsumption_resolution,[],[f178,f51])).
% 0.22/0.54  fof(f178,plain,(
% 0.22/0.54    ~v6_lattices(k1_lattice3(sK0)) | r3_lattices(k1_lattice3(sK0),sK1,sK2) | ~v10_lattices(k1_lattice3(sK0)) | ~l3_lattices(k1_lattice3(sK0))),
% 0.22/0.54    inference(subsumption_resolution,[],[f177,f50])).
% 0.22/0.54  fof(f177,plain,(
% 0.22/0.54    ~v6_lattices(k1_lattice3(sK0)) | r3_lattices(k1_lattice3(sK0),sK1,sK2) | v2_struct_0(k1_lattice3(sK0)) | ~v10_lattices(k1_lattice3(sK0)) | ~l3_lattices(k1_lattice3(sK0))),
% 0.22/0.54    inference(resolution,[],[f176,f55])).
% 0.22/0.54  fof(f55,plain,(
% 0.22/0.54    ( ! [X0] : (v8_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | ~l3_lattices(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f31])).
% 0.22/0.54  fof(f176,plain,(
% 0.22/0.54    ~v8_lattices(k1_lattice3(sK0)) | ~v6_lattices(k1_lattice3(sK0)) | r3_lattices(k1_lattice3(sK0),sK1,sK2)),
% 0.22/0.54    inference(subsumption_resolution,[],[f175,f52])).
% 0.22/0.54  fof(f175,plain,(
% 0.22/0.54    ~v8_lattices(k1_lattice3(sK0)) | ~v6_lattices(k1_lattice3(sK0)) | r3_lattices(k1_lattice3(sK0),sK1,sK2) | ~l3_lattices(k1_lattice3(sK0))),
% 0.22/0.54    inference(subsumption_resolution,[],[f174,f51])).
% 0.22/0.54  fof(f174,plain,(
% 0.22/0.54    ~v8_lattices(k1_lattice3(sK0)) | ~v6_lattices(k1_lattice3(sK0)) | r3_lattices(k1_lattice3(sK0),sK1,sK2) | ~v10_lattices(k1_lattice3(sK0)) | ~l3_lattices(k1_lattice3(sK0))),
% 0.22/0.54    inference(subsumption_resolution,[],[f173,f50])).
% 0.22/0.54  fof(f173,plain,(
% 0.22/0.54    ~v8_lattices(k1_lattice3(sK0)) | ~v6_lattices(k1_lattice3(sK0)) | r3_lattices(k1_lattice3(sK0),sK1,sK2) | v2_struct_0(k1_lattice3(sK0)) | ~v10_lattices(k1_lattice3(sK0)) | ~l3_lattices(k1_lattice3(sK0))),
% 0.22/0.54    inference(resolution,[],[f172,f56])).
% 0.22/0.54  fof(f56,plain,(
% 0.22/0.54    ( ! [X0] : (v9_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | ~l3_lattices(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f31])).
% 0.22/0.54  fof(f172,plain,(
% 0.22/0.54    ~v9_lattices(k1_lattice3(sK0)) | ~v8_lattices(k1_lattice3(sK0)) | ~v6_lattices(k1_lattice3(sK0)) | r3_lattices(k1_lattice3(sK0),sK1,sK2)),
% 0.22/0.54    inference(subsumption_resolution,[],[f171,f50])).
% 0.22/0.54  fof(f171,plain,(
% 0.22/0.54    ~v6_lattices(k1_lattice3(sK0)) | ~v8_lattices(k1_lattice3(sK0)) | ~v9_lattices(k1_lattice3(sK0)) | v2_struct_0(k1_lattice3(sK0)) | r3_lattices(k1_lattice3(sK0),sK1,sK2)),
% 0.22/0.54    inference(subsumption_resolution,[],[f170,f100])).
% 0.22/0.54  fof(f170,plain,(
% 0.22/0.54    ~v6_lattices(k1_lattice3(sK0)) | ~v8_lattices(k1_lattice3(sK0)) | ~v9_lattices(k1_lattice3(sK0)) | ~m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0))) | v2_struct_0(k1_lattice3(sK0)) | r3_lattices(k1_lattice3(sK0),sK1,sK2)),
% 0.22/0.54    inference(subsumption_resolution,[],[f169,f101])).
% 0.22/0.54  fof(f169,plain,(
% 0.22/0.54    ~v6_lattices(k1_lattice3(sK0)) | ~v8_lattices(k1_lattice3(sK0)) | ~v9_lattices(k1_lattice3(sK0)) | ~m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0))) | ~m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0))) | v2_struct_0(k1_lattice3(sK0)) | r3_lattices(k1_lattice3(sK0),sK1,sK2)),
% 0.22/0.54    inference(subsumption_resolution,[],[f168,f52])).
% 0.22/0.54  fof(f168,plain,(
% 0.22/0.54    ~v6_lattices(k1_lattice3(sK0)) | ~v8_lattices(k1_lattice3(sK0)) | ~v9_lattices(k1_lattice3(sK0)) | ~l3_lattices(k1_lattice3(sK0)) | ~m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0))) | ~m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0))) | v2_struct_0(k1_lattice3(sK0)) | r3_lattices(k1_lattice3(sK0),sK1,sK2)),
% 0.22/0.54    inference(resolution,[],[f166,f68])).
% 0.22/0.54  fof(f68,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r1_lattices(X0,X1,X2) | ~v6_lattices(X0) | ~v8_lattices(X0) | ~v9_lattices(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(X0) | r3_lattices(X0,X1,X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f44])).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f43])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).
% 0.22/0.54  fof(f166,plain,(
% 0.22/0.54    r1_lattices(k1_lattice3(sK0),sK1,sK2)),
% 0.22/0.54    inference(subsumption_resolution,[],[f165,f101])).
% 0.22/0.54  fof(f165,plain,(
% 0.22/0.54    ~m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0))) | r1_lattices(k1_lattice3(sK0),sK1,sK2)),
% 0.22/0.54    inference(resolution,[],[f164,f100])).
% 0.22/0.54  fof(f164,plain,(
% 0.22/0.54    ( ! [X0] : (~m1_subset_1(sK2,u1_struct_0(k1_lattice3(X0))) | ~m1_subset_1(sK1,u1_struct_0(k1_lattice3(X0))) | r1_lattices(k1_lattice3(X0),sK1,sK2)) )),
% 0.22/0.54    inference(resolution,[],[f163,f62])).
% 0.22/0.54  fof(f62,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | ~m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) | ~m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) | r1_lattices(k1_lattice3(X0),X1,X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f40])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    ! [X0,X1] : (! [X2] : ((r1_lattices(k1_lattice3(X0),X1,X2) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))) | ~m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))))),
% 0.22/0.54    inference(ennf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,axiom,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) => (r1_lattices(k1_lattice3(X0),X1,X2) <=> r1_tarski(X1,X2))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_lattice3)).
% 0.22/0.54  fof(f163,plain,(
% 0.22/0.54    r1_tarski(sK1,sK2)),
% 0.22/0.54    inference(subsumption_resolution,[],[f162,f101])).
% 0.22/0.54  fof(f162,plain,(
% 0.22/0.54    r1_tarski(sK1,sK2) | ~m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0)))),
% 0.22/0.54    inference(subsumption_resolution,[],[f161,f100])).
% 0.22/0.54  fof(f161,plain,(
% 0.22/0.54    r1_tarski(sK1,sK2) | ~m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0))) | ~m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0)))),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f159])).
% 0.22/0.54  fof(f159,plain,(
% 0.22/0.54    r1_tarski(sK1,sK2) | ~m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0))) | r1_tarski(sK1,sK2) | ~m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0)))),
% 0.22/0.54    inference(resolution,[],[f158,f63])).
% 0.22/0.54  fof(f63,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r1_lattices(k1_lattice3(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) | r1_tarski(X1,X2) | ~m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f40])).
% 0.22/0.54  fof(f158,plain,(
% 0.22/0.54    r1_lattices(k1_lattice3(sK0),sK1,sK2) | r1_tarski(sK1,sK2)),
% 0.22/0.54    inference(subsumption_resolution,[],[f157,f52])).
% 0.22/0.54  fof(f157,plain,(
% 0.22/0.54    r1_tarski(sK1,sK2) | r1_lattices(k1_lattice3(sK0),sK1,sK2) | ~l3_lattices(k1_lattice3(sK0))),
% 0.22/0.54    inference(subsumption_resolution,[],[f156,f51])).
% 0.22/0.54  fof(f156,plain,(
% 0.22/0.54    r1_tarski(sK1,sK2) | r1_lattices(k1_lattice3(sK0),sK1,sK2) | ~v10_lattices(k1_lattice3(sK0)) | ~l3_lattices(k1_lattice3(sK0))),
% 0.22/0.54    inference(subsumption_resolution,[],[f155,f50])).
% 0.22/0.54  fof(f155,plain,(
% 0.22/0.54    r1_tarski(sK1,sK2) | r1_lattices(k1_lattice3(sK0),sK1,sK2) | v2_struct_0(k1_lattice3(sK0)) | ~v10_lattices(k1_lattice3(sK0)) | ~l3_lattices(k1_lattice3(sK0))),
% 0.22/0.54    inference(resolution,[],[f154,f54])).
% 0.22/0.54  fof(f154,plain,(
% 0.22/0.54    ~v6_lattices(k1_lattice3(sK0)) | r1_tarski(sK1,sK2) | r1_lattices(k1_lattice3(sK0),sK1,sK2)),
% 0.22/0.54    inference(subsumption_resolution,[],[f153,f52])).
% 0.22/0.54  fof(f153,plain,(
% 0.22/0.54    ~v6_lattices(k1_lattice3(sK0)) | r1_tarski(sK1,sK2) | r1_lattices(k1_lattice3(sK0),sK1,sK2) | ~l3_lattices(k1_lattice3(sK0))),
% 0.22/0.54    inference(subsumption_resolution,[],[f152,f51])).
% 0.22/0.54  fof(f152,plain,(
% 0.22/0.54    ~v6_lattices(k1_lattice3(sK0)) | r1_tarski(sK1,sK2) | r1_lattices(k1_lattice3(sK0),sK1,sK2) | ~v10_lattices(k1_lattice3(sK0)) | ~l3_lattices(k1_lattice3(sK0))),
% 0.22/0.54    inference(subsumption_resolution,[],[f151,f50])).
% 0.22/0.54  fof(f151,plain,(
% 0.22/0.54    ~v6_lattices(k1_lattice3(sK0)) | r1_tarski(sK1,sK2) | r1_lattices(k1_lattice3(sK0),sK1,sK2) | v2_struct_0(k1_lattice3(sK0)) | ~v10_lattices(k1_lattice3(sK0)) | ~l3_lattices(k1_lattice3(sK0))),
% 0.22/0.54    inference(resolution,[],[f150,f55])).
% 0.22/0.54  fof(f150,plain,(
% 0.22/0.54    ~v8_lattices(k1_lattice3(sK0)) | ~v6_lattices(k1_lattice3(sK0)) | r1_tarski(sK1,sK2) | r1_lattices(k1_lattice3(sK0),sK1,sK2)),
% 0.22/0.54    inference(subsumption_resolution,[],[f149,f52])).
% 0.22/0.54  fof(f149,plain,(
% 0.22/0.54    ~v6_lattices(k1_lattice3(sK0)) | ~v8_lattices(k1_lattice3(sK0)) | r1_tarski(sK1,sK2) | r1_lattices(k1_lattice3(sK0),sK1,sK2) | ~l3_lattices(k1_lattice3(sK0))),
% 0.22/0.54    inference(subsumption_resolution,[],[f148,f51])).
% 0.22/0.54  fof(f148,plain,(
% 0.22/0.54    ~v6_lattices(k1_lattice3(sK0)) | ~v8_lattices(k1_lattice3(sK0)) | r1_tarski(sK1,sK2) | r1_lattices(k1_lattice3(sK0),sK1,sK2) | ~v10_lattices(k1_lattice3(sK0)) | ~l3_lattices(k1_lattice3(sK0))),
% 0.22/0.54    inference(subsumption_resolution,[],[f147,f50])).
% 0.22/0.54  fof(f147,plain,(
% 0.22/0.54    ~v6_lattices(k1_lattice3(sK0)) | ~v8_lattices(k1_lattice3(sK0)) | r1_tarski(sK1,sK2) | r1_lattices(k1_lattice3(sK0),sK1,sK2) | v2_struct_0(k1_lattice3(sK0)) | ~v10_lattices(k1_lattice3(sK0)) | ~l3_lattices(k1_lattice3(sK0))),
% 0.22/0.54    inference(resolution,[],[f142,f56])).
% 0.22/0.54  fof(f142,plain,(
% 0.22/0.54    ~v9_lattices(k1_lattice3(sK0)) | ~v6_lattices(k1_lattice3(sK0)) | ~v8_lattices(k1_lattice3(sK0)) | r1_tarski(sK1,sK2) | r1_lattices(k1_lattice3(sK0),sK1,sK2)),
% 0.22/0.54    inference(subsumption_resolution,[],[f141,f50])).
% 0.22/0.54  fof(f141,plain,(
% 0.22/0.54    r1_tarski(sK1,sK2) | ~v6_lattices(k1_lattice3(sK0)) | ~v8_lattices(k1_lattice3(sK0)) | ~v9_lattices(k1_lattice3(sK0)) | r1_lattices(k1_lattice3(sK0),sK1,sK2) | v2_struct_0(k1_lattice3(sK0))),
% 0.22/0.54    inference(subsumption_resolution,[],[f140,f100])).
% 0.22/0.54  fof(f140,plain,(
% 0.22/0.54    r1_tarski(sK1,sK2) | ~v6_lattices(k1_lattice3(sK0)) | ~v8_lattices(k1_lattice3(sK0)) | ~v9_lattices(k1_lattice3(sK0)) | ~m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0))) | r1_lattices(k1_lattice3(sK0),sK1,sK2) | v2_struct_0(k1_lattice3(sK0))),
% 0.22/0.54    inference(subsumption_resolution,[],[f139,f101])).
% 0.22/0.54  fof(f139,plain,(
% 0.22/0.54    r1_tarski(sK1,sK2) | ~v6_lattices(k1_lattice3(sK0)) | ~v8_lattices(k1_lattice3(sK0)) | ~v9_lattices(k1_lattice3(sK0)) | ~m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0))) | ~m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0))) | r1_lattices(k1_lattice3(sK0),sK1,sK2) | v2_struct_0(k1_lattice3(sK0))),
% 0.22/0.54    inference(subsumption_resolution,[],[f131,f52])).
% 0.22/0.54  fof(f131,plain,(
% 0.22/0.54    r1_tarski(sK1,sK2) | ~v6_lattices(k1_lattice3(sK0)) | ~v8_lattices(k1_lattice3(sK0)) | ~v9_lattices(k1_lattice3(sK0)) | ~l3_lattices(k1_lattice3(sK0)) | ~m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0))) | ~m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0))) | r1_lattices(k1_lattice3(sK0),sK1,sK2) | v2_struct_0(k1_lattice3(sK0))),
% 0.22/0.54    inference(resolution,[],[f129,f69])).
% 0.22/0.54  fof(f69,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r3_lattices(X0,X1,X2) | ~v6_lattices(X0) | ~v8_lattices(X0) | ~v9_lattices(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_lattices(X0,X1,X2) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f44])).
% 0.22/0.54  fof(f129,plain,(
% 0.22/0.54    r3_lattices(k1_lattice3(sK0),sK1,sK2) | r1_tarski(sK1,sK2)),
% 0.22/0.54    inference(resolution,[],[f128,f73])).
% 0.22/0.54  fof(f73,plain,(
% 0.22/0.54    r3_orders_2(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) | r1_tarski(sK1,sK2)),
% 0.22/0.54    inference(definition_unfolding,[],[f45,f49])).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    r1_tarski(sK1,sK2) | r3_orders_2(k3_yellow_1(sK0),sK1,sK2)),
% 0.22/0.54    inference(cnf_transformation,[],[f27])).
% 0.22/0.54  fof(f128,plain,(
% 0.22/0.54    ~r3_orders_2(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) | r3_lattices(k1_lattice3(sK0),sK1,sK2)),
% 0.22/0.54    inference(subsumption_resolution,[],[f126,f101])).
% 0.22/0.54  fof(f126,plain,(
% 0.22/0.54    ~r3_orders_2(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) | ~m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0))) | r3_lattices(k1_lattice3(sK0),sK1,sK2)),
% 0.22/0.54    inference(superposition,[],[f123,f104])).
% 0.22/0.54  fof(f123,plain,(
% 0.22/0.54    ( ! [X0] : (~r3_orders_2(k3_lattice3(k1_lattice3(sK0)),k4_lattice3(k1_lattice3(sK0),X0),sK2) | ~m1_subset_1(X0,u1_struct_0(k1_lattice3(sK0))) | r3_lattices(k1_lattice3(sK0),X0,sK2)) )),
% 0.22/0.54    inference(forward_demodulation,[],[f121,f103])).
% 0.22/0.54  fof(f121,plain,(
% 0.22/0.54    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(k1_lattice3(sK0))) | ~r3_orders_2(k3_lattice3(k1_lattice3(sK0)),k4_lattice3(k1_lattice3(sK0),X0),k4_lattice3(k1_lattice3(sK0),sK2)) | r3_lattices(k1_lattice3(sK0),X0,sK2)) )),
% 0.22/0.54    inference(resolution,[],[f120,f100])).
% 0.22/0.54  fof(f120,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) | ~m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) | ~r3_orders_2(k3_lattice3(k1_lattice3(X0)),k4_lattice3(k1_lattice3(X0),X1),k4_lattice3(k1_lattice3(X0),X2)) | r3_lattices(k1_lattice3(X0),X1,X2)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f119,f52])).
% 0.22/0.54  fof(f119,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~l3_lattices(k1_lattice3(X0)) | ~m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) | ~m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) | ~r3_orders_2(k3_lattice3(k1_lattice3(X0)),k4_lattice3(k1_lattice3(X0),X1),k4_lattice3(k1_lattice3(X0),X2)) | r3_lattices(k1_lattice3(X0),X1,X2)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f118,f50])).
% 0.22/0.54  fof(f118,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (v2_struct_0(k1_lattice3(X0)) | ~l3_lattices(k1_lattice3(X0)) | ~m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) | ~m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) | ~r3_orders_2(k3_lattice3(k1_lattice3(X0)),k4_lattice3(k1_lattice3(X0),X1),k4_lattice3(k1_lattice3(X0),X2)) | r3_lattices(k1_lattice3(X0),X1,X2)) )),
% 0.22/0.54    inference(resolution,[],[f60,f51])).
% 0.22/0.54  fof(f60,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2)) | r3_lattices(X0,X1,X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f39])).
% 0.22/0.54  fof(f72,plain,(
% 0.22/0.54    ~r3_orders_2(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) | ~r1_tarski(sK1,sK2)),
% 0.22/0.54    inference(definition_unfolding,[],[f46,f49])).
% 0.22/0.54  fof(f46,plain,(
% 0.22/0.54    ~r1_tarski(sK1,sK2) | ~r3_orders_2(k3_yellow_1(sK0),sK1,sK2)),
% 0.22/0.54    inference(cnf_transformation,[],[f27])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (12844)------------------------------
% 0.22/0.54  % (12844)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (12844)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (12844)Memory used [KB]: 6396
% 0.22/0.54  % (12844)Time elapsed: 0.097 s
% 0.22/0.54  % (12844)------------------------------
% 0.22/0.54  % (12844)------------------------------
% 0.22/0.54  % (12839)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (12847)Refutation not found, incomplete strategy% (12847)------------------------------
% 0.22/0.54  % (12847)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (12847)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (12847)Memory used [KB]: 10618
% 0.22/0.54  % (12847)Time elapsed: 0.128 s
% 0.22/0.54  % (12847)------------------------------
% 0.22/0.54  % (12847)------------------------------
% 0.22/0.54  % (12843)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (12858)Refutation not found, incomplete strategy% (12858)------------------------------
% 0.22/0.54  % (12858)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (12858)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (12858)Memory used [KB]: 10746
% 0.22/0.54  % (12858)Time elapsed: 0.139 s
% 0.22/0.54  % (12858)------------------------------
% 0.22/0.54  % (12858)------------------------------
% 0.22/0.54  % (12864)Refutation not found, incomplete strategy% (12864)------------------------------
% 0.22/0.54  % (12864)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (12864)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (12864)Memory used [KB]: 10746
% 0.22/0.54  % (12864)Time elapsed: 0.135 s
% 0.22/0.54  % (12864)------------------------------
% 0.22/0.54  % (12864)------------------------------
% 0.22/0.54  % (12841)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (12840)Refutation not found, incomplete strategy% (12840)------------------------------
% 0.22/0.54  % (12840)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (12840)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (12840)Memory used [KB]: 10746
% 0.22/0.54  % (12840)Time elapsed: 0.132 s
% 0.22/0.54  % (12840)------------------------------
% 0.22/0.54  % (12840)------------------------------
% 0.22/0.54  % (12866)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (12846)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.54  % (12838)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (12838)Refutation not found, incomplete strategy% (12838)------------------------------
% 0.22/0.54  % (12838)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (12838)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (12838)Memory used [KB]: 1663
% 0.22/0.54  % (12838)Time elapsed: 0.133 s
% 0.22/0.54  % (12838)------------------------------
% 0.22/0.54  % (12838)------------------------------
% 0.22/0.54  % (12846)Refutation not found, incomplete strategy% (12846)------------------------------
% 0.22/0.54  % (12846)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (12846)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (12846)Memory used [KB]: 10746
% 0.22/0.54  % (12846)Time elapsed: 0.133 s
% 0.22/0.54  % (12846)------------------------------
% 0.22/0.54  % (12846)------------------------------
% 0.22/0.54  % (12863)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.54  % (12837)Success in time 0.181 s
%------------------------------------------------------------------------------
