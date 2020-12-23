%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1914+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:55 EST 2020

% Result     : Theorem 1.67s
% Output     : Refutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   35 (  64 expanded)
%              Number of leaves         :    7 (  17 expanded)
%              Depth                    :   12
%              Number of atoms          :   75 ( 141 expanded)
%              Number of equality atoms :   32 (  56 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f128,plain,(
    $false ),
    inference(subsumption_resolution,[],[f125,f18])).

fof(f18,plain,(
    u1_struct_0(sK0) != u1_struct_0(k7_lattice3(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( u1_struct_0(sK0) != u1_struct_0(k7_lattice3(sK0))
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f15])).

fof(f15,plain,
    ( ? [X0] :
        ( u1_struct_0(X0) != u1_struct_0(k7_lattice3(X0))
        & l1_orders_2(X0) )
   => ( u1_struct_0(sK0) != u1_struct_0(k7_lattice3(sK0))
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != u1_struct_0(k7_lattice3(X0))
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => u1_struct_0(X0) = u1_struct_0(k7_lattice3(X0)) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => u1_struct_0(X0) = u1_struct_0(k7_lattice3(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_yellow_6)).

fof(f125,plain,(
    u1_struct_0(sK0) = u1_struct_0(k7_lattice3(sK0)) ),
    inference(trivial_inequality_removal,[],[f120])).

fof(f120,plain,
    ( k7_lattice3(sK0) != k7_lattice3(sK0)
    | u1_struct_0(sK0) = u1_struct_0(k7_lattice3(sK0)) ),
    inference(superposition,[],[f86,f29])).

fof(f29,plain,(
    k7_lattice3(sK0) = g1_orders_2(u1_struct_0(sK0),k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0))) ),
    inference(resolution,[],[f17,f20])).

fof(f20,plain,(
    ! [X0] :
      ( k7_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k7_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k7_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_lattice3)).

fof(f17,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f86,plain,(
    ! [X2,X3] :
      ( g1_orders_2(X2,X3) != k7_lattice3(sK0)
      | u1_struct_0(k7_lattice3(sK0)) = X2 ) ),
    inference(subsumption_resolution,[],[f83,f37])).

fof(f37,plain,(
    m1_subset_1(u1_orders_2(k7_lattice3(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_lattice3(sK0)),u1_struct_0(k7_lattice3(sK0))))) ),
    inference(resolution,[],[f28,f19])).

fof(f19,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f28,plain,(
    l1_orders_2(k7_lattice3(sK0)) ),
    inference(resolution,[],[f17,f22])).

fof(f22,plain,(
    ! [X0] :
      ( l1_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( l1_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( l1_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_lattice3)).

fof(f83,plain,(
    ! [X2,X3] :
      ( g1_orders_2(X2,X3) != k7_lattice3(sK0)
      | u1_struct_0(k7_lattice3(sK0)) = X2
      | ~ m1_subset_1(u1_orders_2(k7_lattice3(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_lattice3(sK0)),u1_struct_0(k7_lattice3(sK0))))) ) ),
    inference(superposition,[],[f24,f32])).

fof(f32,plain,(
    k7_lattice3(sK0) = g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0))) ),
    inference(subsumption_resolution,[],[f31,f28])).

fof(f31,plain,
    ( k7_lattice3(sK0) = g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0)))
    | ~ l1_orders_2(k7_lattice3(sK0)) ),
    inference(resolution,[],[f27,f23])).

fof(f23,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_orders_2)).

fof(f27,plain,(
    v1_orders_2(k7_lattice3(sK0)) ),
    inference(resolution,[],[f17,f21])).

fof(f21,plain,(
    ! [X0] :
      ( v1_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).

%------------------------------------------------------------------------------
