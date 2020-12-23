%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow_6__t12_yellow_6.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:54 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   39 (  64 expanded)
%              Number of leaves         :    8 (  17 expanded)
%              Depth                    :   10
%              Number of atoms          :   82 ( 139 expanded)
%              Number of equality atoms :   32 (  56 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f181,plain,(
    $false ),
    inference(subsumption_resolution,[],[f180,f50])).

fof(f50,plain,(
    u1_struct_0(sK0) != u1_struct_0(k7_lattice3(sK0)) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( u1_struct_0(sK0) != u1_struct_0(k7_lattice3(sK0))
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f43])).

fof(f43,plain,
    ( ? [X0] :
        ( u1_struct_0(X0) != u1_struct_0(k7_lattice3(X0))
        & l1_orders_2(X0) )
   => ( u1_struct_0(sK0) != u1_struct_0(k7_lattice3(sK0))
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != u1_struct_0(k7_lattice3(X0))
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => u1_struct_0(X0) = u1_struct_0(k7_lattice3(X0)) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => u1_struct_0(X0) = u1_struct_0(k7_lattice3(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t12_yellow_6.p',t12_yellow_6)).

fof(f180,plain,(
    u1_struct_0(sK0) = u1_struct_0(k7_lattice3(sK0)) ),
    inference(trivial_inequality_removal,[],[f178])).

fof(f178,plain,
    ( k7_lattice3(sK0) != k7_lattice3(sK0)
    | u1_struct_0(sK0) = u1_struct_0(k7_lattice3(sK0)) ),
    inference(superposition,[],[f174,f70])).

fof(f70,plain,(
    k7_lattice3(sK0) = g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0))) ),
    inference(subsumption_resolution,[],[f69,f68])).

fof(f68,plain,(
    l1_orders_2(k7_lattice3(sK0)) ),
    inference(resolution,[],[f49,f52])).

fof(f52,plain,(
    ! [X0] :
      ( l1_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( l1_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( l1_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t12_yellow_6.p',dt_k7_lattice3)).

fof(f49,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f69,plain,
    ( k7_lattice3(sK0) = g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0)))
    | ~ l1_orders_2(k7_lattice3(sK0)) ),
    inference(resolution,[],[f67,f57])).

fof(f57,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_orders_2(X0)
       => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t12_yellow_6.p',abstractness_v1_orders_2)).

fof(f67,plain,(
    v1_orders_2(k7_lattice3(sK0)) ),
    inference(resolution,[],[f49,f51])).

fof(f51,plain,(
    ! [X0] :
      ( v1_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f174,plain,(
    ! [X2,X3] :
      ( k7_lattice3(sK0) != g1_orders_2(X2,X3)
      | u1_struct_0(sK0) = X2 ) ),
    inference(subsumption_resolution,[],[f169,f116])).

fof(f116,plain,(
    m1_subset_1(k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(resolution,[],[f64,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t12_yellow_6.p',dt_k3_relset_1)).

fof(f64,plain,(
    m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(resolution,[],[f49,f62])).

fof(f62,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t12_yellow_6.p',dt_u1_orders_2)).

fof(f169,plain,(
    ! [X2,X3] :
      ( k7_lattice3(sK0) != g1_orders_2(X2,X3)
      | u1_struct_0(sK0) = X2
      | ~ m1_subset_1(k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ) ),
    inference(superposition,[],[f58,f66])).

fof(f66,plain,(
    k7_lattice3(sK0) = g1_orders_2(u1_struct_0(sK0),k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0))) ),
    inference(resolution,[],[f49,f53])).

fof(f53,plain,(
    ! [X0] :
      ( k7_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( k7_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k7_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t12_yellow_6.p',d5_lattice3)).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t12_yellow_6.p',free_g1_orders_2)).
%------------------------------------------------------------------------------
