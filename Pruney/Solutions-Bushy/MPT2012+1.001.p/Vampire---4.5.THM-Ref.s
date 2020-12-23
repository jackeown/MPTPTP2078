%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT2012+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:02 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   58 (  99 expanded)
%              Number of leaves         :   10 (  26 expanded)
%              Depth                    :   15
%              Number of atoms          :  168 ( 296 expanded)
%              Number of equality atoms :   60 ( 113 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f90,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f77,f80,f89])).

fof(f89,plain,(
    spl1_5 ),
    inference(avatar_contradiction_clause,[],[f88])).

fof(f88,plain,
    ( $false
    | spl1_5 ),
    inference(subsumption_resolution,[],[f87,f20])).

fof(f20,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0))) != g1_orders_2(u1_struct_0(k3_waybel_9(sK0)),u1_orders_2(k3_waybel_9(sK0)))
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f16])).

fof(f16,plain,
    ( ? [X0] :
        ( g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0))) != g1_orders_2(u1_struct_0(k3_waybel_9(X0)),u1_orders_2(k3_waybel_9(X0)))
        & l1_orders_2(X0) )
   => ( g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0))) != g1_orders_2(u1_struct_0(k3_waybel_9(sK0)),u1_orders_2(k3_waybel_9(sK0)))
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0))) != g1_orders_2(u1_struct_0(k3_waybel_9(X0)),u1_orders_2(k3_waybel_9(X0)))
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0))) = g1_orders_2(u1_struct_0(k3_waybel_9(X0)),u1_orders_2(k3_waybel_9(X0))) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0))) = g1_orders_2(u1_struct_0(k3_waybel_9(X0)),u1_orders_2(k3_waybel_9(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_waybel_9)).

fof(f87,plain,
    ( ~ l1_orders_2(sK0)
    | spl1_5 ),
    inference(resolution,[],[f61,f23])).

fof(f23,plain,(
    ! [X0] :
      ( v1_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( l1_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( l1_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_lattice3)).

fof(f61,plain,
    ( ~ v1_orders_2(k7_lattice3(sK0))
    | spl1_5 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl1_5
  <=> v1_orders_2(k7_lattice3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f80,plain,(
    spl1_4 ),
    inference(avatar_contradiction_clause,[],[f79])).

fof(f79,plain,
    ( $false
    | spl1_4 ),
    inference(subsumption_resolution,[],[f78,f20])).

fof(f78,plain,
    ( ~ l1_orders_2(sK0)
    | spl1_4 ),
    inference(resolution,[],[f58,f24])).

fof(f24,plain,(
    ! [X0] :
      ( l1_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f58,plain,
    ( ~ l1_orders_2(k7_lattice3(sK0))
    | spl1_4 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl1_4
  <=> l1_orders_2(k7_lattice3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f77,plain,(
    spl1_6 ),
    inference(avatar_contradiction_clause,[],[f76])).

fof(f76,plain,
    ( $false
    | spl1_6 ),
    inference(subsumption_resolution,[],[f75,f20])).

fof(f75,plain,
    ( ~ l1_orders_2(sK0)
    | spl1_6 ),
    inference(trivial_inequality_removal,[],[f74])).

fof(f74,plain,
    ( k7_lattice3(sK0) != k7_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | spl1_6 ),
    inference(superposition,[],[f64,f69])).

fof(f69,plain,(
    ! [X0] :
      ( k7_lattice3(X0) = g1_orders_2(u1_struct_0(X0),u1_orders_2(k3_waybel_9(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( k7_lattice3(X0) = g1_orders_2(u1_struct_0(X0),u1_orders_2(k3_waybel_9(X0)))
      | ~ l1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(superposition,[],[f22,f38])).

fof(f38,plain,(
    ! [X0] :
      ( k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0)) = u1_orders_2(k3_waybel_9(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f37,f25])).

fof(f25,plain,(
    ! [X0] :
      ( v6_waybel_0(k3_waybel_9(X0),X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( l1_waybel_0(k3_waybel_9(X0),X0)
        & v6_waybel_0(k3_waybel_9(X0),X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( l1_waybel_0(k3_waybel_9(X0),X0)
        & v6_waybel_0(k3_waybel_9(X0),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_waybel_9)).

fof(f37,plain,(
    ! [X0] :
      ( k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0)) = u1_orders_2(k3_waybel_9(X0))
      | ~ v6_waybel_0(k3_waybel_9(X0),X0)
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f33,f26])).

fof(f26,plain,(
    ! [X0] :
      ( l1_waybel_0(k3_waybel_9(X0),X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0] :
      ( k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0)) = u1_orders_2(k3_waybel_9(X0))
      | ~ l1_waybel_0(k3_waybel_9(X0),X0)
      | ~ v6_waybel_0(k3_waybel_9(X0),X0)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0)) = u1_orders_2(X1)
      | k3_waybel_9(X0) != X1
      | ~ l1_waybel_0(X1,X0)
      | ~ v6_waybel_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k3_waybel_9(X0) = X1
              | u1_waybel_0(X0,X1) != k3_struct_0(X0)
              | k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0)) != u1_orders_2(X1)
              | u1_struct_0(X0) != u1_struct_0(X1) )
            & ( ( u1_waybel_0(X0,X1) = k3_struct_0(X0)
                & k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0)) = u1_orders_2(X1)
                & u1_struct_0(X0) = u1_struct_0(X1) )
              | k3_waybel_9(X0) != X1 ) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v6_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k3_waybel_9(X0) = X1
              | u1_waybel_0(X0,X1) != k3_struct_0(X0)
              | k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0)) != u1_orders_2(X1)
              | u1_struct_0(X0) != u1_struct_0(X1) )
            & ( ( u1_waybel_0(X0,X1) = k3_struct_0(X0)
                & k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0)) = u1_orders_2(X1)
                & u1_struct_0(X0) = u1_struct_0(X1) )
              | k3_waybel_9(X0) != X1 ) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v6_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k3_waybel_9(X0) = X1
          <=> ( u1_waybel_0(X0,X1) = k3_struct_0(X0)
              & k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0)) = u1_orders_2(X1)
              & u1_struct_0(X0) = u1_struct_0(X1) ) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v6_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k3_waybel_9(X0) = X1
          <=> ( u1_waybel_0(X0,X1) = k3_struct_0(X0)
              & k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0)) = u1_orders_2(X1)
              & u1_struct_0(X0) = u1_struct_0(X1) ) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v6_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v6_waybel_0(X1,X0) )
         => ( k3_waybel_9(X0) = X1
          <=> ( u1_waybel_0(X0,X1) = k3_struct_0(X0)
              & k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0)) = u1_orders_2(X1)
              & u1_struct_0(X0) = u1_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_waybel_9)).

fof(f22,plain,(
    ! [X0] :
      ( k7_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f9])).

% (1706)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
fof(f9,plain,(
    ! [X0] :
      ( k7_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k7_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_lattice3)).

fof(f64,plain,
    ( k7_lattice3(sK0) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(k3_waybel_9(sK0)))
    | spl1_6 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl1_6
  <=> k7_lattice3(sK0) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(k3_waybel_9(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f65,plain,
    ( ~ spl1_4
    | ~ spl1_5
    | ~ spl1_6 ),
    inference(avatar_split_clause,[],[f45,f63,f60,f57])).

fof(f45,plain,
    ( k7_lattice3(sK0) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(k3_waybel_9(sK0)))
    | ~ v1_orders_2(k7_lattice3(sK0))
    | ~ l1_orders_2(k7_lattice3(sK0)) ),
    inference(superposition,[],[f42,f27])).

fof(f27,plain,(
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

fof(f42,plain,(
    g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0))) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(k3_waybel_9(sK0))) ),
    inference(subsumption_resolution,[],[f41,f20])).

fof(f41,plain,
    ( g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0))) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(k3_waybel_9(sK0)))
    | ~ l1_orders_2(sK0) ),
    inference(superposition,[],[f21,f40])).

fof(f40,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = u1_struct_0(k3_waybel_9(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f39,f25])).

fof(f39,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = u1_struct_0(k3_waybel_9(X0))
      | ~ v6_waybel_0(k3_waybel_9(X0),X0)
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f34,f26])).

fof(f34,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = u1_struct_0(k3_waybel_9(X0))
      | ~ l1_waybel_0(k3_waybel_9(X0),X0)
      | ~ v6_waybel_0(k3_waybel_9(X0),X0)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = u1_struct_0(X1)
      | k3_waybel_9(X0) != X1
      | ~ l1_waybel_0(X1,X0)
      | ~ v6_waybel_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f21,plain,(
    g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0))) != g1_orders_2(u1_struct_0(k3_waybel_9(sK0)),u1_orders_2(k3_waybel_9(sK0))) ),
    inference(cnf_transformation,[],[f17])).

%------------------------------------------------------------------------------
