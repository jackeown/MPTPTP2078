%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 236 expanded)
%              Number of leaves         :   16 (  72 expanded)
%              Depth                    :   14
%              Number of atoms          :  198 ( 564 expanded)
%              Number of equality atoms :   57 ( 188 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f153,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f51,f62,f96,f101,f118,f121,f152])).

fof(f152,plain,
    ( ~ spl1_2
    | ~ spl1_3
    | ~ spl1_7 ),
    inference(avatar_contradiction_clause,[],[f151])).

fof(f151,plain,
    ( $false
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_7 ),
    inference(subsumption_resolution,[],[f150,f22])).

fof(f22,plain,(
    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != k7_lattice3(k7_lattice3(sK0)) ),
    inference(cnf_transformation,[],[f20])).

% (30841)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
fof(f20,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != k7_lattice3(k7_lattice3(sK0))
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f19])).

fof(f19,plain,
    ( ? [X0] :
        ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != k7_lattice3(k7_lattice3(X0))
        & l1_orders_2(X0) )
   => ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != k7_lattice3(k7_lattice3(sK0))
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != k7_lattice3(k7_lattice3(X0))
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = k7_lattice3(k7_lattice3(X0)) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = k7_lattice3(k7_lattice3(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_lattice3)).

fof(f150,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = k7_lattice3(k7_lattice3(sK0))
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_7 ),
    inference(forward_demodulation,[],[f149,f117])).

fof(f117,plain,
    ( u1_orders_2(sK0) = k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(k7_lattice3(sK0)))
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl1_7
  <=> u1_orders_2(sK0) = k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(k7_lattice3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f149,plain,
    ( k7_lattice3(k7_lattice3(sK0)) = g1_orders_2(u1_struct_0(sK0),k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(k7_lattice3(sK0))))
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(forward_demodulation,[],[f64,f79])).

fof(f79,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k7_lattice3(sK0))
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(subsumption_resolution,[],[f75,f45])).

fof(f45,plain,
    ( l1_orders_2(k7_lattice3(sK0))
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl1_2
  <=> l1_orders_2(k7_lattice3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f75,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k7_lattice3(sK0))
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(trivial_inequality_removal,[],[f69])).

fof(f69,plain,
    ( k7_lattice3(sK0) != k7_lattice3(sK0)
    | u1_struct_0(sK0) = u1_struct_0(k7_lattice3(sK0))
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(superposition,[],[f54,f66])).

fof(f66,plain,
    ( k7_lattice3(sK0) = g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0)))
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(subsumption_resolution,[],[f65,f45])).

fof(f65,plain,
    ( k7_lattice3(sK0) = g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0)))
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ spl1_3 ),
    inference(resolution,[],[f50,f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_orders_2(X0)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_orders_2)).

fof(f50,plain,
    ( v1_orders_2(k7_lattice3(sK0))
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl1_3
  <=> v1_orders_2(k7_lattice3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f54,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != k7_lattice3(sK0)
      | u1_struct_0(X0) = u1_struct_0(sK0)
      | ~ l1_orders_2(X0) ) ),
    inference(superposition,[],[f53,f34])).

fof(f34,plain,(
    k7_lattice3(sK0) = g1_orders_2(u1_struct_0(sK0),k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0))) ),
    inference(resolution,[],[f24,f21])).

fof(f21,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f24,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | k7_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k7_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k7_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_lattice3)).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2)
      | u1_struct_0(X0) = X1
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f28,f23])).

fof(f23,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(f64,plain,
    ( k7_lattice3(k7_lattice3(sK0)) = g1_orders_2(u1_struct_0(k7_lattice3(sK0)),k3_relset_1(u1_struct_0(k7_lattice3(sK0)),u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0))))
    | ~ spl1_2 ),
    inference(resolution,[],[f45,f24])).

fof(f121,plain,(
    spl1_6 ),
    inference(avatar_contradiction_clause,[],[f120])).

fof(f120,plain,
    ( $false
    | spl1_6 ),
    inference(subsumption_resolution,[],[f119,f21])).

fof(f119,plain,
    ( ~ l1_orders_2(sK0)
    | spl1_6 ),
    inference(resolution,[],[f113,f23])).

fof(f113,plain,
    ( ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | spl1_6 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl1_6
  <=> m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f118,plain,
    ( ~ spl1_6
    | spl1_7
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f109,f89,f115,f111])).

% (30842)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
fof(f89,plain,
    ( spl1_4
  <=> k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0)) = u1_orders_2(k7_lattice3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f109,plain,
    ( u1_orders_2(sK0) = k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(k7_lattice3(sK0)))
    | ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl1_4 ),
    inference(superposition,[],[f30,f91])).

fof(f91,plain,
    ( k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0)) = u1_orders_2(k7_lattice3(sK0))
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f89])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k3_relset_1(X0,X1,k3_relset_1(X0,X1,X2)) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k3_relset_1(X0,X1,k3_relset_1(X0,X1,X2)) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k3_relset_1(X0,X1,k3_relset_1(X0,X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_relset_1)).

fof(f101,plain,
    ( ~ spl1_2
    | ~ spl1_3
    | spl1_5 ),
    inference(avatar_contradiction_clause,[],[f100])).

fof(f100,plain,
    ( $false
    | ~ spl1_2
    | ~ spl1_3
    | spl1_5 ),
    inference(subsumption_resolution,[],[f81,f95])).

fof(f95,plain,
    ( k7_lattice3(sK0) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(k7_lattice3(sK0)))
    | spl1_5 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl1_5
  <=> k7_lattice3(sK0) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(k7_lattice3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f81,plain,
    ( k7_lattice3(sK0) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(k7_lattice3(sK0)))
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(backward_demodulation,[],[f66,f79])).

fof(f96,plain,
    ( spl1_4
    | ~ spl1_5
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f87,f48,f43,f93,f89])).

% (30846)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f87,plain,
    ( k7_lattice3(sK0) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(k7_lattice3(sK0)))
    | k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0)) = u1_orders_2(k7_lattice3(sK0))
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(subsumption_resolution,[],[f82,f45])).

fof(f82,plain,
    ( k7_lattice3(sK0) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(k7_lattice3(sK0)))
    | k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0)) = u1_orders_2(k7_lattice3(sK0))
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(superposition,[],[f57,f79])).

fof(f57,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != k7_lattice3(sK0)
      | u1_orders_2(X0) = k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0))
      | ~ l1_orders_2(X0) ) ),
    inference(superposition,[],[f56,f34])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2)
      | u1_orders_2(X0) = X2
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f29,f23])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f62,plain,(
    spl1_1 ),
    inference(avatar_contradiction_clause,[],[f61])).

fof(f61,plain,
    ( $false
    | spl1_1 ),
    inference(subsumption_resolution,[],[f59,f41])).

fof(f41,plain,
    ( ~ m1_subset_1(k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | spl1_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl1_1
  <=> m1_subset_1(k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f59,plain,(
    m1_subset_1(k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(resolution,[],[f52,f21])).

fof(f52,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    inference(resolution,[],[f31,f23])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_relset_1)).

fof(f51,plain,
    ( ~ spl1_1
    | spl1_3 ),
    inference(avatar_split_clause,[],[f37,f48,f39])).

fof(f37,plain,
    ( v1_orders_2(k7_lattice3(sK0))
    | ~ m1_subset_1(k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(superposition,[],[f26,f34])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_orders_2(g1_orders_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( l1_orders_2(g1_orders_2(X0,X1))
        & v1_orders_2(g1_orders_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ( l1_orders_2(g1_orders_2(X0,X1))
        & v1_orders_2(g1_orders_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_orders_2)).

fof(f46,plain,
    ( ~ spl1_1
    | spl1_2 ),
    inference(avatar_split_clause,[],[f36,f43,f39])).

fof(f36,plain,
    ( l1_orders_2(k7_lattice3(sK0))
    | ~ m1_subset_1(k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(superposition,[],[f27,f34])).

fof(f27,plain,(
    ! [X0,X1] :
      ( l1_orders_2(g1_orders_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:01:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (30837)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (30836)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (30837)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (30852)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.51  % (30843)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f153,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f46,f51,f62,f96,f101,f118,f121,f152])).
% 0.21/0.51  fof(f152,plain,(
% 0.21/0.51    ~spl1_2 | ~spl1_3 | ~spl1_7),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f151])).
% 0.21/0.51  fof(f151,plain,(
% 0.21/0.51    $false | (~spl1_2 | ~spl1_3 | ~spl1_7)),
% 0.21/0.51    inference(subsumption_resolution,[],[f150,f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != k7_lattice3(k7_lattice3(sK0))),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  % (30841)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != k7_lattice3(k7_lattice3(sK0)) & l1_orders_2(sK0)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ? [X0] : (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != k7_lattice3(k7_lattice3(X0)) & l1_orders_2(X0)) => (g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != k7_lattice3(k7_lattice3(sK0)) & l1_orders_2(sK0))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ? [X0] : (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != k7_lattice3(k7_lattice3(X0)) & l1_orders_2(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,negated_conjecture,(
% 0.21/0.52    ~! [X0] : (l1_orders_2(X0) => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = k7_lattice3(k7_lattice3(X0)))),
% 0.21/0.52    inference(negated_conjecture,[],[f8])).
% 0.21/0.52  fof(f8,conjecture,(
% 0.21/0.52    ! [X0] : (l1_orders_2(X0) => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = k7_lattice3(k7_lattice3(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_lattice3)).
% 0.21/0.52  fof(f150,plain,(
% 0.21/0.52    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = k7_lattice3(k7_lattice3(sK0)) | (~spl1_2 | ~spl1_3 | ~spl1_7)),
% 0.21/0.52    inference(forward_demodulation,[],[f149,f117])).
% 0.21/0.52  fof(f117,plain,(
% 0.21/0.52    u1_orders_2(sK0) = k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(k7_lattice3(sK0))) | ~spl1_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f115])).
% 0.21/0.52  fof(f115,plain,(
% 0.21/0.52    spl1_7 <=> u1_orders_2(sK0) = k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(k7_lattice3(sK0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.21/0.52  fof(f149,plain,(
% 0.21/0.52    k7_lattice3(k7_lattice3(sK0)) = g1_orders_2(u1_struct_0(sK0),k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(k7_lattice3(sK0)))) | (~spl1_2 | ~spl1_3)),
% 0.21/0.52    inference(forward_demodulation,[],[f64,f79])).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    u1_struct_0(sK0) = u1_struct_0(k7_lattice3(sK0)) | (~spl1_2 | ~spl1_3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f75,f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    l1_orders_2(k7_lattice3(sK0)) | ~spl1_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    spl1_2 <=> l1_orders_2(k7_lattice3(sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    u1_struct_0(sK0) = u1_struct_0(k7_lattice3(sK0)) | ~l1_orders_2(k7_lattice3(sK0)) | (~spl1_2 | ~spl1_3)),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f69])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    k7_lattice3(sK0) != k7_lattice3(sK0) | u1_struct_0(sK0) = u1_struct_0(k7_lattice3(sK0)) | ~l1_orders_2(k7_lattice3(sK0)) | (~spl1_2 | ~spl1_3)),
% 0.21/0.52    inference(superposition,[],[f54,f66])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    k7_lattice3(sK0) = g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0))) | (~spl1_2 | ~spl1_3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f65,f45])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    k7_lattice3(sK0) = g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0))) | ~l1_orders_2(k7_lattice3(sK0)) | ~spl1_3),
% 0.21/0.52    inference(resolution,[],[f50,f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_orders_2(X0) | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 | ~l1_orders_2(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0] : (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 | ~v1_orders_2(X0) | ~l1_orders_2(X0))),
% 0.21/0.52    inference(flattening,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ! [X0] : ((g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 | ~v1_orders_2(X0)) | ~l1_orders_2(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0] : (l1_orders_2(X0) => (v1_orders_2(X0) => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_orders_2)).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    v1_orders_2(k7_lattice3(sK0)) | ~spl1_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    spl1_3 <=> v1_orders_2(k7_lattice3(sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ( ! [X0] : (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != k7_lattice3(sK0) | u1_struct_0(X0) = u1_struct_0(sK0) | ~l1_orders_2(X0)) )),
% 0.21/0.52    inference(superposition,[],[f53,f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    k7_lattice3(sK0) = g1_orders_2(u1_struct_0(sK0),k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0)))),
% 0.21/0.52    inference(resolution,[],[f24,f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    l1_orders_2(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ( ! [X0] : (~l1_orders_2(X0) | k7_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ! [X0] : (k7_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))) | ~l1_orders_2(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0] : (l1_orders_2(X0) => k7_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_lattice3)).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2) | u1_struct_0(X0) = X1 | ~l1_orders_2(X0)) )),
% 0.21/0.52    inference(resolution,[],[f28,f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ( ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0] : (l1_orders_2(X0) => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | X0 = X2) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ! [X2,X3] : (g1_orders_2(X0,X1) = g1_orders_2(X2,X3) => (X1 = X3 & X0 = X2)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_orders_2)).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    k7_lattice3(k7_lattice3(sK0)) = g1_orders_2(u1_struct_0(k7_lattice3(sK0)),k3_relset_1(u1_struct_0(k7_lattice3(sK0)),u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0)))) | ~spl1_2),
% 0.21/0.52    inference(resolution,[],[f45,f24])).
% 0.21/0.52  fof(f121,plain,(
% 0.21/0.52    spl1_6),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f120])).
% 0.21/0.52  fof(f120,plain,(
% 0.21/0.52    $false | spl1_6),
% 0.21/0.52    inference(subsumption_resolution,[],[f119,f21])).
% 0.21/0.52  fof(f119,plain,(
% 0.21/0.52    ~l1_orders_2(sK0) | spl1_6),
% 0.21/0.52    inference(resolution,[],[f113,f23])).
% 0.21/0.52  fof(f113,plain,(
% 0.21/0.52    ~m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | spl1_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f111])).
% 0.21/0.52  fof(f111,plain,(
% 0.21/0.52    spl1_6 <=> m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.21/0.52  fof(f118,plain,(
% 0.21/0.52    ~spl1_6 | spl1_7 | ~spl1_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f109,f89,f115,f111])).
% 0.21/0.52  % (30842)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  fof(f89,plain,(
% 0.21/0.52    spl1_4 <=> k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0)) = u1_orders_2(k7_lattice3(sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.21/0.52  fof(f109,plain,(
% 0.21/0.52    u1_orders_2(sK0) = k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(k7_lattice3(sK0))) | ~m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~spl1_4),
% 0.21/0.52    inference(superposition,[],[f30,f91])).
% 0.21/0.52  fof(f91,plain,(
% 0.21/0.52    k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0)) = u1_orders_2(k7_lattice3(sK0)) | ~spl1_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f89])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k3_relset_1(X0,X1,k3_relset_1(X0,X1,X2)) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k3_relset_1(X0,X1,k3_relset_1(X0,X1,X2)) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k3_relset_1(X0,X1,k3_relset_1(X0,X1,X2)) = X2)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_relset_1)).
% 0.21/0.52  fof(f101,plain,(
% 0.21/0.52    ~spl1_2 | ~spl1_3 | spl1_5),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f100])).
% 0.21/0.52  fof(f100,plain,(
% 0.21/0.52    $false | (~spl1_2 | ~spl1_3 | spl1_5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f81,f95])).
% 0.21/0.52  fof(f95,plain,(
% 0.21/0.52    k7_lattice3(sK0) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(k7_lattice3(sK0))) | spl1_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f93])).
% 0.21/0.52  fof(f93,plain,(
% 0.21/0.52    spl1_5 <=> k7_lattice3(sK0) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(k7_lattice3(sK0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    k7_lattice3(sK0) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(k7_lattice3(sK0))) | (~spl1_2 | ~spl1_3)),
% 0.21/0.52    inference(backward_demodulation,[],[f66,f79])).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    spl1_4 | ~spl1_5 | ~spl1_2 | ~spl1_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f87,f48,f43,f93,f89])).
% 0.21/0.52  % (30846)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  fof(f87,plain,(
% 0.21/0.52    k7_lattice3(sK0) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(k7_lattice3(sK0))) | k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0)) = u1_orders_2(k7_lattice3(sK0)) | (~spl1_2 | ~spl1_3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f82,f45])).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    k7_lattice3(sK0) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(k7_lattice3(sK0))) | k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0)) = u1_orders_2(k7_lattice3(sK0)) | ~l1_orders_2(k7_lattice3(sK0)) | (~spl1_2 | ~spl1_3)),
% 0.21/0.52    inference(superposition,[],[f57,f79])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ( ! [X0] : (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != k7_lattice3(sK0) | u1_orders_2(X0) = k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0)) | ~l1_orders_2(X0)) )),
% 0.21/0.52    inference(superposition,[],[f56,f34])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2) | u1_orders_2(X0) = X2 | ~l1_orders_2(X0)) )),
% 0.21/0.52    inference(resolution,[],[f29,f23])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | X1 = X3) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    spl1_1),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f61])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    $false | spl1_1),
% 0.21/0.52    inference(subsumption_resolution,[],[f59,f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ~m1_subset_1(k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | spl1_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    spl1_1 <=> m1_subset_1(k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    m1_subset_1(k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))),
% 0.21/0.52    inference(resolution,[],[f52,f21])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ( ! [X0] : (~l1_orders_2(X0) | m1_subset_1(k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))) )),
% 0.21/0.52    inference(resolution,[],[f31,f23])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_relset_1)).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ~spl1_1 | spl1_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f37,f48,f39])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    v1_orders_2(k7_lattice3(sK0)) | ~m1_subset_1(k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))),
% 0.21/0.53    inference(superposition,[],[f26,f34])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v1_orders_2(g1_orders_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ! [X0,X1] : ((l1_orders_2(g1_orders_2(X0,X1)) & v1_orders_2(g1_orders_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => (l1_orders_2(g1_orders_2(X0,X1)) & v1_orders_2(g1_orders_2(X0,X1))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_orders_2)).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ~spl1_1 | spl1_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f36,f43,f39])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    l1_orders_2(k7_lattice3(sK0)) | ~m1_subset_1(k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))),
% 0.21/0.53    inference(superposition,[],[f27,f34])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ( ! [X0,X1] : (l1_orders_2(g1_orders_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (30837)------------------------------
% 0.21/0.53  % (30837)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (30837)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (30837)Memory used [KB]: 10746
% 0.21/0.53  % (30837)Time elapsed: 0.102 s
% 0.21/0.53  % (30837)------------------------------
% 0.21/0.53  % (30837)------------------------------
% 0.21/0.53  % (30833)Success in time 0.169 s
%------------------------------------------------------------------------------
