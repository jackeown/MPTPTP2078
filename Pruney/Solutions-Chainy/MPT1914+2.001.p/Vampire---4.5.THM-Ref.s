%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:34 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 202 expanded)
%              Number of leaves         :   11 (  55 expanded)
%              Depth                    :   17
%              Number of atoms          :  114 ( 404 expanded)
%              Number of equality atoms :   39 ( 143 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f94,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f61,f89])).

fof(f89,plain,(
    ~ spl1_2 ),
    inference(avatar_contradiction_clause,[],[f88])).

fof(f88,plain,
    ( $false
    | ~ spl1_2 ),
    inference(subsumption_resolution,[],[f83,f22])).

fof(f22,plain,(
    u1_struct_0(sK0) != u1_struct_0(k7_lattice3(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( u1_struct_0(sK0) != u1_struct_0(k7_lattice3(sK0))
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f19])).

fof(f19,plain,
    ( ? [X0] :
        ( u1_struct_0(X0) != u1_struct_0(k7_lattice3(X0))
        & l1_orders_2(X0) )
   => ( u1_struct_0(sK0) != u1_struct_0(k7_lattice3(sK0))
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != u1_struct_0(k7_lattice3(X0))
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => u1_struct_0(X0) = u1_struct_0(k7_lattice3(X0)) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => u1_struct_0(X0) = u1_struct_0(k7_lattice3(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_yellow_6)).

fof(f83,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k7_lattice3(sK0))
    | ~ spl1_2 ),
    inference(trivial_inequality_removal,[],[f78])).

fof(f78,plain,
    ( k7_lattice3(sK0) != k7_lattice3(sK0)
    | u1_struct_0(sK0) = u1_struct_0(k7_lattice3(sK0))
    | ~ spl1_2 ),
    inference(superposition,[],[f50,f71])).

fof(f71,plain,(
    k7_lattice3(sK0) = g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0))) ),
    inference(subsumption_resolution,[],[f70,f68])).

fof(f68,plain,(
    l1_orders_2(k7_lattice3(sK0)) ),
    inference(forward_demodulation,[],[f65,f37])).

fof(f37,plain,(
    k7_lattice3(sK0) = g1_orders_2(u1_struct_0(sK0),k4_relat_1(u1_orders_2(sK0))) ),
    inference(backward_demodulation,[],[f32,f36])).

fof(f36,plain,(
    k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0)) = k4_relat_1(u1_orders_2(sK0)) ),
    inference(resolution,[],[f33,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k3_relset_1(X0,X1,X2) = k4_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

% (22352)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k3_relset_1(X0,X1,X2) = k4_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k3_relset_1(X0,X1,X2) = k4_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_relset_1)).

fof(f33,plain,(
    m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(resolution,[],[f21,f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f21,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f32,plain,(
    k7_lattice3(sK0) = g1_orders_2(u1_struct_0(sK0),k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0))) ),
    inference(resolution,[],[f21,f24])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_lattice3)).

fof(f65,plain,(
    l1_orders_2(g1_orders_2(u1_struct_0(sK0),k4_relat_1(u1_orders_2(sK0)))) ),
    inference(resolution,[],[f62,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | l1_orders_2(g1_orders_2(X0,X1)) ) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_orders_2)).

fof(f62,plain,(
    m1_subset_1(k4_relat_1(u1_orders_2(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f58,f33])).

fof(f58,plain,
    ( m1_subset_1(k4_relat_1(u1_orders_2(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(superposition,[],[f31,f36])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_relset_1)).

fof(f70,plain,
    ( k7_lattice3(sK0) = g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0)))
    | ~ l1_orders_2(k7_lattice3(sK0)) ),
    inference(resolution,[],[f67,f25])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_orders_2)).

fof(f67,plain,(
    v1_orders_2(k7_lattice3(sK0)) ),
    inference(forward_demodulation,[],[f64,f37])).

fof(f64,plain,(
    v1_orders_2(g1_orders_2(u1_struct_0(sK0),k4_relat_1(u1_orders_2(sK0)))) ),
    inference(resolution,[],[f62,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | v1_orders_2(g1_orders_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f50,plain,
    ( ! [X2,X3] :
        ( g1_orders_2(X2,X3) != k7_lattice3(sK0)
        | u1_struct_0(sK0) = X2 )
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl1_2
  <=> ! [X3,X2] :
        ( g1_orders_2(X2,X3) != k7_lattice3(sK0)
        | u1_struct_0(sK0) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f61,plain,(
    spl1_1 ),
    inference(avatar_contradiction_clause,[],[f60])).

fof(f60,plain,
    ( $false
    | spl1_1 ),
    inference(subsumption_resolution,[],[f59,f33])).

fof(f59,plain,
    ( ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | spl1_1 ),
    inference(subsumption_resolution,[],[f58,f47])).

fof(f47,plain,
    ( ~ m1_subset_1(k4_relat_1(u1_orders_2(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | spl1_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl1_1
  <=> m1_subset_1(k4_relat_1(u1_orders_2(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f51,plain,
    ( ~ spl1_1
    | spl1_2 ),
    inference(avatar_split_clause,[],[f41,f49,f45])).

fof(f41,plain,(
    ! [X2,X3] :
      ( g1_orders_2(X2,X3) != k7_lattice3(sK0)
      | u1_struct_0(sK0) = X2
      | ~ m1_subset_1(k4_relat_1(u1_orders_2(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ) ),
    inference(superposition,[],[f28,f37])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:28:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (22348)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.50  % (22340)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.51  % (22362)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.51  % (22362)Refutation not found, incomplete strategy% (22362)------------------------------
% 0.22/0.51  % (22362)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (22362)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (22362)Memory used [KB]: 10618
% 0.22/0.51  % (22362)Time elapsed: 0.056 s
% 0.22/0.51  % (22362)------------------------------
% 0.22/0.51  % (22362)------------------------------
% 0.22/0.51  % (22348)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % (22346)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (22363)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.52  % (22354)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.52  % (22351)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.52  % (22355)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f94,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f51,f61,f89])).
% 0.22/0.52  fof(f89,plain,(
% 0.22/0.52    ~spl1_2),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f88])).
% 0.22/0.52  fof(f88,plain,(
% 0.22/0.52    $false | ~spl1_2),
% 0.22/0.52    inference(subsumption_resolution,[],[f83,f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    u1_struct_0(sK0) != u1_struct_0(k7_lattice3(sK0))),
% 0.22/0.52    inference(cnf_transformation,[],[f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    u1_struct_0(sK0) != u1_struct_0(k7_lattice3(sK0)) & l1_orders_2(sK0)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ? [X0] : (u1_struct_0(X0) != u1_struct_0(k7_lattice3(X0)) & l1_orders_2(X0)) => (u1_struct_0(sK0) != u1_struct_0(k7_lattice3(sK0)) & l1_orders_2(sK0))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f10,plain,(
% 0.22/0.52    ? [X0] : (u1_struct_0(X0) != u1_struct_0(k7_lattice3(X0)) & l1_orders_2(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,negated_conjecture,(
% 0.22/0.52    ~! [X0] : (l1_orders_2(X0) => u1_struct_0(X0) = u1_struct_0(k7_lattice3(X0)))),
% 0.22/0.52    inference(negated_conjecture,[],[f8])).
% 0.22/0.52  fof(f8,conjecture,(
% 0.22/0.52    ! [X0] : (l1_orders_2(X0) => u1_struct_0(X0) = u1_struct_0(k7_lattice3(X0)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_yellow_6)).
% 0.22/0.52  fof(f83,plain,(
% 0.22/0.52    u1_struct_0(sK0) = u1_struct_0(k7_lattice3(sK0)) | ~spl1_2),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f78])).
% 0.22/0.52  fof(f78,plain,(
% 0.22/0.52    k7_lattice3(sK0) != k7_lattice3(sK0) | u1_struct_0(sK0) = u1_struct_0(k7_lattice3(sK0)) | ~spl1_2),
% 0.22/0.52    inference(superposition,[],[f50,f71])).
% 0.22/0.52  fof(f71,plain,(
% 0.22/0.52    k7_lattice3(sK0) = g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0)))),
% 0.22/0.52    inference(subsumption_resolution,[],[f70,f68])).
% 0.22/0.52  fof(f68,plain,(
% 0.22/0.52    l1_orders_2(k7_lattice3(sK0))),
% 0.22/0.52    inference(forward_demodulation,[],[f65,f37])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    k7_lattice3(sK0) = g1_orders_2(u1_struct_0(sK0),k4_relat_1(u1_orders_2(sK0)))),
% 0.22/0.52    inference(backward_demodulation,[],[f32,f36])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0)) = k4_relat_1(u1_orders_2(sK0))),
% 0.22/0.52    inference(resolution,[],[f33,f30])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k3_relset_1(X0,X1,X2) = k4_relat_1(X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  % (22352)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (k3_relset_1(X0,X1,X2) = k4_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k3_relset_1(X0,X1,X2) = k4_relat_1(X2))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_relset_1)).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))),
% 0.22/0.52    inference(resolution,[],[f21,f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ( ! [X0] : (~l1_orders_2(X0) | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,plain,(
% 0.22/0.52    ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0] : (l1_orders_2(X0) => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    l1_orders_2(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f20])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    k7_lattice3(sK0) = g1_orders_2(u1_struct_0(sK0),k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0)))),
% 0.22/0.52    inference(resolution,[],[f21,f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ( ! [X0] : (~l1_orders_2(X0) | k7_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0)))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    ! [X0] : (k7_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))) | ~l1_orders_2(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0] : (l1_orders_2(X0) => k7_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_lattice3)).
% 0.22/0.52  fof(f65,plain,(
% 0.22/0.52    l1_orders_2(g1_orders_2(u1_struct_0(sK0),k4_relat_1(u1_orders_2(sK0))))),
% 0.22/0.52    inference(resolution,[],[f62,f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | l1_orders_2(g1_orders_2(X0,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ! [X0,X1] : ((l1_orders_2(g1_orders_2(X0,X1)) & v1_orders_2(g1_orders_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 0.22/0.52    inference(ennf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => (l1_orders_2(g1_orders_2(X0,X1)) & v1_orders_2(g1_orders_2(X0,X1))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_orders_2)).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    m1_subset_1(k4_relat_1(u1_orders_2(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))),
% 0.22/0.52    inference(subsumption_resolution,[],[f58,f33])).
% 0.22/0.52  fof(f58,plain,(
% 0.22/0.52    m1_subset_1(k4_relat_1(u1_orders_2(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))),
% 0.22/0.52    inference(superposition,[],[f31,f36])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_relset_1)).
% 0.22/0.52  fof(f70,plain,(
% 0.22/0.52    k7_lattice3(sK0) = g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0))) | ~l1_orders_2(k7_lattice3(sK0))),
% 0.22/0.52    inference(resolution,[],[f67,f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_orders_2(X0) | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 | ~l1_orders_2(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ! [X0] : (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 | ~v1_orders_2(X0) | ~l1_orders_2(X0))),
% 0.22/0.52    inference(flattening,[],[f13])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ! [X0] : ((g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 | ~v1_orders_2(X0)) | ~l1_orders_2(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0] : (l1_orders_2(X0) => (v1_orders_2(X0) => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_orders_2)).
% 0.22/0.52  fof(f67,plain,(
% 0.22/0.52    v1_orders_2(k7_lattice3(sK0))),
% 0.22/0.52    inference(forward_demodulation,[],[f64,f37])).
% 0.22/0.52  fof(f64,plain,(
% 0.22/0.52    v1_orders_2(g1_orders_2(u1_struct_0(sK0),k4_relat_1(u1_orders_2(sK0))))),
% 0.22/0.52    inference(resolution,[],[f62,f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | v1_orders_2(g1_orders_2(X0,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    ( ! [X2,X3] : (g1_orders_2(X2,X3) != k7_lattice3(sK0) | u1_struct_0(sK0) = X2) ) | ~spl1_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f49])).
% 0.22/0.52  fof(f49,plain,(
% 0.22/0.52    spl1_2 <=> ! [X3,X2] : (g1_orders_2(X2,X3) != k7_lattice3(sK0) | u1_struct_0(sK0) = X2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.22/0.52  fof(f61,plain,(
% 0.22/0.52    spl1_1),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f60])).
% 0.22/0.52  fof(f60,plain,(
% 0.22/0.52    $false | spl1_1),
% 0.22/0.52    inference(subsumption_resolution,[],[f59,f33])).
% 0.22/0.52  fof(f59,plain,(
% 0.22/0.52    ~m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | spl1_1),
% 0.22/0.52    inference(subsumption_resolution,[],[f58,f47])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    ~m1_subset_1(k4_relat_1(u1_orders_2(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | spl1_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f45])).
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    spl1_1 <=> m1_subset_1(k4_relat_1(u1_orders_2(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    ~spl1_1 | spl1_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f41,f49,f45])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    ( ! [X2,X3] : (g1_orders_2(X2,X3) != k7_lattice3(sK0) | u1_struct_0(sK0) = X2 | ~m1_subset_1(k4_relat_1(u1_orders_2(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))) )),
% 0.22/0.52    inference(superposition,[],[f28,f37])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | X0 = X2 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ! [X2,X3] : (g1_orders_2(X0,X1) = g1_orders_2(X2,X3) => (X1 = X3 & X0 = X2)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (22348)------------------------------
% 0.22/0.52  % (22348)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (22348)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (22348)Memory used [KB]: 10746
% 0.22/0.52  % (22348)Time elapsed: 0.097 s
% 0.22/0.52  % (22348)------------------------------
% 0.22/0.52  % (22348)------------------------------
% 0.22/0.52  % (22339)Success in time 0.162 s
%------------------------------------------------------------------------------
