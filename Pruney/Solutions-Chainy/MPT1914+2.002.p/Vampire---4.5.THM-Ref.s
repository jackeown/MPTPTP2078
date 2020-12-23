%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:34 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   35 (  57 expanded)
%              Number of leaves         :    7 (  15 expanded)
%              Depth                    :   10
%              Number of atoms          :   80 ( 132 expanded)
%              Number of equality atoms :   37 (  55 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f58,plain,(
    $false ),
    inference(subsumption_resolution,[],[f57,f18])).

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

% (24964)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
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

fof(f57,plain,(
    u1_struct_0(sK0) = u1_struct_0(k7_lattice3(sK0)) ),
    inference(trivial_inequality_removal,[],[f56])).

fof(f56,plain,
    ( k7_lattice3(sK0) != k7_lattice3(sK0)
    | u1_struct_0(sK0) = u1_struct_0(k7_lattice3(sK0)) ),
    inference(superposition,[],[f51,f30])).

fof(f30,plain,(
    k7_lattice3(sK0) = g1_orders_2(u1_struct_0(sK0),k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0))) ),
    inference(resolution,[],[f20,f17])).

fof(f17,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f20,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | k7_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k7_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k7_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_lattice3)).

fof(f51,plain,(
    ! [X0,X1] :
      ( g1_orders_2(X0,X1) != k7_lattice3(sK0)
      | u1_struct_0(k7_lattice3(sK0)) = X0 ) ),
    inference(forward_demodulation,[],[f49,f28])).

fof(f28,plain,(
    k7_lattice3(sK0) = g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0))) ),
    inference(resolution,[],[f27,f17])).

fof(f27,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | k7_lattice3(X0) = g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0))) ) ),
    inference(subsumption_resolution,[],[f26,f22])).

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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( l1_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_lattice3)).

fof(f26,plain,(
    ! [X0] :
      ( k7_lattice3(X0) = g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0)))
      | ~ l1_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f23,f21])).

fof(f21,plain,(
    ! [X0] :
      ( v1_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_orders_2(X0)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
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

% (24963)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_orders_2(X0)
       => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_orders_2)).

fof(f49,plain,(
    ! [X0,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0)))
      | u1_struct_0(k7_lattice3(sK0)) = X0 ) ),
    inference(resolution,[],[f36,f17])).

fof(f36,plain,(
    ! [X4,X2,X3] :
      ( ~ l1_orders_2(X2)
      | g1_orders_2(u1_struct_0(k7_lattice3(X2)),u1_orders_2(k7_lattice3(X2))) != g1_orders_2(X3,X4)
      | u1_struct_0(k7_lattice3(X2)) = X3 ) ),
    inference(resolution,[],[f34,f22])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | u1_struct_0(X0) = X1
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2) ) ),
    inference(resolution,[],[f24,f19])).

fof(f19,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : run_vampire %s %d
% 0.16/0.37  % Computer   : n007.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % WCLimit    : 600
% 0.16/0.37  % DateTime   : Tue Dec  1 20:52:51 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.24/0.52  % (24973)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.24/0.53  % (24972)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.24/0.53  % (24980)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.24/0.53  % (24965)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.24/0.53  % (24980)Refutation not found, incomplete strategy% (24980)------------------------------
% 0.24/0.53  % (24980)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.24/0.53  % (24980)Termination reason: Refutation not found, incomplete strategy
% 0.24/0.53  
% 0.24/0.53  % (24980)Memory used [KB]: 10618
% 0.24/0.53  % (24980)Time elapsed: 0.060 s
% 0.24/0.53  % (24980)------------------------------
% 0.24/0.53  % (24980)------------------------------
% 0.24/0.53  % (24965)Refutation found. Thanks to Tanya!
% 0.24/0.53  % SZS status Theorem for theBenchmark
% 0.24/0.53  % SZS output start Proof for theBenchmark
% 0.24/0.53  fof(f58,plain,(
% 0.24/0.53    $false),
% 0.24/0.53    inference(subsumption_resolution,[],[f57,f18])).
% 0.24/0.53  fof(f18,plain,(
% 0.24/0.53    u1_struct_0(sK0) != u1_struct_0(k7_lattice3(sK0))),
% 0.24/0.53    inference(cnf_transformation,[],[f16])).
% 0.24/0.53  fof(f16,plain,(
% 0.24/0.53    u1_struct_0(sK0) != u1_struct_0(k7_lattice3(sK0)) & l1_orders_2(sK0)),
% 0.24/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f15])).
% 0.24/0.53  fof(f15,plain,(
% 0.24/0.53    ? [X0] : (u1_struct_0(X0) != u1_struct_0(k7_lattice3(X0)) & l1_orders_2(X0)) => (u1_struct_0(sK0) != u1_struct_0(k7_lattice3(sK0)) & l1_orders_2(sK0))),
% 0.24/0.53    introduced(choice_axiom,[])).
% 0.24/0.53  fof(f8,plain,(
% 0.24/0.53    ? [X0] : (u1_struct_0(X0) != u1_struct_0(k7_lattice3(X0)) & l1_orders_2(X0))),
% 0.24/0.53    inference(ennf_transformation,[],[f7])).
% 0.24/0.54  % (24964)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.24/0.54  fof(f7,negated_conjecture,(
% 0.24/0.54    ~! [X0] : (l1_orders_2(X0) => u1_struct_0(X0) = u1_struct_0(k7_lattice3(X0)))),
% 0.24/0.54    inference(negated_conjecture,[],[f6])).
% 0.24/0.54  fof(f6,conjecture,(
% 0.24/0.54    ! [X0] : (l1_orders_2(X0) => u1_struct_0(X0) = u1_struct_0(k7_lattice3(X0)))),
% 0.24/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_yellow_6)).
% 0.24/0.54  fof(f57,plain,(
% 0.24/0.54    u1_struct_0(sK0) = u1_struct_0(k7_lattice3(sK0))),
% 0.24/0.54    inference(trivial_inequality_removal,[],[f56])).
% 0.24/0.54  fof(f56,plain,(
% 0.24/0.54    k7_lattice3(sK0) != k7_lattice3(sK0) | u1_struct_0(sK0) = u1_struct_0(k7_lattice3(sK0))),
% 0.24/0.54    inference(superposition,[],[f51,f30])).
% 0.24/0.54  fof(f30,plain,(
% 0.24/0.54    k7_lattice3(sK0) = g1_orders_2(u1_struct_0(sK0),k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0)))),
% 0.24/0.54    inference(resolution,[],[f20,f17])).
% 0.24/0.54  fof(f17,plain,(
% 0.24/0.54    l1_orders_2(sK0)),
% 0.24/0.54    inference(cnf_transformation,[],[f16])).
% 0.24/0.54  fof(f20,plain,(
% 0.24/0.54    ( ! [X0] : (~l1_orders_2(X0) | k7_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0)))) )),
% 0.24/0.54    inference(cnf_transformation,[],[f10])).
% 0.24/0.54  fof(f10,plain,(
% 0.24/0.54    ! [X0] : (k7_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))) | ~l1_orders_2(X0))),
% 0.24/0.54    inference(ennf_transformation,[],[f4])).
% 0.24/0.54  fof(f4,axiom,(
% 0.24/0.54    ! [X0] : (l1_orders_2(X0) => k7_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))))),
% 0.24/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_lattice3)).
% 0.24/0.54  fof(f51,plain,(
% 0.24/0.54    ( ! [X0,X1] : (g1_orders_2(X0,X1) != k7_lattice3(sK0) | u1_struct_0(k7_lattice3(sK0)) = X0) )),
% 0.24/0.54    inference(forward_demodulation,[],[f49,f28])).
% 0.24/0.54  fof(f28,plain,(
% 0.24/0.54    k7_lattice3(sK0) = g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0)))),
% 0.24/0.54    inference(resolution,[],[f27,f17])).
% 0.24/0.54  fof(f27,plain,(
% 0.24/0.54    ( ! [X0] : (~l1_orders_2(X0) | k7_lattice3(X0) = g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0)))) )),
% 0.24/0.54    inference(subsumption_resolution,[],[f26,f22])).
% 0.24/0.54  fof(f22,plain,(
% 0.24/0.54    ( ! [X0] : (l1_orders_2(k7_lattice3(X0)) | ~l1_orders_2(X0)) )),
% 0.24/0.54    inference(cnf_transformation,[],[f11])).
% 0.24/0.54  fof(f11,plain,(
% 0.24/0.54    ! [X0] : ((l1_orders_2(k7_lattice3(X0)) & v1_orders_2(k7_lattice3(X0))) | ~l1_orders_2(X0))),
% 0.24/0.54    inference(ennf_transformation,[],[f5])).
% 0.24/0.54  fof(f5,axiom,(
% 0.24/0.54    ! [X0] : (l1_orders_2(X0) => (l1_orders_2(k7_lattice3(X0)) & v1_orders_2(k7_lattice3(X0))))),
% 0.24/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_lattice3)).
% 0.24/0.54  fof(f26,plain,(
% 0.24/0.54    ( ! [X0] : (k7_lattice3(X0) = g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0))) | ~l1_orders_2(k7_lattice3(X0)) | ~l1_orders_2(X0)) )),
% 0.24/0.54    inference(resolution,[],[f23,f21])).
% 0.24/0.54  fof(f21,plain,(
% 0.24/0.54    ( ! [X0] : (v1_orders_2(k7_lattice3(X0)) | ~l1_orders_2(X0)) )),
% 0.24/0.54    inference(cnf_transformation,[],[f11])).
% 0.24/0.54  fof(f23,plain,(
% 0.24/0.54    ( ! [X0] : (~v1_orders_2(X0) | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 | ~l1_orders_2(X0)) )),
% 0.24/0.54    inference(cnf_transformation,[],[f13])).
% 0.24/0.54  fof(f13,plain,(
% 0.24/0.54    ! [X0] : (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 | ~v1_orders_2(X0) | ~l1_orders_2(X0))),
% 0.24/0.54    inference(flattening,[],[f12])).
% 0.24/0.54  fof(f12,plain,(
% 0.24/0.54    ! [X0] : ((g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 | ~v1_orders_2(X0)) | ~l1_orders_2(X0))),
% 0.24/0.54    inference(ennf_transformation,[],[f1])).
% 0.24/0.54  % (24963)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.24/0.54  fof(f1,axiom,(
% 0.24/0.54    ! [X0] : (l1_orders_2(X0) => (v1_orders_2(X0) => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0))),
% 0.24/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_orders_2)).
% 0.24/0.54  fof(f49,plain,(
% 0.24/0.54    ( ! [X0,X1] : (g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0))) | u1_struct_0(k7_lattice3(sK0)) = X0) )),
% 0.24/0.54    inference(resolution,[],[f36,f17])).
% 0.24/0.54  fof(f36,plain,(
% 0.24/0.54    ( ! [X4,X2,X3] : (~l1_orders_2(X2) | g1_orders_2(u1_struct_0(k7_lattice3(X2)),u1_orders_2(k7_lattice3(X2))) != g1_orders_2(X3,X4) | u1_struct_0(k7_lattice3(X2)) = X3) )),
% 0.24/0.54    inference(resolution,[],[f34,f22])).
% 0.24/0.54  fof(f34,plain,(
% 0.24/0.54    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | u1_struct_0(X0) = X1 | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2)) )),
% 0.24/0.54    inference(resolution,[],[f24,f19])).
% 0.24/0.54  fof(f19,plain,(
% 0.24/0.54    ( ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0)) )),
% 0.24/0.54    inference(cnf_transformation,[],[f9])).
% 0.24/0.54  fof(f9,plain,(
% 0.24/0.54    ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.24/0.54    inference(ennf_transformation,[],[f2])).
% 0.24/0.54  fof(f2,axiom,(
% 0.24/0.54    ! [X0] : (l1_orders_2(X0) => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))))),
% 0.24/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).
% 0.24/0.54  fof(f24,plain,(
% 0.24/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | X0 = X2) )),
% 0.24/0.54    inference(cnf_transformation,[],[f14])).
% 0.24/0.54  fof(f14,plain,(
% 0.24/0.54    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 0.24/0.54    inference(ennf_transformation,[],[f3])).
% 0.24/0.54  fof(f3,axiom,(
% 0.24/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ! [X2,X3] : (g1_orders_2(X0,X1) = g1_orders_2(X2,X3) => (X1 = X3 & X0 = X2)))),
% 0.24/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).
% 0.24/0.54  % SZS output end Proof for theBenchmark
% 0.24/0.54  % (24965)------------------------------
% 0.24/0.54  % (24965)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.24/0.54  % (24965)Termination reason: Refutation
% 0.24/0.54  
% 0.24/0.54  % (24965)Memory used [KB]: 6268
% 0.24/0.54  % (24965)Time elapsed: 0.102 s
% 0.24/0.54  % (24965)------------------------------
% 0.24/0.54  % (24965)------------------------------
% 0.24/0.54  % (24957)Success in time 0.148 s
%------------------------------------------------------------------------------
