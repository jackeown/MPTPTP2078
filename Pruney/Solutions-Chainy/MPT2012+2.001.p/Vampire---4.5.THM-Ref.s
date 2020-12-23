%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:02 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   42 (  74 expanded)
%              Number of leaves         :    6 (  16 expanded)
%              Depth                    :   10
%              Number of atoms          :  107 ( 190 expanded)
%              Number of equality atoms :   41 (  68 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f50,plain,(
    $false ),
    inference(subsumption_resolution,[],[f49,f47])).

fof(f47,plain,(
    k7_lattice3(sK0) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(k3_waybel_9(sK0))) ),
    inference(backward_demodulation,[],[f42,f46])).

fof(f46,plain,(
    k7_lattice3(sK0) = g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0))) ),
    inference(subsumption_resolution,[],[f45,f38])).

fof(f38,plain,(
    l1_orders_2(k7_lattice3(sK0)) ),
    inference(resolution,[],[f20,f16])).

fof(f16,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f8])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_waybel_9)).

fof(f20,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_orders_2(k7_lattice3(X0)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_lattice3)).

fof(f45,plain,
    ( ~ l1_orders_2(k7_lattice3(sK0))
    | k7_lattice3(sK0) = g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0))) ),
    inference(resolution,[],[f37,f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_orders_2)).

fof(f37,plain,(
    v1_orders_2(k7_lattice3(sK0)) ),
    inference(resolution,[],[f19,f16])).

fof(f19,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | v1_orders_2(k7_lattice3(X0)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f42,plain,(
    g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0))) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(k3_waybel_9(sK0))) ),
    inference(backward_demodulation,[],[f17,f41])).

fof(f41,plain,(
    u1_struct_0(k3_waybel_9(sK0)) = u1_struct_0(sK0) ),
    inference(resolution,[],[f36,f16])).

fof(f36,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | u1_struct_0(X0) = u1_struct_0(k3_waybel_9(X0)) ) ),
    inference(subsumption_resolution,[],[f35,f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_waybel_0(k3_waybel_9(X0),X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( l1_waybel_0(k3_waybel_9(X0),X0)
        & v6_waybel_0(k3_waybel_9(X0),X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( l1_waybel_0(k3_waybel_9(X0),X0)
        & v6_waybel_0(k3_waybel_9(X0),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_waybel_9)).

fof(f35,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | ~ l1_waybel_0(k3_waybel_9(X0),X0)
      | u1_struct_0(X0) = u1_struct_0(k3_waybel_9(X0)) ) ),
    inference(subsumption_resolution,[],[f30,f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | v6_waybel_0(k3_waybel_9(X0),X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | ~ v6_waybel_0(k3_waybel_9(X0),X0)
      | ~ l1_waybel_0(k3_waybel_9(X0),X0)
      | u1_struct_0(X0) = u1_struct_0(k3_waybel_9(X0)) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v6_waybel_0(X1,X0)
      | ~ l1_waybel_0(X1,X0)
      | u1_struct_0(X0) = u1_struct_0(X1)
      | k3_waybel_9(X0) != X1 ) ),
    inference(cnf_transformation,[],[f15])).

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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v6_waybel_0(X1,X0) )
         => ( k3_waybel_9(X0) = X1
          <=> ( u1_waybel_0(X0,X1) = k3_struct_0(X0)
              & k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0)) = u1_orders_2(X1)
              & u1_struct_0(X0) = u1_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_waybel_9)).

fof(f17,plain,(
    g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0))) != g1_orders_2(u1_struct_0(k3_waybel_9(sK0)),u1_orders_2(k3_waybel_9(sK0))) ),
    inference(cnf_transformation,[],[f8])).

fof(f49,plain,(
    k7_lattice3(sK0) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(k3_waybel_9(sK0))) ),
    inference(forward_demodulation,[],[f48,f44])).

fof(f44,plain,(
    u1_orders_2(k3_waybel_9(sK0)) = k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0)) ),
    inference(resolution,[],[f34,f16])).

fof(f34,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0)) = u1_orders_2(k3_waybel_9(X0)) ) ),
    inference(subsumption_resolution,[],[f33,f22])).

fof(f33,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | ~ l1_waybel_0(k3_waybel_9(X0),X0)
      | k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0)) = u1_orders_2(k3_waybel_9(X0)) ) ),
    inference(subsumption_resolution,[],[f29,f21])).

fof(f29,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | ~ v6_waybel_0(k3_waybel_9(X0),X0)
      | ~ l1_waybel_0(k3_waybel_9(X0),X0)
      | k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0)) = u1_orders_2(k3_waybel_9(X0)) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v6_waybel_0(X1,X0)
      | ~ l1_waybel_0(X1,X0)
      | k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0)) = u1_orders_2(X1)
      | k3_waybel_9(X0) != X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f48,plain,(
    k7_lattice3(sK0) = g1_orders_2(u1_struct_0(sK0),k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0))) ),
    inference(resolution,[],[f18,f16])).

% (21491)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
fof(f18,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | k7_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( k7_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k7_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_lattice3)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:19:48 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (21497)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.46  % (21497)Refutation found. Thanks to Tanya!
% 0.22/0.46  % SZS status Theorem for theBenchmark
% 0.22/0.46  % (21489)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.46  % SZS output start Proof for theBenchmark
% 0.22/0.46  fof(f50,plain,(
% 0.22/0.46    $false),
% 0.22/0.46    inference(subsumption_resolution,[],[f49,f47])).
% 0.22/0.46  fof(f47,plain,(
% 0.22/0.46    k7_lattice3(sK0) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(k3_waybel_9(sK0)))),
% 0.22/0.46    inference(backward_demodulation,[],[f42,f46])).
% 0.22/0.46  fof(f46,plain,(
% 0.22/0.46    k7_lattice3(sK0) = g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0)))),
% 0.22/0.46    inference(subsumption_resolution,[],[f45,f38])).
% 0.22/0.46  fof(f38,plain,(
% 0.22/0.46    l1_orders_2(k7_lattice3(sK0))),
% 0.22/0.46    inference(resolution,[],[f20,f16])).
% 0.22/0.46  fof(f16,plain,(
% 0.22/0.46    l1_orders_2(sK0)),
% 0.22/0.46    inference(cnf_transformation,[],[f8])).
% 0.22/0.46  fof(f8,plain,(
% 0.22/0.46    ? [X0] : (g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0))) != g1_orders_2(u1_struct_0(k3_waybel_9(X0)),u1_orders_2(k3_waybel_9(X0))) & l1_orders_2(X0))),
% 0.22/0.46    inference(ennf_transformation,[],[f7])).
% 0.22/0.46  fof(f7,negated_conjecture,(
% 0.22/0.46    ~! [X0] : (l1_orders_2(X0) => g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0))) = g1_orders_2(u1_struct_0(k3_waybel_9(X0)),u1_orders_2(k3_waybel_9(X0))))),
% 0.22/0.46    inference(negated_conjecture,[],[f6])).
% 0.22/0.46  fof(f6,conjecture,(
% 0.22/0.46    ! [X0] : (l1_orders_2(X0) => g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0))) = g1_orders_2(u1_struct_0(k3_waybel_9(X0)),u1_orders_2(k3_waybel_9(X0))))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_waybel_9)).
% 0.22/0.46  fof(f20,plain,(
% 0.22/0.46    ( ! [X0] : (~l1_orders_2(X0) | l1_orders_2(k7_lattice3(X0))) )),
% 0.22/0.46    inference(cnf_transformation,[],[f10])).
% 0.22/0.46  fof(f10,plain,(
% 0.22/0.46    ! [X0] : ((l1_orders_2(k7_lattice3(X0)) & v1_orders_2(k7_lattice3(X0))) | ~l1_orders_2(X0))),
% 0.22/0.46    inference(ennf_transformation,[],[f3])).
% 0.22/0.46  fof(f3,axiom,(
% 0.22/0.46    ! [X0] : (l1_orders_2(X0) => (l1_orders_2(k7_lattice3(X0)) & v1_orders_2(k7_lattice3(X0))))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_lattice3)).
% 0.22/0.46  fof(f45,plain,(
% 0.22/0.46    ~l1_orders_2(k7_lattice3(sK0)) | k7_lattice3(sK0) = g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0)))),
% 0.22/0.46    inference(resolution,[],[f37,f23])).
% 0.22/0.46  fof(f23,plain,(
% 0.22/0.46    ( ! [X0] : (~v1_orders_2(X0) | ~l1_orders_2(X0) | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0) )),
% 0.22/0.46    inference(cnf_transformation,[],[f13])).
% 0.22/0.46  fof(f13,plain,(
% 0.22/0.46    ! [X0] : (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 | ~v1_orders_2(X0) | ~l1_orders_2(X0))),
% 0.22/0.46    inference(flattening,[],[f12])).
% 0.22/0.46  fof(f12,plain,(
% 0.22/0.46    ! [X0] : ((g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 | ~v1_orders_2(X0)) | ~l1_orders_2(X0))),
% 0.22/0.46    inference(ennf_transformation,[],[f1])).
% 0.22/0.46  fof(f1,axiom,(
% 0.22/0.46    ! [X0] : (l1_orders_2(X0) => (v1_orders_2(X0) => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_orders_2)).
% 0.22/0.46  fof(f37,plain,(
% 0.22/0.46    v1_orders_2(k7_lattice3(sK0))),
% 0.22/0.46    inference(resolution,[],[f19,f16])).
% 0.22/0.46  fof(f19,plain,(
% 0.22/0.46    ( ! [X0] : (~l1_orders_2(X0) | v1_orders_2(k7_lattice3(X0))) )),
% 0.22/0.46    inference(cnf_transformation,[],[f10])).
% 0.22/0.46  fof(f42,plain,(
% 0.22/0.46    g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0))) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(k3_waybel_9(sK0)))),
% 0.22/0.46    inference(backward_demodulation,[],[f17,f41])).
% 0.22/0.46  fof(f41,plain,(
% 0.22/0.46    u1_struct_0(k3_waybel_9(sK0)) = u1_struct_0(sK0)),
% 0.22/0.46    inference(resolution,[],[f36,f16])).
% 0.22/0.46  fof(f36,plain,(
% 0.22/0.46    ( ! [X0] : (~l1_orders_2(X0) | u1_struct_0(X0) = u1_struct_0(k3_waybel_9(X0))) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f35,f22])).
% 0.22/0.46  fof(f22,plain,(
% 0.22/0.46    ( ! [X0] : (~l1_orders_2(X0) | l1_waybel_0(k3_waybel_9(X0),X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f11])).
% 0.22/0.46  fof(f11,plain,(
% 0.22/0.46    ! [X0] : ((l1_waybel_0(k3_waybel_9(X0),X0) & v6_waybel_0(k3_waybel_9(X0),X0)) | ~l1_orders_2(X0))),
% 0.22/0.46    inference(ennf_transformation,[],[f5])).
% 0.22/0.46  fof(f5,axiom,(
% 0.22/0.46    ! [X0] : (l1_orders_2(X0) => (l1_waybel_0(k3_waybel_9(X0),X0) & v6_waybel_0(k3_waybel_9(X0),X0)))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_waybel_9)).
% 0.22/0.46  fof(f35,plain,(
% 0.22/0.46    ( ! [X0] : (~l1_orders_2(X0) | ~l1_waybel_0(k3_waybel_9(X0),X0) | u1_struct_0(X0) = u1_struct_0(k3_waybel_9(X0))) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f30,f21])).
% 0.22/0.46  fof(f21,plain,(
% 0.22/0.46    ( ! [X0] : (~l1_orders_2(X0) | v6_waybel_0(k3_waybel_9(X0),X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f11])).
% 0.22/0.46  fof(f30,plain,(
% 0.22/0.46    ( ! [X0] : (~l1_orders_2(X0) | ~v6_waybel_0(k3_waybel_9(X0),X0) | ~l1_waybel_0(k3_waybel_9(X0),X0) | u1_struct_0(X0) = u1_struct_0(k3_waybel_9(X0))) )),
% 0.22/0.46    inference(equality_resolution,[],[f24])).
% 0.22/0.46  fof(f24,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~l1_orders_2(X0) | ~v6_waybel_0(X1,X0) | ~l1_waybel_0(X1,X0) | u1_struct_0(X0) = u1_struct_0(X1) | k3_waybel_9(X0) != X1) )),
% 0.22/0.46    inference(cnf_transformation,[],[f15])).
% 0.22/0.46  fof(f15,plain,(
% 0.22/0.46    ! [X0] : (! [X1] : ((k3_waybel_9(X0) = X1 <=> (u1_waybel_0(X0,X1) = k3_struct_0(X0) & k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0)) = u1_orders_2(X1) & u1_struct_0(X0) = u1_struct_0(X1))) | ~l1_waybel_0(X1,X0) | ~v6_waybel_0(X1,X0)) | ~l1_orders_2(X0))),
% 0.22/0.46    inference(flattening,[],[f14])).
% 0.22/0.46  fof(f14,plain,(
% 0.22/0.46    ! [X0] : (! [X1] : ((k3_waybel_9(X0) = X1 <=> (u1_waybel_0(X0,X1) = k3_struct_0(X0) & k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0)) = u1_orders_2(X1) & u1_struct_0(X0) = u1_struct_0(X1))) | (~l1_waybel_0(X1,X0) | ~v6_waybel_0(X1,X0))) | ~l1_orders_2(X0))),
% 0.22/0.46    inference(ennf_transformation,[],[f4])).
% 0.22/0.46  fof(f4,axiom,(
% 0.22/0.46    ! [X0] : (l1_orders_2(X0) => ! [X1] : ((l1_waybel_0(X1,X0) & v6_waybel_0(X1,X0)) => (k3_waybel_9(X0) = X1 <=> (u1_waybel_0(X0,X1) = k3_struct_0(X0) & k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0)) = u1_orders_2(X1) & u1_struct_0(X0) = u1_struct_0(X1)))))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_waybel_9)).
% 0.22/0.46  fof(f17,plain,(
% 0.22/0.46    g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0))) != g1_orders_2(u1_struct_0(k3_waybel_9(sK0)),u1_orders_2(k3_waybel_9(sK0)))),
% 0.22/0.46    inference(cnf_transformation,[],[f8])).
% 0.22/0.46  fof(f49,plain,(
% 0.22/0.46    k7_lattice3(sK0) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(k3_waybel_9(sK0)))),
% 0.22/0.46    inference(forward_demodulation,[],[f48,f44])).
% 0.22/0.46  fof(f44,plain,(
% 0.22/0.46    u1_orders_2(k3_waybel_9(sK0)) = k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0))),
% 0.22/0.46    inference(resolution,[],[f34,f16])).
% 0.22/0.46  fof(f34,plain,(
% 0.22/0.46    ( ! [X0] : (~l1_orders_2(X0) | k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0)) = u1_orders_2(k3_waybel_9(X0))) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f33,f22])).
% 0.22/0.46  fof(f33,plain,(
% 0.22/0.46    ( ! [X0] : (~l1_orders_2(X0) | ~l1_waybel_0(k3_waybel_9(X0),X0) | k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0)) = u1_orders_2(k3_waybel_9(X0))) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f29,f21])).
% 0.22/0.46  fof(f29,plain,(
% 0.22/0.46    ( ! [X0] : (~l1_orders_2(X0) | ~v6_waybel_0(k3_waybel_9(X0),X0) | ~l1_waybel_0(k3_waybel_9(X0),X0) | k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0)) = u1_orders_2(k3_waybel_9(X0))) )),
% 0.22/0.46    inference(equality_resolution,[],[f25])).
% 0.22/0.46  fof(f25,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~l1_orders_2(X0) | ~v6_waybel_0(X1,X0) | ~l1_waybel_0(X1,X0) | k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0)) = u1_orders_2(X1) | k3_waybel_9(X0) != X1) )),
% 0.22/0.46    inference(cnf_transformation,[],[f15])).
% 0.22/0.46  fof(f48,plain,(
% 0.22/0.46    k7_lattice3(sK0) = g1_orders_2(u1_struct_0(sK0),k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0)))),
% 0.22/0.46    inference(resolution,[],[f18,f16])).
% 0.22/0.47  % (21491)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    ( ! [X0] : (~l1_orders_2(X0) | k7_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0)))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f9])).
% 0.22/0.47  fof(f9,plain,(
% 0.22/0.47    ! [X0] : (k7_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))) | ~l1_orders_2(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0] : (l1_orders_2(X0) => k7_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_lattice3)).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (21497)------------------------------
% 0.22/0.47  % (21497)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (21497)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (21497)Memory used [KB]: 1663
% 0.22/0.47  % (21497)Time elapsed: 0.054 s
% 0.22/0.47  % (21497)------------------------------
% 0.22/0.47  % (21497)------------------------------
% 0.22/0.47  % (21482)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.47  % (21479)Success in time 0.108 s
%------------------------------------------------------------------------------
