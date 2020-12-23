%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:26 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 150 expanded)
%              Number of leaves         :    7 (  32 expanded)
%              Depth                    :   15
%              Number of atoms          :   92 ( 338 expanded)
%              Number of equality atoms :   48 (  97 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f56,plain,(
    $false ),
    inference(subsumption_resolution,[],[f42,f55])).

fof(f55,plain,(
    ! [X0] : k1_yellow_1(X0) = u1_orders_2(k2_yellow_1(X0)) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X3] :
      ( k2_yellow_1(X2) != k2_yellow_1(X3)
      | u1_orders_2(k2_yellow_1(X2)) = k1_yellow_1(X3) ) ),
    inference(superposition,[],[f48,f43])).

fof(f43,plain,(
    ! [X0] : k2_yellow_1(X0) = g1_orders_2(X0,u1_orders_2(k2_yellow_1(X0))) ),
    inference(backward_demodulation,[],[f32,f41])).

fof(f41,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X3] :
      ( k2_yellow_1(X2) != k2_yellow_1(X3)
      | u1_struct_0(k2_yellow_1(X2)) = X3 ) ),
    inference(superposition,[],[f34,f32])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k2_yellow_1(X0) != g1_orders_2(X1,X2)
      | X0 = X1 ) ),
    inference(superposition,[],[f33,f20])).

fof(f20,plain,(
    ! [X0] : k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_yellow_1)).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( g1_orders_2(X0,k1_yellow_1(X0)) != g1_orders_2(X1,X2)
      | X0 = X1 ) ),
    inference(resolution,[],[f25,f21])).

fof(f21,plain,(
    ! [X0] : m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] : m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_relat_2(k1_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v4_relat_2(k1_yellow_1(X0))
      & v1_relat_2(k1_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v8_relat_2(k1_yellow_1(X0))
      & v4_relat_2(k1_yellow_1(X0))
      & v1_relat_2(k1_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k1_yellow_1(X0),X0)
      & v8_relat_2(k1_yellow_1(X0))
      & v4_relat_2(k1_yellow_1(X0))
      & v1_relat_2(k1_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_1)).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(f32,plain,(
    ! [X0] : k2_yellow_1(X0) = g1_orders_2(u1_struct_0(k2_yellow_1(X0)),u1_orders_2(k2_yellow_1(X0))) ),
    inference(subsumption_resolution,[],[f31,f30])).

fof(f30,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(forward_demodulation,[],[f29,f20])).

fof(f29,plain,(
    ! [X0] : l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(resolution,[],[f24,f21])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | l1_orders_2(g1_orders_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_orders_2)).

fof(f31,plain,(
    ! [X0] :
      ( k2_yellow_1(X0) = g1_orders_2(u1_struct_0(k2_yellow_1(X0)),u1_orders_2(k2_yellow_1(X0)))
      | ~ l1_orders_2(k2_yellow_1(X0)) ) ),
    inference(resolution,[],[f22,f28])).

fof(f28,plain,(
    ! [X0] : v1_orders_2(k2_yellow_1(X0)) ),
    inference(forward_demodulation,[],[f27,f20])).

fof(f27,plain,(
    ! [X0] : v1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(resolution,[],[f23,f21])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | v1_orders_2(g1_orders_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f22,plain,(
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

% (14853)Refutation not found, incomplete strategy% (14853)------------------------------
% (14853)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f13,plain,(
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

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k2_yellow_1(X0) != g1_orders_2(X1,X2)
      | k1_yellow_1(X0) = X2 ) ),
    inference(superposition,[],[f47,f20])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( g1_orders_2(X0,k1_yellow_1(X0)) != g1_orders_2(X1,X2)
      | k1_yellow_1(X0) = X2 ) ),
    inference(resolution,[],[f26,f21])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f16])).

% (14841)Refutation not found, incomplete strategy% (14841)------------------------------
% (14841)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (14841)Termination reason: Refutation not found, incomplete strategy

% (14841)Memory used [KB]: 10618
% (14841)Time elapsed: 0.104 s
% (14841)------------------------------
% (14841)------------------------------
fof(f42,plain,(
    k1_yellow_1(sK0) != u1_orders_2(k2_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f19,f41])).

fof(f19,plain,
    ( sK0 != u1_struct_0(k2_yellow_1(sK0))
    | k1_yellow_1(sK0) != u1_orders_2(k2_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( k1_yellow_1(sK0) != u1_orders_2(k2_yellow_1(sK0))
    | sK0 != u1_struct_0(k2_yellow_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f17])).

fof(f17,plain,
    ( ? [X0] :
        ( k1_yellow_1(X0) != u1_orders_2(k2_yellow_1(X0))
        | u1_struct_0(k2_yellow_1(X0)) != X0 )
   => ( k1_yellow_1(sK0) != u1_orders_2(k2_yellow_1(sK0))
      | sK0 != u1_struct_0(k2_yellow_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( k1_yellow_1(X0) != u1_orders_2(k2_yellow_1(X0))
      | u1_struct_0(k2_yellow_1(X0)) != X0 ) ),
    inference(ennf_transformation,[],[f7])).

% (14853)Termination reason: Refutation not found, incomplete strategy

% (14853)Memory used [KB]: 10618
% (14853)Time elapsed: 0.109 s
% (14853)------------------------------
% (14853)------------------------------
fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( k1_yellow_1(X0) = u1_orders_2(k2_yellow_1(X0))
        & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( k1_yellow_1(X0) = u1_orders_2(k2_yellow_1(X0))
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:08:46 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (14840)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (14837)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (14845)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (14833)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (14837)Refutation not found, incomplete strategy% (14837)------------------------------
% 0.21/0.52  % (14837)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (14837)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (14837)Memory used [KB]: 6140
% 0.21/0.52  % (14837)Time elapsed: 0.106 s
% 0.21/0.52  % (14837)------------------------------
% 0.21/0.52  % (14837)------------------------------
% 0.21/0.52  % (14848)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (14853)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  % (14841)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (14840)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(subsumption_resolution,[],[f42,f55])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    ( ! [X0] : (k1_yellow_1(X0) = u1_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.52    inference(equality_resolution,[],[f53])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ( ! [X2,X3] : (k2_yellow_1(X2) != k2_yellow_1(X3) | u1_orders_2(k2_yellow_1(X2)) = k1_yellow_1(X3)) )),
% 0.21/0.52    inference(superposition,[],[f48,f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X0] : (k2_yellow_1(X0) = g1_orders_2(X0,u1_orders_2(k2_yellow_1(X0)))) )),
% 0.21/0.52    inference(backward_demodulation,[],[f32,f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 0.21/0.52    inference(equality_resolution,[],[f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X2,X3] : (k2_yellow_1(X2) != k2_yellow_1(X3) | u1_struct_0(k2_yellow_1(X2)) = X3) )),
% 0.21/0.52    inference(superposition,[],[f34,f32])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k2_yellow_1(X0) != g1_orders_2(X1,X2) | X0 = X1) )),
% 0.21/0.52    inference(superposition,[],[f33,f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ( ! [X0] : (k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0] : k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_yellow_1)).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (g1_orders_2(X0,k1_yellow_1(X0)) != g1_orders_2(X1,X2) | X0 = X1) )),
% 0.21/0.52    inference(resolution,[],[f25,f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ( ! [X0] : (m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ! [X0] : m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.21/0.52    inference(pure_predicate_removal,[],[f10])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ! [X0] : (m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_relat_2(k1_yellow_1(X0)))),
% 0.21/0.52    inference(pure_predicate_removal,[],[f9])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    ! [X0] : (m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v4_relat_2(k1_yellow_1(X0)) & v1_relat_2(k1_yellow_1(X0)))),
% 0.21/0.52    inference(pure_predicate_removal,[],[f8])).
% 0.21/0.52  fof(f8,plain,(
% 0.21/0.52    ! [X0] : (m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(k1_yellow_1(X0)) & v4_relat_2(k1_yellow_1(X0)) & v1_relat_2(k1_yellow_1(X0)))),
% 0.21/0.52    inference(pure_predicate_removal,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0] : (m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k1_yellow_1(X0),X0) & v8_relat_2(k1_yellow_1(X0)) & v4_relat_2(k1_yellow_1(X0)) & v1_relat_2(k1_yellow_1(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_1)).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | X0 = X2) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ! [X2,X3] : (g1_orders_2(X0,X1) = g1_orders_2(X2,X3) => (X1 = X3 & X0 = X2)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ( ! [X0] : (k2_yellow_1(X0) = g1_orders_2(u1_struct_0(k2_yellow_1(X0)),u1_orders_2(k2_yellow_1(X0)))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f31,f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.52    inference(forward_demodulation,[],[f29,f20])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ( ! [X0] : (l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))) )),
% 0.21/0.52    inference(resolution,[],[f24,f21])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | l1_orders_2(g1_orders_2(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0,X1] : ((l1_orders_2(g1_orders_2(X0,X1)) & v1_orders_2(g1_orders_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => (l1_orders_2(g1_orders_2(X0,X1)) & v1_orders_2(g1_orders_2(X0,X1))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_orders_2)).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ( ! [X0] : (k2_yellow_1(X0) = g1_orders_2(u1_struct_0(k2_yellow_1(X0)),u1_orders_2(k2_yellow_1(X0))) | ~l1_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.52    inference(resolution,[],[f22,f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ( ! [X0] : (v1_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.52    inference(forward_demodulation,[],[f27,f20])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ( ! [X0] : (v1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))) )),
% 0.21/0.52    inference(resolution,[],[f23,f21])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | v1_orders_2(g1_orders_2(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_orders_2(X0) | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 | ~l1_orders_2(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0] : (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 | ~v1_orders_2(X0) | ~l1_orders_2(X0))),
% 0.21/0.52    inference(flattening,[],[f13])).
% 0.21/0.52  % (14853)Refutation not found, incomplete strategy% (14853)------------------------------
% 0.21/0.52  % (14853)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ! [X0] : ((g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 | ~v1_orders_2(X0)) | ~l1_orders_2(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0] : (l1_orders_2(X0) => (v1_orders_2(X0) => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_orders_2)).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k2_yellow_1(X0) != g1_orders_2(X1,X2) | k1_yellow_1(X0) = X2) )),
% 0.21/0.52    inference(superposition,[],[f47,f20])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (g1_orders_2(X0,k1_yellow_1(X0)) != g1_orders_2(X1,X2) | k1_yellow_1(X0) = X2) )),
% 0.21/0.52    inference(resolution,[],[f26,f21])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | X1 = X3) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  % (14841)Refutation not found, incomplete strategy% (14841)------------------------------
% 0.21/0.52  % (14841)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (14841)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (14841)Memory used [KB]: 10618
% 0.21/0.52  % (14841)Time elapsed: 0.104 s
% 0.21/0.52  % (14841)------------------------------
% 0.21/0.52  % (14841)------------------------------
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    k1_yellow_1(sK0) != u1_orders_2(k2_yellow_1(sK0))),
% 0.21/0.52    inference(subsumption_resolution,[],[f19,f41])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    sK0 != u1_struct_0(k2_yellow_1(sK0)) | k1_yellow_1(sK0) != u1_orders_2(k2_yellow_1(sK0))),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    k1_yellow_1(sK0) != u1_orders_2(k2_yellow_1(sK0)) | sK0 != u1_struct_0(k2_yellow_1(sK0))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ? [X0] : (k1_yellow_1(X0) != u1_orders_2(k2_yellow_1(X0)) | u1_struct_0(k2_yellow_1(X0)) != X0) => (k1_yellow_1(sK0) != u1_orders_2(k2_yellow_1(sK0)) | sK0 != u1_struct_0(k2_yellow_1(sK0)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ? [X0] : (k1_yellow_1(X0) != u1_orders_2(k2_yellow_1(X0)) | u1_struct_0(k2_yellow_1(X0)) != X0)),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  % (14853)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (14853)Memory used [KB]: 10618
% 0.21/0.52  % (14853)Time elapsed: 0.109 s
% 0.21/0.52  % (14853)------------------------------
% 0.21/0.52  % (14853)------------------------------
% 0.21/0.52  fof(f7,negated_conjecture,(
% 0.21/0.52    ~! [X0] : (k1_yellow_1(X0) = u1_orders_2(k2_yellow_1(X0)) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 0.21/0.52    inference(negated_conjecture,[],[f6])).
% 0.21/0.52  fof(f6,conjecture,(
% 0.21/0.52    ! [X0] : (k1_yellow_1(X0) = u1_orders_2(k2_yellow_1(X0)) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (14840)------------------------------
% 0.21/0.52  % (14840)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (14840)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (14840)Memory used [KB]: 6268
% 0.21/0.52  % (14840)Time elapsed: 0.105 s
% 0.21/0.52  % (14840)------------------------------
% 0.21/0.52  % (14840)------------------------------
% 0.21/0.52  % (14832)Success in time 0.158 s
%------------------------------------------------------------------------------
