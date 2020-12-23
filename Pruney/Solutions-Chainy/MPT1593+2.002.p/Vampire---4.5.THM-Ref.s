%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:26 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   37 (  68 expanded)
%              Number of leaves         :    6 (  17 expanded)
%              Depth                    :   11
%              Number of atoms          :   79 ( 138 expanded)
%              Number of equality atoms :   41 (  63 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f53,plain,(
    $false ),
    inference(subsumption_resolution,[],[f52,f36])).

fof(f36,plain,(
    ! [X0] : k1_yellow_1(X0) = u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( g1_orders_2(X0,k1_yellow_1(X0)) != g1_orders_2(X1,k1_yellow_1(X1))
      | u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) = k1_yellow_1(X1) ) ),
    inference(resolution,[],[f31,f18])).

fof(f18,plain,(
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
    inference(pure_predicate_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k1_yellow_1(X0),X0)
      & v8_relat_2(k1_yellow_1(X0))
      & v4_relat_2(k1_yellow_1(X0))
      & v1_relat_2(k1_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_1)).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | g1_orders_2(X0,k1_yellow_1(X0)) != g1_orders_2(X1,X2)
      | u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) = X2 ) ),
    inference(superposition,[],[f23,f28])).

fof(f28,plain,(
    ! [X0] : g1_orders_2(X0,k1_yellow_1(X0)) = g1_orders_2(u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))),u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))) ),
    inference(subsumption_resolution,[],[f27,f25])).

fof(f25,plain,(
    ! [X0] : l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(definition_unfolding,[],[f20,f17])).

fof(f17,plain,(
    ! [X0] : k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_yellow_1)).

fof(f20,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(f27,plain,(
    ! [X0] :
      ( ~ l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))
      | g1_orders_2(X0,k1_yellow_1(X0)) = g1_orders_2(u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))),u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))) ) ),
    inference(resolution,[],[f21,f26])).

fof(f26,plain,(
    ! [X0] : v1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(definition_unfolding,[],[f19,f17])).

fof(f19,plain,(
    ! [X0] : v1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ) ),
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_orders_2(X0)
       => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_orders_2)).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(f52,plain,(
    k1_yellow_1(sK0) != u1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
    inference(trivial_inequality_removal,[],[f48])).

fof(f48,plain,
    ( sK0 != sK0
    | k1_yellow_1(sK0) != u1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
    inference(backward_demodulation,[],[f24,f47])).

fof(f47,plain,(
    ! [X0] : u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))) = X0 ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( g1_orders_2(X0,k1_yellow_1(X0)) != g1_orders_2(X1,k1_yellow_1(X1))
      | u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))) = X1 ) ),
    inference(resolution,[],[f33,f18])).

fof(f33,plain,(
    ! [X6,X8,X7] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X7,X7)))
      | g1_orders_2(X6,k1_yellow_1(X6)) != g1_orders_2(X7,X8)
      | u1_struct_0(g1_orders_2(X6,k1_yellow_1(X6))) = X7 ) ),
    inference(superposition,[],[f22,f28])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f24,plain,
    ( sK0 != u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | k1_yellow_1(sK0) != u1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
    inference(definition_unfolding,[],[f16,f17,f17])).

fof(f16,plain,
    ( sK0 != u1_struct_0(k2_yellow_1(sK0))
    | k1_yellow_1(sK0) != u1_orders_2(k2_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( k1_yellow_1(X0) != u1_orders_2(k2_yellow_1(X0))
      | u1_struct_0(k2_yellow_1(X0)) != X0 ) ),
    inference(ennf_transformation,[],[f7])).

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
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.20/0.35  % DateTime   : Tue Dec  1 17:40:45 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.52  % (596)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (595)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (613)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (605)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (613)Refutation not found, incomplete strategy% (613)------------------------------
% 0.20/0.53  % (613)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (613)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (613)Memory used [KB]: 10618
% 0.20/0.53  % (613)Time elapsed: 0.071 s
% 0.20/0.53  % (613)------------------------------
% 0.20/0.53  % (613)------------------------------
% 0.20/0.53  % (597)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (597)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f53,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(subsumption_resolution,[],[f52,f36])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    ( ! [X0] : (k1_yellow_1(X0) = u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))) )),
% 0.20/0.53    inference(equality_resolution,[],[f35])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    ( ! [X0,X1] : (g1_orders_2(X0,k1_yellow_1(X0)) != g1_orders_2(X1,k1_yellow_1(X1)) | u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) = k1_yellow_1(X1)) )),
% 0.20/0.53    inference(resolution,[],[f31,f18])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    ( ! [X0] : (m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f11])).
% 0.20/0.53  fof(f11,plain,(
% 0.20/0.53    ! [X0] : m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.20/0.53    inference(pure_predicate_removal,[],[f10])).
% 0.20/0.53  fof(f10,plain,(
% 0.20/0.53    ! [X0] : (m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_relat_2(k1_yellow_1(X0)))),
% 0.20/0.53    inference(pure_predicate_removal,[],[f9])).
% 0.20/0.53  fof(f9,plain,(
% 0.20/0.53    ! [X0] : (m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v4_relat_2(k1_yellow_1(X0)) & v1_relat_2(k1_yellow_1(X0)))),
% 0.20/0.53    inference(pure_predicate_removal,[],[f8])).
% 0.20/0.53  fof(f8,plain,(
% 0.20/0.53    ! [X0] : (m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(k1_yellow_1(X0)) & v4_relat_2(k1_yellow_1(X0)) & v1_relat_2(k1_yellow_1(X0)))),
% 0.20/0.53    inference(pure_predicate_removal,[],[f4])).
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0] : (m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k1_yellow_1(X0),X0) & v8_relat_2(k1_yellow_1(X0)) & v4_relat_2(k1_yellow_1(X0)) & v1_relat_2(k1_yellow_1(X0)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_1)).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) | g1_orders_2(X0,k1_yellow_1(X0)) != g1_orders_2(X1,X2) | u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) = X2) )),
% 0.20/0.53    inference(superposition,[],[f23,f28])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ( ! [X0] : (g1_orders_2(X0,k1_yellow_1(X0)) = g1_orders_2(u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))),u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))))) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f27,f25])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    ( ! [X0] : (l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))) )),
% 0.20/0.53    inference(definition_unfolding,[],[f20,f17])).
% 0.20/0.53  fof(f17,plain,(
% 0.20/0.53    ( ! [X0] : (k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0] : k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_yellow_1)).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    ( ! [X0] : (~l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) | g1_orders_2(X0,k1_yellow_1(X0)) = g1_orders_2(u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))),u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))))) )),
% 0.20/0.53    inference(resolution,[],[f21,f26])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    ( ! [X0] : (v1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))) )),
% 0.20/0.53    inference(definition_unfolding,[],[f19,f17])).
% 0.20/0.53  fof(f19,plain,(
% 0.20/0.53    ( ! [X0] : (v1_orders_2(k2_yellow_1(X0))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f5])).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    ( ! [X0] : (~v1_orders_2(X0) | ~l1_orders_2(X0) | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0) )),
% 0.20/0.53    inference(cnf_transformation,[],[f14])).
% 0.20/0.53  fof(f14,plain,(
% 0.20/0.53    ! [X0] : (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 | ~v1_orders_2(X0) | ~l1_orders_2(X0))),
% 0.20/0.53    inference(flattening,[],[f13])).
% 0.20/0.53  fof(f13,plain,(
% 0.20/0.53    ! [X0] : ((g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 | ~v1_orders_2(X0)) | ~l1_orders_2(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0] : (l1_orders_2(X0) => (v1_orders_2(X0) => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_orders_2)).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | X1 = X3) )),
% 0.20/0.53    inference(cnf_transformation,[],[f15])).
% 0.20/0.53  fof(f15,plain,(
% 0.20/0.53    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 0.20/0.53    inference(ennf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ! [X2,X3] : (g1_orders_2(X0,X1) = g1_orders_2(X2,X3) => (X1 = X3 & X0 = X2)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).
% 0.20/0.53  fof(f52,plain,(
% 0.20/0.53    k1_yellow_1(sK0) != u1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))),
% 0.20/0.53    inference(trivial_inequality_removal,[],[f48])).
% 0.20/0.53  fof(f48,plain,(
% 0.20/0.53    sK0 != sK0 | k1_yellow_1(sK0) != u1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))),
% 0.20/0.53    inference(backward_demodulation,[],[f24,f47])).
% 0.20/0.53  fof(f47,plain,(
% 0.20/0.53    ( ! [X0] : (u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))) = X0) )),
% 0.20/0.53    inference(equality_resolution,[],[f46])).
% 0.20/0.53  fof(f46,plain,(
% 0.20/0.53    ( ! [X0,X1] : (g1_orders_2(X0,k1_yellow_1(X0)) != g1_orders_2(X1,k1_yellow_1(X1)) | u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))) = X1) )),
% 0.20/0.53    inference(resolution,[],[f33,f18])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    ( ! [X6,X8,X7] : (~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X7,X7))) | g1_orders_2(X6,k1_yellow_1(X6)) != g1_orders_2(X7,X8) | u1_struct_0(g1_orders_2(X6,k1_yellow_1(X6))) = X7) )),
% 0.20/0.53    inference(superposition,[],[f22,f28])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | X0 = X2) )),
% 0.20/0.53    inference(cnf_transformation,[],[f15])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    sK0 != u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))) | k1_yellow_1(sK0) != u1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))),
% 0.20/0.53    inference(definition_unfolding,[],[f16,f17,f17])).
% 0.20/0.53  fof(f16,plain,(
% 0.20/0.53    sK0 != u1_struct_0(k2_yellow_1(sK0)) | k1_yellow_1(sK0) != u1_orders_2(k2_yellow_1(sK0))),
% 0.20/0.53    inference(cnf_transformation,[],[f12])).
% 0.20/0.53  fof(f12,plain,(
% 0.20/0.53    ? [X0] : (k1_yellow_1(X0) != u1_orders_2(k2_yellow_1(X0)) | u1_struct_0(k2_yellow_1(X0)) != X0)),
% 0.20/0.53    inference(ennf_transformation,[],[f7])).
% 0.20/0.53  fof(f7,negated_conjecture,(
% 0.20/0.53    ~! [X0] : (k1_yellow_1(X0) = u1_orders_2(k2_yellow_1(X0)) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 0.20/0.53    inference(negated_conjecture,[],[f6])).
% 0.20/0.53  fof(f6,conjecture,(
% 0.20/0.53    ! [X0] : (k1_yellow_1(X0) = u1_orders_2(k2_yellow_1(X0)) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (597)------------------------------
% 0.20/0.53  % (597)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (597)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (597)Memory used [KB]: 6268
% 0.20/0.53  % (597)Time elapsed: 0.076 s
% 0.20/0.53  % (597)------------------------------
% 0.20/0.53  % (597)------------------------------
% 0.20/0.53  % (604)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.54  % (590)Success in time 0.174 s
%------------------------------------------------------------------------------
