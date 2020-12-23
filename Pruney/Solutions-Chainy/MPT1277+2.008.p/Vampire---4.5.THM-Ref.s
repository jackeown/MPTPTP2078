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
% DateTime   : Thu Dec  3 13:12:49 EST 2020

% Result     : Theorem 0.64s
% Output     : Refutation 0.64s
% Verified   : 
% Statistics : Number of formulae       :   42 (  80 expanded)
%              Number of leaves         :    7 (  17 expanded)
%              Depth                    :   12
%              Number of atoms          :  117 ( 285 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f55,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f50,f54])).

fof(f54,plain,(
    spl2_2 ),
    inference(avatar_contradiction_clause,[],[f53])).

fof(f53,plain,
    ( $false
    | spl2_2 ),
    inference(subsumption_resolution,[],[f52,f14])).

fof(f14,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tops_1(k2_tops_1(X0,X1),X0)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tops_1(k2_tops_1(X0,X1),X0)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => v3_tops_1(k2_tops_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => v3_tops_1(k2_tops_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_tops_1)).

fof(f52,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_2 ),
    inference(resolution,[],[f44,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f44,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl2_2
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f50,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f49])).

fof(f49,plain,
    ( $false
    | spl2_1 ),
    inference(subsumption_resolution,[],[f48,f15])).

fof(f15,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f48,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | spl2_1 ),
    inference(subsumption_resolution,[],[f47,f18])).

fof(f18,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f47,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v4_pre_topc(sK1,sK0)
    | spl2_1 ),
    inference(subsumption_resolution,[],[f46,f14])).

fof(f46,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v4_pre_topc(sK1,sK0)
    | spl2_1 ),
    inference(resolution,[],[f40,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

fof(f40,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl2_1
  <=> v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f45,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f36,f42,f38])).

fof(f36,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(subsumption_resolution,[],[f35,f17])).

fof(f17,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f35,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f34,f18])).

fof(f34,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f30,f16])).

fof(f16,plain,(
    ~ v3_tops_1(k2_tops_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f30,plain,
    ( v3_tops_1(k2_tops_1(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(superposition,[],[f22,f28])).

fof(f28,plain,(
    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f26,f18])).

fof(f26,plain,
    ( ~ l1_pre_topc(sK0)
    | k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f19,f14])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_1)).

fof(f22,plain,(
    ! [X0,X1] :
      ( v3_tops_1(k2_tops_1(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(k2_tops_1(X0,X1),X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(k2_tops_1(X0,X1),X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
           => v3_tops_1(k2_tops_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_tops_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:16:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.37  ipcrm: permission denied for id (797114369)
% 0.64/0.57  % (31909)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.64/0.57  % (31905)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.64/0.58  % (31903)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.64/0.58  % (31903)Refutation found. Thanks to Tanya!
% 0.64/0.58  % SZS status Theorem for theBenchmark
% 0.64/0.58  % SZS output start Proof for theBenchmark
% 0.64/0.58  fof(f55,plain,(
% 0.64/0.58    $false),
% 0.64/0.58    inference(avatar_sat_refutation,[],[f45,f50,f54])).
% 0.64/0.58  fof(f54,plain,(
% 0.64/0.58    spl2_2),
% 0.64/0.58    inference(avatar_contradiction_clause,[],[f53])).
% 0.64/0.58  fof(f53,plain,(
% 0.64/0.58    $false | spl2_2),
% 0.64/0.58    inference(subsumption_resolution,[],[f52,f14])).
% 0.64/0.58  fof(f14,plain,(
% 0.64/0.58    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.64/0.58    inference(cnf_transformation,[],[f8])).
% 0.64/0.58  fof(f8,plain,(
% 0.64/0.58    ? [X0] : (? [X1] : (~v3_tops_1(k2_tops_1(X0,X1),X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.64/0.58    inference(flattening,[],[f7])).
% 0.64/0.58  fof(f7,plain,(
% 0.64/0.58    ? [X0] : (? [X1] : ((~v3_tops_1(k2_tops_1(X0,X1),X0) & v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.64/0.58    inference(ennf_transformation,[],[f6])).
% 0.64/0.58  fof(f6,negated_conjecture,(
% 0.64/0.58    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => v3_tops_1(k2_tops_1(X0,X1),X0))))),
% 0.64/0.58    inference(negated_conjecture,[],[f5])).
% 0.64/0.58  fof(f5,conjecture,(
% 0.64/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => v3_tops_1(k2_tops_1(X0,X1),X0))))),
% 0.64/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_tops_1)).
% 0.64/0.58  fof(f52,plain,(
% 0.64/0.58    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl2_2),
% 0.64/0.58    inference(resolution,[],[f44,f23])).
% 0.64/0.58  fof(f23,plain,(
% 0.64/0.58    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.64/0.58    inference(cnf_transformation,[],[f13])).
% 0.64/0.58  fof(f13,plain,(
% 0.64/0.58    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.64/0.58    inference(ennf_transformation,[],[f1])).
% 0.64/0.58  fof(f1,axiom,(
% 0.64/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.64/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.64/0.58  fof(f44,plain,(
% 0.64/0.58    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_2),
% 0.64/0.58    inference(avatar_component_clause,[],[f42])).
% 0.64/0.58  fof(f42,plain,(
% 0.64/0.58    spl2_2 <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.64/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.64/0.58  fof(f50,plain,(
% 0.64/0.58    spl2_1),
% 0.64/0.58    inference(avatar_contradiction_clause,[],[f49])).
% 0.64/0.58  fof(f49,plain,(
% 0.64/0.58    $false | spl2_1),
% 0.64/0.58    inference(subsumption_resolution,[],[f48,f15])).
% 0.64/0.58  fof(f15,plain,(
% 0.64/0.58    v4_pre_topc(sK1,sK0)),
% 0.64/0.58    inference(cnf_transformation,[],[f8])).
% 0.64/0.58  fof(f48,plain,(
% 0.64/0.58    ~v4_pre_topc(sK1,sK0) | spl2_1),
% 0.64/0.58    inference(subsumption_resolution,[],[f47,f18])).
% 0.64/0.58  fof(f18,plain,(
% 0.64/0.58    l1_pre_topc(sK0)),
% 0.64/0.58    inference(cnf_transformation,[],[f8])).
% 0.64/0.58  fof(f47,plain,(
% 0.64/0.58    ~l1_pre_topc(sK0) | ~v4_pre_topc(sK1,sK0) | spl2_1),
% 0.64/0.58    inference(subsumption_resolution,[],[f46,f14])).
% 0.64/0.58  fof(f46,plain,(
% 0.64/0.58    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v4_pre_topc(sK1,sK0) | spl2_1),
% 0.64/0.58    inference(resolution,[],[f40,f21])).
% 0.64/0.58  fof(f21,plain,(
% 0.64/0.58    ( ! [X0,X1] : (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0)) )),
% 0.64/0.58    inference(cnf_transformation,[],[f10])).
% 0.64/0.58  fof(f10,plain,(
% 0.64/0.58    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.64/0.58    inference(ennf_transformation,[],[f2])).
% 0.64/0.58  fof(f2,axiom,(
% 0.64/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.64/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).
% 0.64/0.58  fof(f40,plain,(
% 0.64/0.58    ~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | spl2_1),
% 0.64/0.58    inference(avatar_component_clause,[],[f38])).
% 0.64/0.58  fof(f38,plain,(
% 0.64/0.58    spl2_1 <=> v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 0.64/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.64/0.58  fof(f45,plain,(
% 0.64/0.58    ~spl2_1 | ~spl2_2),
% 0.64/0.58    inference(avatar_split_clause,[],[f36,f42,f38])).
% 0.64/0.58  fof(f36,plain,(
% 0.64/0.58    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 0.64/0.58    inference(subsumption_resolution,[],[f35,f17])).
% 0.64/0.58  fof(f17,plain,(
% 0.64/0.58    v2_pre_topc(sK0)),
% 0.64/0.58    inference(cnf_transformation,[],[f8])).
% 0.64/0.58  fof(f35,plain,(
% 0.64/0.58    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~v2_pre_topc(sK0)),
% 0.64/0.58    inference(subsumption_resolution,[],[f34,f18])).
% 0.64/0.58  fof(f34,plain,(
% 0.64/0.58    ~l1_pre_topc(sK0) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~v2_pre_topc(sK0)),
% 0.64/0.58    inference(subsumption_resolution,[],[f30,f16])).
% 0.64/0.58  fof(f16,plain,(
% 0.64/0.58    ~v3_tops_1(k2_tops_1(sK0,sK1),sK0)),
% 0.64/0.58    inference(cnf_transformation,[],[f8])).
% 0.64/0.58  fof(f30,plain,(
% 0.64/0.58    v3_tops_1(k2_tops_1(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~v2_pre_topc(sK0)),
% 0.64/0.58    inference(superposition,[],[f22,f28])).
% 0.64/0.58  fof(f28,plain,(
% 0.64/0.58    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),
% 0.64/0.58    inference(subsumption_resolution,[],[f26,f18])).
% 0.64/0.58  fof(f26,plain,(
% 0.64/0.58    ~l1_pre_topc(sK0) | k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),
% 0.64/0.58    inference(resolution,[],[f19,f14])).
% 0.64/0.58  fof(f19,plain,(
% 0.64/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))) )),
% 0.64/0.58    inference(cnf_transformation,[],[f9])).
% 0.64/0.58  fof(f9,plain,(
% 0.64/0.58    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.64/0.58    inference(ennf_transformation,[],[f3])).
% 0.64/0.58  fof(f3,axiom,(
% 0.64/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))))),
% 0.64/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_1)).
% 0.64/0.58  fof(f22,plain,(
% 0.64/0.58    ( ! [X0,X1] : (v3_tops_1(k2_tops_1(X0,X1),X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~v2_pre_topc(X0)) )),
% 0.64/0.58    inference(cnf_transformation,[],[f12])).
% 0.64/0.58  fof(f12,plain,(
% 0.64/0.58    ! [X0] : (! [X1] : (v3_tops_1(k2_tops_1(X0,X1),X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.64/0.58    inference(flattening,[],[f11])).
% 0.64/0.58  fof(f11,plain,(
% 0.64/0.58    ! [X0] : (! [X1] : ((v3_tops_1(k2_tops_1(X0,X1),X0) | ~v3_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.64/0.58    inference(ennf_transformation,[],[f4])).
% 0.64/0.58  fof(f4,axiom,(
% 0.64/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) => v3_tops_1(k2_tops_1(X0,X1),X0))))),
% 0.64/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_tops_1)).
% 0.64/0.58  % SZS output end Proof for theBenchmark
% 0.64/0.58  % (31903)------------------------------
% 0.64/0.58  % (31903)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.64/0.58  % (31903)Termination reason: Refutation
% 0.64/0.58  
% 0.64/0.58  % (31903)Memory used [KB]: 10618
% 0.64/0.58  % (31903)Time elapsed: 0.004 s
% 0.64/0.58  % (31903)------------------------------
% 0.64/0.58  % (31903)------------------------------
% 0.64/0.58  % (31766)Success in time 0.215 s
%------------------------------------------------------------------------------
