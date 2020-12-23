%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:39 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 124 expanded)
%              Number of leaves         :    7 (  29 expanded)
%              Depth                    :   13
%              Number of atoms          :  109 ( 351 expanded)
%              Number of equality atoms :   56 ( 126 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f165,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f147,f163])).

fof(f163,plain,(
    spl2_4 ),
    inference(avatar_contradiction_clause,[],[f162])).

fof(f162,plain,
    ( $false
    | spl2_4 ),
    inference(subsumption_resolution,[],[f74,f126])).

fof(f126,plain,(
    u1_struct_0(sK0) = u1_struct_0(sK1) ),
    inference(trivial_inequality_removal,[],[f125])).

fof(f125,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
    | u1_struct_0(sK0) = u1_struct_0(sK1) ),
    inference(superposition,[],[f71,f31])).

fof(f31,plain,(
    u1_pre_topc(sK0) = k9_setfam_1(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f30,f16])).

fof(f16,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_tdlat_3(X1)
          & v1_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_tdlat_3(X1)
          & v1_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ( ( v1_tdlat_3(X0)
                & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
             => v1_tdlat_3(X1) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( ( v1_tdlat_3(X0)
              & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
           => v1_tdlat_3(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tex_2)).

fof(f30,plain,
    ( ~ l1_pre_topc(sK0)
    | u1_pre_topc(sK0) = k9_setfam_1(u1_struct_0(sK0)) ),
    inference(resolution,[],[f14,f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0))
      | ~ v1_tdlat_3(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
      <=> u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tdlat_3)).

fof(f14,plain,(
    v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f71,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X0,k9_setfam_1(X0))
      | u1_struct_0(sK1) = X0 ) ),
    inference(forward_demodulation,[],[f68,f23])).

fof(f23,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f68,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X0,k2_subset_1(k9_setfam_1(X0)))
      | u1_struct_0(sK1) = X0 ) ),
    inference(resolution,[],[f44,f26])).

fof(f26,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k9_setfam_1(X0)) ),
    inference(definition_unfolding,[],[f22,f21])).

fof(f21,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f3])).

% (6926)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
fof(f3,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(f22,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k9_setfam_1(k9_setfam_1(X0)))
      | g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
      | u1_struct_0(sK1) = X0 ) ),
    inference(superposition,[],[f25,f13])).

fof(f13,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k9_setfam_1(k9_setfam_1(X0)))
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2 ) ),
    inference(definition_unfolding,[],[f19,f21,f21])).

fof(f19,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f74,plain,
    ( u1_struct_0(sK0) != u1_struct_0(sK1)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl2_4
  <=> u1_struct_0(sK0) = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f147,plain,(
    ~ spl2_4 ),
    inference(avatar_contradiction_clause,[],[f146])).

fof(f146,plain,
    ( $false
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f141,f86])).

fof(f86,plain,
    ( u1_pre_topc(sK0) != u1_pre_topc(sK1)
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f82,f31])).

fof(f82,plain,
    ( u1_pre_topc(sK1) != k9_setfam_1(u1_struct_0(sK0))
    | ~ spl2_4 ),
    inference(superposition,[],[f29,f75])).

fof(f75,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f73])).

fof(f29,plain,(
    u1_pre_topc(sK1) != k9_setfam_1(u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f27,f15])).

fof(f15,plain,(
    ~ v1_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f27,plain,
    ( u1_pre_topc(sK1) != k9_setfam_1(u1_struct_0(sK1))
    | v1_tdlat_3(sK1) ),
    inference(resolution,[],[f12,f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | u1_pre_topc(X0) != k9_setfam_1(u1_struct_0(X0))
      | v1_tdlat_3(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f12,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f141,plain,(
    u1_pre_topc(sK0) = u1_pre_topc(sK1) ),
    inference(trivial_inequality_removal,[],[f140])).

fof(f140,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
    | u1_pre_topc(sK0) = u1_pre_topc(sK1) ),
    inference(superposition,[],[f94,f31])).

fof(f94,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X0,k9_setfam_1(X0))
      | k9_setfam_1(X0) = u1_pre_topc(sK1) ) ),
    inference(forward_demodulation,[],[f93,f23])).

fof(f93,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X0,k9_setfam_1(X0))
      | u1_pre_topc(sK1) = k2_subset_1(k9_setfam_1(X0)) ) ),
    inference(forward_demodulation,[],[f90,f23])).

fof(f90,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X0,k2_subset_1(k9_setfam_1(X0)))
      | u1_pre_topc(sK1) = k2_subset_1(k9_setfam_1(X0)) ) ),
    inference(resolution,[],[f46,f26])).

fof(f46,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X5,k9_setfam_1(k9_setfam_1(X4)))
      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X4,X5)
      | u1_pre_topc(sK1) = X5 ) ),
    inference(superposition,[],[f24,f13])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k9_setfam_1(k9_setfam_1(X0)))
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X1 = X3 ) ),
    inference(definition_unfolding,[],[f20,f21,f21])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:17:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.51  % (6918)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.51  % (6918)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % (6910)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (6914)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f165,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f147,f163])).
% 0.20/0.51  fof(f163,plain,(
% 0.20/0.51    spl2_4),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f162])).
% 0.20/0.51  fof(f162,plain,(
% 0.20/0.51    $false | spl2_4),
% 0.20/0.51    inference(subsumption_resolution,[],[f74,f126])).
% 0.20/0.51  fof(f126,plain,(
% 0.20/0.51    u1_struct_0(sK0) = u1_struct_0(sK1)),
% 0.20/0.51    inference(trivial_inequality_removal,[],[f125])).
% 0.20/0.51  fof(f125,plain,(
% 0.20/0.51    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | u1_struct_0(sK0) = u1_struct_0(sK1)),
% 0.20/0.51    inference(superposition,[],[f71,f31])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    u1_pre_topc(sK0) = k9_setfam_1(u1_struct_0(sK0))),
% 0.20/0.51    inference(subsumption_resolution,[],[f30,f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    l1_pre_topc(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (~v1_tdlat_3(X1) & v1_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 0.20/0.51    inference(flattening,[],[f8])).
% 0.20/0.51  fof(f8,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : ((~v1_tdlat_3(X1) & (v1_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,negated_conjecture,(
% 0.20/0.51    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ((v1_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v1_tdlat_3(X1))))),
% 0.20/0.51    inference(negated_conjecture,[],[f6])).
% 0.20/0.51  fof(f6,conjecture,(
% 0.20/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ((v1_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v1_tdlat_3(X1))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tex_2)).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ~l1_pre_topc(sK0) | u1_pre_topc(sK0) = k9_setfam_1(u1_struct_0(sK0))),
% 0.20/0.51    inference(resolution,[],[f14,f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ( ! [X0] : (~l1_pre_topc(X0) | u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0)) | ~v1_tdlat_3(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,plain,(
% 0.20/0.51    ! [X0] : ((v1_tdlat_3(X0) <=> u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0] : (l1_pre_topc(X0) => (v1_tdlat_3(X0) <=> u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tdlat_3)).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    v1_tdlat_3(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f9])).
% 0.20/0.51  fof(f71,plain,(
% 0.20/0.51    ( ! [X0] : (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X0,k9_setfam_1(X0)) | u1_struct_0(sK1) = X0) )),
% 0.20/0.51    inference(forward_demodulation,[],[f68,f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0] : k2_subset_1(X0) = X0),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.20/0.51  fof(f68,plain,(
% 0.20/0.51    ( ! [X0] : (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X0,k2_subset_1(k9_setfam_1(X0))) | u1_struct_0(sK1) = X0) )),
% 0.20/0.51    inference(resolution,[],[f44,f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k9_setfam_1(X0))) )),
% 0.20/0.51    inference(definition_unfolding,[],[f22,f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ( ! [X0] : (k1_zfmisc_1(X0) = k9_setfam_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f3])).
% 0.20/0.51  % (6926)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.20/0.51  fof(f44,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k9_setfam_1(k9_setfam_1(X0))) | g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | u1_struct_0(sK1) = X0) )),
% 0.20/0.51    inference(superposition,[],[f25,f13])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),
% 0.20/0.51    inference(cnf_transformation,[],[f9])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k9_setfam_1(k9_setfam_1(X0))) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | X0 = X2) )),
% 0.20/0.51    inference(definition_unfolding,[],[f19,f21,f21])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | X0 = X2) )),
% 0.20/0.51    inference(cnf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,plain,(
% 0.20/0.51    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.51    inference(ennf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).
% 0.20/0.51  fof(f74,plain,(
% 0.20/0.51    u1_struct_0(sK0) != u1_struct_0(sK1) | spl2_4),
% 0.20/0.51    inference(avatar_component_clause,[],[f73])).
% 0.20/0.51  fof(f73,plain,(
% 0.20/0.51    spl2_4 <=> u1_struct_0(sK0) = u1_struct_0(sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.51  fof(f147,plain,(
% 0.20/0.51    ~spl2_4),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f146])).
% 0.20/0.51  fof(f146,plain,(
% 0.20/0.51    $false | ~spl2_4),
% 0.20/0.51    inference(subsumption_resolution,[],[f141,f86])).
% 0.20/0.51  fof(f86,plain,(
% 0.20/0.51    u1_pre_topc(sK0) != u1_pre_topc(sK1) | ~spl2_4),
% 0.20/0.51    inference(forward_demodulation,[],[f82,f31])).
% 0.20/0.51  fof(f82,plain,(
% 0.20/0.51    u1_pre_topc(sK1) != k9_setfam_1(u1_struct_0(sK0)) | ~spl2_4),
% 0.20/0.51    inference(superposition,[],[f29,f75])).
% 0.20/0.51  fof(f75,plain,(
% 0.20/0.51    u1_struct_0(sK0) = u1_struct_0(sK1) | ~spl2_4),
% 0.20/0.51    inference(avatar_component_clause,[],[f73])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    u1_pre_topc(sK1) != k9_setfam_1(u1_struct_0(sK1))),
% 0.20/0.51    inference(subsumption_resolution,[],[f27,f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ~v1_tdlat_3(sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f9])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    u1_pre_topc(sK1) != k9_setfam_1(u1_struct_0(sK1)) | v1_tdlat_3(sK1)),
% 0.20/0.51    inference(resolution,[],[f12,f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ( ! [X0] : (~l1_pre_topc(X0) | u1_pre_topc(X0) != k9_setfam_1(u1_struct_0(X0)) | v1_tdlat_3(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f10])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    l1_pre_topc(sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f9])).
% 0.20/0.51  fof(f141,plain,(
% 0.20/0.51    u1_pre_topc(sK0) = u1_pre_topc(sK1)),
% 0.20/0.51    inference(trivial_inequality_removal,[],[f140])).
% 0.20/0.51  fof(f140,plain,(
% 0.20/0.51    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | u1_pre_topc(sK0) = u1_pre_topc(sK1)),
% 0.20/0.51    inference(superposition,[],[f94,f31])).
% 0.20/0.51  fof(f94,plain,(
% 0.20/0.51    ( ! [X0] : (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X0,k9_setfam_1(X0)) | k9_setfam_1(X0) = u1_pre_topc(sK1)) )),
% 0.20/0.51    inference(forward_demodulation,[],[f93,f23])).
% 0.20/0.51  fof(f93,plain,(
% 0.20/0.51    ( ! [X0] : (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X0,k9_setfam_1(X0)) | u1_pre_topc(sK1) = k2_subset_1(k9_setfam_1(X0))) )),
% 0.20/0.51    inference(forward_demodulation,[],[f90,f23])).
% 0.20/0.51  fof(f90,plain,(
% 0.20/0.51    ( ! [X0] : (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X0,k2_subset_1(k9_setfam_1(X0))) | u1_pre_topc(sK1) = k2_subset_1(k9_setfam_1(X0))) )),
% 0.20/0.51    inference(resolution,[],[f46,f26])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    ( ! [X4,X5] : (~m1_subset_1(X5,k9_setfam_1(k9_setfam_1(X4))) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X4,X5) | u1_pre_topc(sK1) = X5) )),
% 0.20/0.51    inference(superposition,[],[f24,f13])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k9_setfam_1(k9_setfam_1(X0))) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | X1 = X3) )),
% 0.20/0.51    inference(definition_unfolding,[],[f20,f21,f21])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | X1 = X3) )),
% 0.20/0.51    inference(cnf_transformation,[],[f11])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (6918)------------------------------
% 0.20/0.51  % (6918)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (6918)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (6918)Memory used [KB]: 10746
% 0.20/0.51  % (6918)Time elapsed: 0.096 s
% 0.20/0.51  % (6918)------------------------------
% 0.20/0.51  % (6918)------------------------------
% 0.20/0.52  % (6908)Success in time 0.155 s
%------------------------------------------------------------------------------
