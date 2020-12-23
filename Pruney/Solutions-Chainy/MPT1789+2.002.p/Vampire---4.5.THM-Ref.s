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
% DateTime   : Thu Dec  3 13:19:21 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 235 expanded)
%              Number of leaves         :    8 (  49 expanded)
%              Depth                    :   10
%              Number of atoms          :  156 (1093 expanded)
%              Number of equality atoms :   37 ( 310 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f71,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f63,f70])).

fof(f70,plain,(
    spl2_2 ),
    inference(avatar_contradiction_clause,[],[f69])).

fof(f69,plain,
    ( $false
    | spl2_2 ),
    inference(unit_resulting_resolution,[],[f35,f37,f66,f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f66,plain,
    ( ! [X0] : k6_tmap_1(sK0,sK1) != g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,sK1)),X0)
    | spl2_2 ),
    inference(forward_demodulation,[],[f65,f38])).

fof(f38,plain,(
    k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f21,f22,f23,f20,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_tmap_1)).

fof(f20,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k5_tmap_1(X0,X1) != u1_pre_topc(k6_tmap_1(X0,X1))
            | u1_struct_0(X0) != u1_struct_0(k6_tmap_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k5_tmap_1(X0,X1) != u1_pre_topc(k6_tmap_1(X0,X1))
            | u1_struct_0(X0) != u1_struct_0(k6_tmap_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
              & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).

fof(f23,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f22,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f21,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f65,plain,
    ( ! [X0] : g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)) != g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,sK1)),X0)
    | spl2_2 ),
    inference(unit_resulting_resolution,[],[f39,f52,f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f52,plain,
    ( u1_struct_0(sK0) != u1_struct_0(k6_tmap_1(sK0,sK1))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl2_2
  <=> u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f39,plain,(
    m1_subset_1(k5_tmap_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(unit_resulting_resolution,[],[f21,f22,f23,f20,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_tmap_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_tmap_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_tmap_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_tmap_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_tmap_1)).

fof(f37,plain,(
    l1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f21,f22,f23,f20,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k6_tmap_1(X0,X1))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_tmap_1)).

fof(f35,plain,(
    v1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f21,f22,f23,f20,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_pre_topc(k6_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f63,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f62])).

fof(f62,plain,
    ( $false
    | spl2_1 ),
    inference(unit_resulting_resolution,[],[f35,f37,f55,f24])).

fof(f55,plain,
    ( ! [X0] : k6_tmap_1(sK0,sK1) != g1_pre_topc(X0,u1_pre_topc(k6_tmap_1(sK0,sK1)))
    | spl2_1 ),
    inference(forward_demodulation,[],[f54,f38])).

fof(f54,plain,
    ( ! [X0] : g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)) != g1_pre_topc(X0,u1_pre_topc(k6_tmap_1(sK0,sK1)))
    | spl2_1 ),
    inference(unit_resulting_resolution,[],[f48,f39,f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f48,plain,
    ( k5_tmap_1(sK0,sK1) != u1_pre_topc(k6_tmap_1(sK0,sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl2_1
  <=> k5_tmap_1(sK0,sK1) = u1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f53,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f19,f50,f46])).

fof(f19,plain,
    ( u1_struct_0(sK0) != u1_struct_0(k6_tmap_1(sK0,sK1))
    | k5_tmap_1(sK0,sK1) != u1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:50:32 EST 2020
% 0.21/0.34  % CPUTime    : 
% 0.21/0.50  % (16054)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (16072)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.50  % (16053)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.50  % (16054)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f53,f63,f70])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    spl2_2),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f69])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    $false | spl2_2),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f35,f37,f66,f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_pre_topc(X0) | ~l1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f10])).
% 0.21/0.50  fof(f10,plain,(
% 0.21/0.50    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    ( ! [X0] : (k6_tmap_1(sK0,sK1) != g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,sK1)),X0)) ) | spl2_2),
% 0.21/0.50    inference(forward_demodulation,[],[f65,f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1))),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f21,f22,f23,f20,f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_tmap_1)).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.50    inference(cnf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : ((k5_tmap_1(X0,X1) != u1_pre_topc(k6_tmap_1(X0,X1)) | u1_struct_0(X0) != u1_struct_0(k6_tmap_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f8])).
% 0.21/0.50  fof(f8,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : ((k5_tmap_1(X0,X1) != u1_pre_topc(k6_tmap_1(X0,X1)) | u1_struct_0(X0) != u1_struct_0(k6_tmap_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,negated_conjecture,(
% 0.21/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 0.21/0.50    inference(negated_conjecture,[],[f6])).
% 0.21/0.50  fof(f6,conjecture,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    l1_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f9])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    v2_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f9])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ~v2_struct_0(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f9])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    ( ! [X0] : (g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)) != g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,sK1)),X0)) ) | spl2_2),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f39,f52,f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | X0 = X2) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    u1_struct_0(sK0) != u1_struct_0(k6_tmap_1(sK0,sK1)) | spl2_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    spl2_2 <=> u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    m1_subset_1(k5_tmap_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f21,f22,f23,f20,f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ( ! [X0,X1] : (m1_subset_1(k5_tmap_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(k5_tmap_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(k5_tmap_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k5_tmap_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_tmap_1)).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    l1_pre_topc(k6_tmap_1(sK0,sK1))),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f21,f22,f23,f20,f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ( ! [X0,X1] : (l1_pre_topc(k6_tmap_1(X0,X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_tmap_1)).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    v1_pre_topc(k6_tmap_1(sK0,sK1))),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f21,f22,f23,f20,f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_pre_topc(k6_tmap_1(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    spl2_1),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f62])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    $false | spl2_1),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f35,f37,f55,f24])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ( ! [X0] : (k6_tmap_1(sK0,sK1) != g1_pre_topc(X0,u1_pre_topc(k6_tmap_1(sK0,sK1)))) ) | spl2_1),
% 0.21/0.51    inference(forward_demodulation,[],[f54,f38])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ( ! [X0] : (g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)) != g1_pre_topc(X0,u1_pre_topc(k6_tmap_1(sK0,sK1)))) ) | spl2_1),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f48,f39,f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | X1 = X3) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    k5_tmap_1(sK0,sK1) != u1_pre_topc(k6_tmap_1(sK0,sK1)) | spl2_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f46])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    spl2_1 <=> k5_tmap_1(sK0,sK1) = u1_pre_topc(k6_tmap_1(sK0,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    ~spl2_1 | ~spl2_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f19,f50,f46])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    u1_struct_0(sK0) != u1_struct_0(k6_tmap_1(sK0,sK1)) | k5_tmap_1(sK0,sK1) != u1_pre_topc(k6_tmap_1(sK0,sK1))),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (16054)------------------------------
% 0.21/0.51  % (16054)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (16054)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (16054)Memory used [KB]: 6268
% 0.21/0.51  % (16054)Time elapsed: 0.109 s
% 0.21/0.51  % (16054)------------------------------
% 0.21/0.51  % (16054)------------------------------
% 0.21/0.51  % (16056)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (16071)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.51  % (16047)Success in time 0.152 s
%------------------------------------------------------------------------------
