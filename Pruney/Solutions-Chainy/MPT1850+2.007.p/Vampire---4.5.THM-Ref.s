%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:39 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 103 expanded)
%              Number of leaves         :   15 (  39 expanded)
%              Depth                    :    8
%              Number of atoms          :  140 ( 275 expanded)
%              Number of equality atoms :   50 (  90 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f96,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f29,f34,f39,f44,f49,f55,f62,f86,f94,f95])).

fof(f95,plain,
    ( u1_struct_0(sK0) != u1_struct_0(sK1)
    | u1_pre_topc(sK0) != u1_pre_topc(sK1)
    | u1_pre_topc(sK0) != k1_zfmisc_1(u1_struct_0(sK0))
    | u1_pre_topc(sK1) = k1_zfmisc_1(u1_struct_0(sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f94,plain,
    ( spl2_10
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f89,f52,f41,f91])).

fof(f91,plain,
    ( spl2_10
  <=> u1_pre_topc(sK0) = u1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f41,plain,
    ( spl2_4
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f52,plain,
    ( spl2_6
  <=> u1_pre_topc(sK0) = k1_zfmisc_1(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f89,plain,
    ( u1_pre_topc(sK0) = u1_pre_topc(sK1)
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(trivial_inequality_removal,[],[f87])).

fof(f87,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
    | u1_pre_topc(sK0) = u1_pre_topc(sK1)
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(superposition,[],[f76,f43])).

fof(f43,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f41])).

fof(f76,plain,
    ( ! [X0,X1] :
        ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | u1_pre_topc(sK0) = X1 )
    | ~ spl2_6 ),
    inference(superposition,[],[f74,f54])).

fof(f54,plain,
    ( u1_pre_topc(sK0) = k1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f52])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( g1_pre_topc(X0,k1_zfmisc_1(X0)) != g1_pre_topc(X1,X2)
      | k1_zfmisc_1(X0) = X2 ) ),
    inference(resolution,[],[f21,f22])).

fof(f22,plain,(
    ! [X0] : m1_subset_1(k1_zfmisc_1(X0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(definition_unfolding,[],[f17,f16])).

% (4656)Refutation not found, incomplete strategy% (4656)------------------------------
% (4656)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f16,plain,(
    ! [X0] : k9_setfam_1(X0) = k1_zfmisc_1(X0) ),
    inference(cnf_transformation,[],[f2])).

% (4656)Termination reason: Refutation not found, incomplete strategy

% (4656)Memory used [KB]: 10746
% (4656)Time elapsed: 0.077 s
% (4656)------------------------------
% (4656)------------------------------
fof(f2,axiom,(
    ! [X0] : k9_setfam_1(X0) = k1_zfmisc_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(f17,plain,(
    ! [X0] : m1_subset_1(k9_setfam_1(X0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : m1_subset_1(k9_setfam_1(X0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_setfam_1)).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f86,plain,
    ( spl2_9
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f81,f52,f41,f83])).

fof(f83,plain,
    ( spl2_9
  <=> u1_struct_0(sK0) = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f81,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(trivial_inequality_removal,[],[f79])).

fof(f79,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
    | u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(superposition,[],[f71,f43])).

fof(f71,plain,
    ( ! [X0,X1] :
        ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | u1_struct_0(sK0) = X0 )
    | ~ spl2_6 ),
    inference(superposition,[],[f69,f54])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( g1_pre_topc(X0,k1_zfmisc_1(X0)) != g1_pre_topc(X1,X2)
      | X0 = X1 ) ),
    inference(resolution,[],[f20,f22])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f62,plain,
    ( spl2_2
    | ~ spl2_7
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f57,f46,f59,f31])).

% (4634)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
fof(f31,plain,
    ( spl2_2
  <=> v1_tdlat_3(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f59,plain,
    ( spl2_7
  <=> u1_pre_topc(sK1) = k1_zfmisc_1(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f46,plain,
    ( spl2_5
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f57,plain,
    ( u1_pre_topc(sK1) != k1_zfmisc_1(u1_struct_0(sK1))
    | v1_tdlat_3(sK1)
    | ~ spl2_5 ),
    inference(resolution,[],[f24,f48])).

fof(f48,plain,
    ( l1_pre_topc(sK1)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f46])).

fof(f24,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | u1_pre_topc(X0) != k1_zfmisc_1(u1_struct_0(X0))
      | v1_tdlat_3(X0) ) ),
    inference(definition_unfolding,[],[f18,f16])).

fof(f18,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | u1_pre_topc(X0) != k9_setfam_1(u1_struct_0(X0))
      | v1_tdlat_3(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
      <=> u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tdlat_3)).

fof(f55,plain,
    ( ~ spl2_1
    | spl2_6
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f50,f36,f52,f26])).

fof(f26,plain,
    ( spl2_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f36,plain,
    ( spl2_3
  <=> v1_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f50,plain,
    ( u1_pre_topc(sK0) = k1_zfmisc_1(u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_3 ),
    inference(resolution,[],[f23,f38])).

fof(f38,plain,
    ( v1_tdlat_3(sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f36])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_tdlat_3(X0)
      | u1_pre_topc(X0) = k1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f19,f16])).

fof(f19,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0))
      | ~ v1_tdlat_3(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f49,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f11,f46])).

fof(f11,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_tdlat_3(X1)
          & v1_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_tdlat_3(X1)
          & v1_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ( ( v1_tdlat_3(X0)
                & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
             => v1_tdlat_3(X1) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( ( v1_tdlat_3(X0)
              & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
           => v1_tdlat_3(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tex_2)).

fof(f44,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f12,f41])).

fof(f12,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f39,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f13,f36])).

fof(f13,plain,(
    v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f34,plain,(
    ~ spl2_2 ),
    inference(avatar_split_clause,[],[f14,f31])).

fof(f14,plain,(
    ~ v1_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f29,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f15,f26])).

fof(f15,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:42:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (4642)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.51  % (4638)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (4650)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.52  % (4650)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % (4656)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.52  % (4658)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.52  % (4648)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f96,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f29,f34,f39,f44,f49,f55,f62,f86,f94,f95])).
% 0.22/0.52  fof(f95,plain,(
% 0.22/0.52    u1_struct_0(sK0) != u1_struct_0(sK1) | u1_pre_topc(sK0) != u1_pre_topc(sK1) | u1_pre_topc(sK0) != k1_zfmisc_1(u1_struct_0(sK0)) | u1_pre_topc(sK1) = k1_zfmisc_1(u1_struct_0(sK1))),
% 0.22/0.52    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.52  fof(f94,plain,(
% 0.22/0.52    spl2_10 | ~spl2_4 | ~spl2_6),
% 0.22/0.52    inference(avatar_split_clause,[],[f89,f52,f41,f91])).
% 0.22/0.52  fof(f91,plain,(
% 0.22/0.52    spl2_10 <=> u1_pre_topc(sK0) = u1_pre_topc(sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    spl2_4 <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    spl2_6 <=> u1_pre_topc(sK0) = k1_zfmisc_1(u1_struct_0(sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.52  fof(f89,plain,(
% 0.22/0.52    u1_pre_topc(sK0) = u1_pre_topc(sK1) | (~spl2_4 | ~spl2_6)),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f87])).
% 0.22/0.52  fof(f87,plain,(
% 0.22/0.52    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | u1_pre_topc(sK0) = u1_pre_topc(sK1) | (~spl2_4 | ~spl2_6)),
% 0.22/0.52    inference(superposition,[],[f76,f43])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) | ~spl2_4),
% 0.22/0.53    inference(avatar_component_clause,[],[f41])).
% 0.22/0.53  fof(f76,plain,(
% 0.22/0.53    ( ! [X0,X1] : (g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | u1_pre_topc(sK0) = X1) ) | ~spl2_6),
% 0.22/0.53    inference(superposition,[],[f74,f54])).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    u1_pre_topc(sK0) = k1_zfmisc_1(u1_struct_0(sK0)) | ~spl2_6),
% 0.22/0.53    inference(avatar_component_clause,[],[f52])).
% 0.22/0.53  fof(f74,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (g1_pre_topc(X0,k1_zfmisc_1(X0)) != g1_pre_topc(X1,X2) | k1_zfmisc_1(X0) = X2) )),
% 0.22/0.53    inference(resolution,[],[f21,f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ( ! [X0] : (m1_subset_1(k1_zfmisc_1(X0),k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.53    inference(definition_unfolding,[],[f17,f16])).
% 0.22/0.53  % (4656)Refutation not found, incomplete strategy% (4656)------------------------------
% 0.22/0.53  % (4656)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ( ! [X0] : (k9_setfam_1(X0) = k1_zfmisc_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f2])).
% 0.22/0.53  % (4656)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (4656)Memory used [KB]: 10746
% 0.22/0.53  % (4656)Time elapsed: 0.077 s
% 0.22/0.53  % (4656)------------------------------
% 0.22/0.53  % (4656)------------------------------
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0] : k9_setfam_1(X0) = k1_zfmisc_1(X0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ( ! [X0] : (m1_subset_1(k9_setfam_1(X0),k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0] : m1_subset_1(k9_setfam_1(X0),k1_zfmisc_1(k1_zfmisc_1(X0)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_setfam_1)).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | X1 = X3) )),
% 0.22/0.53    inference(cnf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,plain,(
% 0.22/0.53    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.53    inference(ennf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).
% 0.22/0.53  fof(f86,plain,(
% 0.22/0.53    spl2_9 | ~spl2_4 | ~spl2_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f81,f52,f41,f83])).
% 0.22/0.53  fof(f83,plain,(
% 0.22/0.53    spl2_9 <=> u1_struct_0(sK0) = u1_struct_0(sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.22/0.53  fof(f81,plain,(
% 0.22/0.53    u1_struct_0(sK0) = u1_struct_0(sK1) | (~spl2_4 | ~spl2_6)),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f79])).
% 0.22/0.53  fof(f79,plain,(
% 0.22/0.53    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | u1_struct_0(sK0) = u1_struct_0(sK1) | (~spl2_4 | ~spl2_6)),
% 0.22/0.53    inference(superposition,[],[f71,f43])).
% 0.22/0.53  fof(f71,plain,(
% 0.22/0.53    ( ! [X0,X1] : (g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | u1_struct_0(sK0) = X0) ) | ~spl2_6),
% 0.22/0.53    inference(superposition,[],[f69,f54])).
% 0.22/0.53  fof(f69,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (g1_pre_topc(X0,k1_zfmisc_1(X0)) != g1_pre_topc(X1,X2) | X0 = X1) )),
% 0.22/0.53    inference(resolution,[],[f20,f22])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | X0 = X2) )),
% 0.22/0.53    inference(cnf_transformation,[],[f10])).
% 0.22/0.53  fof(f62,plain,(
% 0.22/0.53    spl2_2 | ~spl2_7 | ~spl2_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f57,f46,f59,f31])).
% 0.22/0.53  % (4634)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    spl2_2 <=> v1_tdlat_3(sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    spl2_7 <=> u1_pre_topc(sK1) = k1_zfmisc_1(u1_struct_0(sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    spl2_5 <=> l1_pre_topc(sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    u1_pre_topc(sK1) != k1_zfmisc_1(u1_struct_0(sK1)) | v1_tdlat_3(sK1) | ~spl2_5),
% 0.22/0.53    inference(resolution,[],[f24,f48])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    l1_pre_topc(sK1) | ~spl2_5),
% 0.22/0.53    inference(avatar_component_clause,[],[f46])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ( ! [X0] : (~l1_pre_topc(X0) | u1_pre_topc(X0) != k1_zfmisc_1(u1_struct_0(X0)) | v1_tdlat_3(X0)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f18,f16])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ( ! [X0] : (~l1_pre_topc(X0) | u1_pre_topc(X0) != k9_setfam_1(u1_struct_0(X0)) | v1_tdlat_3(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,plain,(
% 0.22/0.53    ! [X0] : ((v1_tdlat_3(X0) <=> u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0] : (l1_pre_topc(X0) => (v1_tdlat_3(X0) <=> u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tdlat_3)).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    ~spl2_1 | spl2_6 | ~spl2_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f50,f36,f52,f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    spl2_1 <=> l1_pre_topc(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    spl2_3 <=> v1_tdlat_3(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    u1_pre_topc(sK0) = k1_zfmisc_1(u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~spl2_3),
% 0.22/0.53    inference(resolution,[],[f23,f38])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    v1_tdlat_3(sK0) | ~spl2_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f36])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_tdlat_3(X0) | u1_pre_topc(X0) = k1_zfmisc_1(u1_struct_0(X0)) | ~l1_pre_topc(X0)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f19,f16])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ( ! [X0] : (~l1_pre_topc(X0) | u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0)) | ~v1_tdlat_3(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f9])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    spl2_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f11,f46])).
% 0.22/0.53  fof(f11,plain,(
% 0.22/0.53    l1_pre_topc(sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (~v1_tdlat_3(X1) & v1_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 0.22/0.53    inference(flattening,[],[f7])).
% 0.22/0.53  fof(f7,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : ((~v1_tdlat_3(X1) & (v1_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,negated_conjecture,(
% 0.22/0.53    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ((v1_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v1_tdlat_3(X1))))),
% 0.22/0.53    inference(negated_conjecture,[],[f5])).
% 0.22/0.53  fof(f5,conjecture,(
% 0.22/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ((v1_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v1_tdlat_3(X1))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tex_2)).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    spl2_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f12,f41])).
% 0.22/0.53  fof(f12,plain,(
% 0.22/0.53    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),
% 0.22/0.53    inference(cnf_transformation,[],[f8])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    spl2_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f13,f36])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    v1_tdlat_3(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f8])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ~spl2_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f14,f31])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ~v1_tdlat_3(sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f8])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    spl2_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f15,f26])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    l1_pre_topc(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f8])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (4650)------------------------------
% 0.22/0.53  % (4650)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (4650)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (4650)Memory used [KB]: 10746
% 0.22/0.53  % (4650)Time elapsed: 0.107 s
% 0.22/0.53  % (4650)------------------------------
% 0.22/0.53  % (4650)------------------------------
% 0.22/0.53  % (4633)Success in time 0.167 s
%------------------------------------------------------------------------------
