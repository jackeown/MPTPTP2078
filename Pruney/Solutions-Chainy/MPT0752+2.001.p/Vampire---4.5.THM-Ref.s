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
% DateTime   : Thu Dec  3 12:55:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   46 (  55 expanded)
%              Number of leaves         :   12 (  19 expanded)
%              Depth                    :    9
%              Number of atoms          :   98 ( 114 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f63,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f50,f53,f55,f61])).

fof(f61,plain,(
    spl2_3 ),
    inference(avatar_contradiction_clause,[],[f59])).

fof(f59,plain,
    ( $false
    | spl2_3 ),
    inference(resolution,[],[f58,f42])).

fof(f42,plain,
    ( ~ v5_relat_1(k1_xboole_0,sK0)
    | spl2_3 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl2_3
  <=> v5_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f58,plain,(
    ! [X0] : v5_relat_1(k1_xboole_0,X0) ),
    inference(resolution,[],[f57,f21])).

fof(f21,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(sK1(X0)))
      | v5_relat_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f56,f25])).

fof(f25,plain,(
    ! [X0] : v1_relat_1(sK1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
    ? [X1] :
      ( v5_ordinal1(X1)
      & v1_funct_1(X1)
      & v5_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_ordinal1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(sK1(X0)))
      | v5_relat_1(X1,X0) ) ),
    inference(resolution,[],[f29,f26])).

fof(f26,plain,(
    ! [X0] : v5_relat_1(sK1(X0),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | v5_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v5_relat_1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v5_relat_1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v5_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_relat_1)).

fof(f55,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f54,f44])).

fof(f44,plain,
    ( spl2_4
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f54,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f24,f20])).

fof(f20,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f53,plain,(
    spl2_2 ),
    inference(avatar_contradiction_clause,[],[f52])).

fof(f52,plain,
    ( $false
    | spl2_2 ),
    inference(subsumption_resolution,[],[f51,f38])).

fof(f38,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl2_2
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f51,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[],[f23,f20])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

fof(f50,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f49])).

fof(f49,plain,
    ( $false
    | spl2_1 ),
    inference(subsumption_resolution,[],[f48,f34])).

fof(f34,plain,
    ( ~ v5_ordinal1(k1_xboole_0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl2_1
  <=> v5_ordinal1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f48,plain,(
    v5_ordinal1(k1_xboole_0) ),
    inference(resolution,[],[f22,f20])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v5_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( v5_ordinal1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v5_ordinal1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_ordinal1)).

fof(f47,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f19,f44,f40,f36,f32])).

fof(f19,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v5_relat_1(k1_xboole_0,sK0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_ordinal1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ~ v5_ordinal1(k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v5_relat_1(k1_xboole_0,X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( v5_ordinal1(k1_xboole_0)
        & v1_funct_1(k1_xboole_0)
        & v5_relat_1(k1_xboole_0,X0)
        & v1_relat_1(k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( v5_ordinal1(k1_xboole_0)
      & v1_funct_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X0)
      & v1_relat_1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_ordinal1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:50:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.42  % (19018)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.21/0.42  % (19018)Refutation not found, incomplete strategy% (19018)------------------------------
% 0.21/0.42  % (19018)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (19018)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.42  
% 0.21/0.42  % (19018)Memory used [KB]: 9850
% 0.21/0.42  % (19018)Time elapsed: 0.003 s
% 0.21/0.42  % (19018)------------------------------
% 0.21/0.42  % (19018)------------------------------
% 0.21/0.45  % (19027)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=on:gs=on:gsem=on:irw=on:nm=0:nwc=2.5:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (19015)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.21/0.48  % (19015)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f47,f50,f53,f55,f61])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    spl2_3),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f59])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    $false | spl2_3),
% 0.21/0.48    inference(resolution,[],[f58,f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ~v5_relat_1(k1_xboole_0,sK0) | spl2_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    spl2_3 <=> v5_relat_1(k1_xboole_0,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    ( ! [X0] : (v5_relat_1(k1_xboole_0,X0)) )),
% 0.21/0.48    inference(resolution,[],[f57,f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(sK1(X0))) | v5_relat_1(X1,X0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f56,f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ( ! [X0] : (v1_relat_1(sK1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0] : ? [X1] : (v5_ordinal1(X1) & v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_ordinal1)).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_relat_1(sK1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(sK1(X0))) | v5_relat_1(X1,X0)) )),
% 0.21/0.48    inference(resolution,[],[f29,f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ( ! [X0] : (v5_relat_1(sK1(X0),X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v5_relat_1(X1,X0) | ~v1_relat_1(X1) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | v5_relat_1(X2,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (v5_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (v5_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1))) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X1)) => v5_relat_1(X2,X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_relat_1)).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    spl2_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f54,f44])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    spl2_4 <=> v1_relat_1(k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    v1_relat_1(k1_xboole_0)),
% 0.21/0.48    inference(resolution,[],[f24,f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_xboole_0(X0) | v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    spl2_2),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f52])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    $false | spl2_2),
% 0.21/0.48    inference(subsumption_resolution,[],[f51,f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ~v1_funct_1(k1_xboole_0) | spl2_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    spl2_2 <=> v1_funct_1(k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    v1_funct_1(k1_xboole_0)),
% 0.21/0.48    inference(resolution,[],[f23,f20])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_xboole_0(X0) | v1_funct_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    spl2_1),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f49])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    $false | spl2_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f48,f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ~v5_ordinal1(k1_xboole_0) | spl2_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    spl2_1 <=> v5_ordinal1(k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    v5_ordinal1(k1_xboole_0)),
% 0.21/0.48    inference(resolution,[],[f22,f20])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_xboole_0(X0) | v5_ordinal1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0] : (v5_ordinal1(X0) | ~v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0] : (v1_xboole_0(X0) => v5_ordinal1(X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_ordinal1)).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f19,f44,f40,f36,f32])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ~v1_relat_1(k1_xboole_0) | ~v5_relat_1(k1_xboole_0,sK0) | ~v1_funct_1(k1_xboole_0) | ~v5_ordinal1(k1_xboole_0)),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ? [X0] : (~v5_ordinal1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v5_relat_1(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,negated_conjecture,(
% 0.21/0.48    ~! [X0] : (v5_ordinal1(k1_xboole_0) & v1_funct_1(k1_xboole_0) & v5_relat_1(k1_xboole_0,X0) & v1_relat_1(k1_xboole_0))),
% 0.21/0.48    inference(negated_conjecture,[],[f9])).
% 0.21/0.48  fof(f9,conjecture,(
% 0.21/0.48    ! [X0] : (v5_ordinal1(k1_xboole_0) & v1_funct_1(k1_xboole_0) & v5_relat_1(k1_xboole_0,X0) & v1_relat_1(k1_xboole_0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_ordinal1)).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (19015)------------------------------
% 0.21/0.48  % (19015)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (19015)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (19015)Memory used [KB]: 5373
% 0.21/0.48  % (19015)Time elapsed: 0.040 s
% 0.21/0.48  % (19015)------------------------------
% 0.21/0.48  % (19015)------------------------------
% 0.21/0.48  % (19008)Success in time 0.121 s
%------------------------------------------------------------------------------
