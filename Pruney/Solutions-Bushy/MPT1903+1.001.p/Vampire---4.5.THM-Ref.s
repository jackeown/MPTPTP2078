%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1903+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:54 EST 2020

% Result     : Theorem 1.40s
% Output     : Refutation 1.40s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 450 expanded)
%              Number of leaves         :   34 ( 165 expanded)
%              Depth                    :   14
%              Number of atoms          :  582 (1568 expanded)
%              Number of equality atoms :   67 ( 270 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f468,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f92,f97,f102,f107,f113,f120,f141,f157,f166,f171,f241,f275,f314,f319,f466])).

fof(f466,plain,
    ( ~ spl3_3
    | ~ spl3_7
    | ~ spl3_10
    | spl3_14
    | ~ spl3_15
    | ~ spl3_16 ),
    inference(avatar_contradiction_clause,[],[f465])).

fof(f465,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_10
    | spl3_14
    | ~ spl3_15
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f464,f274])).

fof(f274,plain,
    ( ~ v4_pre_topc(sK2(sK0),g1_pre_topc(u1_struct_0(sK0),k1_tex_1(u1_struct_0(sK0))))
    | spl3_14 ),
    inference(avatar_component_clause,[],[f272])).

fof(f272,plain,
    ( spl3_14
  <=> v4_pre_topc(sK2(sK0),g1_pre_topc(u1_struct_0(sK0),k1_tex_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f464,plain,
    ( v4_pre_topc(sK2(sK0),g1_pre_topc(u1_struct_0(sK0),k1_tex_1(u1_struct_0(sK0))))
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_10
    | ~ spl3_15
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f461,f313])).

fof(f313,plain,
    ( sK2(sK0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k6_relat_1(u1_struct_0(sK0)),sK2(sK0))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f311])).

fof(f311,plain,
    ( spl3_15
  <=> sK2(sK0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k6_relat_1(u1_struct_0(sK0)),sK2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f461,plain,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k6_relat_1(u1_struct_0(sK0)),sK2(sK0)),g1_pre_topc(u1_struct_0(sK0),k1_tex_1(u1_struct_0(sK0))))
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_10
    | ~ spl3_16 ),
    inference(unit_resulting_resolution,[],[f101,f140,f170,f143,f84,f318,f299])).

fof(f299,plain,(
    ! [X24,X23,X25,X22] :
      ( ~ m1_subset_1(k6_relat_1(X23),k1_zfmisc_1(k2_zfmisc_1(X22,u1_struct_0(X24))))
      | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
      | ~ v5_pre_topc(k6_relat_1(X23),g1_pre_topc(X22,k1_tex_1(X22)),X24)
      | ~ v4_pre_topc(X25,X24)
      | ~ v1_funct_2(k6_relat_1(X23),X22,u1_struct_0(X24))
      | v4_pre_topc(k8_relset_1(X22,u1_struct_0(X24),k6_relat_1(X23),X25),g1_pre_topc(X22,k1_tex_1(X22)))
      | ~ l1_pre_topc(X24) ) ),
    inference(subsumption_resolution,[],[f289,f80])).

fof(f80,plain,(
    ! [X0] : l1_pre_topc(g1_pre_topc(X0,k1_tex_1(X0))) ),
    inference(definition_unfolding,[],[f51,f53])).

fof(f53,plain,(
    ! [X0] : k2_tex_1(X0) = g1_pre_topc(X0,k1_tex_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tex_1(X0) = g1_pre_topc(X0,k1_tex_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tex_1)).

fof(f51,plain,(
    ! [X0] : l1_pre_topc(k2_tex_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : l1_pre_topc(k2_tex_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tex_1)).

fof(f289,plain,(
    ! [X24,X23,X25,X22] :
      ( ~ m1_subset_1(k6_relat_1(X23),k1_zfmisc_1(k2_zfmisc_1(X22,u1_struct_0(X24))))
      | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
      | ~ v5_pre_topc(k6_relat_1(X23),g1_pre_topc(X22,k1_tex_1(X22)),X24)
      | ~ v4_pre_topc(X25,X24)
      | ~ v1_funct_2(k6_relat_1(X23),X22,u1_struct_0(X24))
      | v4_pre_topc(k8_relset_1(X22,u1_struct_0(X24),k6_relat_1(X23),X25),g1_pre_topc(X22,k1_tex_1(X22)))
      | ~ l1_pre_topc(X24)
      | ~ l1_pre_topc(g1_pre_topc(X22,k1_tex_1(X22))) ) ),
    inference(superposition,[],[f161,f194])).

fof(f194,plain,(
    ! [X0] : u1_struct_0(g1_pre_topc(X0,k1_tex_1(X0))) = X0 ),
    inference(unit_resulting_resolution,[],[f122,f127,f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f127,plain,(
    ! [X0] : g1_pre_topc(X0,k1_tex_1(X0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(X0,k1_tex_1(X0))),u1_pre_topc(g1_pre_topc(X0,k1_tex_1(X0)))) ),
    inference(unit_resulting_resolution,[],[f80,f83,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
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

fof(f83,plain,(
    ! [X0] : v1_pre_topc(g1_pre_topc(X0,k1_tex_1(X0))) ),
    inference(definition_unfolding,[],[f56,f53])).

fof(f56,plain,(
    ! [X0] : v1_pre_topc(k2_tex_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v2_tdlat_3(k2_tex_1(X0))
      & v2_pre_topc(k2_tex_1(X0))
      & v1_pre_topc(k2_tex_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tex_1)).

fof(f122,plain,(
    ! [X0] : m1_subset_1(u1_pre_topc(g1_pre_topc(X0,k1_tex_1(X0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(X0,k1_tex_1(X0)))))) ),
    inference(unit_resulting_resolution,[],[f80,f63])).

fof(f63,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f161,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(k6_relat_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v5_pre_topc(k6_relat_1(X2),X3,X1)
      | ~ v4_pre_topc(X0,X1)
      | ~ v1_funct_2(k6_relat_1(X2),u1_struct_0(X3),u1_struct_0(X1))
      | v4_pre_topc(k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),k6_relat_1(X2),X0),X3)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X3) ) ),
    inference(resolution,[],[f65,f55])).

fof(f55,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f65,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v4_pre_topc(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2)),X0)
                    & v4_pre_topc(sK1(X0,X1,X2),X1)
                    & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v4_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f39,f40])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
          & v4_pre_topc(X3,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2)),X0)
        & v4_pre_topc(sK1(X0,X1,X2),X1)
        & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v4_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v4_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v4_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X3] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      | ~ v4_pre_topc(X3,X1)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v4_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

% (4659)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v4_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

% (4660)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( v4_pre_topc(X3,X1)
                     => v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_pre_topc)).

fof(f318,plain,
    ( v5_pre_topc(k6_relat_1(u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),k1_tex_1(u1_struct_0(sK0))),sK0)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f316])).

fof(f316,plain,
    ( spl3_16
  <=> v5_pre_topc(k6_relat_1(u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),k1_tex_1(u1_struct_0(sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f84,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f60,f52])).

fof(f52,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f60,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f143,plain,(
    ! [X0] : v1_funct_2(k6_relat_1(X0),X0,X0) ),
    inference(unit_resulting_resolution,[],[f55,f85,f84,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_partfun1(X2,X0)
      | v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f34])).

% (4653)Refutation not found, incomplete strategy% (4653)------------------------------
% (4653)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (4653)Termination reason: Refutation not found, incomplete strategy

% (4653)Memory used [KB]: 1791
% (4653)Time elapsed: 0.155 s
% (4653)------------------------------
% (4653)------------------------------
fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

fof(f85,plain,(
    ! [X0] : v1_partfun1(k6_relat_1(X0),X0) ),
    inference(definition_unfolding,[],[f59,f52])).

fof(f59,plain,(
    ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f170,plain,
    ( m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl3_10
  <=> m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f140,plain,
    ( v4_pre_topc(sK2(sK0),sK0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl3_7
  <=> v4_pre_topc(sK2(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f101,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl3_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f319,plain,
    ( spl3_16
    | spl3_13 ),
    inference(avatar_split_clause,[],[f260,f238,f316])).

fof(f238,plain,
    ( spl3_13
  <=> v2_struct_0(g1_pre_topc(u1_struct_0(sK0),k1_tex_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f260,plain,
    ( v5_pre_topc(k6_relat_1(u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),k1_tex_1(u1_struct_0(sK0))),sK0)
    | spl3_13 ),
    inference(unit_resulting_resolution,[],[f55,f143,f84,f240,f204])).

fof(f204,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK0))))
      | ~ v1_funct_2(X1,X2,u1_struct_0(sK0))
      | v5_pre_topc(X1,g1_pre_topc(X2,k1_tex_1(X2)),sK0)
      | v2_struct_0(g1_pre_topc(X2,k1_tex_1(X2))) ) ),
    inference(forward_demodulation,[],[f201,f194])).

fof(f201,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK0))))
      | ~ v1_funct_2(X1,u1_struct_0(g1_pre_topc(X2,k1_tex_1(X2))),u1_struct_0(sK0))
      | ~ v1_funct_1(X1)
      | v5_pre_topc(X1,g1_pre_topc(X2,k1_tex_1(X2)),sK0)
      | v2_struct_0(g1_pre_topc(X2,k1_tex_1(X2))) ) ),
    inference(backward_demodulation,[],[f149,f194])).

fof(f149,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(X2,k1_tex_1(X2))),u1_struct_0(sK0))))
      | ~ v1_funct_2(X1,u1_struct_0(g1_pre_topc(X2,k1_tex_1(X2))),u1_struct_0(sK0))
      | ~ v1_funct_1(X1)
      | v5_pre_topc(X1,g1_pre_topc(X2,k1_tex_1(X2)),sK0)
      | v2_struct_0(g1_pre_topc(X2,k1_tex_1(X2))) ) ),
    inference(subsumption_resolution,[],[f146,f80])).

fof(f146,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(X2,k1_tex_1(X2))),u1_struct_0(sK0))))
      | ~ v1_funct_2(X1,u1_struct_0(g1_pre_topc(X2,k1_tex_1(X2))),u1_struct_0(sK0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(g1_pre_topc(X2,k1_tex_1(X2)))
      | v5_pre_topc(X1,g1_pre_topc(X2,k1_tex_1(X2)),sK0)
      | v2_struct_0(g1_pre_topc(X2,k1_tex_1(X2))) ) ),
    inference(resolution,[],[f49,f82])).

fof(f82,plain,(
    ! [X0] : v2_pre_topc(g1_pre_topc(X0,k1_tex_1(X0))) ),
    inference(definition_unfolding,[],[f57,f53])).

fof(f57,plain,(
    ! [X0] : v2_pre_topc(k2_tex_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f49,plain,(
    ! [X2,X1] :
      ( ~ v2_pre_topc(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | v5_pre_topc(X2,X1,sK0)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ~ v2_tdlat_3(sK0)
    & ! [X1] :
        ( ! [X2] :
            ( v5_pre_topc(X2,X1,sK0)
            | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
            | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK0))
            | ~ v1_funct_1(X2) )
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f36])).

fof(f36,plain,
    ( ? [X0] :
        ( ~ v2_tdlat_3(X0)
        & ! [X1] :
            ( ! [X2] :
                ( v5_pre_topc(X2,X1,X0)
                | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                | ~ v1_funct_1(X2) )
            | ~ l1_pre_topc(X1)
            | ~ v2_pre_topc(X1)
            | v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ~ v2_tdlat_3(sK0)
      & ! [X1] :
          ( ! [X2] :
              ( v5_pre_topc(X2,X1,sK0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] :
      ( ~ v2_tdlat_3(X0)
      & ! [X1] :
          ( ! [X2] :
              ( v5_pre_topc(X2,X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ~ v2_tdlat_3(X0)
      & ! [X1] :
          ( ! [X2] :
              ( v5_pre_topc(X2,X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

% (4662)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ( ! [X1] :
              ( ( l1_pre_topc(X1)
                & v2_pre_topc(X1)
                & ~ v2_struct_0(X1) )
             => ! [X2] :
                  ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                    & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                    & v1_funct_1(X2) )
                 => v5_pre_topc(X2,X1,X0) ) )
         => v2_tdlat_3(X0) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X2) )
               => v5_pre_topc(X2,X1,X0) ) )
       => v2_tdlat_3(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_tex_2)).

fof(f240,plain,
    ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),k1_tex_1(u1_struct_0(sK0))))
    | spl3_13 ),
    inference(avatar_component_clause,[],[f238])).

fof(f314,plain,
    ( spl3_15
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f173,f168,f311])).

fof(f173,plain,
    ( sK2(sK0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k6_relat_1(u1_struct_0(sK0)),sK2(sK0))
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f170,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k8_relset_1(X0,X0,k6_relat_1(X0),X1) = X1 ) ),
    inference(definition_unfolding,[],[f75,f52])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_2)).

fof(f275,plain,
    ( ~ spl3_14
    | spl3_8
    | spl3_9
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f226,f168,f163,f154,f272])).

fof(f154,plain,
    ( spl3_8
  <=> k1_xboole_0 = sK2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f163,plain,
    ( spl3_9
  <=> u1_struct_0(sK0) = sK2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f226,plain,
    ( ~ v4_pre_topc(sK2(sK0),g1_pre_topc(u1_struct_0(sK0),k1_tex_1(u1_struct_0(sK0))))
    | spl3_8
    | spl3_9
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f165,f170,f156,f205])).

fof(f205,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | X0 = X1
      | k1_xboole_0 = X0
      | ~ v4_pre_topc(X0,g1_pre_topc(X1,k1_tex_1(X1))) ) ),
    inference(forward_demodulation,[],[f202,f194])).

fof(f202,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | k1_xboole_0 = X0
      | ~ v4_pre_topc(X0,g1_pre_topc(X1,k1_tex_1(X1)))
      | u1_struct_0(g1_pre_topc(X1,k1_tex_1(X1))) = X0 ) ),
    inference(backward_demodulation,[],[f152,f194])).

fof(f152,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ v4_pre_topc(X0,g1_pre_topc(X1,k1_tex_1(X1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(X1,k1_tex_1(X1)))))
      | u1_struct_0(g1_pre_topc(X1,k1_tex_1(X1))) = X0 ) ),
    inference(subsumption_resolution,[],[f151,f82])).

fof(f151,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ v4_pre_topc(X0,g1_pre_topc(X1,k1_tex_1(X1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(X1,k1_tex_1(X1)))))
      | u1_struct_0(g1_pre_topc(X1,k1_tex_1(X1))) = X0
      | ~ v2_pre_topc(g1_pre_topc(X1,k1_tex_1(X1))) ) ),
    inference(subsumption_resolution,[],[f150,f80])).

% (4660)Refutation not found, incomplete strategy% (4660)------------------------------
% (4660)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (4650)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% (4639)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% (4636)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% (4660)Termination reason: Refutation not found, incomplete strategy

% (4660)Memory used [KB]: 10618
% (4660)Time elapsed: 0.144 s
% (4660)------------------------------
% (4660)------------------------------
% (4662)Refutation not found, incomplete strategy% (4662)------------------------------
% (4662)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (4658)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% (4665)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% (4650)Refutation not found, incomplete strategy% (4650)------------------------------
% (4650)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (4650)Termination reason: Refutation not found, incomplete strategy

% (4650)Memory used [KB]: 1791
% (4650)Time elapsed: 0.138 s
% (4650)------------------------------
% (4650)------------------------------
% (4654)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% (4663)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
fof(f150,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ v4_pre_topc(X0,g1_pre_topc(X1,k1_tex_1(X1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(X1,k1_tex_1(X1)))))
      | u1_struct_0(g1_pre_topc(X1,k1_tex_1(X1))) = X0
      | ~ l1_pre_topc(g1_pre_topc(X1,k1_tex_1(X1)))
      | ~ v2_pre_topc(g1_pre_topc(X1,k1_tex_1(X1))) ) ),
    inference(resolution,[],[f70,f81])).

fof(f81,plain,(
    ! [X0] : v2_tdlat_3(g1_pre_topc(X0,k1_tex_1(X0))) ),
    inference(definition_unfolding,[],[f58,f53])).

fof(f58,plain,(
    ! [X0] : v2_tdlat_3(k2_tex_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f70,plain,(
    ! [X2,X0] :
      ( ~ v2_tdlat_3(X0)
      | k1_xboole_0 = X2
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X0) = X2
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( ( v2_tdlat_3(X0)
          | ( u1_struct_0(X0) != sK2(X0)
            & k1_xboole_0 != sK2(X0)
            & v4_pre_topc(sK2(X0),X0)
            & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( u1_struct_0(X0) = X2
              | k1_xboole_0 = X2
              | ~ v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f43,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] :
          ( u1_struct_0(X0) != X1
          & k1_xboole_0 != X1
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( u1_struct_0(X0) != sK2(X0)
        & k1_xboole_0 != sK2(X0)
        & v4_pre_topc(sK2(X0),X0)
        & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ( ( v2_tdlat_3(X0)
          | ? [X1] :
              ( u1_struct_0(X0) != X1
              & k1_xboole_0 != X1
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( u1_struct_0(X0) = X2
              | k1_xboole_0 = X2
              | ~ v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f42])).

% (4646)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% (4665)Refutation not found, incomplete strategy% (4665)------------------------------
% (4665)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (4665)Termination reason: Refutation not found, incomplete strategy

% (4665)Memory used [KB]: 1663
% (4665)Time elapsed: 0.002 s
% (4665)------------------------------
% (4665)------------------------------
% (4652)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
fof(f42,plain,(
    ! [X0] :
      ( ( ( v2_tdlat_3(X0)
          | ? [X1] :
              ( u1_struct_0(X0) != X1
              & k1_xboole_0 != X1
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( u1_struct_0(X0) = X1
              | k1_xboole_0 = X1
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v2_tdlat_3(X0)
      <=> ! [X1] :
            ( u1_struct_0(X0) = X1
            | k1_xboole_0 = X1
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v2_tdlat_3(X0)
      <=> ! [X1] :
            ( u1_struct_0(X0) = X1
            | k1_xboole_0 = X1
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ~ ( u1_struct_0(X0) != X1
                & k1_xboole_0 != X1
                & v4_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_tdlat_3)).

fof(f156,plain,
    ( k1_xboole_0 != sK2(sK0)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f154])).

fof(f165,plain,
    ( u1_struct_0(sK0) != sK2(sK0)
    | spl3_9 ),
    inference(avatar_component_clause,[],[f163])).

fof(f241,plain,
    ( ~ spl3_13
    | spl3_6 ),
    inference(avatar_split_clause,[],[f129,f117,f238])).

fof(f117,plain,
    ( spl3_6
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f129,plain,
    ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),k1_tex_1(u1_struct_0(sK0))))
    | spl3_6 ),
    inference(unit_resulting_resolution,[],[f119,f86])).

fof(f86,plain,(
    ! [X0] :
      ( ~ v2_struct_0(g1_pre_topc(X0,k1_tex_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f61,f53])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k2_tex_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k2_tex_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ~ v2_struct_0(k2_tex_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_tex_1)).

fof(f119,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f117])).

fof(f171,plain,
    ( spl3_10
    | ~ spl3_2
    | ~ spl3_3
    | spl3_4 ),
    inference(avatar_split_clause,[],[f131,f104,f99,f94,f168])).

fof(f94,plain,
    ( spl3_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f104,plain,
    ( spl3_4
  <=> v2_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f131,plain,
    ( m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2
    | ~ spl3_3
    | spl3_4 ),
    inference(unit_resulting_resolution,[],[f96,f101,f106,f71])).

fof(f71,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f106,plain,
    ( ~ v2_tdlat_3(sK0)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f104])).

fof(f96,plain,
    ( v2_pre_topc(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f94])).

fof(f166,plain,
    ( ~ spl3_9
    | ~ spl3_2
    | ~ spl3_3
    | spl3_4 ),
    inference(avatar_split_clause,[],[f130,f104,f99,f94,f163])).

fof(f130,plain,
    ( u1_struct_0(sK0) != sK2(sK0)
    | ~ spl3_2
    | ~ spl3_3
    | spl3_4 ),
    inference(unit_resulting_resolution,[],[f96,f101,f106,f74])).

fof(f74,plain,(
    ! [X0] :
      ( u1_struct_0(X0) != sK2(X0)
      | v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f157,plain,
    ( ~ spl3_8
    | ~ spl3_2
    | ~ spl3_3
    | spl3_4 ),
    inference(avatar_split_clause,[],[f126,f104,f99,f94,f154])).

fof(f126,plain,
    ( k1_xboole_0 != sK2(sK0)
    | ~ spl3_2
    | ~ spl3_3
    | spl3_4 ),
    inference(unit_resulting_resolution,[],[f96,f101,f106,f73])).

fof(f73,plain,(
    ! [X0] :
      ( k1_xboole_0 != sK2(X0)
      | v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f141,plain,
    ( spl3_7
    | ~ spl3_2
    | ~ spl3_3
    | spl3_4 ),
    inference(avatar_split_clause,[],[f123,f104,f99,f94,f138])).

fof(f123,plain,
    ( v4_pre_topc(sK2(sK0),sK0)
    | ~ spl3_2
    | ~ spl3_3
    | spl3_4 ),
    inference(unit_resulting_resolution,[],[f106,f101,f96,f72])).

fof(f72,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | v4_pre_topc(sK2(X0),X0)
      | ~ l1_pre_topc(X0)
      | v2_tdlat_3(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f120,plain,
    ( ~ spl3_6
    | spl3_1
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f115,f110,f89,f117])).

fof(f89,plain,
    ( spl3_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f110,plain,
    ( spl3_5
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f115,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl3_1
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f91,f112,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f112,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f110])).

fof(f91,plain,
    ( ~ v2_struct_0(sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f89])).

fof(f113,plain,
    ( spl3_5
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f108,f99,f110])).

fof(f108,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f101,f62])).

fof(f62,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f107,plain,(
    ~ spl3_4 ),
    inference(avatar_split_clause,[],[f50,f104])).

fof(f50,plain,(
    ~ v2_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f102,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f48,f99])).

fof(f48,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f97,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f47,f94])).

fof(f47,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f92,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f46,f89])).

fof(f46,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f37])).

%------------------------------------------------------------------------------
