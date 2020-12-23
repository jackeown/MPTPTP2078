%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.24s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 269 expanded)
%              Number of leaves         :   35 ( 102 expanded)
%              Depth                    :    8
%              Number of atoms          :  425 (1595 expanded)
%              Number of equality atoms :   36 ( 182 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f246,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f62,f67,f72,f77,f82,f87,f92,f97,f102,f107,f112,f120,f125,f130,f139,f145,f148,f158,f164,f167,f172,f188,f202,f205,f209,f245])).

fof(f245,plain,
    ( spl5_17
    | ~ spl5_9
    | spl5_28 ),
    inference(avatar_split_clause,[],[f244,f199,f94,f136])).

fof(f136,plain,
    ( spl5_17
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f94,plain,
    ( spl5_9
  <=> m1_subset_1(sK4,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f199,plain,
    ( spl5_28
  <=> k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) = k2_pre_topc(sK0,k2_tarski(sK4,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f244,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | spl5_28 ),
    inference(trivial_inequality_removal,[],[f243])).

fof(f243,plain,
    ( k2_pre_topc(sK0,k2_tarski(sK4,sK4)) != k2_pre_topc(sK0,k2_tarski(sK4,sK4))
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | spl5_28 ),
    inference(superposition,[],[f201,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f47,f40])).

fof(f40,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f201,plain,
    ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) != k2_pre_topc(sK0,k2_tarski(sK4,sK4))
    | spl5_28 ),
    inference(avatar_component_clause,[],[f199])).

fof(f209,plain,
    ( ~ spl5_19
    | spl5_27 ),
    inference(avatar_contradiction_clause,[],[f207])).

fof(f207,plain,
    ( $false
    | ~ spl5_19
    | spl5_27 ),
    inference(unit_resulting_resolution,[],[f153,f197,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f45,f40])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

% (28927)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
fof(f197,plain,
    ( ~ m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | spl5_27 ),
    inference(avatar_component_clause,[],[f195])).

fof(f195,plain,
    ( spl5_27
  <=> m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f153,plain,
    ( r2_hidden(sK4,u1_struct_0(sK1))
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl5_19
  <=> r2_hidden(sK4,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f205,plain,
    ( ~ spl5_16
    | spl5_26 ),
    inference(avatar_contradiction_clause,[],[f203])).

fof(f203,plain,
    ( $false
    | ~ spl5_16
    | spl5_26 ),
    inference(unit_resulting_resolution,[],[f134,f193,f50])).

fof(f193,plain,
    ( ~ m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_26 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl5_26
  <=> m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f134,plain,
    ( r2_hidden(sK4,u1_struct_0(sK0))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl5_16
  <=> r2_hidden(sK4,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f202,plain,
    ( spl5_3
    | ~ spl5_26
    | ~ spl5_27
    | ~ spl5_11
    | ~ spl5_15
    | ~ spl5_10
    | ~ spl5_14
    | ~ spl5_1
    | ~ spl5_8
    | ~ spl5_7
    | spl5_2
    | ~ spl5_6
    | ~ spl5_5
    | ~ spl5_4
    | ~ spl5_28
    | spl5_25 ),
    inference(avatar_split_clause,[],[f189,f185,f199,f69,f74,f79,f59,f84,f89,f54,f122,f99,f127,f104,f195,f191,f64])).

fof(f64,plain,
    ( spl5_3
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f104,plain,
    ( spl5_11
  <=> v3_borsuk_1(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f127,plain,
    ( spl5_15
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f99,plain,
    ( spl5_10
  <=> v5_pre_topc(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f122,plain,
    ( spl5_14
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f54,plain,
    ( spl5_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f89,plain,
    ( spl5_8
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f84,plain,
    ( spl5_7
  <=> v4_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f59,plain,
    ( spl5_2
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f79,plain,
    ( spl5_6
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f74,plain,
    ( spl5_5
  <=> v3_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f69,plain,
    ( spl5_4
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f185,plain,
    ( spl5_25
  <=> k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_tarski(sK4,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f189,plain,
    ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) != k2_pre_topc(sK0,k2_tarski(sK4,sK4))
    | ~ v2_pre_topc(sK0)
    | ~ v3_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v4_tex_2(sK1,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v3_borsuk_1(sK2,sK0,sK1)
    | ~ m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | spl5_25 ),
    inference(superposition,[],[f187,f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X1] :
      ( k2_pre_topc(X0,X4) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)
      | ~ v2_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v3_borsuk_1(X2,X0,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v3_borsuk_1(X2,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | X3 != X4
      | k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4)
                      | X3 != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ v3_borsuk_1(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v5_pre_topc(X2,X0,X1)
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v4_tex_2(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4)
                      | X3 != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ v3_borsuk_1(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v5_pre_topc(X2,X0,X1)
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v4_tex_2(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & v4_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v5_pre_topc(X2,X0,X1)
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v3_borsuk_1(X2,X0,X1)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                       => ( X3 = X4
                         => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tex_2)).

fof(f187,plain,
    ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_tarski(sK4,sK4))
    | spl5_25 ),
    inference(avatar_component_clause,[],[f185])).

fof(f188,plain,
    ( spl5_20
    | ~ spl5_12
    | ~ spl5_25
    | spl5_22 ),
    inference(avatar_split_clause,[],[f182,f169,f185,f109,f155])).

fof(f155,plain,
    ( spl5_20
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f109,plain,
    ( spl5_12
  <=> m1_subset_1(sK4,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f169,plain,
    ( spl5_22
  <=> k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f182,plain,
    ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_tarski(sK4,sK4))
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1))
    | spl5_22 ),
    inference(superposition,[],[f171,f51])).

fof(f171,plain,
    ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK4))
    | spl5_22 ),
    inference(avatar_component_clause,[],[f169])).

fof(f172,plain,(
    ~ spl5_22 ),
    inference(avatar_split_clause,[],[f49,f169])).

fof(f49,plain,(
    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK4)) ),
    inference(definition_unfolding,[],[f26,f25])).

fof(f25,plain,(
    sK3 = sK4 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4))
                      & X3 = X4
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & v3_borsuk_1(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v5_pre_topc(X2,X0,X1)
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & m1_pre_topc(X1,X0)
          & v4_tex_2(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4))
                      & X3 = X4
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & v3_borsuk_1(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v5_pre_topc(X2,X0,X1)
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & m1_pre_topc(X1,X0)
          & v4_tex_2(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & v4_tex_2(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v5_pre_topc(X2,X0,X1)
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( v3_borsuk_1(X2,X0,X1)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X1))
                     => ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( X3 = X4
                           => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & v4_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v5_pre_topc(X2,X0,X1)
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v3_borsuk_1(X2,X0,X1)
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ( X3 = X4
                         => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tex_2)).

fof(f26,plain,(
    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) ),
    inference(cnf_transformation,[],[f12])).

fof(f167,plain,
    ( ~ spl5_13
    | spl5_21 ),
    inference(avatar_contradiction_clause,[],[f165])).

fof(f165,plain,
    ( $false
    | ~ spl5_13
    | spl5_21 ),
    inference(unit_resulting_resolution,[],[f119,f163,f41])).

fof(f41,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f163,plain,
    ( ~ l1_struct_0(sK1)
    | spl5_21 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl5_21
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f119,plain,
    ( l1_pre_topc(sK1)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl5_13
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f164,plain,
    ( spl5_2
    | ~ spl5_21
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f159,f155,f161,f59])).

fof(f159,plain,
    ( ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl5_20 ),
    inference(resolution,[],[f157,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f157,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f155])).

fof(f158,plain,
    ( spl5_19
    | spl5_20
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f115,f109,f155,f151])).

fof(f115,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | r2_hidden(sK4,u1_struct_0(sK1))
    | ~ spl5_12 ),
    inference(resolution,[],[f111,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f111,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f109])).

fof(f148,plain,
    ( ~ spl5_6
    | spl5_18 ),
    inference(avatar_contradiction_clause,[],[f146])).

fof(f146,plain,
    ( $false
    | ~ spl5_6
    | spl5_18 ),
    inference(unit_resulting_resolution,[],[f81,f144,f41])).

fof(f144,plain,
    ( ~ l1_struct_0(sK0)
    | spl5_18 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl5_18
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f81,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f79])).

fof(f145,plain,
    ( spl5_3
    | ~ spl5_18
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f140,f136,f142,f64])).

fof(f140,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_17 ),
    inference(resolution,[],[f138,f44])).

fof(f138,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f136])).

fof(f139,plain,
    ( spl5_16
    | spl5_17
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f114,f94,f136,f132])).

fof(f114,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(sK4,u1_struct_0(sK0))
    | ~ spl5_9 ),
    inference(resolution,[],[f96,f46])).

fof(f96,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f94])).

fof(f130,plain,(
    spl5_15 ),
    inference(avatar_split_clause,[],[f31,f127])).

fof(f31,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f12])).

fof(f125,plain,(
    spl5_14 ),
    inference(avatar_split_clause,[],[f29,f122])).

fof(f29,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f120,plain,
    ( spl5_13
    | ~ spl5_6
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f113,f89,f79,f117])).

fof(f113,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK1)
    | ~ spl5_8 ),
    inference(resolution,[],[f91,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f91,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f89])).

fof(f112,plain,(
    spl5_12 ),
    inference(avatar_split_clause,[],[f48,f109])).

fof(f48,plain,(
    m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(definition_unfolding,[],[f27,f25])).

% (28921)Refutation not found, incomplete strategy% (28921)------------------------------
% (28921)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (28921)Termination reason: Refutation not found, incomplete strategy

% (28921)Memory used [KB]: 10746
% (28921)Time elapsed: 0.104 s
% (28921)------------------------------
% (28921)------------------------------
% (28914)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f27,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f107,plain,(
    spl5_11 ),
    inference(avatar_split_clause,[],[f32,f104])).

fof(f32,plain,(
    v3_borsuk_1(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f102,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f30,f99])).

fof(f30,plain,(
    v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f97,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f24,f94])).

fof(f24,plain,(
    m1_subset_1(sK4,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f92,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f35,f89])).

fof(f35,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f87,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f34,f84])).

fof(f34,plain,(
    v4_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f82,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f39,f79])).

fof(f39,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f77,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f38,f74])).

fof(f38,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f72,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f37,f69])).

fof(f37,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f67,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f36,f64])).

fof(f36,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f62,plain,(
    ~ spl5_2 ),
    inference(avatar_split_clause,[],[f33,f59])).

fof(f33,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f57,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f28,f54])).

fof(f28,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:46:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (28921)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.50  % (28933)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.50  % (28925)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.50  % (28935)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.51  % (28917)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (28913)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (28912)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (28933)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f246,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f57,f62,f67,f72,f77,f82,f87,f92,f97,f102,f107,f112,f120,f125,f130,f139,f145,f148,f158,f164,f167,f172,f188,f202,f205,f209,f245])).
% 0.21/0.51  fof(f245,plain,(
% 0.21/0.51    spl5_17 | ~spl5_9 | spl5_28),
% 0.21/0.51    inference(avatar_split_clause,[],[f244,f199,f94,f136])).
% 0.21/0.51  fof(f136,plain,(
% 0.21/0.51    spl5_17 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    spl5_9 <=> m1_subset_1(sK4,u1_struct_0(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.51  fof(f199,plain,(
% 0.21/0.51    spl5_28 <=> k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) = k2_pre_topc(sK0,k2_tarski(sK4,sK4))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 0.21/0.51  fof(f244,plain,(
% 0.21/0.51    ~m1_subset_1(sK4,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | spl5_28),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f243])).
% 0.21/0.51  fof(f243,plain,(
% 0.21/0.51    k2_pre_topc(sK0,k2_tarski(sK4,sK4)) != k2_pre_topc(sK0,k2_tarski(sK4,sK4)) | ~m1_subset_1(sK4,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | spl5_28),
% 0.21/0.51    inference(superposition,[],[f201,f51])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k2_tarski(X1,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f47,f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.51    inference(flattening,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 1.24/0.51  fof(f7,axiom,(
% 1.24/0.51    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 1.24/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 1.24/0.51  fof(f201,plain,(
% 1.24/0.51    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) != k2_pre_topc(sK0,k2_tarski(sK4,sK4)) | spl5_28),
% 1.24/0.51    inference(avatar_component_clause,[],[f199])).
% 1.24/0.51  fof(f209,plain,(
% 1.24/0.51    ~spl5_19 | spl5_27),
% 1.24/0.51    inference(avatar_contradiction_clause,[],[f207])).
% 1.24/0.51  fof(f207,plain,(
% 1.24/0.51    $false | (~spl5_19 | spl5_27)),
% 1.24/0.51    inference(unit_resulting_resolution,[],[f153,f197,f50])).
% 1.24/0.51  fof(f50,plain,(
% 1.24/0.51    ( ! [X0,X1] : (m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 1.24/0.51    inference(definition_unfolding,[],[f45,f40])).
% 1.24/0.51  fof(f45,plain,(
% 1.24/0.51    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))) )),
% 1.24/0.51    inference(cnf_transformation,[],[f19])).
% 1.24/0.51  fof(f19,plain,(
% 1.24/0.51    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 1.24/0.51    inference(ennf_transformation,[],[f2])).
% 1.24/0.51  fof(f2,axiom,(
% 1.24/0.51    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 1.24/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).
% 1.24/0.51  % (28927)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.24/0.51  fof(f197,plain,(
% 1.24/0.51    ~m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK1))) | spl5_27),
% 1.24/0.51    inference(avatar_component_clause,[],[f195])).
% 1.24/0.51  fof(f195,plain,(
% 1.24/0.51    spl5_27 <=> m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.24/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 1.24/0.51  fof(f153,plain,(
% 1.24/0.51    r2_hidden(sK4,u1_struct_0(sK1)) | ~spl5_19),
% 1.24/0.51    inference(avatar_component_clause,[],[f151])).
% 1.24/0.51  fof(f151,plain,(
% 1.24/0.51    spl5_19 <=> r2_hidden(sK4,u1_struct_0(sK1))),
% 1.24/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 1.24/0.51  fof(f205,plain,(
% 1.24/0.51    ~spl5_16 | spl5_26),
% 1.24/0.51    inference(avatar_contradiction_clause,[],[f203])).
% 1.24/0.51  fof(f203,plain,(
% 1.24/0.51    $false | (~spl5_16 | spl5_26)),
% 1.24/0.51    inference(unit_resulting_resolution,[],[f134,f193,f50])).
% 1.24/0.51  fof(f193,plain,(
% 1.24/0.51    ~m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK0))) | spl5_26),
% 1.24/0.51    inference(avatar_component_clause,[],[f191])).
% 1.24/0.51  fof(f191,plain,(
% 1.24/0.51    spl5_26 <=> m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.24/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 1.24/0.51  fof(f134,plain,(
% 1.24/0.51    r2_hidden(sK4,u1_struct_0(sK0)) | ~spl5_16),
% 1.24/0.51    inference(avatar_component_clause,[],[f132])).
% 1.24/0.51  fof(f132,plain,(
% 1.24/0.51    spl5_16 <=> r2_hidden(sK4,u1_struct_0(sK0))),
% 1.24/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 1.24/0.51  fof(f202,plain,(
% 1.24/0.51    spl5_3 | ~spl5_26 | ~spl5_27 | ~spl5_11 | ~spl5_15 | ~spl5_10 | ~spl5_14 | ~spl5_1 | ~spl5_8 | ~spl5_7 | spl5_2 | ~spl5_6 | ~spl5_5 | ~spl5_4 | ~spl5_28 | spl5_25),
% 1.24/0.51    inference(avatar_split_clause,[],[f189,f185,f199,f69,f74,f79,f59,f84,f89,f54,f122,f99,f127,f104,f195,f191,f64])).
% 1.24/0.51  fof(f64,plain,(
% 1.24/0.51    spl5_3 <=> v2_struct_0(sK0)),
% 1.24/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.24/0.51  fof(f104,plain,(
% 1.24/0.51    spl5_11 <=> v3_borsuk_1(sK2,sK0,sK1)),
% 1.24/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 1.24/0.51  fof(f127,plain,(
% 1.24/0.51    spl5_15 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.24/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 1.24/0.51  fof(f99,plain,(
% 1.24/0.51    spl5_10 <=> v5_pre_topc(sK2,sK0,sK1)),
% 1.24/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 1.24/0.51  fof(f122,plain,(
% 1.24/0.51    spl5_14 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.24/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 1.24/0.51  fof(f54,plain,(
% 1.24/0.51    spl5_1 <=> v1_funct_1(sK2)),
% 1.24/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.24/0.51  fof(f89,plain,(
% 1.24/0.51    spl5_8 <=> m1_pre_topc(sK1,sK0)),
% 1.24/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.24/0.51  fof(f84,plain,(
% 1.24/0.51    spl5_7 <=> v4_tex_2(sK1,sK0)),
% 1.24/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.24/0.51  fof(f59,plain,(
% 1.24/0.51    spl5_2 <=> v2_struct_0(sK1)),
% 1.24/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.24/0.51  fof(f79,plain,(
% 1.24/0.51    spl5_6 <=> l1_pre_topc(sK0)),
% 1.24/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.24/0.51  fof(f74,plain,(
% 1.24/0.51    spl5_5 <=> v3_tdlat_3(sK0)),
% 1.24/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.24/0.51  fof(f69,plain,(
% 1.24/0.51    spl5_4 <=> v2_pre_topc(sK0)),
% 1.24/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.24/0.51  fof(f185,plain,(
% 1.24/0.51    spl5_25 <=> k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_tarski(sK4,sK4))),
% 1.24/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 1.24/0.51  fof(f189,plain,(
% 1.24/0.51    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) != k2_pre_topc(sK0,k2_tarski(sK4,sK4)) | ~v2_pre_topc(sK0) | ~v3_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v4_tex_2(sK1,sK0) | ~m1_pre_topc(sK1,sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v3_borsuk_1(sK2,sK0,sK1) | ~m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | spl5_25),
% 1.24/0.51    inference(superposition,[],[f187,f52])).
% 1.24/0.51  fof(f52,plain,(
% 1.24/0.51    ( ! [X4,X2,X0,X1] : (k2_pre_topc(X0,X4) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4) | ~v2_pre_topc(X0) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0)) )),
% 1.24/0.51    inference(equality_resolution,[],[f43])).
% 1.24/0.51  fof(f43,plain,(
% 1.24/0.51    ( ! [X4,X2,X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | X3 != X4 | k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4)) )),
% 1.24/0.51    inference(cnf_transformation,[],[f16])).
% 1.24/0.51  fof(f16,plain,(
% 1.24/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.24/0.51    inference(flattening,[],[f15])).
% 1.24/0.51  fof(f15,plain,(
% 1.24/0.51    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : (! [X4] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.24/0.51    inference(ennf_transformation,[],[f8])).
% 1.24/0.51  fof(f8,axiom,(
% 1.24/0.51    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4))))))))),
% 1.24/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tex_2)).
% 1.24/0.51  fof(f187,plain,(
% 1.24/0.51    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_tarski(sK4,sK4)) | spl5_25),
% 1.24/0.51    inference(avatar_component_clause,[],[f185])).
% 1.24/0.51  fof(f188,plain,(
% 1.24/0.51    spl5_20 | ~spl5_12 | ~spl5_25 | spl5_22),
% 1.24/0.51    inference(avatar_split_clause,[],[f182,f169,f185,f109,f155])).
% 1.24/0.51  fof(f155,plain,(
% 1.24/0.51    spl5_20 <=> v1_xboole_0(u1_struct_0(sK1))),
% 1.24/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 1.24/0.51  fof(f109,plain,(
% 1.24/0.51    spl5_12 <=> m1_subset_1(sK4,u1_struct_0(sK1))),
% 1.24/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 1.24/0.51  fof(f169,plain,(
% 1.24/0.51    spl5_22 <=> k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK4))),
% 1.24/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 1.24/0.51  fof(f182,plain,(
% 1.24/0.51    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_tarski(sK4,sK4)) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK1)) | spl5_22),
% 1.24/0.51    inference(superposition,[],[f171,f51])).
% 1.24/0.51  fof(f171,plain,(
% 1.24/0.51    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK4)) | spl5_22),
% 1.24/0.51    inference(avatar_component_clause,[],[f169])).
% 1.24/0.51  fof(f172,plain,(
% 1.24/0.51    ~spl5_22),
% 1.24/0.51    inference(avatar_split_clause,[],[f49,f169])).
% 1.24/0.51  fof(f49,plain,(
% 1.24/0.51    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK4))),
% 1.24/0.51    inference(definition_unfolding,[],[f26,f25])).
% 1.24/0.51  fof(f25,plain,(
% 1.24/0.51    sK3 = sK4),
% 1.24/0.51    inference(cnf_transformation,[],[f12])).
% 1.24/0.51  fof(f12,plain,(
% 1.24/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.24/0.51    inference(flattening,[],[f11])).
% 1.24/0.51  fof(f11,plain,(
% 1.24/0.51    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (? [X4] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.24/0.51    inference(ennf_transformation,[],[f10])).
% 1.24/0.51  fof(f10,negated_conjecture,(
% 1.24/0.51    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)))))))))),
% 1.24/0.51    inference(negated_conjecture,[],[f9])).
% 1.24/0.51  fof(f9,conjecture,(
% 1.24/0.51    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)))))))))),
% 1.24/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tex_2)).
% 1.24/0.51  fof(f26,plain,(
% 1.24/0.51    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4))),
% 1.24/0.51    inference(cnf_transformation,[],[f12])).
% 1.24/0.51  fof(f167,plain,(
% 1.24/0.51    ~spl5_13 | spl5_21),
% 1.24/0.51    inference(avatar_contradiction_clause,[],[f165])).
% 1.24/0.51  fof(f165,plain,(
% 1.24/0.51    $false | (~spl5_13 | spl5_21)),
% 1.24/0.51    inference(unit_resulting_resolution,[],[f119,f163,f41])).
% 1.24/0.51  fof(f41,plain,(
% 1.24/0.51    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.24/0.51    inference(cnf_transformation,[],[f13])).
% 1.24/0.51  fof(f13,plain,(
% 1.24/0.51    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.24/0.51    inference(ennf_transformation,[],[f4])).
% 1.24/0.51  fof(f4,axiom,(
% 1.24/0.51    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.24/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.24/0.51  fof(f163,plain,(
% 1.24/0.51    ~l1_struct_0(sK1) | spl5_21),
% 1.24/0.51    inference(avatar_component_clause,[],[f161])).
% 1.24/0.51  fof(f161,plain,(
% 1.24/0.51    spl5_21 <=> l1_struct_0(sK1)),
% 1.24/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 1.24/0.51  fof(f119,plain,(
% 1.24/0.51    l1_pre_topc(sK1) | ~spl5_13),
% 1.24/0.51    inference(avatar_component_clause,[],[f117])).
% 1.24/0.51  fof(f117,plain,(
% 1.24/0.51    spl5_13 <=> l1_pre_topc(sK1)),
% 1.24/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 1.24/0.51  fof(f164,plain,(
% 1.24/0.51    spl5_2 | ~spl5_21 | ~spl5_20),
% 1.24/0.51    inference(avatar_split_clause,[],[f159,f155,f161,f59])).
% 1.24/0.51  fof(f159,plain,(
% 1.24/0.51    ~l1_struct_0(sK1) | v2_struct_0(sK1) | ~spl5_20),
% 1.24/0.51    inference(resolution,[],[f157,f44])).
% 1.24/0.51  fof(f44,plain,(
% 1.24/0.51    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.24/0.51    inference(cnf_transformation,[],[f18])).
% 1.24/0.51  fof(f18,plain,(
% 1.24/0.51    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.24/0.51    inference(flattening,[],[f17])).
% 1.24/0.51  fof(f17,plain,(
% 1.24/0.51    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.24/0.51    inference(ennf_transformation,[],[f6])).
% 1.24/0.51  fof(f6,axiom,(
% 1.24/0.51    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.24/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 1.24/0.51  fof(f157,plain,(
% 1.24/0.51    v1_xboole_0(u1_struct_0(sK1)) | ~spl5_20),
% 1.24/0.51    inference(avatar_component_clause,[],[f155])).
% 1.24/0.51  fof(f158,plain,(
% 1.24/0.51    spl5_19 | spl5_20 | ~spl5_12),
% 1.24/0.51    inference(avatar_split_clause,[],[f115,f109,f155,f151])).
% 1.24/0.51  fof(f115,plain,(
% 1.24/0.51    v1_xboole_0(u1_struct_0(sK1)) | r2_hidden(sK4,u1_struct_0(sK1)) | ~spl5_12),
% 1.24/0.51    inference(resolution,[],[f111,f46])).
% 1.24/0.51  fof(f46,plain,(
% 1.24/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.24/0.51    inference(cnf_transformation,[],[f21])).
% 1.24/0.51  fof(f21,plain,(
% 1.24/0.51    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.24/0.51    inference(flattening,[],[f20])).
% 1.24/0.51  fof(f20,plain,(
% 1.24/0.51    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.24/0.51    inference(ennf_transformation,[],[f3])).
% 1.24/0.51  fof(f3,axiom,(
% 1.24/0.51    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.24/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 1.24/0.51  fof(f111,plain,(
% 1.24/0.51    m1_subset_1(sK4,u1_struct_0(sK1)) | ~spl5_12),
% 1.24/0.51    inference(avatar_component_clause,[],[f109])).
% 1.24/0.51  fof(f148,plain,(
% 1.24/0.51    ~spl5_6 | spl5_18),
% 1.24/0.51    inference(avatar_contradiction_clause,[],[f146])).
% 1.24/0.51  fof(f146,plain,(
% 1.24/0.51    $false | (~spl5_6 | spl5_18)),
% 1.24/0.51    inference(unit_resulting_resolution,[],[f81,f144,f41])).
% 1.24/0.51  fof(f144,plain,(
% 1.24/0.51    ~l1_struct_0(sK0) | spl5_18),
% 1.24/0.51    inference(avatar_component_clause,[],[f142])).
% 1.24/0.51  fof(f142,plain,(
% 1.24/0.51    spl5_18 <=> l1_struct_0(sK0)),
% 1.24/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 1.24/0.51  fof(f81,plain,(
% 1.24/0.51    l1_pre_topc(sK0) | ~spl5_6),
% 1.24/0.51    inference(avatar_component_clause,[],[f79])).
% 1.24/0.51  fof(f145,plain,(
% 1.24/0.51    spl5_3 | ~spl5_18 | ~spl5_17),
% 1.24/0.51    inference(avatar_split_clause,[],[f140,f136,f142,f64])).
% 1.24/0.51  fof(f140,plain,(
% 1.24/0.51    ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl5_17),
% 1.24/0.51    inference(resolution,[],[f138,f44])).
% 1.24/0.51  fof(f138,plain,(
% 1.24/0.51    v1_xboole_0(u1_struct_0(sK0)) | ~spl5_17),
% 1.24/0.51    inference(avatar_component_clause,[],[f136])).
% 1.24/0.51  fof(f139,plain,(
% 1.24/0.51    spl5_16 | spl5_17 | ~spl5_9),
% 1.24/0.51    inference(avatar_split_clause,[],[f114,f94,f136,f132])).
% 1.24/0.51  fof(f114,plain,(
% 1.24/0.51    v1_xboole_0(u1_struct_0(sK0)) | r2_hidden(sK4,u1_struct_0(sK0)) | ~spl5_9),
% 1.24/0.51    inference(resolution,[],[f96,f46])).
% 1.24/0.51  fof(f96,plain,(
% 1.24/0.51    m1_subset_1(sK4,u1_struct_0(sK0)) | ~spl5_9),
% 1.24/0.51    inference(avatar_component_clause,[],[f94])).
% 1.24/0.51  fof(f130,plain,(
% 1.24/0.51    spl5_15),
% 1.24/0.51    inference(avatar_split_clause,[],[f31,f127])).
% 1.24/0.51  fof(f31,plain,(
% 1.24/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.24/0.51    inference(cnf_transformation,[],[f12])).
% 1.24/0.51  fof(f125,plain,(
% 1.24/0.51    spl5_14),
% 1.24/0.51    inference(avatar_split_clause,[],[f29,f122])).
% 1.24/0.51  fof(f29,plain,(
% 1.24/0.51    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.24/0.51    inference(cnf_transformation,[],[f12])).
% 1.24/0.51  fof(f120,plain,(
% 1.24/0.51    spl5_13 | ~spl5_6 | ~spl5_8),
% 1.24/0.51    inference(avatar_split_clause,[],[f113,f89,f79,f117])).
% 1.24/0.51  fof(f113,plain,(
% 1.24/0.51    ~l1_pre_topc(sK0) | l1_pre_topc(sK1) | ~spl5_8),
% 1.24/0.51    inference(resolution,[],[f91,f42])).
% 1.24/0.51  fof(f42,plain,(
% 1.24/0.51    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 1.24/0.51    inference(cnf_transformation,[],[f14])).
% 1.24/0.51  fof(f14,plain,(
% 1.24/0.51    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.24/0.51    inference(ennf_transformation,[],[f5])).
% 1.24/0.51  fof(f5,axiom,(
% 1.24/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.24/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.24/0.51  fof(f91,plain,(
% 1.24/0.51    m1_pre_topc(sK1,sK0) | ~spl5_8),
% 1.24/0.51    inference(avatar_component_clause,[],[f89])).
% 1.24/0.51  fof(f112,plain,(
% 1.24/0.51    spl5_12),
% 1.24/0.51    inference(avatar_split_clause,[],[f48,f109])).
% 1.24/0.51  fof(f48,plain,(
% 1.24/0.51    m1_subset_1(sK4,u1_struct_0(sK1))),
% 1.24/0.51    inference(definition_unfolding,[],[f27,f25])).
% 1.24/0.51  % (28921)Refutation not found, incomplete strategy% (28921)------------------------------
% 1.24/0.51  % (28921)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.51  % (28921)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.51  
% 1.24/0.51  % (28921)Memory used [KB]: 10746
% 1.24/0.51  % (28921)Time elapsed: 0.104 s
% 1.24/0.51  % (28921)------------------------------
% 1.24/0.51  % (28921)------------------------------
% 1.24/0.51  % (28914)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.24/0.51  fof(f27,plain,(
% 1.24/0.51    m1_subset_1(sK3,u1_struct_0(sK1))),
% 1.24/0.51    inference(cnf_transformation,[],[f12])).
% 1.24/0.51  fof(f107,plain,(
% 1.24/0.51    spl5_11),
% 1.24/0.51    inference(avatar_split_clause,[],[f32,f104])).
% 1.24/0.51  fof(f32,plain,(
% 1.24/0.51    v3_borsuk_1(sK2,sK0,sK1)),
% 1.24/0.51    inference(cnf_transformation,[],[f12])).
% 1.24/0.51  fof(f102,plain,(
% 1.24/0.51    spl5_10),
% 1.24/0.51    inference(avatar_split_clause,[],[f30,f99])).
% 1.24/0.51  fof(f30,plain,(
% 1.24/0.51    v5_pre_topc(sK2,sK0,sK1)),
% 1.24/0.51    inference(cnf_transformation,[],[f12])).
% 1.24/0.51  fof(f97,plain,(
% 1.24/0.51    spl5_9),
% 1.24/0.51    inference(avatar_split_clause,[],[f24,f94])).
% 1.24/0.51  fof(f24,plain,(
% 1.24/0.51    m1_subset_1(sK4,u1_struct_0(sK0))),
% 1.24/0.51    inference(cnf_transformation,[],[f12])).
% 1.24/0.51  fof(f92,plain,(
% 1.24/0.51    spl5_8),
% 1.24/0.51    inference(avatar_split_clause,[],[f35,f89])).
% 1.24/0.51  fof(f35,plain,(
% 1.24/0.51    m1_pre_topc(sK1,sK0)),
% 1.24/0.51    inference(cnf_transformation,[],[f12])).
% 1.24/0.51  fof(f87,plain,(
% 1.24/0.51    spl5_7),
% 1.24/0.51    inference(avatar_split_clause,[],[f34,f84])).
% 1.24/0.51  fof(f34,plain,(
% 1.24/0.51    v4_tex_2(sK1,sK0)),
% 1.24/0.51    inference(cnf_transformation,[],[f12])).
% 1.24/0.51  fof(f82,plain,(
% 1.24/0.51    spl5_6),
% 1.24/0.51    inference(avatar_split_clause,[],[f39,f79])).
% 1.24/0.52  fof(f39,plain,(
% 1.24/0.52    l1_pre_topc(sK0)),
% 1.24/0.52    inference(cnf_transformation,[],[f12])).
% 1.24/0.52  fof(f77,plain,(
% 1.24/0.52    spl5_5),
% 1.24/0.52    inference(avatar_split_clause,[],[f38,f74])).
% 1.24/0.52  fof(f38,plain,(
% 1.24/0.52    v3_tdlat_3(sK0)),
% 1.24/0.52    inference(cnf_transformation,[],[f12])).
% 1.24/0.52  fof(f72,plain,(
% 1.24/0.52    spl5_4),
% 1.24/0.52    inference(avatar_split_clause,[],[f37,f69])).
% 1.24/0.52  fof(f37,plain,(
% 1.24/0.52    v2_pre_topc(sK0)),
% 1.24/0.52    inference(cnf_transformation,[],[f12])).
% 1.24/0.52  fof(f67,plain,(
% 1.24/0.52    ~spl5_3),
% 1.24/0.52    inference(avatar_split_clause,[],[f36,f64])).
% 1.24/0.52  fof(f36,plain,(
% 1.24/0.52    ~v2_struct_0(sK0)),
% 1.24/0.52    inference(cnf_transformation,[],[f12])).
% 1.24/0.52  fof(f62,plain,(
% 1.24/0.52    ~spl5_2),
% 1.24/0.52    inference(avatar_split_clause,[],[f33,f59])).
% 1.24/0.52  fof(f33,plain,(
% 1.24/0.52    ~v2_struct_0(sK1)),
% 1.24/0.52    inference(cnf_transformation,[],[f12])).
% 1.24/0.52  fof(f57,plain,(
% 1.24/0.52    spl5_1),
% 1.24/0.52    inference(avatar_split_clause,[],[f28,f54])).
% 1.24/0.52  fof(f28,plain,(
% 1.24/0.52    v1_funct_1(sK2)),
% 1.24/0.52    inference(cnf_transformation,[],[f12])).
% 1.24/0.52  % SZS output end Proof for theBenchmark
% 1.24/0.52  % (28933)------------------------------
% 1.24/0.52  % (28933)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.52  % (28933)Termination reason: Refutation
% 1.24/0.52  
% 1.24/0.52  % (28933)Memory used [KB]: 10874
% 1.24/0.52  % (28933)Time elapsed: 0.065 s
% 1.24/0.52  % (28933)------------------------------
% 1.24/0.52  % (28933)------------------------------
% 1.24/0.52  % (28911)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.24/0.52  % (28910)Success in time 0.159 s
%------------------------------------------------------------------------------
