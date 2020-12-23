%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:33 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 499 expanded)
%              Number of leaves         :   38 ( 229 expanded)
%              Depth                    :   12
%              Number of atoms          :  604 (4829 expanded)
%              Number of equality atoms :   86 ( 846 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f304,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f75,f83,f86,f92,f139,f141,f143,f145,f147,f149,f151,f161,f210,f212,f216,f219,f245,f250,f252,f254,f257,f258,f299,f303])).

fof(f303,plain,(
    spl5_33 ),
    inference(avatar_contradiction_clause,[],[f301])).

fof(f301,plain,
    ( $false
    | spl5_33 ),
    inference(resolution,[],[f300,f35])).

fof(f35,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4))
    & sK3 = sK4
    & m1_subset_1(sK4,u1_struct_0(sK0))
    & m1_subset_1(sK3,u1_struct_0(sK1))
    & v3_borsuk_1(sK2,sK0,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v5_pre_topc(sK2,sK0,sK1)
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & m1_pre_topc(sK1,sK0)
    & v4_tex_2(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v3_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f14,f30,f29,f28,f27,f26])).

fof(f26,plain,
    ( ? [X0] :
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
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X4))
                      & X3 = X4
                      & m1_subset_1(X4,u1_struct_0(sK0)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & v3_borsuk_1(X2,sK0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v5_pre_topc(X2,sK0,X1)
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & m1_pre_topc(X1,sK0)
          & v4_tex_2(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v3_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X4))
                    & X3 = X4
                    & m1_subset_1(X4,u1_struct_0(sK0)) )
                & m1_subset_1(X3,u1_struct_0(X1)) )
            & v3_borsuk_1(X2,sK0,X1)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v5_pre_topc(X2,sK0,X1)
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & m1_pre_topc(X1,sK0)
        & v4_tex_2(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k6_domain_1(u1_struct_0(sK1),X3))
                  & X3 = X4
                  & m1_subset_1(X4,u1_struct_0(sK0)) )
              & m1_subset_1(X3,u1_struct_0(sK1)) )
          & v3_borsuk_1(X2,sK0,sK1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v5_pre_topc(X2,sK0,sK1)
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & m1_pre_topc(sK1,sK0)
      & v4_tex_2(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k6_domain_1(u1_struct_0(sK1),X3))
                & X3 = X4
                & m1_subset_1(X4,u1_struct_0(sK0)) )
            & m1_subset_1(X3,u1_struct_0(sK1)) )
        & v3_borsuk_1(X2,sK0,sK1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v5_pre_topc(X2,sK0,sK1)
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),X3))
              & X3 = X4
              & m1_subset_1(X4,u1_struct_0(sK0)) )
          & m1_subset_1(X3,u1_struct_0(sK1)) )
      & v3_borsuk_1(sK2,sK0,sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v5_pre_topc(sK2,sK0,sK1)
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),X3))
            & X3 = X4
            & m1_subset_1(X4,u1_struct_0(sK0)) )
        & m1_subset_1(X3,u1_struct_0(sK1)) )
   => ( ? [X4] :
          ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3))
          & sK3 = X4
          & m1_subset_1(X4,u1_struct_0(sK0)) )
      & m1_subset_1(sK3,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X4] :
        ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3))
        & sK3 = X4
        & m1_subset_1(X4,u1_struct_0(sK0)) )
   => ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4))
      & sK3 = sK4
      & m1_subset_1(sK4,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tex_2)).

fof(f300,plain,
    ( ~ l1_pre_topc(sK0)
    | spl5_33 ),
    inference(resolution,[],[f298,f50])).

fof(f50,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f298,plain,
    ( ~ l1_struct_0(sK0)
    | spl5_33 ),
    inference(avatar_component_clause,[],[f296])).

fof(f296,plain,
    ( spl5_33
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f299,plain,
    ( spl5_5
    | ~ spl5_33
    | ~ spl5_24
    | ~ spl5_28 ),
    inference(avatar_split_clause,[],[f282,f242,f207,f296,f99])).

fof(f99,plain,
    ( spl5_5
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f207,plain,
    ( spl5_24
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f242,plain,
    ( spl5_28
  <=> k1_xboole_0 = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

% (5465)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
fof(f282,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_28 ),
    inference(superposition,[],[f54,f244])).

fof(f244,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f242])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f258,plain,
    ( ~ spl5_25
    | spl5_26
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f225,f159,f231,f227])).

fof(f227,plain,
    ( spl5_25
  <=> m1_subset_1(k1_enumset1(sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f231,plain,
    ( spl5_26
  <=> k2_pre_topc(sK0,k1_enumset1(sK4,sK4,sK4)) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k1_enumset1(sK4,sK4,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f159,plain,
    ( spl5_16
  <=> ! [X0] :
        ( k2_pre_topc(sK0,k1_enumset1(X0,X0,X0)) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k1_enumset1(X0,X0,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(k1_enumset1(X0,X0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f225,plain,
    ( k2_pre_topc(sK0,k1_enumset1(sK4,sK4,sK4)) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k1_enumset1(sK4,sK4,sK4))
    | ~ m1_subset_1(k1_enumset1(sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_16 ),
    inference(resolution,[],[f160,f60])).

fof(f60,plain,(
    m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(definition_unfolding,[],[f44,f46])).

fof(f46,plain,(
    sK3 = sK4 ),
    inference(cnf_transformation,[],[f31])).

fof(f44,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f160,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | k2_pre_topc(sK0,k1_enumset1(X0,X0,X0)) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k1_enumset1(X0,X0,X0))
        | ~ m1_subset_1(k1_enumset1(X0,X0,X0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f159])).

fof(f257,plain,
    ( ~ spl5_2
    | ~ spl5_4
    | ~ spl5_26 ),
    inference(avatar_contradiction_clause,[],[f256])).

fof(f256,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_26 ),
    inference(trivial_inequality_removal,[],[f255])).

fof(f255,plain,
    ( k2_pre_topc(sK0,k1_enumset1(sK4,sK4,sK4)) != k2_pre_topc(sK0,k1_enumset1(sK4,sK4,sK4))
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_26 ),
    inference(superposition,[],[f96,f233])).

fof(f233,plain,
    ( k2_pre_topc(sK0,k1_enumset1(sK4,sK4,sK4)) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k1_enumset1(sK4,sK4,sK4))
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f231])).

fof(f96,plain,
    ( k2_pre_topc(sK0,k1_enumset1(sK4,sK4,sK4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k1_enumset1(sK4,sK4,sK4))
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(backward_demodulation,[],[f94,f95])).

fof(f95,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK4) = k1_enumset1(sK4,sK4,sK4)
    | ~ spl5_4 ),
    inference(resolution,[],[f82,f60])).

fof(f82,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK1))
        | k1_enumset1(X1,X1,X1) = k6_domain_1(u1_struct_0(sK1),X1) )
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl5_4
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK1))
        | k1_enumset1(X1,X1,X1) = k6_domain_1(u1_struct_0(sK1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f94,plain,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK4)) != k2_pre_topc(sK0,k1_enumset1(sK4,sK4,sK4))
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f59,f93])).

fof(f93,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK4) = k1_enumset1(sK4,sK4,sK4)
    | ~ spl5_2 ),
    inference(resolution,[],[f74,f45])).

fof(f45,plain,(
    m1_subset_1(sK4,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f31])).

fof(f74,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_enumset1(X0,X0,X0) = k6_domain_1(u1_struct_0(sK0),X0) )
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl5_2
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_enumset1(X0,X0,X0) = k6_domain_1(u1_struct_0(sK0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f59,plain,(
    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK4)) ),
    inference(definition_unfolding,[],[f47,f46])).

fof(f47,plain,(
    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) ),
    inference(cnf_transformation,[],[f31])).

fof(f254,plain,(
    spl5_27 ),
    inference(avatar_contradiction_clause,[],[f253])).

fof(f253,plain,
    ( $false
    | spl5_27 ),
    inference(resolution,[],[f240,f45])).

fof(f240,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | spl5_27 ),
    inference(avatar_component_clause,[],[f238])).

fof(f238,plain,
    ( spl5_27
  <=> m1_subset_1(sK4,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f252,plain,(
    ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f251])).

fof(f251,plain,
    ( $false
    | ~ spl5_5 ),
    inference(resolution,[],[f101,f32])).

fof(f32,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f101,plain,
    ( v2_struct_0(sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f99])).

fof(f250,plain,
    ( spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_1
    | spl5_8
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_13
    | spl5_14 ),
    inference(avatar_split_clause,[],[f221,f135,f131,f127,f123,f119,f115,f111,f69,f107,f103,f99])).

fof(f103,plain,
    ( spl5_6
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f107,plain,
    ( spl5_7
  <=> v3_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f69,plain,
    ( spl5_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f111,plain,
    ( spl5_8
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f115,plain,
    ( spl5_9
  <=> v4_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f119,plain,
    ( spl5_10
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f123,plain,
    ( spl5_11
  <=> v5_pre_topc(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f127,plain,
    ( spl5_12
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f131,plain,
    ( spl5_13
  <=> v3_borsuk_1(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f135,plain,
    ( spl5_14
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f221,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v3_borsuk_1(sK2,sK0,sK1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)
      | ~ m1_pre_topc(sK1,sK0)
      | ~ v4_tex_2(sK1,sK0)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v3_tdlat_3(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f40,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_borsuk_1(sK2,X1,X2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v5_pre_topc(sK2,X1,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | k2_pre_topc(X1,X0) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),sK2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ v4_tex_2(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v3_tdlat_3(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f63,f39])).

fof(f39,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f63,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v3_borsuk_1(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | k2_pre_topc(X0,X4) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)
      | ~ m1_pre_topc(X1,X0)
      | ~ v4_tex_2(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4)
      | X3 != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v3_borsuk_1(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ v4_tex_2(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tex_2)).

fof(f40,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f245,plain,
    ( ~ spl5_27
    | spl5_28
    | spl5_25 ),
    inference(avatar_split_clause,[],[f235,f227,f242,f238])).

fof(f235,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | spl5_25 ),
    inference(resolution,[],[f229,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_enumset1(X1,X1,X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(definition_unfolding,[],[f56,f58])).

fof(f58,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f49,f55])).

fof(f55,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f49,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ( k1_xboole_0 != X0
       => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_subset_1)).

fof(f229,plain,
    ( ~ m1_subset_1(k1_enumset1(sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_25 ),
    inference(avatar_component_clause,[],[f227])).

fof(f219,plain,
    ( ~ spl5_3
    | spl5_23 ),
    inference(avatar_contradiction_clause,[],[f217])).

fof(f217,plain,
    ( $false
    | ~ spl5_3
    | spl5_23 ),
    inference(resolution,[],[f213,f78])).

fof(f78,plain,
    ( l1_pre_topc(sK1)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl5_3
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f213,plain,
    ( ~ l1_pre_topc(sK1)
    | spl5_23 ),
    inference(resolution,[],[f205,f50])).

fof(f205,plain,
    ( ~ l1_struct_0(sK1)
    | spl5_23 ),
    inference(avatar_component_clause,[],[f203])).

fof(f203,plain,
    ( spl5_23
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f216,plain,(
    spl5_24 ),
    inference(avatar_contradiction_clause,[],[f214])).

fof(f214,plain,
    ( $false
    | spl5_24 ),
    inference(resolution,[],[f209,f48])).

fof(f48,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f209,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl5_24 ),
    inference(avatar_component_clause,[],[f207])).

fof(f212,plain,(
    ~ spl5_8 ),
    inference(avatar_contradiction_clause,[],[f211])).

fof(f211,plain,
    ( $false
    | ~ spl5_8 ),
    inference(resolution,[],[f113,f36])).

fof(f36,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f113,plain,
    ( v2_struct_0(sK1)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f111])).

fof(f210,plain,
    ( spl5_8
    | ~ spl5_23
    | ~ spl5_24
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f181,f155,f207,f203,f111])).

fof(f155,plain,
    ( spl5_15
  <=> k1_xboole_0 = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f181,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl5_15 ),
    inference(superposition,[],[f54,f157])).

fof(f157,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f155])).

fof(f161,plain,
    ( spl5_15
    | spl5_16
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f152,f135,f159,f155])).

fof(f152,plain,
    ( ! [X0] :
        ( k2_pre_topc(sK0,k1_enumset1(X0,X0,X0)) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k1_enumset1(X0,X0,X0))
        | ~ m1_subset_1(k1_enumset1(X0,X0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = u1_struct_0(sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl5_14 ),
    inference(resolution,[],[f136,f61])).

fof(f136,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f135])).

fof(f151,plain,(
    spl5_12 ),
    inference(avatar_contradiction_clause,[],[f150])).

fof(f150,plain,
    ( $false
    | spl5_12 ),
    inference(resolution,[],[f129,f42])).

fof(f42,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f31])).

fof(f129,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | spl5_12 ),
    inference(avatar_component_clause,[],[f127])).

fof(f149,plain,(
    spl5_13 ),
    inference(avatar_contradiction_clause,[],[f148])).

fof(f148,plain,
    ( $false
    | spl5_13 ),
    inference(resolution,[],[f133,f43])).

fof(f43,plain,(
    v3_borsuk_1(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f133,plain,
    ( ~ v3_borsuk_1(sK2,sK0,sK1)
    | spl5_13 ),
    inference(avatar_component_clause,[],[f131])).

fof(f147,plain,(
    spl5_11 ),
    inference(avatar_contradiction_clause,[],[f146])).

fof(f146,plain,
    ( $false
    | spl5_11 ),
    inference(resolution,[],[f125,f41])).

fof(f41,plain,(
    v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f125,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | spl5_11 ),
    inference(avatar_component_clause,[],[f123])).

fof(f145,plain,(
    spl5_10 ),
    inference(avatar_contradiction_clause,[],[f144])).

fof(f144,plain,
    ( $false
    | spl5_10 ),
    inference(resolution,[],[f121,f38])).

fof(f38,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f121,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | spl5_10 ),
    inference(avatar_component_clause,[],[f119])).

fof(f143,plain,(
    spl5_9 ),
    inference(avatar_contradiction_clause,[],[f142])).

fof(f142,plain,
    ( $false
    | spl5_9 ),
    inference(resolution,[],[f117,f37])).

fof(f37,plain,(
    v4_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f117,plain,
    ( ~ v4_tex_2(sK1,sK0)
    | spl5_9 ),
    inference(avatar_component_clause,[],[f115])).

fof(f141,plain,(
    spl5_7 ),
    inference(avatar_contradiction_clause,[],[f140])).

fof(f140,plain,
    ( $false
    | spl5_7 ),
    inference(resolution,[],[f109,f34])).

fof(f34,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f109,plain,
    ( ~ v3_tdlat_3(sK0)
    | spl5_7 ),
    inference(avatar_component_clause,[],[f107])).

fof(f139,plain,(
    spl5_6 ),
    inference(avatar_contradiction_clause,[],[f138])).

fof(f138,plain,
    ( $false
    | spl5_6 ),
    inference(resolution,[],[f105,f33])).

fof(f33,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f105,plain,
    ( ~ v2_pre_topc(sK0)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f103])).

fof(f92,plain,(
    spl5_3 ),
    inference(avatar_contradiction_clause,[],[f90])).

fof(f90,plain,
    ( $false
    | spl5_3 ),
    inference(resolution,[],[f89,f35])).

fof(f89,plain,
    ( ~ l1_pre_topc(sK0)
    | spl5_3 ),
    inference(resolution,[],[f88,f38])).

fof(f88,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0) )
    | spl5_3 ),
    inference(resolution,[],[f79,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f79,plain,
    ( ~ l1_pre_topc(sK1)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f77])).

fof(f86,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f84])).

fof(f84,plain,
    ( $false
    | spl5_1 ),
    inference(resolution,[],[f71,f35])).

fof(f71,plain,
    ( ~ l1_pre_topc(sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f83,plain,
    ( ~ spl5_3
    | spl5_4 ),
    inference(avatar_split_clause,[],[f67,f81,f77])).

fof(f67,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK1))
      | k1_enumset1(X1,X1,X1) = k6_domain_1(u1_struct_0(sK1),X1)
      | ~ l1_pre_topc(sK1) ) ),
    inference(resolution,[],[f65,f36])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | k1_enumset1(X0,X0,X0) = k6_domain_1(u1_struct_0(X1),X0)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f64,f50])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X1)
      | k1_enumset1(X0,X0,X0) = k6_domain_1(u1_struct_0(X1),X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f62,f54])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_enumset1(X1,X1,X1) ) ),
    inference(definition_unfolding,[],[f57,f58])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f75,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f66,f73,f69])).

fof(f66,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_enumset1(X0,X0,X0) = k6_domain_1(u1_struct_0(sK0),X0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f65,f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:23:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (5449)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.48  % (5449)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.49  % (5442)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f304,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f75,f83,f86,f92,f139,f141,f143,f145,f147,f149,f151,f161,f210,f212,f216,f219,f245,f250,f252,f254,f257,f258,f299,f303])).
% 0.22/0.49  fof(f303,plain,(
% 0.22/0.49    spl5_33),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f301])).
% 0.22/0.49  fof(f301,plain,(
% 0.22/0.49    $false | spl5_33),
% 0.22/0.49    inference(resolution,[],[f300,f35])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    l1_pre_topc(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f31])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    ((((k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) & sK3 = sK4 & m1_subset_1(sK4,u1_struct_0(sK0))) & m1_subset_1(sK3,u1_struct_0(sK1))) & v3_borsuk_1(sK2,sK0,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v5_pre_topc(sK2,sK0,sK1) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & m1_pre_topc(sK1,sK0) & v4_tex_2(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v3_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f14,f30,f29,f28,f27,f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(sK0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,sK0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v5_pre_topc(X2,sK0,X1) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,sK0) & v4_tex_2(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v3_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(sK0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,sK0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v5_pre_topc(X2,sK0,X1) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,sK0) & v4_tex_2(X1,sK0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k6_domain_1(u1_struct_0(sK1),X3)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(sK0))) & m1_subset_1(X3,u1_struct_0(sK1))) & v3_borsuk_1(X2,sK0,sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v5_pre_topc(X2,sK0,sK1) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & m1_pre_topc(sK1,sK0) & v4_tex_2(sK1,sK0) & ~v2_struct_0(sK1))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ? [X2] : (? [X3] : (? [X4] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k6_domain_1(u1_struct_0(sK1),X3)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(sK0))) & m1_subset_1(X3,u1_struct_0(sK1))) & v3_borsuk_1(X2,sK0,sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v5_pre_topc(X2,sK0,sK1) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),X3)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(sK0))) & m1_subset_1(X3,u1_struct_0(sK1))) & v3_borsuk_1(sK2,sK0,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v5_pre_topc(sK2,sK0,sK1) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ? [X3] : (? [X4] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),X3)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(sK0))) & m1_subset_1(X3,u1_struct_0(sK1))) => (? [X4] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) & sK3 = X4 & m1_subset_1(X4,u1_struct_0(sK0))) & m1_subset_1(sK3,u1_struct_0(sK1)))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ? [X4] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) & sK3 = X4 & m1_subset_1(X4,u1_struct_0(sK0))) => (k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) & sK3 = sK4 & m1_subset_1(sK4,u1_struct_0(sK0)))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (? [X4] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,negated_conjecture,(
% 0.22/0.49    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)))))))))),
% 0.22/0.49    inference(negated_conjecture,[],[f11])).
% 0.22/0.49  fof(f11,conjecture,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)))))))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tex_2)).
% 0.22/0.49  fof(f300,plain,(
% 0.22/0.49    ~l1_pre_topc(sK0) | spl5_33),
% 0.22/0.49    inference(resolution,[],[f298,f50])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.49  fof(f298,plain,(
% 0.22/0.49    ~l1_struct_0(sK0) | spl5_33),
% 0.22/0.49    inference(avatar_component_clause,[],[f296])).
% 0.22/0.49  fof(f296,plain,(
% 0.22/0.49    spl5_33 <=> l1_struct_0(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).
% 0.22/0.49  fof(f299,plain,(
% 0.22/0.49    spl5_5 | ~spl5_33 | ~spl5_24 | ~spl5_28),
% 0.22/0.49    inference(avatar_split_clause,[],[f282,f242,f207,f296,f99])).
% 0.22/0.49  fof(f99,plain,(
% 0.22/0.49    spl5_5 <=> v2_struct_0(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.22/0.49  fof(f207,plain,(
% 0.22/0.49    spl5_24 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.22/0.49  fof(f242,plain,(
% 0.22/0.49    spl5_28 <=> k1_xboole_0 = u1_struct_0(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 0.22/0.50  % (5465)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.50  fof(f282,plain,(
% 0.22/0.50    ~v1_xboole_0(k1_xboole_0) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl5_28),
% 0.22/0.50    inference(superposition,[],[f54,f244])).
% 0.22/0.50  fof(f244,plain,(
% 0.22/0.50    k1_xboole_0 = u1_struct_0(sK0) | ~spl5_28),
% 0.22/0.50    inference(avatar_component_clause,[],[f242])).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.22/0.50  fof(f258,plain,(
% 0.22/0.50    ~spl5_25 | spl5_26 | ~spl5_16),
% 0.22/0.50    inference(avatar_split_clause,[],[f225,f159,f231,f227])).
% 0.22/0.50  fof(f227,plain,(
% 0.22/0.50    spl5_25 <=> m1_subset_1(k1_enumset1(sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 0.22/0.50  fof(f231,plain,(
% 0.22/0.50    spl5_26 <=> k2_pre_topc(sK0,k1_enumset1(sK4,sK4,sK4)) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k1_enumset1(sK4,sK4,sK4))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 0.22/0.50  fof(f159,plain,(
% 0.22/0.50    spl5_16 <=> ! [X0] : (k2_pre_topc(sK0,k1_enumset1(X0,X0,X0)) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k1_enumset1(X0,X0,X0)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(k1_enumset1(X0,X0,X0),k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.22/0.50  fof(f225,plain,(
% 0.22/0.50    k2_pre_topc(sK0,k1_enumset1(sK4,sK4,sK4)) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k1_enumset1(sK4,sK4,sK4)) | ~m1_subset_1(k1_enumset1(sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_16),
% 0.22/0.50    inference(resolution,[],[f160,f60])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    m1_subset_1(sK4,u1_struct_0(sK1))),
% 0.22/0.50    inference(definition_unfolding,[],[f44,f46])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    sK3 = sK4),
% 0.22/0.50    inference(cnf_transformation,[],[f31])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    m1_subset_1(sK3,u1_struct_0(sK1))),
% 0.22/0.50    inference(cnf_transformation,[],[f31])).
% 0.22/0.50  fof(f160,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | k2_pre_topc(sK0,k1_enumset1(X0,X0,X0)) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k1_enumset1(X0,X0,X0)) | ~m1_subset_1(k1_enumset1(X0,X0,X0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_16),
% 0.22/0.50    inference(avatar_component_clause,[],[f159])).
% 0.22/0.50  fof(f257,plain,(
% 0.22/0.50    ~spl5_2 | ~spl5_4 | ~spl5_26),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f256])).
% 0.22/0.50  fof(f256,plain,(
% 0.22/0.50    $false | (~spl5_2 | ~spl5_4 | ~spl5_26)),
% 0.22/0.50    inference(trivial_inequality_removal,[],[f255])).
% 0.22/0.50  fof(f255,plain,(
% 0.22/0.50    k2_pre_topc(sK0,k1_enumset1(sK4,sK4,sK4)) != k2_pre_topc(sK0,k1_enumset1(sK4,sK4,sK4)) | (~spl5_2 | ~spl5_4 | ~spl5_26)),
% 0.22/0.50    inference(superposition,[],[f96,f233])).
% 0.22/0.50  fof(f233,plain,(
% 0.22/0.50    k2_pre_topc(sK0,k1_enumset1(sK4,sK4,sK4)) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k1_enumset1(sK4,sK4,sK4)) | ~spl5_26),
% 0.22/0.50    inference(avatar_component_clause,[],[f231])).
% 0.22/0.50  fof(f96,plain,(
% 0.22/0.50    k2_pre_topc(sK0,k1_enumset1(sK4,sK4,sK4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k1_enumset1(sK4,sK4,sK4)) | (~spl5_2 | ~spl5_4)),
% 0.22/0.50    inference(backward_demodulation,[],[f94,f95])).
% 0.22/0.50  fof(f95,plain,(
% 0.22/0.50    k6_domain_1(u1_struct_0(sK1),sK4) = k1_enumset1(sK4,sK4,sK4) | ~spl5_4),
% 0.22/0.50    inference(resolution,[],[f82,f60])).
% 0.22/0.50  fof(f82,plain,(
% 0.22/0.50    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK1)) | k1_enumset1(X1,X1,X1) = k6_domain_1(u1_struct_0(sK1),X1)) ) | ~spl5_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f81])).
% 0.22/0.50  fof(f81,plain,(
% 0.22/0.50    spl5_4 <=> ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK1)) | k1_enumset1(X1,X1,X1) = k6_domain_1(u1_struct_0(sK1),X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.50  fof(f94,plain,(
% 0.22/0.50    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK4)) != k2_pre_topc(sK0,k1_enumset1(sK4,sK4,sK4)) | ~spl5_2),
% 0.22/0.50    inference(backward_demodulation,[],[f59,f93])).
% 0.22/0.50  fof(f93,plain,(
% 0.22/0.50    k6_domain_1(u1_struct_0(sK0),sK4) = k1_enumset1(sK4,sK4,sK4) | ~spl5_2),
% 0.22/0.50    inference(resolution,[],[f74,f45])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    m1_subset_1(sK4,u1_struct_0(sK0))),
% 0.22/0.50    inference(cnf_transformation,[],[f31])).
% 0.22/0.50  fof(f74,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k1_enumset1(X0,X0,X0) = k6_domain_1(u1_struct_0(sK0),X0)) ) | ~spl5_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f73])).
% 0.22/0.50  fof(f73,plain,(
% 0.22/0.50    spl5_2 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k1_enumset1(X0,X0,X0) = k6_domain_1(u1_struct_0(sK0),X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK4))),
% 0.22/0.50    inference(definition_unfolding,[],[f47,f46])).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4))),
% 0.22/0.50    inference(cnf_transformation,[],[f31])).
% 0.22/0.50  fof(f254,plain,(
% 0.22/0.50    spl5_27),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f253])).
% 0.22/0.50  fof(f253,plain,(
% 0.22/0.50    $false | spl5_27),
% 0.22/0.50    inference(resolution,[],[f240,f45])).
% 0.22/0.50  fof(f240,plain,(
% 0.22/0.50    ~m1_subset_1(sK4,u1_struct_0(sK0)) | spl5_27),
% 0.22/0.50    inference(avatar_component_clause,[],[f238])).
% 0.22/0.50  fof(f238,plain,(
% 0.22/0.50    spl5_27 <=> m1_subset_1(sK4,u1_struct_0(sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 0.22/0.50  fof(f252,plain,(
% 0.22/0.50    ~spl5_5),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f251])).
% 0.22/0.50  fof(f251,plain,(
% 0.22/0.50    $false | ~spl5_5),
% 0.22/0.50    inference(resolution,[],[f101,f32])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ~v2_struct_0(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f31])).
% 0.22/0.50  fof(f101,plain,(
% 0.22/0.50    v2_struct_0(sK0) | ~spl5_5),
% 0.22/0.50    inference(avatar_component_clause,[],[f99])).
% 0.22/0.50  fof(f250,plain,(
% 0.22/0.50    spl5_5 | ~spl5_6 | ~spl5_7 | ~spl5_1 | spl5_8 | ~spl5_9 | ~spl5_10 | ~spl5_11 | ~spl5_12 | ~spl5_13 | spl5_14),
% 0.22/0.50    inference(avatar_split_clause,[],[f221,f135,f131,f127,f123,f119,f115,f111,f69,f107,f103,f99])).
% 0.22/0.50  fof(f103,plain,(
% 0.22/0.50    spl5_6 <=> v2_pre_topc(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.22/0.50  fof(f107,plain,(
% 0.22/0.50    spl5_7 <=> v3_tdlat_3(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.22/0.50  fof(f69,plain,(
% 0.22/0.50    spl5_1 <=> l1_pre_topc(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.50  fof(f111,plain,(
% 0.22/0.50    spl5_8 <=> v2_struct_0(sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.22/0.50  fof(f115,plain,(
% 0.22/0.50    spl5_9 <=> v4_tex_2(sK1,sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.22/0.50  fof(f119,plain,(
% 0.22/0.50    spl5_10 <=> m1_pre_topc(sK1,sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.22/0.50  fof(f123,plain,(
% 0.22/0.50    spl5_11 <=> v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.22/0.50  fof(f127,plain,(
% 0.22/0.50    spl5_12 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.22/0.50  fof(f131,plain,(
% 0.22/0.50    spl5_13 <=> v3_borsuk_1(sK2,sK0,sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.22/0.50  fof(f135,plain,(
% 0.22/0.50    spl5_14 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.22/0.50  fof(f221,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v3_borsuk_1(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) | ~m1_pre_topc(sK1,sK0) | ~v4_tex_2(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v3_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.50    inference(resolution,[],[f40,f87])).
% 0.22/0.50  fof(f87,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X2)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2))) | ~v3_borsuk_1(sK2,X1,X2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v5_pre_topc(sK2,X1,X2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | k2_pre_topc(X1,X0) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),sK2,X0) | ~m1_pre_topc(X2,X1) | ~v4_tex_2(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v3_tdlat_3(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.22/0.50    inference(resolution,[],[f63,f39])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    v1_funct_1(sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f31])).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | k2_pre_topc(X0,X4) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.50    inference(equality_resolution,[],[f53])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X3,X1] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : (! [X4] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,axiom,(
% 0.22/0.50    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4))))))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tex_2)).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.50    inference(cnf_transformation,[],[f31])).
% 0.22/0.50  fof(f245,plain,(
% 0.22/0.50    ~spl5_27 | spl5_28 | spl5_25),
% 0.22/0.50    inference(avatar_split_clause,[],[f235,f227,f242,f238])).
% 0.22/0.50  fof(f235,plain,(
% 0.22/0.50    k1_xboole_0 = u1_struct_0(sK0) | ~m1_subset_1(sK4,u1_struct_0(sK0)) | spl5_25),
% 0.22/0.50    inference(resolution,[],[f229,f61])).
% 0.22/0.50  fof(f61,plain,(
% 0.22/0.50    ( ! [X0,X1] : (m1_subset_1(k1_enumset1(X1,X1,X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0)) )),
% 0.22/0.50    inference(definition_unfolding,[],[f56,f58])).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.22/0.50    inference(definition_unfolding,[],[f49,f55])).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0))),
% 0.22/0.50    inference(flattening,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0,X1] : ((m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0) | ~m1_subset_1(X1,X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X1,X0) => (k1_xboole_0 != X0 => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_subset_1)).
% 0.22/0.50  fof(f229,plain,(
% 0.22/0.50    ~m1_subset_1(k1_enumset1(sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK0))) | spl5_25),
% 0.22/0.50    inference(avatar_component_clause,[],[f227])).
% 0.22/0.50  fof(f219,plain,(
% 0.22/0.50    ~spl5_3 | spl5_23),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f217])).
% 0.22/0.50  fof(f217,plain,(
% 0.22/0.50    $false | (~spl5_3 | spl5_23)),
% 0.22/0.50    inference(resolution,[],[f213,f78])).
% 0.22/0.50  fof(f78,plain,(
% 0.22/0.50    l1_pre_topc(sK1) | ~spl5_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f77])).
% 0.22/0.50  fof(f77,plain,(
% 0.22/0.50    spl5_3 <=> l1_pre_topc(sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.50  fof(f213,plain,(
% 0.22/0.50    ~l1_pre_topc(sK1) | spl5_23),
% 0.22/0.50    inference(resolution,[],[f205,f50])).
% 0.22/0.50  fof(f205,plain,(
% 0.22/0.50    ~l1_struct_0(sK1) | spl5_23),
% 0.22/0.50    inference(avatar_component_clause,[],[f203])).
% 0.22/0.50  fof(f203,plain,(
% 0.22/0.50    spl5_23 <=> l1_struct_0(sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 0.22/0.50  fof(f216,plain,(
% 0.22/0.50    spl5_24),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f214])).
% 0.22/0.50  fof(f214,plain,(
% 0.22/0.50    $false | spl5_24),
% 0.22/0.50    inference(resolution,[],[f209,f48])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    v1_xboole_0(k1_xboole_0)),
% 0.22/0.50    inference(cnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    v1_xboole_0(k1_xboole_0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.50  fof(f209,plain,(
% 0.22/0.50    ~v1_xboole_0(k1_xboole_0) | spl5_24),
% 0.22/0.50    inference(avatar_component_clause,[],[f207])).
% 0.22/0.50  fof(f212,plain,(
% 0.22/0.50    ~spl5_8),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f211])).
% 0.22/0.50  fof(f211,plain,(
% 0.22/0.50    $false | ~spl5_8),
% 0.22/0.50    inference(resolution,[],[f113,f36])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ~v2_struct_0(sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f31])).
% 0.22/0.50  fof(f113,plain,(
% 0.22/0.50    v2_struct_0(sK1) | ~spl5_8),
% 0.22/0.50    inference(avatar_component_clause,[],[f111])).
% 0.22/0.50  fof(f210,plain,(
% 0.22/0.50    spl5_8 | ~spl5_23 | ~spl5_24 | ~spl5_15),
% 0.22/0.50    inference(avatar_split_clause,[],[f181,f155,f207,f203,f111])).
% 0.22/0.50  fof(f155,plain,(
% 0.22/0.50    spl5_15 <=> k1_xboole_0 = u1_struct_0(sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.22/0.50  fof(f181,plain,(
% 0.22/0.50    ~v1_xboole_0(k1_xboole_0) | ~l1_struct_0(sK1) | v2_struct_0(sK1) | ~spl5_15),
% 0.22/0.50    inference(superposition,[],[f54,f157])).
% 0.22/0.50  fof(f157,plain,(
% 0.22/0.50    k1_xboole_0 = u1_struct_0(sK1) | ~spl5_15),
% 0.22/0.50    inference(avatar_component_clause,[],[f155])).
% 0.22/0.50  fof(f161,plain,(
% 0.22/0.50    spl5_15 | spl5_16 | ~spl5_14),
% 0.22/0.50    inference(avatar_split_clause,[],[f152,f135,f159,f155])).
% 0.22/0.50  fof(f152,plain,(
% 0.22/0.50    ( ! [X0] : (k2_pre_topc(sK0,k1_enumset1(X0,X0,X0)) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k1_enumset1(X0,X0,X0)) | ~m1_subset_1(k1_enumset1(X0,X0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = u1_struct_0(sK1) | ~m1_subset_1(X0,u1_struct_0(sK1))) ) | ~spl5_14),
% 0.22/0.50    inference(resolution,[],[f136,f61])).
% 0.22/0.50  fof(f136,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_14),
% 0.22/0.50    inference(avatar_component_clause,[],[f135])).
% 0.22/0.50  fof(f151,plain,(
% 0.22/0.50    spl5_12),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f150])).
% 0.22/0.50  fof(f150,plain,(
% 0.22/0.50    $false | spl5_12),
% 0.22/0.50    inference(resolution,[],[f129,f42])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.50    inference(cnf_transformation,[],[f31])).
% 0.22/0.50  fof(f129,plain,(
% 0.22/0.50    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | spl5_12),
% 0.22/0.50    inference(avatar_component_clause,[],[f127])).
% 0.22/0.50  fof(f149,plain,(
% 0.22/0.50    spl5_13),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f148])).
% 0.22/0.50  fof(f148,plain,(
% 0.22/0.50    $false | spl5_13),
% 0.22/0.50    inference(resolution,[],[f133,f43])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    v3_borsuk_1(sK2,sK0,sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f31])).
% 0.22/0.50  fof(f133,plain,(
% 0.22/0.50    ~v3_borsuk_1(sK2,sK0,sK1) | spl5_13),
% 0.22/0.50    inference(avatar_component_clause,[],[f131])).
% 0.22/0.50  fof(f147,plain,(
% 0.22/0.50    spl5_11),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f146])).
% 0.22/0.50  fof(f146,plain,(
% 0.22/0.50    $false | spl5_11),
% 0.22/0.50    inference(resolution,[],[f125,f41])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f31])).
% 0.22/0.50  fof(f125,plain,(
% 0.22/0.50    ~v5_pre_topc(sK2,sK0,sK1) | spl5_11),
% 0.22/0.50    inference(avatar_component_clause,[],[f123])).
% 0.22/0.50  fof(f145,plain,(
% 0.22/0.50    spl5_10),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f144])).
% 0.22/0.50  fof(f144,plain,(
% 0.22/0.50    $false | spl5_10),
% 0.22/0.50    inference(resolution,[],[f121,f38])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    m1_pre_topc(sK1,sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f31])).
% 0.22/0.50  fof(f121,plain,(
% 0.22/0.50    ~m1_pre_topc(sK1,sK0) | spl5_10),
% 0.22/0.50    inference(avatar_component_clause,[],[f119])).
% 0.22/0.50  fof(f143,plain,(
% 0.22/0.50    spl5_9),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f142])).
% 0.22/0.50  fof(f142,plain,(
% 0.22/0.50    $false | spl5_9),
% 0.22/0.50    inference(resolution,[],[f117,f37])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    v4_tex_2(sK1,sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f31])).
% 0.22/0.50  fof(f117,plain,(
% 0.22/0.50    ~v4_tex_2(sK1,sK0) | spl5_9),
% 0.22/0.50    inference(avatar_component_clause,[],[f115])).
% 0.22/0.50  fof(f141,plain,(
% 0.22/0.50    spl5_7),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f140])).
% 0.22/0.50  fof(f140,plain,(
% 0.22/0.50    $false | spl5_7),
% 0.22/0.50    inference(resolution,[],[f109,f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    v3_tdlat_3(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f31])).
% 0.22/0.50  fof(f109,plain,(
% 0.22/0.50    ~v3_tdlat_3(sK0) | spl5_7),
% 0.22/0.50    inference(avatar_component_clause,[],[f107])).
% 0.22/0.50  fof(f139,plain,(
% 0.22/0.50    spl5_6),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f138])).
% 0.22/0.50  fof(f138,plain,(
% 0.22/0.50    $false | spl5_6),
% 0.22/0.50    inference(resolution,[],[f105,f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    v2_pre_topc(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f31])).
% 0.22/0.50  fof(f105,plain,(
% 0.22/0.50    ~v2_pre_topc(sK0) | spl5_6),
% 0.22/0.50    inference(avatar_component_clause,[],[f103])).
% 0.22/0.50  fof(f92,plain,(
% 0.22/0.50    spl5_3),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f90])).
% 0.22/0.50  fof(f90,plain,(
% 0.22/0.50    $false | spl5_3),
% 0.22/0.50    inference(resolution,[],[f89,f35])).
% 0.22/0.50  fof(f89,plain,(
% 0.22/0.50    ~l1_pre_topc(sK0) | spl5_3),
% 0.22/0.50    inference(resolution,[],[f88,f38])).
% 0.22/0.50  fof(f88,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_pre_topc(sK1,X0) | ~l1_pre_topc(X0)) ) | spl5_3),
% 0.22/0.50    inference(resolution,[],[f79,f51])).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.22/0.50  fof(f79,plain,(
% 0.22/0.50    ~l1_pre_topc(sK1) | spl5_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f77])).
% 0.22/0.50  fof(f86,plain,(
% 0.22/0.50    spl5_1),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f84])).
% 0.22/0.50  fof(f84,plain,(
% 0.22/0.50    $false | spl5_1),
% 0.22/0.50    inference(resolution,[],[f71,f35])).
% 0.22/0.50  fof(f71,plain,(
% 0.22/0.50    ~l1_pre_topc(sK0) | spl5_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f69])).
% 0.22/0.50  fof(f83,plain,(
% 0.22/0.50    ~spl5_3 | spl5_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f67,f81,f77])).
% 0.22/0.50  fof(f67,plain,(
% 0.22/0.50    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK1)) | k1_enumset1(X1,X1,X1) = k6_domain_1(u1_struct_0(sK1),X1) | ~l1_pre_topc(sK1)) )),
% 0.22/0.50    inference(resolution,[],[f65,f36])).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v2_struct_0(X1) | ~m1_subset_1(X0,u1_struct_0(X1)) | k1_enumset1(X0,X0,X0) = k6_domain_1(u1_struct_0(X1),X0) | ~l1_pre_topc(X1)) )),
% 0.22/0.50    inference(resolution,[],[f64,f50])).
% 0.22/0.50  fof(f64,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~l1_struct_0(X1) | k1_enumset1(X0,X0,X0) = k6_domain_1(u1_struct_0(X1),X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | v2_struct_0(X1)) )),
% 0.22/0.50    inference(resolution,[],[f62,f54])).
% 0.22/0.50  fof(f62,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_enumset1(X1,X1,X1)) )),
% 0.22/0.50    inference(definition_unfolding,[],[f57,f58])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.50    inference(flattening,[],[f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,axiom,(
% 0.22/0.50    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.22/0.50  fof(f75,plain,(
% 0.22/0.50    ~spl5_1 | spl5_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f66,f73,f69])).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k1_enumset1(X0,X0,X0) = k6_domain_1(u1_struct_0(sK0),X0) | ~l1_pre_topc(sK0)) )),
% 0.22/0.50    inference(resolution,[],[f65,f32])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (5449)------------------------------
% 0.22/0.50  % (5449)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (5449)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (5449)Memory used [KB]: 6396
% 0.22/0.50  % (5449)Time elapsed: 0.093 s
% 0.22/0.50  % (5449)------------------------------
% 0.22/0.50  % (5449)------------------------------
% 0.22/0.50  % (5436)Success in time 0.136 s
%------------------------------------------------------------------------------
