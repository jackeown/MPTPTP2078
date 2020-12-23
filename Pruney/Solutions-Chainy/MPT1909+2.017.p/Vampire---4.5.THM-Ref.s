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
% DateTime   : Thu Dec  3 13:22:29 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 590 expanded)
%              Number of leaves         :   30 ( 266 expanded)
%              Depth                    :   22
%              Number of atoms          :  637 (6348 expanded)
%              Number of equality atoms :  104 (1172 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f268,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f101,f105,f110,f121,f125,f131,f136,f252,f267])).

fof(f267,plain,
    ( ~ spl5_1
    | spl5_5 ),
    inference(avatar_contradiction_clause,[],[f266])).

fof(f266,plain,
    ( $false
    | ~ spl5_1
    | spl5_5 ),
    inference(subsumption_resolution,[],[f97,f257])).

fof(f257,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl5_5 ),
    inference(subsumption_resolution,[],[f139,f116])).

fof(f116,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl5_5
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f139,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f89,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f89,plain,(
    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f87,f46])).

fof(f46,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f21,f41,f40,f39,f38,f37])).

fof(f37,plain,
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

fof(f38,plain,
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

fof(f39,plain,
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

fof(f40,plain,
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

fof(f41,plain,
    ( ? [X4] :
        ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3))
        & sK3 = X4
        & m1_subset_1(X4,u1_struct_0(sK0)) )
   => ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4))
      & sK3 = sK4
      & m1_subset_1(sK4,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
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

fof(f87,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f49,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f49,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f97,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl5_1
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f252,plain,
    ( ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(avatar_contradiction_clause,[],[f251])).

fof(f251,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f250,f137])).

fof(f137,plain,
    ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK0),sK4))
    | ~ spl5_8 ),
    inference(backward_demodulation,[],[f82,f130])).

fof(f130,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK4) = k6_domain_1(u1_struct_0(sK1),sK4)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl5_8
  <=> k6_domain_1(u1_struct_0(sK0),sK4) = k6_domain_1(u1_struct_0(sK1),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f82,plain,(
    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK4)) ),
    inference(definition_unfolding,[],[f58,f57])).

fof(f57,plain,(
    sK3 = sK4 ),
    inference(cnf_transformation,[],[f42])).

fof(f58,plain,(
    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) ),
    inference(cnf_transformation,[],[f42])).

fof(f250,plain,
    ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK0),sK4))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f249,f233])).

fof(f233,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK4),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f232,f56])).

fof(f56,plain,(
    m1_subset_1(sK4,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f42])).

fof(f232,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK4),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(superposition,[],[f104,f230])).

fof(f230,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK4) = k7_domain_1(u1_struct_0(sK0),sK4,sK4)
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f229,f109])).

fof(f109,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK4) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl5_4
  <=> k6_domain_1(u1_struct_0(sK0),sK4) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f229,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k7_domain_1(u1_struct_0(sK0),sK4,sK4)
    | ~ spl5_2 ),
    inference(resolution,[],[f100,f56])).

fof(f100,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k7_domain_1(u1_struct_0(sK0),X0,sK4) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK4) )
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl5_2
  <=> ! [X0] :
        ( k7_domain_1(u1_struct_0(sK0),X0,sK4) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK4)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f104,plain,
    ( ! [X1] :
        ( m1_subset_1(k7_domain_1(u1_struct_0(sK0),X1,sK4),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl5_3
  <=> ! [X1] :
        ( m1_subset_1(k7_domain_1(u1_struct_0(sK0),X1,sK4),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f249,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK4),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK0),sK4))
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(resolution,[],[f175,f242])).

fof(f242,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f241,f83])).

fof(f83,plain,(
    m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(definition_unfolding,[],[f55,f57])).

fof(f55,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f42])).

fof(f241,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(superposition,[],[f124,f240])).

fof(f240,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK4) = k7_domain_1(u1_struct_0(sK1),sK4,sK4)
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f239,f109])).

fof(f239,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k7_domain_1(u1_struct_0(sK1),sK4,sK4)
    | ~ spl5_6 ),
    inference(resolution,[],[f120,f83])).

fof(f120,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK4) = k7_domain_1(u1_struct_0(sK1),X0,sK4) )
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl5_6
  <=> ! [X0] :
        ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK4) = k7_domain_1(u1_struct_0(sK1),X0,sK4)
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f124,plain,
    ( ! [X1] :
        ( m1_subset_1(k7_domain_1(u1_struct_0(sK1),X1,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X1,u1_struct_0(sK1)) )
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl5_7
  <=> ! [X1] :
        ( m1_subset_1(k7_domain_1(u1_struct_0(sK1),X1,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X1,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f175,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) ) ),
    inference(subsumption_resolution,[],[f174,f43])).

fof(f43,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f174,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f173,f44])).

fof(f44,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f173,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f172,f45])).

fof(f45,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f172,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)
      | ~ v3_tdlat_3(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f171,f46])).

fof(f171,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)
      | ~ l1_pre_topc(sK0)
      | ~ v3_tdlat_3(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f170,f47])).

fof(f47,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f170,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v3_tdlat_3(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f169,f48])).

fof(f48,plain,(
    v4_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f169,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)
      | ~ v4_tex_2(sK1,sK0)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v3_tdlat_3(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f168,f49])).

fof(f168,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)
      | ~ m1_pre_topc(sK1,sK0)
      | ~ v4_tex_2(sK1,sK0)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v3_tdlat_3(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f167,f50])).

fof(f50,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f167,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)
      | ~ v1_funct_1(sK2)
      | ~ m1_pre_topc(sK1,sK0)
      | ~ v4_tex_2(sK1,sK0)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v3_tdlat_3(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f166,f51])).

fof(f51,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f42])).

fof(f166,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(sK2)
      | ~ m1_pre_topc(sK1,sK0)
      | ~ v4_tex_2(sK1,sK0)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v3_tdlat_3(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f165,f52])).

fof(f52,plain,(
    v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f165,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(sK2)
      | ~ m1_pre_topc(sK1,sK0)
      | ~ v4_tex_2(sK1,sK0)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v3_tdlat_3(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f160,f54])).

fof(f54,plain,(
    v3_borsuk_1(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f160,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v3_borsuk_1(sK2,sK0,sK1)
      | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(sK2)
      | ~ m1_pre_topc(sK1,sK0)
      | ~ v4_tex_2(sK1,sK0)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v3_tdlat_3(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f53,f86])).

fof(f86,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v3_borsuk_1(X2,X0,X1)
      | k2_pre_topc(X0,X4) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)
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
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
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
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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

fof(f53,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f42])).

fof(f136,plain,(
    ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f135])).

fof(f135,plain,
    ( $false
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f134,f90])).

fof(f90,plain,(
    l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f88,f46])).

fof(f88,plain,
    ( l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f49,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f134,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ spl5_5 ),
    inference(resolution,[],[f133,f60])).

fof(f60,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f133,plain,
    ( ~ l1_struct_0(sK1)
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f132,f47])).

fof(f132,plain,
    ( ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl5_5 ),
    inference(resolution,[],[f117,f66])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f117,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f115])).

fof(f131,plain,
    ( spl5_5
    | spl5_8
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f126,f107,f128,f115])).

fof(f126,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK4) = k6_domain_1(u1_struct_0(sK1),sK4)
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f113,f109])).

fof(f113,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK4) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(resolution,[],[f83,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f68,f81])).

fof(f81,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f59,f80])).

fof(f80,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f67,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f69,f78])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f72,f77])).

fof(f77,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f73,f76])).

fof(f76,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f74,f75])).

fof(f75,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f74,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f73,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f72,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f69,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f67,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f59,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f68,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f125,plain,
    ( spl5_5
    | spl5_7 ),
    inference(avatar_split_clause,[],[f112,f123,f115])).

fof(f112,plain,(
    ! [X1] :
      ( m1_subset_1(k7_domain_1(u1_struct_0(sK1),X1,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | v1_xboole_0(u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f83,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_domain_1)).

fof(f121,plain,
    ( spl5_5
    | spl5_6 ),
    inference(avatar_split_clause,[],[f111,f119,f115])).

fof(f111,plain,(
    ! [X0] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK4) = k7_domain_1(u1_struct_0(sK1),X0,sK4)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | v1_xboole_0(u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f83,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | k7_domain_1(X0,X1,X2) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f71,f80])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_domain_1)).

fof(f110,plain,
    ( spl5_1
    | spl5_4 ),
    inference(avatar_split_clause,[],[f93,f107,f95])).

fof(f93,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK4) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f56,f84])).

fof(f105,plain,
    ( spl5_1
    | spl5_3 ),
    inference(avatar_split_clause,[],[f92,f103,f95])).

fof(f92,plain,(
    ! [X1] :
      ( m1_subset_1(k7_domain_1(u1_struct_0(sK0),X1,sK4),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | v1_xboole_0(u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f56,f70])).

fof(f101,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f91,f99,f95])).

fof(f91,plain,(
    ! [X0] :
      ( k7_domain_1(u1_struct_0(sK0),X0,sK4) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK4)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v1_xboole_0(u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f56,f85])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:28:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.46  % (21308)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.19/0.47  % (21324)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.19/0.48  % (21308)Refutation found. Thanks to Tanya!
% 0.19/0.48  % SZS status Theorem for theBenchmark
% 0.19/0.48  % SZS output start Proof for theBenchmark
% 0.19/0.48  fof(f268,plain,(
% 0.19/0.48    $false),
% 0.19/0.48    inference(avatar_sat_refutation,[],[f101,f105,f110,f121,f125,f131,f136,f252,f267])).
% 0.19/0.48  fof(f267,plain,(
% 0.19/0.48    ~spl5_1 | spl5_5),
% 0.19/0.48    inference(avatar_contradiction_clause,[],[f266])).
% 0.19/0.48  fof(f266,plain,(
% 0.19/0.48    $false | (~spl5_1 | spl5_5)),
% 0.19/0.48    inference(subsumption_resolution,[],[f97,f257])).
% 0.19/0.48  fof(f257,plain,(
% 0.19/0.48    ~v1_xboole_0(u1_struct_0(sK0)) | spl5_5),
% 0.19/0.48    inference(subsumption_resolution,[],[f139,f116])).
% 0.19/0.48  fof(f116,plain,(
% 0.19/0.48    ~v1_xboole_0(u1_struct_0(sK1)) | spl5_5),
% 0.19/0.48    inference(avatar_component_clause,[],[f115])).
% 0.19/0.48  fof(f115,plain,(
% 0.19/0.48    spl5_5 <=> v1_xboole_0(u1_struct_0(sK1))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.19/0.48  fof(f139,plain,(
% 0.19/0.48    v1_xboole_0(u1_struct_0(sK1)) | ~v1_xboole_0(u1_struct_0(sK0))),
% 0.19/0.48    inference(resolution,[],[f89,f64])).
% 0.19/0.48  fof(f64,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f26])).
% 0.19/0.48  fof(f26,plain,(
% 0.19/0.48    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.19/0.48    inference(ennf_transformation,[],[f8])).
% 0.19/0.48  fof(f8,axiom,(
% 0.19/0.48    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.19/0.48  fof(f89,plain,(
% 0.19/0.48    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.48    inference(subsumption_resolution,[],[f87,f46])).
% 0.19/0.48  fof(f46,plain,(
% 0.19/0.48    l1_pre_topc(sK0)),
% 0.19/0.48    inference(cnf_transformation,[],[f42])).
% 0.19/0.48  fof(f42,plain,(
% 0.19/0.48    ((((k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) & sK3 = sK4 & m1_subset_1(sK4,u1_struct_0(sK0))) & m1_subset_1(sK3,u1_struct_0(sK1))) & v3_borsuk_1(sK2,sK0,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v5_pre_topc(sK2,sK0,sK1) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & m1_pre_topc(sK1,sK0) & v4_tex_2(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v3_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.19/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f21,f41,f40,f39,f38,f37])).
% 0.19/0.48  fof(f37,plain,(
% 0.19/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(sK0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,sK0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v5_pre_topc(X2,sK0,X1) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,sK0) & v4_tex_2(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v3_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.19/0.48    introduced(choice_axiom,[])).
% 0.19/0.48  fof(f38,plain,(
% 0.19/0.48    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(sK0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,sK0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v5_pre_topc(X2,sK0,X1) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,sK0) & v4_tex_2(X1,sK0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k6_domain_1(u1_struct_0(sK1),X3)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(sK0))) & m1_subset_1(X3,u1_struct_0(sK1))) & v3_borsuk_1(X2,sK0,sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v5_pre_topc(X2,sK0,sK1) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & m1_pre_topc(sK1,sK0) & v4_tex_2(sK1,sK0) & ~v2_struct_0(sK1))),
% 0.19/0.48    introduced(choice_axiom,[])).
% 0.19/0.48  fof(f39,plain,(
% 0.19/0.48    ? [X2] : (? [X3] : (? [X4] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k6_domain_1(u1_struct_0(sK1),X3)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(sK0))) & m1_subset_1(X3,u1_struct_0(sK1))) & v3_borsuk_1(X2,sK0,sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v5_pre_topc(X2,sK0,sK1) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),X3)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(sK0))) & m1_subset_1(X3,u1_struct_0(sK1))) & v3_borsuk_1(sK2,sK0,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v5_pre_topc(sK2,sK0,sK1) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.19/0.48    introduced(choice_axiom,[])).
% 0.19/0.48  fof(f40,plain,(
% 0.19/0.48    ? [X3] : (? [X4] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),X3)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(sK0))) & m1_subset_1(X3,u1_struct_0(sK1))) => (? [X4] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) & sK3 = X4 & m1_subset_1(X4,u1_struct_0(sK0))) & m1_subset_1(sK3,u1_struct_0(sK1)))),
% 0.19/0.48    introduced(choice_axiom,[])).
% 0.19/0.48  fof(f41,plain,(
% 0.19/0.48    ? [X4] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) & sK3 = X4 & m1_subset_1(X4,u1_struct_0(sK0))) => (k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) & sK3 = sK4 & m1_subset_1(sK4,u1_struct_0(sK0)))),
% 0.19/0.48    introduced(choice_axiom,[])).
% 0.19/0.48  fof(f21,plain,(
% 0.19/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.19/0.48    inference(flattening,[],[f20])).
% 0.19/0.48  fof(f20,plain,(
% 0.19/0.48    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (? [X4] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.19/0.48    inference(ennf_transformation,[],[f19])).
% 0.19/0.48  fof(f19,negated_conjecture,(
% 0.19/0.48    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)))))))))),
% 0.19/0.48    inference(negated_conjecture,[],[f18])).
% 0.19/0.48  fof(f18,conjecture,(
% 0.19/0.48    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)))))))))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tex_2)).
% 0.19/0.48  fof(f87,plain,(
% 0.19/0.48    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.19/0.48    inference(resolution,[],[f49,f62])).
% 0.19/0.48  fof(f62,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f24])).
% 0.19/0.48  fof(f24,plain,(
% 0.19/0.48    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.19/0.48    inference(ennf_transformation,[],[f16])).
% 0.19/0.48  fof(f16,axiom,(
% 0.19/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.19/0.48  fof(f49,plain,(
% 0.19/0.48    m1_pre_topc(sK1,sK0)),
% 0.19/0.48    inference(cnf_transformation,[],[f42])).
% 0.19/0.48  fof(f97,plain,(
% 0.19/0.48    v1_xboole_0(u1_struct_0(sK0)) | ~spl5_1),
% 0.19/0.48    inference(avatar_component_clause,[],[f95])).
% 0.19/0.48  fof(f95,plain,(
% 0.19/0.48    spl5_1 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.19/0.48  fof(f252,plain,(
% 0.19/0.48    ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_6 | ~spl5_7 | ~spl5_8),
% 0.19/0.48    inference(avatar_contradiction_clause,[],[f251])).
% 0.19/0.48  fof(f251,plain,(
% 0.19/0.48    $false | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_6 | ~spl5_7 | ~spl5_8)),
% 0.19/0.48    inference(subsumption_resolution,[],[f250,f137])).
% 0.19/0.48  fof(f137,plain,(
% 0.19/0.48    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK0),sK4)) | ~spl5_8),
% 0.19/0.48    inference(backward_demodulation,[],[f82,f130])).
% 0.19/0.48  fof(f130,plain,(
% 0.19/0.48    k6_domain_1(u1_struct_0(sK0),sK4) = k6_domain_1(u1_struct_0(sK1),sK4) | ~spl5_8),
% 0.19/0.48    inference(avatar_component_clause,[],[f128])).
% 0.19/0.48  fof(f128,plain,(
% 0.19/0.48    spl5_8 <=> k6_domain_1(u1_struct_0(sK0),sK4) = k6_domain_1(u1_struct_0(sK1),sK4)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.19/0.48  fof(f82,plain,(
% 0.19/0.48    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK4))),
% 0.19/0.48    inference(definition_unfolding,[],[f58,f57])).
% 0.19/0.48  fof(f57,plain,(
% 0.19/0.48    sK3 = sK4),
% 0.19/0.48    inference(cnf_transformation,[],[f42])).
% 0.19/0.48  fof(f58,plain,(
% 0.19/0.48    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4))),
% 0.19/0.48    inference(cnf_transformation,[],[f42])).
% 0.19/0.48  fof(f250,plain,(
% 0.19/0.48    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK0),sK4)) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_6 | ~spl5_7)),
% 0.19/0.48    inference(subsumption_resolution,[],[f249,f233])).
% 0.19/0.48  fof(f233,plain,(
% 0.19/0.48    m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK4),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_2 | ~spl5_3 | ~spl5_4)),
% 0.19/0.48    inference(subsumption_resolution,[],[f232,f56])).
% 0.19/0.48  fof(f56,plain,(
% 0.19/0.48    m1_subset_1(sK4,u1_struct_0(sK0))),
% 0.19/0.48    inference(cnf_transformation,[],[f42])).
% 0.19/0.48  fof(f232,plain,(
% 0.19/0.48    m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK4),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK4,u1_struct_0(sK0)) | (~spl5_2 | ~spl5_3 | ~spl5_4)),
% 0.19/0.48    inference(superposition,[],[f104,f230])).
% 0.19/0.48  fof(f230,plain,(
% 0.19/0.48    k6_domain_1(u1_struct_0(sK0),sK4) = k7_domain_1(u1_struct_0(sK0),sK4,sK4) | (~spl5_2 | ~spl5_4)),
% 0.19/0.48    inference(forward_demodulation,[],[f229,f109])).
% 0.19/0.48  fof(f109,plain,(
% 0.19/0.48    k6_domain_1(u1_struct_0(sK0),sK4) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) | ~spl5_4),
% 0.19/0.48    inference(avatar_component_clause,[],[f107])).
% 0.19/0.48  fof(f107,plain,(
% 0.19/0.48    spl5_4 <=> k6_domain_1(u1_struct_0(sK0),sK4) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.19/0.48  fof(f229,plain,(
% 0.19/0.48    k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k7_domain_1(u1_struct_0(sK0),sK4,sK4) | ~spl5_2),
% 0.19/0.48    inference(resolution,[],[f100,f56])).
% 0.19/0.48  fof(f100,plain,(
% 0.19/0.48    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k7_domain_1(u1_struct_0(sK0),X0,sK4) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK4)) ) | ~spl5_2),
% 0.19/0.48    inference(avatar_component_clause,[],[f99])).
% 0.19/0.48  fof(f99,plain,(
% 0.19/0.48    spl5_2 <=> ! [X0] : (k7_domain_1(u1_struct_0(sK0),X0,sK4) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK4) | ~m1_subset_1(X0,u1_struct_0(sK0)))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.19/0.48  fof(f104,plain,(
% 0.19/0.48    ( ! [X1] : (m1_subset_1(k7_domain_1(u1_struct_0(sK0),X1,sK4),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl5_3),
% 0.19/0.48    inference(avatar_component_clause,[],[f103])).
% 0.19/0.48  fof(f103,plain,(
% 0.19/0.48    spl5_3 <=> ! [X1] : (m1_subset_1(k7_domain_1(u1_struct_0(sK0),X1,sK4),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.19/0.48  fof(f249,plain,(
% 0.19/0.48    ~m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK4),k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK0),sK4)) | (~spl5_4 | ~spl5_6 | ~spl5_7)),
% 0.19/0.48    inference(resolution,[],[f175,f242])).
% 0.19/0.48  fof(f242,plain,(
% 0.19/0.48    m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK4),k1_zfmisc_1(u1_struct_0(sK1))) | (~spl5_4 | ~spl5_6 | ~spl5_7)),
% 0.19/0.48    inference(subsumption_resolution,[],[f241,f83])).
% 0.19/0.48  fof(f83,plain,(
% 0.19/0.48    m1_subset_1(sK4,u1_struct_0(sK1))),
% 0.19/0.48    inference(definition_unfolding,[],[f55,f57])).
% 0.19/0.48  fof(f55,plain,(
% 0.19/0.48    m1_subset_1(sK3,u1_struct_0(sK1))),
% 0.19/0.48    inference(cnf_transformation,[],[f42])).
% 0.19/0.48  fof(f241,plain,(
% 0.19/0.48    m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK4),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | (~spl5_4 | ~spl5_6 | ~spl5_7)),
% 0.19/0.48    inference(superposition,[],[f124,f240])).
% 0.19/0.48  fof(f240,plain,(
% 0.19/0.48    k6_domain_1(u1_struct_0(sK0),sK4) = k7_domain_1(u1_struct_0(sK1),sK4,sK4) | (~spl5_4 | ~spl5_6)),
% 0.19/0.48    inference(forward_demodulation,[],[f239,f109])).
% 0.19/0.48  fof(f239,plain,(
% 0.19/0.48    k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k7_domain_1(u1_struct_0(sK1),sK4,sK4) | ~spl5_6),
% 0.19/0.48    inference(resolution,[],[f120,f83])).
% 0.19/0.48  fof(f120,plain,(
% 0.19/0.48    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK4) = k7_domain_1(u1_struct_0(sK1),X0,sK4)) ) | ~spl5_6),
% 0.19/0.48    inference(avatar_component_clause,[],[f119])).
% 0.19/0.48  fof(f119,plain,(
% 0.19/0.48    spl5_6 <=> ! [X0] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK4) = k7_domain_1(u1_struct_0(sK1),X0,sK4) | ~m1_subset_1(X0,u1_struct_0(sK1)))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.19/0.48  fof(f124,plain,(
% 0.19/0.48    ( ! [X1] : (m1_subset_1(k7_domain_1(u1_struct_0(sK1),X1,sK4),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X1,u1_struct_0(sK1))) ) | ~spl5_7),
% 0.19/0.48    inference(avatar_component_clause,[],[f123])).
% 0.19/0.48  fof(f123,plain,(
% 0.19/0.48    spl5_7 <=> ! [X1] : (m1_subset_1(k7_domain_1(u1_struct_0(sK1),X1,sK4),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X1,u1_struct_0(sK1)))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.19/0.48  fof(f175,plain,(
% 0.19/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)) )),
% 0.19/0.48    inference(subsumption_resolution,[],[f174,f43])).
% 0.19/0.48  fof(f43,plain,(
% 0.19/0.48    ~v2_struct_0(sK0)),
% 0.19/0.48    inference(cnf_transformation,[],[f42])).
% 0.19/0.48  fof(f174,plain,(
% 0.19/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) | v2_struct_0(sK0)) )),
% 0.19/0.48    inference(subsumption_resolution,[],[f173,f44])).
% 0.19/0.48  fof(f44,plain,(
% 0.19/0.48    v2_pre_topc(sK0)),
% 0.19/0.48    inference(cnf_transformation,[],[f42])).
% 0.19/0.48  fof(f173,plain,(
% 0.19/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.19/0.48    inference(subsumption_resolution,[],[f172,f45])).
% 0.19/0.48  fof(f45,plain,(
% 0.19/0.48    v3_tdlat_3(sK0)),
% 0.19/0.48    inference(cnf_transformation,[],[f42])).
% 0.19/0.48  fof(f172,plain,(
% 0.19/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) | ~v3_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.19/0.48    inference(subsumption_resolution,[],[f171,f46])).
% 0.19/0.48  fof(f171,plain,(
% 0.19/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) | ~l1_pre_topc(sK0) | ~v3_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.19/0.48    inference(subsumption_resolution,[],[f170,f47])).
% 0.19/0.48  fof(f47,plain,(
% 0.19/0.48    ~v2_struct_0(sK1)),
% 0.19/0.48    inference(cnf_transformation,[],[f42])).
% 0.19/0.48  fof(f170,plain,(
% 0.19/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v3_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.19/0.48    inference(subsumption_resolution,[],[f169,f48])).
% 0.19/0.48  fof(f48,plain,(
% 0.19/0.48    v4_tex_2(sK1,sK0)),
% 0.19/0.48    inference(cnf_transformation,[],[f42])).
% 0.19/0.48  fof(f169,plain,(
% 0.19/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) | ~v4_tex_2(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v3_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.19/0.48    inference(subsumption_resolution,[],[f168,f49])).
% 0.19/0.48  fof(f168,plain,(
% 0.19/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) | ~m1_pre_topc(sK1,sK0) | ~v4_tex_2(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v3_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.19/0.48    inference(subsumption_resolution,[],[f167,f50])).
% 0.19/0.48  fof(f50,plain,(
% 0.19/0.48    v1_funct_1(sK2)),
% 0.19/0.48    inference(cnf_transformation,[],[f42])).
% 0.19/0.48  fof(f167,plain,(
% 0.19/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK0) | ~v4_tex_2(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v3_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.19/0.48    inference(subsumption_resolution,[],[f166,f51])).
% 0.19/0.49  fof(f51,plain,(
% 0.19/0.49    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.19/0.49    inference(cnf_transformation,[],[f42])).
% 0.19/0.49  fof(f166,plain,(
% 0.19/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK0) | ~v4_tex_2(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v3_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.19/0.49    inference(subsumption_resolution,[],[f165,f52])).
% 0.19/0.49  fof(f52,plain,(
% 0.19/0.49    v5_pre_topc(sK2,sK0,sK1)),
% 0.19/0.49    inference(cnf_transformation,[],[f42])).
% 0.19/0.49  fof(f165,plain,(
% 0.19/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) | ~v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK0) | ~v4_tex_2(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v3_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.19/0.49    inference(subsumption_resolution,[],[f160,f54])).
% 0.19/0.49  fof(f54,plain,(
% 0.19/0.49    v3_borsuk_1(sK2,sK0,sK1)),
% 0.19/0.49    inference(cnf_transformation,[],[f42])).
% 0.19/0.49  fof(f160,plain,(
% 0.19/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v3_borsuk_1(sK2,sK0,sK1) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) | ~v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK0) | ~v4_tex_2(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v3_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.19/0.49    inference(resolution,[],[f53,f86])).
% 0.19/0.49  fof(f86,plain,(
% 0.19/0.49    ( ! [X4,X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_borsuk_1(X2,X0,X1) | k2_pre_topc(X0,X4) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.19/0.49    inference(equality_resolution,[],[f65])).
% 0.19/0.49  fof(f65,plain,(
% 0.19/0.49    ( ! [X4,X2,X0,X3,X1] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f28])).
% 0.19/0.49  fof(f28,plain,(
% 0.19/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.49    inference(flattening,[],[f27])).
% 0.19/0.49  fof(f27,plain,(
% 0.19/0.49    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : (! [X4] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.19/0.49    inference(ennf_transformation,[],[f17])).
% 0.19/0.49  fof(f17,axiom,(
% 0.19/0.49    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4))))))))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tex_2)).
% 0.19/0.49  fof(f53,plain,(
% 0.19/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.19/0.49    inference(cnf_transformation,[],[f42])).
% 0.19/0.49  fof(f136,plain,(
% 0.19/0.49    ~spl5_5),
% 0.19/0.49    inference(avatar_contradiction_clause,[],[f135])).
% 0.19/0.49  fof(f135,plain,(
% 0.19/0.49    $false | ~spl5_5),
% 0.19/0.49    inference(subsumption_resolution,[],[f134,f90])).
% 0.19/0.49  fof(f90,plain,(
% 0.19/0.49    l1_pre_topc(sK1)),
% 0.19/0.49    inference(subsumption_resolution,[],[f88,f46])).
% 0.19/0.49  fof(f88,plain,(
% 0.19/0.49    l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 0.19/0.49    inference(resolution,[],[f49,f61])).
% 0.19/0.49  fof(f61,plain,(
% 0.19/0.49    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f23])).
% 0.19/0.49  fof(f23,plain,(
% 0.19/0.49    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.19/0.49    inference(ennf_transformation,[],[f10])).
% 0.19/0.49  fof(f10,axiom,(
% 0.19/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.19/0.49  fof(f134,plain,(
% 0.19/0.49    ~l1_pre_topc(sK1) | ~spl5_5),
% 0.19/0.49    inference(resolution,[],[f133,f60])).
% 0.19/0.49  fof(f60,plain,(
% 0.19/0.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f22])).
% 0.19/0.49  fof(f22,plain,(
% 0.19/0.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.19/0.49    inference(ennf_transformation,[],[f9])).
% 0.19/0.49  fof(f9,axiom,(
% 0.19/0.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.19/0.49  fof(f133,plain,(
% 0.19/0.49    ~l1_struct_0(sK1) | ~spl5_5),
% 0.19/0.49    inference(subsumption_resolution,[],[f132,f47])).
% 0.19/0.49  fof(f132,plain,(
% 0.19/0.49    ~l1_struct_0(sK1) | v2_struct_0(sK1) | ~spl5_5),
% 0.19/0.49    inference(resolution,[],[f117,f66])).
% 0.19/0.49  fof(f66,plain,(
% 0.19/0.49    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f30])).
% 0.19/0.49  fof(f30,plain,(
% 0.19/0.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.19/0.49    inference(flattening,[],[f29])).
% 0.19/0.49  fof(f29,plain,(
% 0.19/0.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.19/0.49    inference(ennf_transformation,[],[f11])).
% 0.19/0.49  fof(f11,axiom,(
% 0.19/0.49    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.19/0.49  fof(f117,plain,(
% 0.19/0.49    v1_xboole_0(u1_struct_0(sK1)) | ~spl5_5),
% 0.19/0.49    inference(avatar_component_clause,[],[f115])).
% 0.19/0.49  fof(f131,plain,(
% 0.19/0.49    spl5_5 | spl5_8 | ~spl5_4),
% 0.19/0.49    inference(avatar_split_clause,[],[f126,f107,f128,f115])).
% 0.19/0.49  fof(f126,plain,(
% 0.19/0.49    k6_domain_1(u1_struct_0(sK0),sK4) = k6_domain_1(u1_struct_0(sK1),sK4) | v1_xboole_0(u1_struct_0(sK1)) | ~spl5_4),
% 0.19/0.49    inference(forward_demodulation,[],[f113,f109])).
% 0.19/0.49  fof(f113,plain,(
% 0.19/0.49    k6_domain_1(u1_struct_0(sK1),sK4) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) | v1_xboole_0(u1_struct_0(sK1))),
% 0.19/0.49    inference(resolution,[],[f83,f84])).
% 0.19/0.49  fof(f84,plain,(
% 0.19/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) | v1_xboole_0(X0)) )),
% 0.19/0.49    inference(definition_unfolding,[],[f68,f81])).
% 0.19/0.49  fof(f81,plain,(
% 0.19/0.49    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.19/0.49    inference(definition_unfolding,[],[f59,f80])).
% 0.19/0.49  fof(f80,plain,(
% 0.19/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.19/0.49    inference(definition_unfolding,[],[f67,f79])).
% 0.19/0.49  fof(f79,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.19/0.49    inference(definition_unfolding,[],[f69,f78])).
% 0.19/0.49  fof(f78,plain,(
% 0.19/0.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.19/0.49    inference(definition_unfolding,[],[f72,f77])).
% 0.19/0.49  fof(f77,plain,(
% 0.19/0.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.19/0.49    inference(definition_unfolding,[],[f73,f76])).
% 0.19/0.49  fof(f76,plain,(
% 0.19/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.19/0.49    inference(definition_unfolding,[],[f74,f75])).
% 0.19/0.49  fof(f75,plain,(
% 0.19/0.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f7])).
% 0.19/0.49  fof(f7,axiom,(
% 0.19/0.49    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.19/0.49  fof(f74,plain,(
% 0.19/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f6])).
% 0.19/0.49  fof(f6,axiom,(
% 0.19/0.49    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.19/0.49  fof(f73,plain,(
% 0.19/0.49    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f5])).
% 0.19/0.49  fof(f5,axiom,(
% 0.19/0.49    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.19/0.49  fof(f72,plain,(
% 0.19/0.49    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f4])).
% 0.19/0.49  fof(f4,axiom,(
% 0.19/0.49    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.19/0.49  fof(f69,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f3])).
% 0.19/0.49  fof(f3,axiom,(
% 0.19/0.49    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.19/0.49  fof(f67,plain,(
% 0.19/0.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f2])).
% 0.19/0.49  fof(f2,axiom,(
% 0.19/0.49    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.19/0.49  fof(f59,plain,(
% 0.19/0.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f1])).
% 0.19/0.49  fof(f1,axiom,(
% 0.19/0.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.19/0.49  fof(f68,plain,(
% 0.19/0.49    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f32])).
% 0.19/0.49  fof(f32,plain,(
% 0.19/0.49    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.19/0.49    inference(flattening,[],[f31])).
% 0.19/0.49  fof(f31,plain,(
% 0.19/0.49    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.19/0.49    inference(ennf_transformation,[],[f14])).
% 0.19/0.49  fof(f14,axiom,(
% 0.19/0.49    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.19/0.49  fof(f125,plain,(
% 0.19/0.49    spl5_5 | spl5_7),
% 0.19/0.49    inference(avatar_split_clause,[],[f112,f123,f115])).
% 0.19/0.49  fof(f112,plain,(
% 0.19/0.49    ( ! [X1] : (m1_subset_1(k7_domain_1(u1_struct_0(sK1),X1,sK4),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X1,u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK1))) )),
% 0.19/0.49    inference(resolution,[],[f83,f70])).
% 0.19/0.49  fof(f70,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f34])).
% 0.19/0.49  fof(f34,plain,(
% 0.19/0.49    ! [X0,X1,X2] : (m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.19/0.49    inference(flattening,[],[f33])).
% 0.19/0.49  fof(f33,plain,(
% 0.19/0.49    ! [X0,X1,X2] : (m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.19/0.49    inference(ennf_transformation,[],[f13])).
% 0.19/0.49  fof(f13,axiom,(
% 0.19/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,X0) & m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_domain_1)).
% 0.19/0.49  fof(f121,plain,(
% 0.19/0.49    spl5_5 | spl5_6),
% 0.19/0.49    inference(avatar_split_clause,[],[f111,f119,f115])).
% 0.19/0.49  fof(f111,plain,(
% 0.19/0.49    ( ! [X0] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK4) = k7_domain_1(u1_struct_0(sK1),X0,sK4) | ~m1_subset_1(X0,u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK1))) )),
% 0.19/0.49    inference(resolution,[],[f83,f85])).
% 0.19/0.49  fof(f85,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | k7_domain_1(X0,X1,X2) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.19/0.49    inference(definition_unfolding,[],[f71,f80])).
% 0.19/0.49  fof(f71,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f36])).
% 0.19/0.49  fof(f36,plain,(
% 0.19/0.49    ! [X0,X1,X2] : (k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.19/0.49    inference(flattening,[],[f35])).
% 0.19/0.49  fof(f35,plain,(
% 0.19/0.49    ! [X0,X1,X2] : (k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2) | (~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.19/0.49    inference(ennf_transformation,[],[f15])).
% 0.19/0.49  fof(f15,axiom,(
% 0.19/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,X0) & m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_domain_1)).
% 0.19/0.49  fof(f110,plain,(
% 0.19/0.49    spl5_1 | spl5_4),
% 0.19/0.49    inference(avatar_split_clause,[],[f93,f107,f95])).
% 0.19/0.49  fof(f93,plain,(
% 0.19/0.49    k6_domain_1(u1_struct_0(sK0),sK4) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) | v1_xboole_0(u1_struct_0(sK0))),
% 0.19/0.49    inference(resolution,[],[f56,f84])).
% 0.19/0.49  fof(f105,plain,(
% 0.19/0.49    spl5_1 | spl5_3),
% 0.19/0.49    inference(avatar_split_clause,[],[f92,f103,f95])).
% 0.19/0.49  fof(f92,plain,(
% 0.19/0.49    ( ! [X1] : (m1_subset_1(k7_domain_1(u1_struct_0(sK0),X1,sK4),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))) )),
% 0.19/0.49    inference(resolution,[],[f56,f70])).
% 0.19/0.49  fof(f101,plain,(
% 0.19/0.49    spl5_1 | spl5_2),
% 0.19/0.49    inference(avatar_split_clause,[],[f91,f99,f95])).
% 0.19/0.49  fof(f91,plain,(
% 0.19/0.49    ( ! [X0] : (k7_domain_1(u1_struct_0(sK0),X0,sK4) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK4) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))) )),
% 0.19/0.49    inference(resolution,[],[f56,f85])).
% 0.19/0.49  % SZS output end Proof for theBenchmark
% 0.19/0.49  % (21308)------------------------------
% 0.19/0.49  % (21308)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (21308)Termination reason: Refutation
% 0.19/0.49  
% 0.19/0.49  % (21308)Memory used [KB]: 10874
% 0.19/0.49  % (21308)Time elapsed: 0.066 s
% 0.19/0.49  % (21308)------------------------------
% 0.19/0.49  % (21308)------------------------------
% 0.19/0.49  % (21299)Success in time 0.137 s
%------------------------------------------------------------------------------
