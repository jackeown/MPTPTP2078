%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:29 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 595 expanded)
%              Number of leaves         :   31 ( 267 expanded)
%              Depth                    :   22
%              Number of atoms          :  646 (6357 expanded)
%              Number of equality atoms :  104 (1172 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f273,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f105,f109,f114,f125,f129,f135,f140,f257,f272])).

fof(f272,plain,
    ( ~ spl5_1
    | spl5_5 ),
    inference(avatar_contradiction_clause,[],[f271])).

fof(f271,plain,
    ( $false
    | ~ spl5_1
    | spl5_5 ),
    inference(subsumption_resolution,[],[f101,f262])).

fof(f262,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl5_5 ),
    inference(subsumption_resolution,[],[f186,f120])).

fof(f120,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl5_5
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f186,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f142,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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

fof(f142,plain,(
    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f93,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f93,plain,(
    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f91,f49])).

fof(f49,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f23,f44,f43,f42,f41,f40])).

fof(f40,plain,
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

fof(f41,plain,
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

fof(f42,plain,
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

fof(f43,plain,
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

fof(f44,plain,
    ( ? [X4] :
        ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3))
        & sK3 = X4
        & m1_subset_1(X4,u1_struct_0(sK0)) )
   => ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4))
      & sK3 = sK4
      & m1_subset_1(sK4,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
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

fof(f91,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f52,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).

fof(f52,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f101,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl5_1
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f257,plain,
    ( ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(avatar_contradiction_clause,[],[f256])).

fof(f256,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f255,f141])).

fof(f141,plain,
    ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK0),sK4))
    | ~ spl5_8 ),
    inference(backward_demodulation,[],[f86,f134])).

fof(f134,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK4) = k6_domain_1(u1_struct_0(sK1),sK4)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl5_8
  <=> k6_domain_1(u1_struct_0(sK0),sK4) = k6_domain_1(u1_struct_0(sK1),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f86,plain,(
    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK4)) ),
    inference(definition_unfolding,[],[f61,f60])).

fof(f60,plain,(
    sK3 = sK4 ),
    inference(cnf_transformation,[],[f45])).

fof(f61,plain,(
    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) ),
    inference(cnf_transformation,[],[f45])).

fof(f255,plain,
    ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK0),sK4))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f254,f238])).

fof(f238,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK4),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f237,f59])).

fof(f59,plain,(
    m1_subset_1(sK4,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f45])).

fof(f237,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK4),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(superposition,[],[f108,f235])).

fof(f235,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK4) = k7_domain_1(u1_struct_0(sK0),sK4,sK4)
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f234,f113])).

fof(f113,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK4) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl5_4
  <=> k6_domain_1(u1_struct_0(sK0),sK4) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f234,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k7_domain_1(u1_struct_0(sK0),sK4,sK4)
    | ~ spl5_2 ),
    inference(resolution,[],[f104,f59])).

fof(f104,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k7_domain_1(u1_struct_0(sK0),X0,sK4) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK4) )
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl5_2
  <=> ! [X0] :
        ( k7_domain_1(u1_struct_0(sK0),X0,sK4) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK4)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f108,plain,
    ( ! [X1] :
        ( m1_subset_1(k7_domain_1(u1_struct_0(sK0),X1,sK4),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl5_3
  <=> ! [X1] :
        ( m1_subset_1(k7_domain_1(u1_struct_0(sK0),X1,sK4),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f254,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK4),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK0),sK4))
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(resolution,[],[f158,f247])).

fof(f247,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f246,f87])).

fof(f87,plain,(
    m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(definition_unfolding,[],[f58,f60])).

fof(f58,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f45])).

fof(f246,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(superposition,[],[f128,f245])).

fof(f245,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK4) = k7_domain_1(u1_struct_0(sK1),sK4,sK4)
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f244,f113])).

fof(f244,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k7_domain_1(u1_struct_0(sK1),sK4,sK4)
    | ~ spl5_6 ),
    inference(resolution,[],[f124,f87])).

fof(f124,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK4) = k7_domain_1(u1_struct_0(sK1),X0,sK4) )
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl5_6
  <=> ! [X0] :
        ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK4) = k7_domain_1(u1_struct_0(sK1),X0,sK4)
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f128,plain,
    ( ! [X1] :
        ( m1_subset_1(k7_domain_1(u1_struct_0(sK1),X1,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X1,u1_struct_0(sK1)) )
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl5_7
  <=> ! [X1] :
        ( m1_subset_1(k7_domain_1(u1_struct_0(sK1),X1,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X1,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f158,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) ) ),
    inference(subsumption_resolution,[],[f157,f46])).

fof(f46,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f157,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f156,f47])).

fof(f47,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f156,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f155,f48])).

fof(f48,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f155,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)
      | ~ v3_tdlat_3(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f154,f49])).

fof(f154,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)
      | ~ l1_pre_topc(sK0)
      | ~ v3_tdlat_3(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f153,f50])).

fof(f50,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f153,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v3_tdlat_3(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f152,f51])).

fof(f51,plain,(
    v4_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f152,plain,(
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
    inference(subsumption_resolution,[],[f151,f52])).

fof(f151,plain,(
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
    inference(subsumption_resolution,[],[f150,f53])).

fof(f53,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f150,plain,(
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
    inference(subsumption_resolution,[],[f149,f54])).

fof(f54,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f45])).

fof(f149,plain,(
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
    inference(subsumption_resolution,[],[f148,f55])).

fof(f55,plain,(
    v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f148,plain,(
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
    inference(subsumption_resolution,[],[f143,f57])).

fof(f57,plain,(
    v3_borsuk_1(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f143,plain,(
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
    inference(resolution,[],[f56,f90])).

fof(f90,plain,(
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
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
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
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
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

fof(f56,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f45])).

fof(f140,plain,(
    ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f139])).

fof(f139,plain,
    ( $false
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f138,f94])).

fof(f94,plain,(
    l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f92,f49])).

fof(f92,plain,
    ( l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f52,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f138,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ spl5_5 ),
    inference(resolution,[],[f137,f63])).

fof(f63,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f137,plain,
    ( ~ l1_struct_0(sK1)
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f136,f50])).

fof(f136,plain,
    ( ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl5_5 ),
    inference(resolution,[],[f121,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f121,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f119])).

fof(f135,plain,
    ( spl5_5
    | spl5_8
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f130,f111,f132,f119])).

fof(f130,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK4) = k6_domain_1(u1_struct_0(sK1),sK4)
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f117,f113])).

fof(f117,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK4) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(resolution,[],[f87,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f71,f85])).

fof(f85,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f62,f84])).

fof(f84,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f70,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f73,f82])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f76,f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f77,f80])).

fof(f80,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f78,f79])).

fof(f79,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f78,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f77,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f76,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f73,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f70,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f62,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f71,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f129,plain,
    ( spl5_5
    | spl5_7 ),
    inference(avatar_split_clause,[],[f116,f127,f119])).

fof(f116,plain,(
    ! [X1] :
      ( m1_subset_1(k7_domain_1(u1_struct_0(sK1),X1,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | v1_xboole_0(u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f87,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_domain_1)).

fof(f125,plain,
    ( spl5_5
    | spl5_6 ),
    inference(avatar_split_clause,[],[f115,f123,f119])).

fof(f115,plain,(
    ! [X0] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK4) = k7_domain_1(u1_struct_0(sK1),X0,sK4)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | v1_xboole_0(u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f87,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | k7_domain_1(X0,X1,X2) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f75,f84])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_domain_1)).

fof(f114,plain,
    ( spl5_1
    | spl5_4 ),
    inference(avatar_split_clause,[],[f97,f111,f99])).

fof(f97,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK4) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f59,f88])).

fof(f109,plain,
    ( spl5_1
    | spl5_3 ),
    inference(avatar_split_clause,[],[f96,f107,f99])).

fof(f96,plain,(
    ! [X1] :
      ( m1_subset_1(k7_domain_1(u1_struct_0(sK0),X1,sK4),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | v1_xboole_0(u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f59,f74])).

fof(f105,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f95,f103,f99])).

fof(f95,plain,(
    ! [X0] :
      ( k7_domain_1(u1_struct_0(sK0),X0,sK4) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK4)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v1_xboole_0(u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f59,f89])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:42:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (29810)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.48  % (29793)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (29807)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (29800)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (29797)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (29801)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (29796)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (29805)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (29795)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (29809)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.52  % (29796)Refutation not found, incomplete strategy% (29796)------------------------------
% 0.21/0.52  % (29796)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (29796)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (29796)Memory used [KB]: 6268
% 0.21/0.52  % (29796)Time elapsed: 0.107 s
% 0.21/0.52  % (29796)------------------------------
% 0.21/0.52  % (29796)------------------------------
% 0.21/0.52  % (29799)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (29815)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (29816)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.52  % (29817)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (29794)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (29809)Refutation not found, incomplete strategy% (29809)------------------------------
% 0.21/0.53  % (29809)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (29809)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (29809)Memory used [KB]: 10746
% 0.21/0.53  % (29809)Time elapsed: 0.119 s
% 0.21/0.53  % (29809)------------------------------
% 0.21/0.53  % (29809)------------------------------
% 0.21/0.53  % (29800)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % (29813)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (29814)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (29812)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (29802)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (29811)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (29798)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (29807)Refutation not found, incomplete strategy% (29807)------------------------------
% 0.21/0.53  % (29807)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (29807)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (29807)Memory used [KB]: 6268
% 0.21/0.53  % (29807)Time elapsed: 0.123 s
% 0.21/0.53  % (29807)------------------------------
% 0.21/0.53  % (29807)------------------------------
% 0.21/0.53  % (29802)Refutation not found, incomplete strategy% (29802)------------------------------
% 0.21/0.53  % (29802)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (29802)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (29802)Memory used [KB]: 10746
% 0.21/0.53  % (29802)Time elapsed: 0.093 s
% 0.21/0.53  % (29802)------------------------------
% 0.21/0.53  % (29802)------------------------------
% 0.21/0.53  % (29821)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (29820)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (29818)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (29804)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (29806)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (29819)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (29808)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (29792)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (29803)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f273,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f105,f109,f114,f125,f129,f135,f140,f257,f272])).
% 0.21/0.54  fof(f272,plain,(
% 0.21/0.54    ~spl5_1 | spl5_5),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f271])).
% 0.21/0.54  fof(f271,plain,(
% 0.21/0.54    $false | (~spl5_1 | spl5_5)),
% 0.21/0.54    inference(subsumption_resolution,[],[f101,f262])).
% 0.21/0.54  fof(f262,plain,(
% 0.21/0.54    ~v1_xboole_0(u1_struct_0(sK0)) | spl5_5),
% 0.21/0.54    inference(subsumption_resolution,[],[f186,f120])).
% 0.21/0.54  fof(f120,plain,(
% 0.21/0.54    ~v1_xboole_0(u1_struct_0(sK1)) | spl5_5),
% 0.21/0.54    inference(avatar_component_clause,[],[f119])).
% 0.21/0.54  fof(f119,plain,(
% 0.21/0.54    spl5_5 <=> v1_xboole_0(u1_struct_0(sK1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.54  fof(f186,plain,(
% 0.21/0.54    v1_xboole_0(u1_struct_0(sK1)) | ~v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.54    inference(resolution,[],[f142,f67])).
% 0.21/0.54  fof(f67,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.21/0.54  fof(f142,plain,(
% 0.21/0.54    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.54    inference(resolution,[],[f93,f72])).
% 0.21/0.54  fof(f72,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f35])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.21/0.54    inference(unused_predicate_definition_removal,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.54  fof(f93,plain,(
% 0.21/0.54    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.21/0.54    inference(subsumption_resolution,[],[f91,f49])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    l1_pre_topc(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f45])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ((((k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) & sK3 = sK4 & m1_subset_1(sK4,u1_struct_0(sK0))) & m1_subset_1(sK3,u1_struct_0(sK1))) & v3_borsuk_1(sK2,sK0,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v5_pre_topc(sK2,sK0,sK1) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & m1_pre_topc(sK1,sK0) & v4_tex_2(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v3_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f23,f44,f43,f42,f41,f40])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(sK0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,sK0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v5_pre_topc(X2,sK0,X1) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,sK0) & v4_tex_2(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v3_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(sK0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,sK0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v5_pre_topc(X2,sK0,X1) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,sK0) & v4_tex_2(X1,sK0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k6_domain_1(u1_struct_0(sK1),X3)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(sK0))) & m1_subset_1(X3,u1_struct_0(sK1))) & v3_borsuk_1(X2,sK0,sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v5_pre_topc(X2,sK0,sK1) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & m1_pre_topc(sK1,sK0) & v4_tex_2(sK1,sK0) & ~v2_struct_0(sK1))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    ? [X2] : (? [X3] : (? [X4] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k6_domain_1(u1_struct_0(sK1),X3)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(sK0))) & m1_subset_1(X3,u1_struct_0(sK1))) & v3_borsuk_1(X2,sK0,sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v5_pre_topc(X2,sK0,sK1) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),X3)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(sK0))) & m1_subset_1(X3,u1_struct_0(sK1))) & v3_borsuk_1(sK2,sK0,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v5_pre_topc(sK2,sK0,sK1) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    ? [X3] : (? [X4] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),X3)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(sK0))) & m1_subset_1(X3,u1_struct_0(sK1))) => (? [X4] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) & sK3 = X4 & m1_subset_1(X4,u1_struct_0(sK0))) & m1_subset_1(sK3,u1_struct_0(sK1)))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ? [X4] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) & sK3 = X4 & m1_subset_1(X4,u1_struct_0(sK0))) => (k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) & sK3 = sK4 & m1_subset_1(sK4,u1_struct_0(sK0)))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (? [X4] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f20])).
% 0.21/0.54  fof(f20,negated_conjecture,(
% 0.21/0.54    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)))))))))),
% 0.21/0.54    inference(negated_conjecture,[],[f19])).
% 0.21/0.54  fof(f19,conjecture,(
% 0.21/0.54    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)))))))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tex_2)).
% 0.21/0.54  fof(f91,plain,(
% 0.21/0.54    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0)) | ~l1_pre_topc(sK0)),
% 0.21/0.54    inference(resolution,[],[f52,f65])).
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~l1_pre_topc(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f17])).
% 0.21/0.54  fof(f17,axiom,(
% 0.21/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    m1_pre_topc(sK1,sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f45])).
% 0.21/0.54  fof(f101,plain,(
% 0.21/0.54    v1_xboole_0(u1_struct_0(sK0)) | ~spl5_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f99])).
% 0.21/0.54  fof(f99,plain,(
% 0.21/0.54    spl5_1 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.54  fof(f257,plain,(
% 0.21/0.54    ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_6 | ~spl5_7 | ~spl5_8),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f256])).
% 0.21/0.54  fof(f256,plain,(
% 0.21/0.54    $false | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_6 | ~spl5_7 | ~spl5_8)),
% 0.21/0.54    inference(subsumption_resolution,[],[f255,f141])).
% 0.21/0.54  fof(f141,plain,(
% 0.21/0.54    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK0),sK4)) | ~spl5_8),
% 0.21/0.54    inference(backward_demodulation,[],[f86,f134])).
% 0.21/0.54  fof(f134,plain,(
% 0.21/0.54    k6_domain_1(u1_struct_0(sK0),sK4) = k6_domain_1(u1_struct_0(sK1),sK4) | ~spl5_8),
% 0.21/0.54    inference(avatar_component_clause,[],[f132])).
% 0.21/0.54  fof(f132,plain,(
% 0.21/0.54    spl5_8 <=> k6_domain_1(u1_struct_0(sK0),sK4) = k6_domain_1(u1_struct_0(sK1),sK4)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.54  fof(f86,plain,(
% 0.21/0.54    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK4))),
% 0.21/0.54    inference(definition_unfolding,[],[f61,f60])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    sK3 = sK4),
% 0.21/0.54    inference(cnf_transformation,[],[f45])).
% 0.21/0.54  fof(f61,plain,(
% 0.21/0.54    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4))),
% 0.21/0.54    inference(cnf_transformation,[],[f45])).
% 0.21/0.54  fof(f255,plain,(
% 0.21/0.54    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK0),sK4)) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_6 | ~spl5_7)),
% 0.21/0.54    inference(subsumption_resolution,[],[f254,f238])).
% 0.21/0.54  fof(f238,plain,(
% 0.21/0.54    m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK4),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_2 | ~spl5_3 | ~spl5_4)),
% 0.21/0.54    inference(subsumption_resolution,[],[f237,f59])).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    m1_subset_1(sK4,u1_struct_0(sK0))),
% 0.21/0.54    inference(cnf_transformation,[],[f45])).
% 0.21/0.54  fof(f237,plain,(
% 0.21/0.54    m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK4),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK4,u1_struct_0(sK0)) | (~spl5_2 | ~spl5_3 | ~spl5_4)),
% 0.21/0.54    inference(superposition,[],[f108,f235])).
% 0.21/0.54  fof(f235,plain,(
% 0.21/0.54    k6_domain_1(u1_struct_0(sK0),sK4) = k7_domain_1(u1_struct_0(sK0),sK4,sK4) | (~spl5_2 | ~spl5_4)),
% 0.21/0.54    inference(forward_demodulation,[],[f234,f113])).
% 0.21/0.54  fof(f113,plain,(
% 0.21/0.54    k6_domain_1(u1_struct_0(sK0),sK4) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) | ~spl5_4),
% 0.21/0.54    inference(avatar_component_clause,[],[f111])).
% 0.21/0.54  fof(f111,plain,(
% 0.21/0.54    spl5_4 <=> k6_domain_1(u1_struct_0(sK0),sK4) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.54  fof(f234,plain,(
% 0.21/0.54    k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k7_domain_1(u1_struct_0(sK0),sK4,sK4) | ~spl5_2),
% 0.21/0.54    inference(resolution,[],[f104,f59])).
% 0.21/0.54  fof(f104,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k7_domain_1(u1_struct_0(sK0),X0,sK4) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK4)) ) | ~spl5_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f103])).
% 0.21/0.54  fof(f103,plain,(
% 0.21/0.54    spl5_2 <=> ! [X0] : (k7_domain_1(u1_struct_0(sK0),X0,sK4) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK4) | ~m1_subset_1(X0,u1_struct_0(sK0)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.54  fof(f108,plain,(
% 0.21/0.54    ( ! [X1] : (m1_subset_1(k7_domain_1(u1_struct_0(sK0),X1,sK4),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl5_3),
% 0.21/0.54    inference(avatar_component_clause,[],[f107])).
% 0.21/0.54  fof(f107,plain,(
% 0.21/0.54    spl5_3 <=> ! [X1] : (m1_subset_1(k7_domain_1(u1_struct_0(sK0),X1,sK4),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.54  fof(f254,plain,(
% 0.21/0.54    ~m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK4),k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK0),sK4)) | (~spl5_4 | ~spl5_6 | ~spl5_7)),
% 0.21/0.54    inference(resolution,[],[f158,f247])).
% 0.21/0.54  fof(f247,plain,(
% 0.21/0.54    m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK4),k1_zfmisc_1(u1_struct_0(sK1))) | (~spl5_4 | ~spl5_6 | ~spl5_7)),
% 0.21/0.54    inference(subsumption_resolution,[],[f246,f87])).
% 0.21/0.54  fof(f87,plain,(
% 0.21/0.54    m1_subset_1(sK4,u1_struct_0(sK1))),
% 0.21/0.54    inference(definition_unfolding,[],[f58,f60])).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    m1_subset_1(sK3,u1_struct_0(sK1))),
% 0.21/0.54    inference(cnf_transformation,[],[f45])).
% 0.21/0.54  fof(f246,plain,(
% 0.21/0.54    m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK4),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | (~spl5_4 | ~spl5_6 | ~spl5_7)),
% 0.21/0.54    inference(superposition,[],[f128,f245])).
% 0.21/0.54  fof(f245,plain,(
% 0.21/0.54    k6_domain_1(u1_struct_0(sK0),sK4) = k7_domain_1(u1_struct_0(sK1),sK4,sK4) | (~spl5_4 | ~spl5_6)),
% 0.21/0.54    inference(forward_demodulation,[],[f244,f113])).
% 0.21/0.54  fof(f244,plain,(
% 0.21/0.54    k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k7_domain_1(u1_struct_0(sK1),sK4,sK4) | ~spl5_6),
% 0.21/0.54    inference(resolution,[],[f124,f87])).
% 0.21/0.54  fof(f124,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK4) = k7_domain_1(u1_struct_0(sK1),X0,sK4)) ) | ~spl5_6),
% 0.21/0.54    inference(avatar_component_clause,[],[f123])).
% 0.21/0.54  fof(f123,plain,(
% 0.21/0.54    spl5_6 <=> ! [X0] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK4) = k7_domain_1(u1_struct_0(sK1),X0,sK4) | ~m1_subset_1(X0,u1_struct_0(sK1)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.54  fof(f128,plain,(
% 0.21/0.54    ( ! [X1] : (m1_subset_1(k7_domain_1(u1_struct_0(sK1),X1,sK4),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X1,u1_struct_0(sK1))) ) | ~spl5_7),
% 0.21/0.54    inference(avatar_component_clause,[],[f127])).
% 0.21/0.54  fof(f127,plain,(
% 0.21/0.54    spl5_7 <=> ! [X1] : (m1_subset_1(k7_domain_1(u1_struct_0(sK1),X1,sK4),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X1,u1_struct_0(sK1)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.54  fof(f158,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f157,f46])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    ~v2_struct_0(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f45])).
% 0.21/0.54  fof(f157,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f156,f47])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    v2_pre_topc(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f45])).
% 0.21/0.54  fof(f156,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f155,f48])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    v3_tdlat_3(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f45])).
% 0.21/0.54  fof(f155,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) | ~v3_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f154,f49])).
% 0.21/0.54  fof(f154,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) | ~l1_pre_topc(sK0) | ~v3_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f153,f50])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    ~v2_struct_0(sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f45])).
% 0.21/0.54  fof(f153,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v3_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f152,f51])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    v4_tex_2(sK1,sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f45])).
% 0.21/0.54  fof(f152,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) | ~v4_tex_2(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v3_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f151,f52])).
% 0.21/0.54  fof(f151,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) | ~m1_pre_topc(sK1,sK0) | ~v4_tex_2(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v3_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f150,f53])).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    v1_funct_1(sK2)),
% 0.21/0.54    inference(cnf_transformation,[],[f45])).
% 0.21/0.54  fof(f150,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK0) | ~v4_tex_2(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v3_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f149,f54])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.54    inference(cnf_transformation,[],[f45])).
% 0.21/0.54  fof(f149,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK0) | ~v4_tex_2(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v3_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f148,f55])).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    v5_pre_topc(sK2,sK0,sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f45])).
% 0.21/0.54  fof(f148,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) | ~v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK0) | ~v4_tex_2(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v3_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f143,f57])).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    v3_borsuk_1(sK2,sK0,sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f45])).
% 0.21/0.54  fof(f143,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v3_borsuk_1(sK2,sK0,sK1) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) | ~v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK0) | ~v4_tex_2(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v3_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(resolution,[],[f56,f90])).
% 0.21/0.54  fof(f90,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_borsuk_1(X2,X0,X1) | k2_pre_topc(X0,X4) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(equality_resolution,[],[f68])).
% 0.21/0.54  fof(f68,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X3,X1] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : (! [X4] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f18])).
% 0.21/0.54  fof(f18,axiom,(
% 0.21/0.54    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4))))))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tex_2)).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.54    inference(cnf_transformation,[],[f45])).
% 0.21/0.54  fof(f140,plain,(
% 0.21/0.54    ~spl5_5),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f139])).
% 0.21/0.54  fof(f139,plain,(
% 0.21/0.54    $false | ~spl5_5),
% 0.21/0.54    inference(subsumption_resolution,[],[f138,f94])).
% 0.21/0.54  fof(f94,plain,(
% 0.21/0.54    l1_pre_topc(sK1)),
% 0.21/0.54    inference(subsumption_resolution,[],[f92,f49])).
% 0.21/0.54  fof(f92,plain,(
% 0.21/0.54    l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 0.21/0.54    inference(resolution,[],[f52,f64])).
% 0.21/0.54  fof(f64,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,axiom,(
% 0.21/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.54  fof(f138,plain,(
% 0.21/0.54    ~l1_pre_topc(sK1) | ~spl5_5),
% 0.21/0.54    inference(resolution,[],[f137,f63])).
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,axiom,(
% 0.21/0.54    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.54  fof(f137,plain,(
% 0.21/0.54    ~l1_struct_0(sK1) | ~spl5_5),
% 0.21/0.54    inference(subsumption_resolution,[],[f136,f50])).
% 0.21/0.54  fof(f136,plain,(
% 0.21/0.54    ~l1_struct_0(sK1) | v2_struct_0(sK1) | ~spl5_5),
% 0.21/0.54    inference(resolution,[],[f121,f69])).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,axiom,(
% 0.21/0.54    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.54  fof(f121,plain,(
% 0.21/0.54    v1_xboole_0(u1_struct_0(sK1)) | ~spl5_5),
% 0.21/0.54    inference(avatar_component_clause,[],[f119])).
% 0.21/0.54  fof(f135,plain,(
% 0.21/0.54    spl5_5 | spl5_8 | ~spl5_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f130,f111,f132,f119])).
% 0.21/0.54  fof(f130,plain,(
% 0.21/0.54    k6_domain_1(u1_struct_0(sK0),sK4) = k6_domain_1(u1_struct_0(sK1),sK4) | v1_xboole_0(u1_struct_0(sK1)) | ~spl5_4),
% 0.21/0.54    inference(forward_demodulation,[],[f117,f113])).
% 0.21/0.54  fof(f117,plain,(
% 0.21/0.54    k6_domain_1(u1_struct_0(sK1),sK4) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) | v1_xboole_0(u1_struct_0(sK1))),
% 0.21/0.54    inference(resolution,[],[f87,f88])).
% 0.21/0.54  fof(f88,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) | v1_xboole_0(X0)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f71,f85])).
% 0.21/0.54  fof(f85,plain,(
% 0.21/0.54    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f62,f84])).
% 0.21/0.54  fof(f84,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f70,f83])).
% 0.21/0.54  fof(f83,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f73,f82])).
% 0.21/0.54  fof(f82,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f76,f81])).
% 0.21/0.54  fof(f81,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f77,f80])).
% 0.21/0.54  fof(f80,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f78,f79])).
% 0.21/0.54  fof(f79,plain,(
% 0.21/0.54    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.21/0.54  fof(f78,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.21/0.54  fof(f77,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.21/0.54  fof(f76,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.54  fof(f73,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.54  fof(f70,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.54  fof(f71,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f34])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.54    inference(flattening,[],[f33])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,axiom,(
% 0.21/0.54    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.21/0.54  fof(f129,plain,(
% 0.21/0.54    spl5_5 | spl5_7),
% 0.21/0.54    inference(avatar_split_clause,[],[f116,f127,f119])).
% 0.21/0.54  fof(f116,plain,(
% 0.21/0.54    ( ! [X1] : (m1_subset_1(k7_domain_1(u1_struct_0(sK1),X1,sK4),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X1,u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK1))) )),
% 0.21/0.54    inference(resolution,[],[f87,f74])).
% 0.21/0.54  fof(f74,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.54    inference(flattening,[],[f36])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,X0) & m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_domain_1)).
% 0.21/0.54  fof(f125,plain,(
% 0.21/0.54    spl5_5 | spl5_6),
% 0.21/0.54    inference(avatar_split_clause,[],[f115,f123,f119])).
% 0.21/0.54  fof(f115,plain,(
% 0.21/0.54    ( ! [X0] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK4) = k7_domain_1(u1_struct_0(sK1),X0,sK4) | ~m1_subset_1(X0,u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK1))) )),
% 0.21/0.54    inference(resolution,[],[f87,f89])).
% 0.21/0.54  fof(f89,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | k7_domain_1(X0,X1,X2) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f75,f84])).
% 0.21/0.54  fof(f75,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f39])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.54    inference(flattening,[],[f38])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2) | (~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f16])).
% 0.21/0.54  fof(f16,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,X0) & m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_domain_1)).
% 0.21/0.54  fof(f114,plain,(
% 0.21/0.54    spl5_1 | spl5_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f97,f111,f99])).
% 0.21/0.54  fof(f97,plain,(
% 0.21/0.54    k6_domain_1(u1_struct_0(sK0),sK4) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) | v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.54    inference(resolution,[],[f59,f88])).
% 0.21/0.54  fof(f109,plain,(
% 0.21/0.54    spl5_1 | spl5_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f96,f107,f99])).
% 0.21/0.54  fof(f96,plain,(
% 0.21/0.54    ( ! [X1] : (m1_subset_1(k7_domain_1(u1_struct_0(sK0),X1,sK4),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))) )),
% 0.21/0.54    inference(resolution,[],[f59,f74])).
% 0.21/0.54  fof(f105,plain,(
% 0.21/0.54    spl5_1 | spl5_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f95,f103,f99])).
% 0.21/0.54  fof(f95,plain,(
% 0.21/0.54    ( ! [X0] : (k7_domain_1(u1_struct_0(sK0),X0,sK4) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK4) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))) )),
% 0.21/0.54    inference(resolution,[],[f59,f89])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (29800)------------------------------
% 0.21/0.54  % (29800)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (29800)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (29800)Memory used [KB]: 10874
% 0.21/0.54  % (29800)Time elapsed: 0.118 s
% 0.21/0.54  % (29800)------------------------------
% 0.21/0.54  % (29800)------------------------------
% 0.21/0.54  % (29791)Success in time 0.177 s
%------------------------------------------------------------------------------
