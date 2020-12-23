%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:27 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  184 (24540 expanded)
%              Number of leaves         :   29 (5073 expanded)
%              Depth                    :   22
%              Number of atoms          :  693 (253199 expanded)
%              Number of equality atoms :   61 (28412 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f654,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f198,f330,f392,f497,f610,f614,f618,f622,f626,f630,f634,f653])).

fof(f653,plain,(
    ~ spl6_38 ),
    inference(avatar_contradiction_clause,[],[f650])).

fof(f650,plain,
    ( $false
    | ~ spl6_38 ),
    inference(unit_resulting_resolution,[],[f255,f298,f299,f609])).

fof(f609,plain,
    ( ! [X0] :
        ( k2_pre_topc(sK0,X0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl6_38 ),
    inference(avatar_component_clause,[],[f608])).

fof(f608,plain,
    ( spl6_38
  <=> ! [X0] :
        ( k2_pre_topc(sK0,X0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f299,plain,(
    k2_pre_topc(sK0,k2_tarski(sK4,sK4)) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_tarski(sK4,sK4)) ),
    inference(backward_demodulation,[],[f291,f296])).

fof(f296,plain,(
    k2_tarski(sK4,sK4) = k6_domain_1(k2_struct_0(sK1),sK4) ),
    inference(unit_resulting_resolution,[],[f132,f268,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k2_tarski(X1,X1) ) ),
    inference(definition_unfolding,[],[f76,f86])).

fof(f86,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f76,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f268,plain,(
    m1_subset_1(sK4,k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f93,f267])).

fof(f267,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(backward_demodulation,[],[f266,f265])).

fof(f265,plain,(
    k2_struct_0(sK1) = k2_pre_topc(sK1,sK5(sK1,u1_struct_0(sK1))) ),
    inference(unit_resulting_resolution,[],[f121,f178,f263,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

fof(f263,plain,(
    v1_tops_1(sK5(sK1,u1_struct_0(sK1)),sK1) ),
    inference(unit_resulting_resolution,[],[f131,f120,f63,f121,f180,f178,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tex_2(X1,X0)
      | v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
           => v1_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tex_2)).

fof(f180,plain,(
    v3_tex_2(sK5(sK1,u1_struct_0(sK1)),sK1) ),
    inference(unit_resulting_resolution,[],[f131,f63,f120,f121,f137,f173,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | v3_tex_2(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( v3_tex_2(X2,X0)
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( v3_tex_2(X2,X0)
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ~ ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ~ ( v3_tex_2(X2,X0)
                      & r1_tarski(X1,X2) ) )
              & v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tex_2)).

fof(f173,plain,(
    v2_tex_2(u1_struct_0(sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f121,f122,f63,f63,f123,f137,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X1)
      | v2_tex_2(u1_struct_0(X1),X0) ) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | ~ v1_tdlat_3(X1)
      | v2_tex_2(X2,X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v2_tex_2(X2,X0)
                <=> v1_tdlat_3(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tex_2)).

fof(f123,plain,(
    m1_pre_topc(sK1,sK1) ),
    inference(unit_resulting_resolution,[],[f121,f81])).

fof(f81,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f122,plain,(
    v1_tdlat_3(sK1) ),
    inference(unit_resulting_resolution,[],[f66,f69,f63,f64,f65,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(X1)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ v4_tex_2(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
          | ~ v4_tex_2(X1,X0)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
          | ~ v4_tex_2(X1,X0)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( ( v4_tex_2(X1,X0)
              & ~ v2_struct_0(X1) )
           => ( v1_tdlat_3(X1)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc35_tex_2)).

fof(f65,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
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
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
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

fof(f64,plain,(
    v4_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f69,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f66,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f137,plain,(
    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unit_resulting_resolution,[],[f121,f123,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f63,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f120,plain,(
    v2_pre_topc(sK1) ),
    inference(unit_resulting_resolution,[],[f69,f67,f65,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f67,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f131,plain,(
    v3_tdlat_3(sK1) ),
    inference(unit_resulting_resolution,[],[f66,f69,f65,f122,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( v3_tdlat_3(X1)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tdlat_3(X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tdlat_3(X1)
          | ~ v1_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tdlat_3(X1)
          | ~ v1_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tdlat_3(X1)
           => v3_tdlat_3(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc18_tex_2)).

fof(f178,plain,(
    m1_subset_1(sK5(sK1,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unit_resulting_resolution,[],[f63,f120,f131,f121,f137,f173,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f121,plain,(
    l1_pre_topc(sK1) ),
    inference(unit_resulting_resolution,[],[f69,f65,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f266,plain,(
    u1_struct_0(sK1) = k2_pre_topc(sK1,sK5(sK1,u1_struct_0(sK1))) ),
    inference(unit_resulting_resolution,[],[f121,f178,f263,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).

fof(f93,plain,(
    m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(definition_unfolding,[],[f57,f55])).

fof(f55,plain,(
    sK3 = sK4 ),
    inference(cnf_transformation,[],[f26])).

fof(f57,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f132,plain,(
    ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(unit_resulting_resolution,[],[f63,f124,f85])).

fof(f85,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

fof(f124,plain,(
    l1_struct_0(sK1) ),
    inference(unit_resulting_resolution,[],[f121,f92])).

fof(f92,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f291,plain,(
    k2_pre_topc(sK0,k2_tarski(sK4,sK4)) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k6_domain_1(k2_struct_0(sK1),sK4)) ),
    inference(backward_demodulation,[],[f256,f267])).

fof(f256,plain,(
    k8_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK4)) != k2_pre_topc(sK0,k2_tarski(sK4,sK4)) ),
    inference(backward_demodulation,[],[f240,f253])).

fof(f253,plain,(
    k2_tarski(sK4,sK4) = k6_domain_1(k2_struct_0(sK0),sK4) ),
    inference(unit_resulting_resolution,[],[f118,f237,f95])).

fof(f237,plain,(
    m1_subset_1(sK4,k2_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f54,f236])).

fof(f236,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(backward_demodulation,[],[f235,f234])).

fof(f234,plain,(
    k2_struct_0(sK0) = k2_pre_topc(sK0,sK5(sK0,u1_struct_0(sK1))) ),
    inference(unit_resulting_resolution,[],[f69,f169,f232,f74])).

fof(f232,plain,(
    v1_tops_1(sK5(sK0,u1_struct_0(sK1)),sK0) ),
    inference(unit_resulting_resolution,[],[f68,f67,f66,f69,f171,f169,f84])).

fof(f171,plain,(
    v3_tex_2(sK5(sK0,u1_struct_0(sK1)),sK0) ),
    inference(unit_resulting_resolution,[],[f68,f66,f67,f69,f119,f166,f91])).

fof(f166,plain,(
    v2_tex_2(u1_struct_0(sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f69,f122,f66,f63,f65,f119,f98])).

fof(f119,plain,(
    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f69,f65,f78])).

fof(f68,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f169,plain,(
    m1_subset_1(sK5(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f66,f67,f68,f69,f119,f166,f89])).

fof(f235,plain,(
    u1_struct_0(sK0) = k2_pre_topc(sK0,sK5(sK0,u1_struct_0(sK1))) ),
    inference(unit_resulting_resolution,[],[f69,f169,f232,f72])).

fof(f54,plain,(
    m1_subset_1(sK4,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f118,plain,(
    ~ v1_xboole_0(k2_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f66,f111,f85])).

fof(f111,plain,(
    l1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f69,f92])).

fof(f240,plain,(
    k2_pre_topc(sK0,k6_domain_1(k2_struct_0(sK0),sK4)) != k8_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK4)) ),
    inference(backward_demodulation,[],[f94,f236])).

fof(f94,plain,(
    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK4)) ),
    inference(definition_unfolding,[],[f56,f55])).

fof(f56,plain,(
    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) ),
    inference(cnf_transformation,[],[f26])).

fof(f298,plain,(
    m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(k2_struct_0(sK1))) ),
    inference(backward_demodulation,[],[f297,f296])).

fof(f297,plain,(
    m1_subset_1(k6_domain_1(k2_struct_0(sK1),sK4),k1_zfmisc_1(k2_struct_0(sK1))) ),
    inference(unit_resulting_resolution,[],[f132,f268,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f255,plain,(
    m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f254,f253])).

fof(f254,plain,(
    m1_subset_1(k6_domain_1(k2_struct_0(sK0),sK4),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f118,f237,f75])).

fof(f634,plain,(
    ~ spl6_35 ),
    inference(avatar_contradiction_clause,[],[f631])).

fof(f631,plain,
    ( $false
    | ~ spl6_35 ),
    inference(unit_resulting_resolution,[],[f63,f598])).

fof(f598,plain,
    ( v2_struct_0(sK1)
    | ~ spl6_35 ),
    inference(avatar_component_clause,[],[f596])).

fof(f596,plain,
    ( spl6_35
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f630,plain,(
    spl6_37 ),
    inference(avatar_contradiction_clause,[],[f627])).

fof(f627,plain,
    ( $false
    | spl6_37 ),
    inference(unit_resulting_resolution,[],[f287,f606])).

fof(f606,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | spl6_37 ),
    inference(avatar_component_clause,[],[f604])).

fof(f604,plain,
    ( spl6_37
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f287,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f239,f267])).

fof(f239,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f61,f236])).

fof(f61,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f26])).

fof(f626,plain,(
    spl6_36 ),
    inference(avatar_contradiction_clause,[],[f623])).

fof(f623,plain,
    ( $false
    | spl6_36 ),
    inference(unit_resulting_resolution,[],[f286,f602])).

fof(f602,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | spl6_36 ),
    inference(avatar_component_clause,[],[f600])).

fof(f600,plain,
    ( spl6_36
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f286,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f238,f267])).

fof(f238,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f59,f236])).

fof(f59,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f622,plain,(
    spl6_34 ),
    inference(avatar_contradiction_clause,[],[f619])).

fof(f619,plain,
    ( $false
    | spl6_34 ),
    inference(unit_resulting_resolution,[],[f64,f594])).

fof(f594,plain,
    ( ~ v4_tex_2(sK1,sK0)
    | spl6_34 ),
    inference(avatar_component_clause,[],[f592])).

fof(f592,plain,
    ( spl6_34
  <=> v4_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f618,plain,(
    spl6_33 ),
    inference(avatar_contradiction_clause,[],[f615])).

fof(f615,plain,
    ( $false
    | spl6_33 ),
    inference(unit_resulting_resolution,[],[f65,f590])).

fof(f590,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | spl6_33 ),
    inference(avatar_component_clause,[],[f588])).

fof(f588,plain,
    ( spl6_33
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f614,plain,(
    spl6_32 ),
    inference(avatar_contradiction_clause,[],[f611])).

fof(f611,plain,
    ( $false
    | spl6_32 ),
    inference(unit_resulting_resolution,[],[f60,f586])).

fof(f586,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | spl6_32 ),
    inference(avatar_component_clause,[],[f584])).

fof(f584,plain,
    ( spl6_32
  <=> v5_pre_topc(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f60,plain,(
    v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f610,plain,
    ( ~ spl6_6
    | ~ spl6_32
    | spl6_21
    | ~ spl6_33
    | ~ spl6_34
    | spl6_35
    | ~ spl6_9
    | ~ spl6_13
    | ~ spl6_36
    | ~ spl6_37
    | spl6_38 ),
    inference(avatar_split_clause,[],[f562,f608,f604,f600,f380,f311,f596,f592,f588,f454,f584,f185])).

fof(f185,plain,
    ( spl6_6
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f454,plain,
    ( spl6_21
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f311,plain,
    ( spl6_9
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f380,plain,
    ( spl6_13
  <=> v3_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f562,plain,(
    ! [X0] :
      ( k2_pre_topc(sK0,X0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
      | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
      | ~ v3_tdlat_3(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | ~ v4_tex_2(sK1,sK0)
      | ~ m1_pre_topc(sK1,sK0)
      | v2_struct_0(sK0)
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | ~ v2_pre_topc(sK0) ) ),
    inference(forward_demodulation,[],[f561,f236])).

fof(f561,plain,(
    ! [X0] :
      ( k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
      | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
      | ~ v3_tdlat_3(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | ~ v4_tex_2(sK1,sK0)
      | ~ m1_pre_topc(sK1,sK0)
      | v2_struct_0(sK0)
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | ~ v2_pre_topc(sK0) ) ),
    inference(forward_demodulation,[],[f560,f267])).

fof(f560,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
      | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
      | ~ v3_tdlat_3(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | ~ v4_tex_2(sK1,sK0)
      | ~ m1_pre_topc(sK1,sK0)
      | v2_struct_0(sK0)
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | ~ v2_pre_topc(sK0)
      | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) ) ),
    inference(forward_demodulation,[],[f559,f236])).

fof(f559,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
      | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
      | ~ v3_tdlat_3(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | ~ v4_tex_2(sK1,sK0)
      | ~ m1_pre_topc(sK1,sK0)
      | v2_struct_0(sK0)
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) ) ),
    inference(forward_demodulation,[],[f558,f267])).

fof(f558,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
      | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
      | ~ v3_tdlat_3(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | ~ v4_tex_2(sK1,sK0)
      | ~ m1_pre_topc(sK1,sK0)
      | v2_struct_0(sK0)
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) ) ),
    inference(forward_demodulation,[],[f557,f236])).

fof(f557,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
      | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
      | ~ v3_tdlat_3(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | ~ v4_tex_2(sK1,sK0)
      | ~ m1_pre_topc(sK1,sK0)
      | v2_struct_0(sK0)
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) ) ),
    inference(forward_demodulation,[],[f556,f267])).

fof(f556,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
      | ~ v3_tdlat_3(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | ~ v4_tex_2(sK1,sK0)
      | ~ m1_pre_topc(sK1,sK0)
      | v2_struct_0(sK0)
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) ) ),
    inference(forward_demodulation,[],[f555,f236])).

fof(f555,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
      | ~ v3_tdlat_3(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | ~ v4_tex_2(sK1,sK0)
      | ~ m1_pre_topc(sK1,sK0)
      | v2_struct_0(sK0)
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) ) ),
    inference(forward_demodulation,[],[f554,f267])).

fof(f554,plain,(
    ! [X0] :
      ( ~ v3_tdlat_3(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | ~ v4_tex_2(sK1,sK0)
      | ~ m1_pre_topc(sK1,sK0)
      | v2_struct_0(sK0)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) ) ),
    inference(resolution,[],[f99,f62])).

fof(f62,plain,(
    v3_borsuk_1(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_borsuk_1(sK2,X0,X1)
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0)
      | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v5_pre_topc(sK2,X0,X1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X2) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,X2) ) ),
    inference(resolution,[],[f58,f96])).

fof(f96,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v2_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v3_borsuk_1(X2,X0,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X4) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
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

fof(f58,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f497,plain,(
    ~ spl6_21 ),
    inference(avatar_contradiction_clause,[],[f494])).

fof(f494,plain,
    ( $false
    | ~ spl6_21 ),
    inference(unit_resulting_resolution,[],[f66,f456])).

fof(f456,plain,
    ( v2_struct_0(sK0)
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f454])).

fof(f392,plain,(
    spl6_13 ),
    inference(avatar_contradiction_clause,[],[f387])).

fof(f387,plain,
    ( $false
    | spl6_13 ),
    inference(unit_resulting_resolution,[],[f68,f382])).

fof(f382,plain,
    ( ~ v3_tdlat_3(sK0)
    | spl6_13 ),
    inference(avatar_component_clause,[],[f380])).

fof(f330,plain,(
    spl6_9 ),
    inference(avatar_contradiction_clause,[],[f325])).

fof(f325,plain,
    ( $false
    | spl6_9 ),
    inference(unit_resulting_resolution,[],[f69,f110,f313,f80])).

fof(f313,plain,
    ( ~ l1_pre_topc(sK0)
    | spl6_9 ),
    inference(avatar_component_clause,[],[f311])).

fof(f110,plain,(
    m1_pre_topc(sK0,sK0) ),
    inference(unit_resulting_resolution,[],[f69,f81])).

fof(f198,plain,(
    spl6_6 ),
    inference(avatar_contradiction_clause,[],[f194])).

fof(f194,plain,
    ( $false
    | spl6_6 ),
    inference(unit_resulting_resolution,[],[f69,f67,f110,f187,f79])).

fof(f187,plain,
    ( ~ v2_pre_topc(sK0)
    | spl6_6 ),
    inference(avatar_component_clause,[],[f185])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:20:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.44  % (24111)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.46  % (24111)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f654,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(avatar_sat_refutation,[],[f198,f330,f392,f497,f610,f614,f618,f622,f626,f630,f634,f653])).
% 0.20/0.46  fof(f653,plain,(
% 0.20/0.46    ~spl6_38),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f650])).
% 0.20/0.46  fof(f650,plain,(
% 0.20/0.46    $false | ~spl6_38),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f255,f298,f299,f609])).
% 0.20/0.46  fof(f609,plain,(
% 0.20/0.46    ( ! [X0] : (k2_pre_topc(sK0,X0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) ) | ~spl6_38),
% 0.20/0.46    inference(avatar_component_clause,[],[f608])).
% 0.20/0.46  fof(f608,plain,(
% 0.20/0.46    spl6_38 <=> ! [X0] : (k2_pre_topc(sK0,X0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).
% 0.20/0.46  fof(f299,plain,(
% 0.20/0.46    k2_pre_topc(sK0,k2_tarski(sK4,sK4)) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_tarski(sK4,sK4))),
% 0.20/0.46    inference(backward_demodulation,[],[f291,f296])).
% 0.20/0.46  fof(f296,plain,(
% 0.20/0.46    k2_tarski(sK4,sK4) = k6_domain_1(k2_struct_0(sK1),sK4)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f132,f268,f95])).
% 0.20/0.46  fof(f95,plain,(
% 0.20/0.46    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k2_tarski(X1,X1)) )),
% 0.20/0.46    inference(definition_unfolding,[],[f76,f86])).
% 0.20/0.46  fof(f86,plain,(
% 0.20/0.46    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.46  fof(f76,plain,(
% 0.20/0.46    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f34])).
% 0.20/0.46  fof(f34,plain,(
% 0.20/0.46    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.46    inference(flattening,[],[f33])).
% 0.20/0.46  fof(f33,plain,(
% 0.20/0.46    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f12])).
% 0.20/0.46  fof(f12,axiom,(
% 0.20/0.46    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.20/0.46  fof(f268,plain,(
% 0.20/0.46    m1_subset_1(sK4,k2_struct_0(sK1))),
% 0.20/0.46    inference(backward_demodulation,[],[f93,f267])).
% 0.20/0.46  fof(f267,plain,(
% 0.20/0.46    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.20/0.46    inference(backward_demodulation,[],[f266,f265])).
% 0.20/0.46  fof(f265,plain,(
% 0.20/0.46    k2_struct_0(sK1) = k2_pre_topc(sK1,sK5(sK1,u1_struct_0(sK1)))),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f121,f178,f263,f74])).
% 0.20/0.46  fof(f74,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f30])).
% 0.20/0.46  fof(f30,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f13])).
% 0.20/0.46  fof(f13,axiom,(
% 0.20/0.46    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).
% 0.20/0.46  fof(f263,plain,(
% 0.20/0.46    v1_tops_1(sK5(sK1,u1_struct_0(sK1)),sK1)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f131,f120,f63,f121,f180,f178,f84])).
% 0.20/0.46  fof(f84,plain,(
% 0.20/0.46    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tex_2(X1,X0) | v1_tops_1(X1,X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f46])).
% 0.20/0.46  fof(f46,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (v1_tops_1(X1,X0) | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.46    inference(flattening,[],[f45])).
% 0.20/0.46  fof(f45,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) | ~v3_tex_2(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f20])).
% 0.20/0.46  fof(f20,axiom,(
% 0.20/0.46    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) => v1_tops_1(X1,X0))))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tex_2)).
% 0.20/0.46  fof(f180,plain,(
% 0.20/0.46    v3_tex_2(sK5(sK1,u1_struct_0(sK1)),sK1)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f131,f63,f120,f121,f137,f173,f91])).
% 0.20/0.46  fof(f91,plain,(
% 0.20/0.46    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | v3_tex_2(sK5(X0,X1),X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f52])).
% 0.20/0.46  fof(f52,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (? [X2] : (v3_tex_2(X2,X0) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.46    inference(flattening,[],[f51])).
% 0.20/0.46  fof(f51,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : ((? [X2] : ((v3_tex_2(X2,X0) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f21])).
% 0.20/0.46  fof(f21,axiom,(
% 0.20/0.46    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(v3_tex_2(X2,X0) & r1_tarski(X1,X2))) & v2_tex_2(X1,X0))))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tex_2)).
% 0.20/0.46  fof(f173,plain,(
% 0.20/0.46    v2_tex_2(u1_struct_0(sK1),sK1)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f121,f122,f63,f63,f123,f137,f98])).
% 0.20/0.46  fof(f98,plain,(
% 0.20/0.46    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tdlat_3(X1) | v2_tex_2(u1_struct_0(X1),X0)) )),
% 0.20/0.46    inference(equality_resolution,[],[f87])).
% 0.20/0.46  fof(f87,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | ~v1_tdlat_3(X1) | v2_tex_2(X2,X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f50])).
% 0.20/0.46  fof(f50,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.46    inference(flattening,[],[f49])).
% 0.20/0.46  fof(f49,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f19])).
% 0.20/0.46  fof(f19,axiom,(
% 0.20/0.46    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v2_tex_2(X2,X0) <=> v1_tdlat_3(X1))))))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tex_2)).
% 0.20/0.46  fof(f123,plain,(
% 0.20/0.46    m1_pre_topc(sK1,sK1)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f121,f81])).
% 0.20/0.46  fof(f81,plain,(
% 0.20/0.46    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f40])).
% 0.20/0.46  fof(f40,plain,(
% 0.20/0.46    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f15])).
% 0.20/0.46  fof(f15,axiom,(
% 0.20/0.46    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.20/0.46  fof(f122,plain,(
% 0.20/0.46    v1_tdlat_3(sK1)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f66,f69,f63,f64,f65,f82])).
% 0.20/0.46  fof(f82,plain,(
% 0.20/0.46    ( ! [X0,X1] : (v1_tdlat_3(X1) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~v4_tex_2(X1,X0) | v2_struct_0(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f42])).
% 0.20/0.46  fof(f42,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : ((v1_tdlat_3(X1) & ~v2_struct_0(X1)) | ~v4_tex_2(X1,X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.46    inference(flattening,[],[f41])).
% 0.20/0.46  fof(f41,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (((v1_tdlat_3(X1) & ~v2_struct_0(X1)) | (~v4_tex_2(X1,X0) | v2_struct_0(X1))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f17])).
% 0.20/0.46  fof(f17,axiom,(
% 0.20/0.46    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => (v1_tdlat_3(X1) & ~v2_struct_0(X1)))))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc35_tex_2)).
% 0.20/0.46  fof(f65,plain,(
% 0.20/0.46    m1_pre_topc(sK1,sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f26])).
% 0.20/0.46  fof(f26,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.46    inference(flattening,[],[f25])).
% 0.20/0.46  fof(f25,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (? [X4] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f24])).
% 0.20/0.46  fof(f24,negated_conjecture,(
% 0.20/0.46    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)))))))))),
% 0.20/0.46    inference(negated_conjecture,[],[f23])).
% 0.20/0.46  fof(f23,conjecture,(
% 0.20/0.46    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)))))))))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tex_2)).
% 0.20/0.46  fof(f64,plain,(
% 0.20/0.46    v4_tex_2(sK1,sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f26])).
% 0.20/0.46  fof(f69,plain,(
% 0.20/0.46    l1_pre_topc(sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f26])).
% 0.20/0.46  fof(f66,plain,(
% 0.20/0.46    ~v2_struct_0(sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f26])).
% 0.20/0.46  fof(f137,plain,(
% 0.20/0.46    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f121,f123,f78])).
% 0.20/0.46  fof(f78,plain,(
% 0.20/0.46    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f36])).
% 0.20/0.46  fof(f36,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f14])).
% 0.20/0.46  fof(f14,axiom,(
% 0.20/0.46    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.20/0.46  fof(f63,plain,(
% 0.20/0.46    ~v2_struct_0(sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f26])).
% 0.20/0.46  fof(f120,plain,(
% 0.20/0.46    v2_pre_topc(sK1)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f69,f67,f65,f79])).
% 0.20/0.46  fof(f79,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_pre_topc(X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f38])).
% 0.20/0.46  fof(f38,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.46    inference(flattening,[],[f37])).
% 0.20/0.46  fof(f37,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f6])).
% 0.20/0.46  fof(f6,axiom,(
% 0.20/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.20/0.46  fof(f67,plain,(
% 0.20/0.46    v2_pre_topc(sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f26])).
% 0.20/0.46  fof(f131,plain,(
% 0.20/0.46    v3_tdlat_3(sK1)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f66,f69,f65,f122,f83])).
% 0.20/0.46  fof(f83,plain,(
% 0.20/0.46    ( ! [X0,X1] : (v3_tdlat_3(X1) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v1_tdlat_3(X1) | v2_struct_0(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f44])).
% 0.20/0.46  fof(f44,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (v3_tdlat_3(X1) | ~v1_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.46    inference(flattening,[],[f43])).
% 0.20/0.46  fof(f43,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : ((v3_tdlat_3(X1) | ~v1_tdlat_3(X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f16])).
% 0.20/0.46  fof(f16,axiom,(
% 0.20/0.46    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tdlat_3(X1) => v3_tdlat_3(X1))))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc18_tex_2)).
% 0.20/0.46  fof(f178,plain,(
% 0.20/0.46    m1_subset_1(sK5(sK1,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f63,f120,f131,f121,f137,f173,f89])).
% 0.20/0.46  fof(f89,plain,(
% 0.20/0.46    ( ! [X0,X1] : (m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | v2_struct_0(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f52])).
% 0.20/0.46  fof(f121,plain,(
% 0.20/0.46    l1_pre_topc(sK1)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f69,f65,f80])).
% 0.20/0.46  fof(f80,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f39])).
% 0.20/0.46  fof(f39,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f8])).
% 0.20/0.46  fof(f8,axiom,(
% 0.20/0.46    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.20/0.46  fof(f266,plain,(
% 0.20/0.46    u1_struct_0(sK1) = k2_pre_topc(sK1,sK5(sK1,u1_struct_0(sK1)))),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f121,f178,f263,f72])).
% 0.20/0.46  fof(f72,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f29])).
% 0.20/0.46  fof(f29,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f18])).
% 0.20/0.46  fof(f18,axiom,(
% 0.20/0.46    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).
% 0.20/0.46  fof(f93,plain,(
% 0.20/0.46    m1_subset_1(sK4,u1_struct_0(sK1))),
% 0.20/0.46    inference(definition_unfolding,[],[f57,f55])).
% 0.20/0.46  fof(f55,plain,(
% 0.20/0.46    sK3 = sK4),
% 0.20/0.46    inference(cnf_transformation,[],[f26])).
% 0.20/0.46  fof(f57,plain,(
% 0.20/0.46    m1_subset_1(sK3,u1_struct_0(sK1))),
% 0.20/0.46    inference(cnf_transformation,[],[f26])).
% 0.20/0.46  fof(f132,plain,(
% 0.20/0.46    ~v1_xboole_0(k2_struct_0(sK1))),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f63,f124,f85])).
% 0.20/0.46  fof(f85,plain,(
% 0.20/0.46    ( ! [X0] : (v2_struct_0(X0) | ~l1_struct_0(X0) | ~v1_xboole_0(k2_struct_0(X0))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f48])).
% 0.20/0.46  fof(f48,plain,(
% 0.20/0.46    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.46    inference(flattening,[],[f47])).
% 0.20/0.46  fof(f47,plain,(
% 0.20/0.46    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f9])).
% 0.20/0.46  fof(f9,axiom,(
% 0.20/0.46    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).
% 0.20/0.46  fof(f124,plain,(
% 0.20/0.46    l1_struct_0(sK1)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f121,f92])).
% 0.20/0.46  fof(f92,plain,(
% 0.20/0.46    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f53])).
% 0.20/0.46  fof(f53,plain,(
% 0.20/0.46    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f7])).
% 0.20/0.46  fof(f7,axiom,(
% 0.20/0.46    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.46  fof(f291,plain,(
% 0.20/0.46    k2_pre_topc(sK0,k2_tarski(sK4,sK4)) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k6_domain_1(k2_struct_0(sK1),sK4))),
% 0.20/0.46    inference(backward_demodulation,[],[f256,f267])).
% 0.20/0.46  fof(f256,plain,(
% 0.20/0.46    k8_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK4)) != k2_pre_topc(sK0,k2_tarski(sK4,sK4))),
% 0.20/0.46    inference(backward_demodulation,[],[f240,f253])).
% 0.20/0.46  fof(f253,plain,(
% 0.20/0.46    k2_tarski(sK4,sK4) = k6_domain_1(k2_struct_0(sK0),sK4)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f118,f237,f95])).
% 0.20/0.46  fof(f237,plain,(
% 0.20/0.46    m1_subset_1(sK4,k2_struct_0(sK0))),
% 0.20/0.46    inference(backward_demodulation,[],[f54,f236])).
% 0.20/0.46  fof(f236,plain,(
% 0.20/0.46    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.20/0.46    inference(backward_demodulation,[],[f235,f234])).
% 0.20/0.46  fof(f234,plain,(
% 0.20/0.46    k2_struct_0(sK0) = k2_pre_topc(sK0,sK5(sK0,u1_struct_0(sK1)))),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f69,f169,f232,f74])).
% 0.20/0.46  fof(f232,plain,(
% 0.20/0.46    v1_tops_1(sK5(sK0,u1_struct_0(sK1)),sK0)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f68,f67,f66,f69,f171,f169,f84])).
% 0.20/0.46  fof(f171,plain,(
% 0.20/0.46    v3_tex_2(sK5(sK0,u1_struct_0(sK1)),sK0)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f68,f66,f67,f69,f119,f166,f91])).
% 0.20/0.46  fof(f166,plain,(
% 0.20/0.46    v2_tex_2(u1_struct_0(sK1),sK0)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f69,f122,f66,f63,f65,f119,f98])).
% 0.20/0.46  fof(f119,plain,(
% 0.20/0.46    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f69,f65,f78])).
% 0.20/0.46  fof(f68,plain,(
% 0.20/0.46    v3_tdlat_3(sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f26])).
% 0.20/0.46  fof(f169,plain,(
% 0.20/0.46    m1_subset_1(sK5(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f66,f67,f68,f69,f119,f166,f89])).
% 0.20/0.46  fof(f235,plain,(
% 0.20/0.46    u1_struct_0(sK0) = k2_pre_topc(sK0,sK5(sK0,u1_struct_0(sK1)))),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f69,f169,f232,f72])).
% 0.20/0.46  fof(f54,plain,(
% 0.20/0.46    m1_subset_1(sK4,u1_struct_0(sK0))),
% 0.20/0.46    inference(cnf_transformation,[],[f26])).
% 0.20/0.46  fof(f118,plain,(
% 0.20/0.46    ~v1_xboole_0(k2_struct_0(sK0))),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f66,f111,f85])).
% 0.20/0.46  fof(f111,plain,(
% 0.20/0.46    l1_struct_0(sK0)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f69,f92])).
% 0.20/0.46  fof(f240,plain,(
% 0.20/0.46    k2_pre_topc(sK0,k6_domain_1(k2_struct_0(sK0),sK4)) != k8_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK4))),
% 0.20/0.46    inference(backward_demodulation,[],[f94,f236])).
% 0.20/0.46  fof(f94,plain,(
% 0.20/0.46    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK4))),
% 0.20/0.46    inference(definition_unfolding,[],[f56,f55])).
% 0.20/0.46  fof(f56,plain,(
% 0.20/0.46    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4))),
% 0.20/0.46    inference(cnf_transformation,[],[f26])).
% 0.20/0.46  fof(f298,plain,(
% 0.20/0.46    m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(k2_struct_0(sK1)))),
% 0.20/0.46    inference(backward_demodulation,[],[f297,f296])).
% 0.20/0.46  fof(f297,plain,(
% 0.20/0.46    m1_subset_1(k6_domain_1(k2_struct_0(sK1),sK4),k1_zfmisc_1(k2_struct_0(sK1)))),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f132,f268,f75])).
% 0.20/0.46  fof(f75,plain,(
% 0.20/0.46    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f32])).
% 0.20/0.46  fof(f32,plain,(
% 0.20/0.46    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.46    inference(flattening,[],[f31])).
% 0.20/0.46  fof(f31,plain,(
% 0.20/0.46    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f11])).
% 0.20/0.46  fof(f11,axiom,(
% 0.20/0.46    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.20/0.46  fof(f255,plain,(
% 0.20/0.46    m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.20/0.46    inference(backward_demodulation,[],[f254,f253])).
% 0.20/0.46  fof(f254,plain,(
% 0.20/0.46    m1_subset_1(k6_domain_1(k2_struct_0(sK0),sK4),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f118,f237,f75])).
% 0.20/0.46  fof(f634,plain,(
% 0.20/0.46    ~spl6_35),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f631])).
% 0.20/0.46  fof(f631,plain,(
% 0.20/0.46    $false | ~spl6_35),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f63,f598])).
% 0.20/0.46  fof(f598,plain,(
% 0.20/0.46    v2_struct_0(sK1) | ~spl6_35),
% 0.20/0.46    inference(avatar_component_clause,[],[f596])).
% 0.20/0.46  fof(f596,plain,(
% 0.20/0.46    spl6_35 <=> v2_struct_0(sK1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).
% 0.20/0.46  fof(f630,plain,(
% 0.20/0.46    spl6_37),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f627])).
% 0.20/0.46  fof(f627,plain,(
% 0.20/0.46    $false | spl6_37),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f287,f606])).
% 0.20/0.46  fof(f606,plain,(
% 0.20/0.46    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | spl6_37),
% 0.20/0.46    inference(avatar_component_clause,[],[f604])).
% 0.20/0.46  fof(f604,plain,(
% 0.20/0.46    spl6_37 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).
% 0.20/0.46  fof(f287,plain,(
% 0.20/0.46    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.20/0.46    inference(backward_demodulation,[],[f239,f267])).
% 0.20/0.46  fof(f239,plain,(
% 0.20/0.46    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1))))),
% 0.20/0.46    inference(backward_demodulation,[],[f61,f236])).
% 0.20/0.46  fof(f61,plain,(
% 0.20/0.46    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.20/0.46    inference(cnf_transformation,[],[f26])).
% 0.20/0.46  fof(f626,plain,(
% 0.20/0.46    spl6_36),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f623])).
% 0.20/0.46  fof(f623,plain,(
% 0.20/0.46    $false | spl6_36),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f286,f602])).
% 0.20/0.46  fof(f602,plain,(
% 0.20/0.46    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | spl6_36),
% 0.20/0.46    inference(avatar_component_clause,[],[f600])).
% 0.20/0.46  fof(f600,plain,(
% 0.20/0.46    spl6_36 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).
% 0.20/0.46  fof(f286,plain,(
% 0.20/0.46    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.20/0.46    inference(backward_demodulation,[],[f238,f267])).
% 0.20/0.46  fof(f238,plain,(
% 0.20/0.46    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1))),
% 0.20/0.46    inference(backward_demodulation,[],[f59,f236])).
% 0.20/0.46  fof(f59,plain,(
% 0.20/0.46    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.20/0.46    inference(cnf_transformation,[],[f26])).
% 0.20/0.46  fof(f622,plain,(
% 0.20/0.46    spl6_34),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f619])).
% 0.20/0.46  fof(f619,plain,(
% 0.20/0.46    $false | spl6_34),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f64,f594])).
% 0.20/0.46  fof(f594,plain,(
% 0.20/0.46    ~v4_tex_2(sK1,sK0) | spl6_34),
% 0.20/0.46    inference(avatar_component_clause,[],[f592])).
% 0.20/0.46  fof(f592,plain,(
% 0.20/0.46    spl6_34 <=> v4_tex_2(sK1,sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).
% 0.20/0.46  fof(f618,plain,(
% 0.20/0.46    spl6_33),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f615])).
% 0.20/0.46  fof(f615,plain,(
% 0.20/0.46    $false | spl6_33),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f65,f590])).
% 0.20/0.46  fof(f590,plain,(
% 0.20/0.46    ~m1_pre_topc(sK1,sK0) | spl6_33),
% 0.20/0.46    inference(avatar_component_clause,[],[f588])).
% 0.20/0.46  fof(f588,plain,(
% 0.20/0.46    spl6_33 <=> m1_pre_topc(sK1,sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 0.20/0.46  fof(f614,plain,(
% 0.20/0.46    spl6_32),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f611])).
% 0.20/0.46  fof(f611,plain,(
% 0.20/0.46    $false | spl6_32),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f60,f586])).
% 0.20/0.46  fof(f586,plain,(
% 0.20/0.46    ~v5_pre_topc(sK2,sK0,sK1) | spl6_32),
% 0.20/0.46    inference(avatar_component_clause,[],[f584])).
% 0.20/0.46  fof(f584,plain,(
% 0.20/0.46    spl6_32 <=> v5_pre_topc(sK2,sK0,sK1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 0.20/0.46  fof(f60,plain,(
% 0.20/0.46    v5_pre_topc(sK2,sK0,sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f26])).
% 0.20/0.46  fof(f610,plain,(
% 0.20/0.46    ~spl6_6 | ~spl6_32 | spl6_21 | ~spl6_33 | ~spl6_34 | spl6_35 | ~spl6_9 | ~spl6_13 | ~spl6_36 | ~spl6_37 | spl6_38),
% 0.20/0.46    inference(avatar_split_clause,[],[f562,f608,f604,f600,f380,f311,f596,f592,f588,f454,f584,f185])).
% 0.20/0.46  fof(f185,plain,(
% 0.20/0.46    spl6_6 <=> v2_pre_topc(sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.20/0.46  fof(f454,plain,(
% 0.20/0.46    spl6_21 <=> v2_struct_0(sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 0.20/0.46  fof(f311,plain,(
% 0.20/0.46    spl6_9 <=> l1_pre_topc(sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.20/0.46  fof(f380,plain,(
% 0.20/0.46    spl6_13 <=> v3_tdlat_3(sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.20/0.46  fof(f562,plain,(
% 0.20/0.46    ( ! [X0] : (k2_pre_topc(sK0,X0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v3_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v4_tex_2(sK1,sK0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0) | ~v5_pre_topc(sK2,sK0,sK1) | ~v2_pre_topc(sK0)) )),
% 0.20/0.46    inference(forward_demodulation,[],[f561,f236])).
% 0.20/0.46  fof(f561,plain,(
% 0.20/0.46    ( ! [X0] : (k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v3_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v4_tex_2(sK1,sK0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0) | ~v5_pre_topc(sK2,sK0,sK1) | ~v2_pre_topc(sK0)) )),
% 0.20/0.46    inference(forward_demodulation,[],[f560,f267])).
% 0.20/0.46  fof(f560,plain,(
% 0.20/0.46    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v3_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v4_tex_2(sK1,sK0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0) | ~v5_pre_topc(sK2,sK0,sK1) | ~v2_pre_topc(sK0) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)) )),
% 0.20/0.46    inference(forward_demodulation,[],[f559,f236])).
% 0.20/0.46  fof(f559,plain,(
% 0.20/0.46    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v3_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v4_tex_2(sK1,sK0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0) | ~v5_pre_topc(sK2,sK0,sK1) | ~v2_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)) )),
% 0.20/0.46    inference(forward_demodulation,[],[f558,f267])).
% 0.20/0.46  fof(f558,plain,(
% 0.20/0.46    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v3_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v4_tex_2(sK1,sK0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0) | ~v5_pre_topc(sK2,sK0,sK1) | ~v2_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)) )),
% 0.20/0.46    inference(forward_demodulation,[],[f557,f236])).
% 0.20/0.46  fof(f557,plain,(
% 0.20/0.46    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v3_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v4_tex_2(sK1,sK0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0) | ~v5_pre_topc(sK2,sK0,sK1) | ~v2_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)) )),
% 0.20/0.46    inference(forward_demodulation,[],[f556,f267])).
% 0.20/0.46  fof(f556,plain,(
% 0.20/0.46    ( ! [X0] : (~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v3_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v4_tex_2(sK1,sK0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v2_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)) )),
% 0.20/0.46    inference(forward_demodulation,[],[f555,f236])).
% 0.20/0.46  fof(f555,plain,(
% 0.20/0.46    ( ! [X0] : (~v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | ~v3_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v4_tex_2(sK1,sK0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v2_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)) )),
% 0.20/0.46    inference(forward_demodulation,[],[f554,f267])).
% 0.20/0.46  fof(f554,plain,(
% 0.20/0.46    ( ! [X0] : (~v3_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v4_tex_2(sK1,sK0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v2_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)) )),
% 0.20/0.46    inference(resolution,[],[f99,f62])).
% 0.20/0.46  fof(f62,plain,(
% 0.20/0.46    v3_borsuk_1(sK2,sK0,sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f26])).
% 0.20/0.46  fof(f99,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~v3_borsuk_1(sK2,X0,X1) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0) | ~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) | ~v5_pre_topc(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X2) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,X2)) )),
% 0.20/0.46    inference(resolution,[],[f58,f96])).
% 0.20/0.46  fof(f96,plain,(
% 0.20/0.46    ( ! [X4,X2,X0,X1] : (~v1_funct_1(X2) | ~v2_pre_topc(X0) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X4) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) )),
% 0.20/0.46    inference(equality_resolution,[],[f70])).
% 0.20/0.46  fof(f70,plain,(
% 0.20/0.46    ( ! [X4,X2,X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | X3 != X4 | k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f28])).
% 0.20/0.46  fof(f28,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.46    inference(flattening,[],[f27])).
% 0.20/0.46  fof(f27,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : (! [X4] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f22])).
% 0.20/0.46  fof(f22,axiom,(
% 0.20/0.46    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4))))))))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tex_2)).
% 0.20/0.46  fof(f58,plain,(
% 0.20/0.46    v1_funct_1(sK2)),
% 0.20/0.46    inference(cnf_transformation,[],[f26])).
% 0.20/0.46  fof(f497,plain,(
% 0.20/0.46    ~spl6_21),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f494])).
% 0.20/0.46  fof(f494,plain,(
% 0.20/0.46    $false | ~spl6_21),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f66,f456])).
% 0.20/0.46  fof(f456,plain,(
% 0.20/0.46    v2_struct_0(sK0) | ~spl6_21),
% 0.20/0.46    inference(avatar_component_clause,[],[f454])).
% 0.20/0.46  fof(f392,plain,(
% 0.20/0.46    spl6_13),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f387])).
% 0.20/0.46  fof(f387,plain,(
% 0.20/0.46    $false | spl6_13),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f68,f382])).
% 0.20/0.46  fof(f382,plain,(
% 0.20/0.46    ~v3_tdlat_3(sK0) | spl6_13),
% 0.20/0.46    inference(avatar_component_clause,[],[f380])).
% 0.20/0.46  fof(f330,plain,(
% 0.20/0.46    spl6_9),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f325])).
% 0.20/0.46  fof(f325,plain,(
% 0.20/0.46    $false | spl6_9),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f69,f110,f313,f80])).
% 0.20/0.46  fof(f313,plain,(
% 0.20/0.46    ~l1_pre_topc(sK0) | spl6_9),
% 0.20/0.46    inference(avatar_component_clause,[],[f311])).
% 0.20/0.46  fof(f110,plain,(
% 0.20/0.46    m1_pre_topc(sK0,sK0)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f69,f81])).
% 0.20/0.46  fof(f198,plain,(
% 0.20/0.46    spl6_6),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f194])).
% 0.20/0.46  fof(f194,plain,(
% 0.20/0.46    $false | spl6_6),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f69,f67,f110,f187,f79])).
% 0.20/0.46  fof(f187,plain,(
% 0.20/0.46    ~v2_pre_topc(sK0) | spl6_6),
% 0.20/0.46    inference(avatar_component_clause,[],[f185])).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (24111)------------------------------
% 0.20/0.46  % (24111)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (24111)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (24111)Memory used [KB]: 6652
% 0.20/0.46  % (24111)Time elapsed: 0.047 s
% 0.20/0.46  % (24111)------------------------------
% 0.20/0.46  % (24111)------------------------------
% 0.20/0.47  % (24085)Success in time 0.107 s
%------------------------------------------------------------------------------
