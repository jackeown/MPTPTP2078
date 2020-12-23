%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 935 expanded)
%              Number of leaves         :    9 ( 167 expanded)
%              Depth                    :   19
%              Number of atoms          :  493 (8777 expanded)
%              Number of equality atoms :   72 (1072 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f195,plain,(
    $false ),
    inference(subsumption_resolution,[],[f194,f151])).

fof(f151,plain,(
    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k1_tarski(sK3)) != k2_pre_topc(sK0,k1_tarski(sK3)) ),
    inference(backward_demodulation,[],[f146,f150])).

fof(f150,plain,(
    k1_tarski(sK3) = u1_struct_0(k1_tex_2(sK0,sK3)) ),
    inference(subsumption_resolution,[],[f149,f41])).

fof(f41,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f13])).

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
    inference(flattening,[],[f12])).

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
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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

fof(f149,plain,
    ( k1_tarski(sK3) = u1_struct_0(k1_tex_2(sK0,sK3))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f148,f62])).

fof(f62,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f45,f44])).

fof(f44,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f45,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f148,plain,
    ( k1_tarski(sK3) = u1_struct_0(k1_tex_2(sK0,sK3))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f104,f48])).

fof(f48,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f104,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k1_tarski(sK3) = u1_struct_0(k1_tex_2(sK0,sK3)) ),
    inference(backward_demodulation,[],[f68,f102])).

fof(f102,plain,(
    k6_domain_1(u1_struct_0(sK0),sK3) = u1_struct_0(k1_tex_2(sK0,sK3)) ),
    inference(subsumption_resolution,[],[f101,f81])).

fof(f81,plain,(
    v1_pre_topc(k1_tex_2(sK0,sK3)) ),
    inference(subsumption_resolution,[],[f80,f41])).

fof(f80,plain,
    ( v2_struct_0(sK0)
    | v1_pre_topc(k1_tex_2(sK0,sK3)) ),
    inference(subsumption_resolution,[],[f77,f44])).

fof(f77,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_pre_topc(k1_tex_2(sK0,sK3)) ),
    inference(resolution,[],[f55,f60])).

fof(f60,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f29,f30])).

fof(f30,plain,(
    sK3 = sK4 ),
    inference(cnf_transformation,[],[f13])).

fof(f29,plain,(
    m1_subset_1(sK4,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_pre_topc(k1_tex_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).

fof(f101,plain,
    ( ~ v1_pre_topc(k1_tex_2(sK0,sK3))
    | k6_domain_1(u1_struct_0(sK0),sK3) = u1_struct_0(k1_tex_2(sK0,sK3)) ),
    inference(subsumption_resolution,[],[f100,f75])).

fof(f75,plain,(
    ~ v2_struct_0(k1_tex_2(sK0,sK3)) ),
    inference(subsumption_resolution,[],[f74,f41])).

fof(f74,plain,
    ( v2_struct_0(sK0)
    | ~ v2_struct_0(k1_tex_2(sK0,sK3)) ),
    inference(subsumption_resolution,[],[f71,f44])).

fof(f71,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v2_struct_0(k1_tex_2(sK0,sK3)) ),
    inference(resolution,[],[f54,f60])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_struct_0(k1_tex_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f100,plain,
    ( v2_struct_0(k1_tex_2(sK0,sK3))
    | ~ v1_pre_topc(k1_tex_2(sK0,sK3))
    | k6_domain_1(u1_struct_0(sK0),sK3) = u1_struct_0(k1_tex_2(sK0,sK3)) ),
    inference(subsumption_resolution,[],[f99,f41])).

fof(f99,plain,
    ( v2_struct_0(sK0)
    | v2_struct_0(k1_tex_2(sK0,sK3))
    | ~ v1_pre_topc(k1_tex_2(sK0,sK3))
    | k6_domain_1(u1_struct_0(sK0),sK3) = u1_struct_0(k1_tex_2(sK0,sK3)) ),
    inference(subsumption_resolution,[],[f92,f44])).

fof(f92,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(k1_tex_2(sK0,sK3))
    | ~ v1_pre_topc(k1_tex_2(sK0,sK3))
    | k6_domain_1(u1_struct_0(sK0),sK3) = u1_struct_0(k1_tex_2(sK0,sK3)) ),
    inference(resolution,[],[f61,f60])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_struct_0(k1_tex_2(X0,X1))
      | ~ v1_pre_topc(k1_tex_2(X0,X1))
      | k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f58,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | m1_pre_topc(k1_tex_2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(k1_tex_2(X0,X1))
      | ~ v1_pre_topc(k1_tex_2(X0,X1))
      | ~ m1_pre_topc(k1_tex_2(X0,X1),X0)
      | k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X2,X0)
      | u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)
      | k1_tex_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_tex_2(X0,X1) = X2
              <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_tex_2(X0,X1) = X2
              <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_pre_topc(X2)
                & ~ v2_struct_0(X2) )
             => ( k1_tex_2(X0,X1) = X2
              <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tex_2)).

fof(f68,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k6_domain_1(u1_struct_0(sK0),sK3) = k1_tarski(sK3) ),
    inference(resolution,[],[f53,f60])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f146,plain,(
    k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,sK3))) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k1_tarski(sK3)) ),
    inference(backward_demodulation,[],[f103,f143])).

fof(f143,plain,(
    k1_tarski(sK3) = u1_struct_0(k1_tex_2(sK1,sK3)) ),
    inference(subsumption_resolution,[],[f142,f38])).

fof(f38,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f142,plain,
    ( k1_tarski(sK3) = u1_struct_0(k1_tex_2(sK1,sK3))
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f141,f105])).

fof(f105,plain,(
    l1_struct_0(sK1) ),
    inference(resolution,[],[f64,f45])).

fof(f64,plain,(
    l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f63,f44])).

fof(f63,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK1) ),
    inference(resolution,[],[f46,f40])).

fof(f40,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f141,plain,
    ( k1_tarski(sK3) = u1_struct_0(k1_tex_2(sK1,sK3))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f97,f48])).

fof(f97,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | k1_tarski(sK3) = u1_struct_0(k1_tex_2(sK1,sK3)) ),
    inference(backward_demodulation,[],[f67,f96])).

fof(f96,plain,(
    k6_domain_1(u1_struct_0(sK1),sK3) = u1_struct_0(k1_tex_2(sK1,sK3)) ),
    inference(subsumption_resolution,[],[f95,f79])).

fof(f79,plain,(
    v1_pre_topc(k1_tex_2(sK1,sK3)) ),
    inference(subsumption_resolution,[],[f78,f38])).

fof(f78,plain,
    ( v2_struct_0(sK1)
    | v1_pre_topc(k1_tex_2(sK1,sK3)) ),
    inference(subsumption_resolution,[],[f76,f64])).

fof(f76,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | v1_pre_topc(k1_tex_2(sK1,sK3)) ),
    inference(resolution,[],[f55,f32])).

fof(f32,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f95,plain,
    ( ~ v1_pre_topc(k1_tex_2(sK1,sK3))
    | k6_domain_1(u1_struct_0(sK1),sK3) = u1_struct_0(k1_tex_2(sK1,sK3)) ),
    inference(subsumption_resolution,[],[f94,f73])).

fof(f73,plain,(
    ~ v2_struct_0(k1_tex_2(sK1,sK3)) ),
    inference(subsumption_resolution,[],[f72,f38])).

fof(f72,plain,
    ( v2_struct_0(sK1)
    | ~ v2_struct_0(k1_tex_2(sK1,sK3)) ),
    inference(subsumption_resolution,[],[f70,f64])).

fof(f70,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ v2_struct_0(k1_tex_2(sK1,sK3)) ),
    inference(resolution,[],[f54,f32])).

fof(f94,plain,
    ( v2_struct_0(k1_tex_2(sK1,sK3))
    | ~ v1_pre_topc(k1_tex_2(sK1,sK3))
    | k6_domain_1(u1_struct_0(sK1),sK3) = u1_struct_0(k1_tex_2(sK1,sK3)) ),
    inference(subsumption_resolution,[],[f93,f38])).

fof(f93,plain,
    ( v2_struct_0(sK1)
    | v2_struct_0(k1_tex_2(sK1,sK3))
    | ~ v1_pre_topc(k1_tex_2(sK1,sK3))
    | k6_domain_1(u1_struct_0(sK1),sK3) = u1_struct_0(k1_tex_2(sK1,sK3)) ),
    inference(subsumption_resolution,[],[f91,f64])).

fof(f91,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | v2_struct_0(k1_tex_2(sK1,sK3))
    | ~ v1_pre_topc(k1_tex_2(sK1,sK3))
    | k6_domain_1(u1_struct_0(sK1),sK3) = u1_struct_0(k1_tex_2(sK1,sK3)) ),
    inference(resolution,[],[f61,f32])).

fof(f67,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | k6_domain_1(u1_struct_0(sK1),sK3) = k1_tarski(sK3) ),
    inference(resolution,[],[f53,f32])).

fof(f103,plain,(
    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(k1_tex_2(sK1,sK3))) != k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,sK3))) ),
    inference(backward_demodulation,[],[f98,f102])).

fof(f98,plain,(
    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK3)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(k1_tex_2(sK1,sK3))) ),
    inference(backward_demodulation,[],[f59,f96])).

fof(f59,plain,(
    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK3)) ),
    inference(backward_demodulation,[],[f31,f30])).

fof(f31,plain,(
    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) ),
    inference(cnf_transformation,[],[f13])).

fof(f194,plain,(
    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k1_tarski(sK3)) = k2_pre_topc(sK0,k1_tarski(sK3)) ),
    inference(subsumption_resolution,[],[f192,f152])).

fof(f152,plain,(
    m1_subset_1(k1_tarski(sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f137,f150])).

fof(f137,plain,(
    m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK3)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f133,f44])).

fof(f133,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK3)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f90,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f90,plain,(
    m1_pre_topc(k1_tex_2(sK0,sK3),sK0) ),
    inference(subsumption_resolution,[],[f89,f41])).

fof(f89,plain,
    ( v2_struct_0(sK0)
    | m1_pre_topc(k1_tex_2(sK0,sK3),sK0) ),
    inference(subsumption_resolution,[],[f86,f44])).

fof(f86,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | m1_pre_topc(k1_tex_2(sK0,sK3),sK0) ),
    inference(resolution,[],[f56,f60])).

fof(f192,plain,
    ( ~ m1_subset_1(k1_tarski(sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k1_tarski(sK3)) = k2_pre_topc(sK0,k1_tarski(sK3)) ),
    inference(resolution,[],[f144,f125])).

fof(f125,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) ) ),
    inference(subsumption_resolution,[],[f124,f37])).

fof(f37,plain,(
    v3_borsuk_1(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f124,plain,(
    ! [X0] :
      ( ~ v3_borsuk_1(sK2,sK0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) ) ),
    inference(subsumption_resolution,[],[f123,f41])).

fof(f123,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ v3_borsuk_1(sK2,sK0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) ) ),
    inference(subsumption_resolution,[],[f122,f35])).

fof(f35,plain,(
    v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f122,plain,(
    ! [X0] :
      ( ~ v5_pre_topc(sK2,sK0,sK1)
      | v2_struct_0(sK0)
      | ~ v3_borsuk_1(sK2,sK0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) ) ),
    inference(subsumption_resolution,[],[f121,f34])).

fof(f34,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f121,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | v2_struct_0(sK0)
      | ~ v3_borsuk_1(sK2,sK0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) ) ),
    inference(subsumption_resolution,[],[f120,f33])).

fof(f33,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f120,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | v2_struct_0(sK0)
      | ~ v3_borsuk_1(sK2,sK0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) ) ),
    inference(subsumption_resolution,[],[f119,f40])).

fof(f119,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK1,sK0)
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | v2_struct_0(sK0)
      | ~ v3_borsuk_1(sK2,sK0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) ) ),
    inference(subsumption_resolution,[],[f118,f39])).

fof(f39,plain,(
    v4_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f118,plain,(
    ! [X0] :
      ( ~ v4_tex_2(sK1,sK0)
      | ~ m1_pre_topc(sK1,sK0)
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | v2_struct_0(sK0)
      | ~ v3_borsuk_1(sK2,sK0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) ) ),
    inference(subsumption_resolution,[],[f117,f38])).

fof(f117,plain,(
    ! [X0] :
      ( v2_struct_0(sK1)
      | ~ v4_tex_2(sK1,sK0)
      | ~ m1_pre_topc(sK1,sK0)
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | v2_struct_0(sK0)
      | ~ v3_borsuk_1(sK2,sK0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) ) ),
    inference(subsumption_resolution,[],[f116,f44])).

fof(f116,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | ~ v4_tex_2(sK1,sK0)
      | ~ m1_pre_topc(sK1,sK0)
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | v2_struct_0(sK0)
      | ~ v3_borsuk_1(sK2,sK0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) ) ),
    inference(subsumption_resolution,[],[f115,f43])).

fof(f43,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f115,plain,(
    ! [X0] :
      ( ~ v3_tdlat_3(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | ~ v4_tex_2(sK1,sK0)
      | ~ m1_pre_topc(sK1,sK0)
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | v2_struct_0(sK0)
      | ~ v3_borsuk_1(sK2,sK0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) ) ),
    inference(subsumption_resolution,[],[f114,f42])).

fof(f42,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f114,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ v3_tdlat_3(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | ~ v4_tex_2(sK1,sK0)
      | ~ m1_pre_topc(sK1,sK0)
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | v2_struct_0(sK0)
      | ~ v3_borsuk_1(sK2,sK0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) ) ),
    inference(resolution,[],[f57,f36])).

fof(f36,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f13])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v5_pre_topc(X2,X0,X1)
      | v2_struct_0(X0)
      | ~ v3_borsuk_1(X2,X0,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X4) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
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
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f144,plain,(
    m1_subset_1(k1_tarski(sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(backward_demodulation,[],[f130,f143])).

fof(f130,plain,(
    m1_subset_1(u1_struct_0(k1_tex_2(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f127,f64])).

fof(f127,plain,
    ( ~ l1_pre_topc(sK1)
    | m1_subset_1(u1_struct_0(k1_tex_2(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(resolution,[],[f88,f47])).

fof(f88,plain,(
    m1_pre_topc(k1_tex_2(sK1,sK3),sK1) ),
    inference(subsumption_resolution,[],[f87,f38])).

fof(f87,plain,
    ( v2_struct_0(sK1)
    | m1_pre_topc(k1_tex_2(sK1,sK3),sK1) ),
    inference(subsumption_resolution,[],[f85,f64])).

fof(f85,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | m1_pre_topc(k1_tex_2(sK1,sK3),sK1) ),
    inference(resolution,[],[f56,f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:26:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (564)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (572)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (572)Refutation not found, incomplete strategy% (572)------------------------------
% 0.21/0.47  % (572)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (572)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (572)Memory used [KB]: 10618
% 0.21/0.47  % (572)Time elapsed: 0.062 s
% 0.21/0.47  % (572)------------------------------
% 0.21/0.47  % (572)------------------------------
% 0.21/0.48  % (566)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % (551)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (556)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (569)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.48  % (560)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.49  % (569)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f195,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(subsumption_resolution,[],[f194,f151])).
% 0.21/0.49  fof(f151,plain,(
% 0.21/0.49    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k1_tarski(sK3)) != k2_pre_topc(sK0,k1_tarski(sK3))),
% 0.21/0.49    inference(backward_demodulation,[],[f146,f150])).
% 0.21/0.49  fof(f150,plain,(
% 0.21/0.49    k1_tarski(sK3) = u1_struct_0(k1_tex_2(sK0,sK3))),
% 0.21/0.49    inference(subsumption_resolution,[],[f149,f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ~v2_struct_0(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (? [X4] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,negated_conjecture,(
% 0.21/0.49    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)))))))))),
% 0.21/0.49    inference(negated_conjecture,[],[f10])).
% 0.21/0.49  fof(f10,conjecture,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)))))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tex_2)).
% 0.21/0.49  fof(f149,plain,(
% 0.21/0.49    k1_tarski(sK3) = u1_struct_0(k1_tex_2(sK0,sK3)) | v2_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f148,f62])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    l1_struct_0(sK0)),
% 0.21/0.49    inference(resolution,[],[f45,f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    l1_pre_topc(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.49  fof(f148,plain,(
% 0.21/0.49    k1_tarski(sK3) = u1_struct_0(k1_tex_2(sK0,sK3)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.49    inference(resolution,[],[f104,f48])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    v1_xboole_0(u1_struct_0(sK0)) | k1_tarski(sK3) = u1_struct_0(k1_tex_2(sK0,sK3))),
% 0.21/0.49    inference(backward_demodulation,[],[f68,f102])).
% 0.21/0.49  fof(f102,plain,(
% 0.21/0.49    k6_domain_1(u1_struct_0(sK0),sK3) = u1_struct_0(k1_tex_2(sK0,sK3))),
% 0.21/0.49    inference(subsumption_resolution,[],[f101,f81])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    v1_pre_topc(k1_tex_2(sK0,sK3))),
% 0.21/0.49    inference(subsumption_resolution,[],[f80,f41])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    v2_struct_0(sK0) | v1_pre_topc(k1_tex_2(sK0,sK3))),
% 0.21/0.49    inference(subsumption_resolution,[],[f77,f44])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_pre_topc(k1_tex_2(sK0,sK3))),
% 0.21/0.49    inference(resolution,[],[f55,f60])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    m1_subset_1(sK3,u1_struct_0(sK0))),
% 0.21/0.49    inference(forward_demodulation,[],[f29,f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    sK3 = sK4),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    m1_subset_1(sK4,u1_struct_0(sK0))),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v1_pre_topc(k1_tex_2(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).
% 0.21/0.49  fof(f101,plain,(
% 0.21/0.49    ~v1_pre_topc(k1_tex_2(sK0,sK3)) | k6_domain_1(u1_struct_0(sK0),sK3) = u1_struct_0(k1_tex_2(sK0,sK3))),
% 0.21/0.49    inference(subsumption_resolution,[],[f100,f75])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    ~v2_struct_0(k1_tex_2(sK0,sK3))),
% 0.21/0.49    inference(subsumption_resolution,[],[f74,f41])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    v2_struct_0(sK0) | ~v2_struct_0(k1_tex_2(sK0,sK3))),
% 0.21/0.49    inference(subsumption_resolution,[],[f71,f44])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v2_struct_0(k1_tex_2(sK0,sK3))),
% 0.21/0.49    inference(resolution,[],[f54,f60])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~v2_struct_0(k1_tex_2(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    v2_struct_0(k1_tex_2(sK0,sK3)) | ~v1_pre_topc(k1_tex_2(sK0,sK3)) | k6_domain_1(u1_struct_0(sK0),sK3) = u1_struct_0(k1_tex_2(sK0,sK3))),
% 0.21/0.49    inference(subsumption_resolution,[],[f99,f41])).
% 0.21/0.49  fof(f99,plain,(
% 0.21/0.49    v2_struct_0(sK0) | v2_struct_0(k1_tex_2(sK0,sK3)) | ~v1_pre_topc(k1_tex_2(sK0,sK3)) | k6_domain_1(u1_struct_0(sK0),sK3) = u1_struct_0(k1_tex_2(sK0,sK3))),
% 0.21/0.49    inference(subsumption_resolution,[],[f92,f44])).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v2_struct_0(k1_tex_2(sK0,sK3)) | ~v1_pre_topc(k1_tex_2(sK0,sK3)) | k6_domain_1(u1_struct_0(sK0),sK3) = u1_struct_0(k1_tex_2(sK0,sK3))),
% 0.21/0.49    inference(resolution,[],[f61,f60])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(k1_tex_2(X0,X1)) | ~v1_pre_topc(k1_tex_2(X0,X1)) | k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f58,f56])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0) | m1_pre_topc(k1_tex_2(X0,X1),X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(k1_tex_2(X0,X1)) | ~v1_pre_topc(k1_tex_2(X0,X1)) | ~m1_pre_topc(k1_tex_2(X0,X1),X0) | k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1))) )),
% 0.21/0.49    inference(equality_resolution,[],[f51])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X2,X0) | u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) | k1_tex_2(X0,X1) != X2) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => (k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tex_2)).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    v1_xboole_0(u1_struct_0(sK0)) | k6_domain_1(u1_struct_0(sK0),sK3) = k1_tarski(sK3)),
% 0.21/0.49    inference(resolution,[],[f53,f60])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.49    inference(flattening,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.21/0.49  fof(f146,plain,(
% 0.21/0.49    k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,sK3))) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k1_tarski(sK3))),
% 0.21/0.49    inference(backward_demodulation,[],[f103,f143])).
% 0.21/0.49  fof(f143,plain,(
% 0.21/0.49    k1_tarski(sK3) = u1_struct_0(k1_tex_2(sK1,sK3))),
% 0.21/0.49    inference(subsumption_resolution,[],[f142,f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ~v2_struct_0(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f142,plain,(
% 0.21/0.49    k1_tarski(sK3) = u1_struct_0(k1_tex_2(sK1,sK3)) | v2_struct_0(sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f141,f105])).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    l1_struct_0(sK1)),
% 0.21/0.49    inference(resolution,[],[f64,f45])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    l1_pre_topc(sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f63,f44])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | l1_pre_topc(sK1)),
% 0.21/0.49    inference(resolution,[],[f46,f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    m1_pre_topc(sK1,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.49  fof(f141,plain,(
% 0.21/0.49    k1_tarski(sK3) = u1_struct_0(k1_tex_2(sK1,sK3)) | ~l1_struct_0(sK1) | v2_struct_0(sK1)),
% 0.21/0.49    inference(resolution,[],[f97,f48])).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    v1_xboole_0(u1_struct_0(sK1)) | k1_tarski(sK3) = u1_struct_0(k1_tex_2(sK1,sK3))),
% 0.21/0.49    inference(backward_demodulation,[],[f67,f96])).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    k6_domain_1(u1_struct_0(sK1),sK3) = u1_struct_0(k1_tex_2(sK1,sK3))),
% 0.21/0.49    inference(subsumption_resolution,[],[f95,f79])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    v1_pre_topc(k1_tex_2(sK1,sK3))),
% 0.21/0.49    inference(subsumption_resolution,[],[f78,f38])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    v2_struct_0(sK1) | v1_pre_topc(k1_tex_2(sK1,sK3))),
% 0.21/0.49    inference(subsumption_resolution,[],[f76,f64])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    ~l1_pre_topc(sK1) | v2_struct_0(sK1) | v1_pre_topc(k1_tex_2(sK1,sK3))),
% 0.21/0.49    inference(resolution,[],[f55,f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    m1_subset_1(sK3,u1_struct_0(sK1))),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    ~v1_pre_topc(k1_tex_2(sK1,sK3)) | k6_domain_1(u1_struct_0(sK1),sK3) = u1_struct_0(k1_tex_2(sK1,sK3))),
% 0.21/0.49    inference(subsumption_resolution,[],[f94,f73])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    ~v2_struct_0(k1_tex_2(sK1,sK3))),
% 0.21/0.49    inference(subsumption_resolution,[],[f72,f38])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    v2_struct_0(sK1) | ~v2_struct_0(k1_tex_2(sK1,sK3))),
% 0.21/0.49    inference(subsumption_resolution,[],[f70,f64])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    ~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~v2_struct_0(k1_tex_2(sK1,sK3))),
% 0.21/0.49    inference(resolution,[],[f54,f32])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    v2_struct_0(k1_tex_2(sK1,sK3)) | ~v1_pre_topc(k1_tex_2(sK1,sK3)) | k6_domain_1(u1_struct_0(sK1),sK3) = u1_struct_0(k1_tex_2(sK1,sK3))),
% 0.21/0.49    inference(subsumption_resolution,[],[f93,f38])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    v2_struct_0(sK1) | v2_struct_0(k1_tex_2(sK1,sK3)) | ~v1_pre_topc(k1_tex_2(sK1,sK3)) | k6_domain_1(u1_struct_0(sK1),sK3) = u1_struct_0(k1_tex_2(sK1,sK3))),
% 0.21/0.49    inference(subsumption_resolution,[],[f91,f64])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    ~l1_pre_topc(sK1) | v2_struct_0(sK1) | v2_struct_0(k1_tex_2(sK1,sK3)) | ~v1_pre_topc(k1_tex_2(sK1,sK3)) | k6_domain_1(u1_struct_0(sK1),sK3) = u1_struct_0(k1_tex_2(sK1,sK3))),
% 0.21/0.49    inference(resolution,[],[f61,f32])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    v1_xboole_0(u1_struct_0(sK1)) | k6_domain_1(u1_struct_0(sK1),sK3) = k1_tarski(sK3)),
% 0.21/0.49    inference(resolution,[],[f53,f32])).
% 0.21/0.49  fof(f103,plain,(
% 0.21/0.49    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(k1_tex_2(sK1,sK3))) != k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,sK3)))),
% 0.21/0.49    inference(backward_demodulation,[],[f98,f102])).
% 0.21/0.49  fof(f98,plain,(
% 0.21/0.49    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK3)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(k1_tex_2(sK1,sK3)))),
% 0.21/0.49    inference(backward_demodulation,[],[f59,f96])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK3))),
% 0.21/0.49    inference(backward_demodulation,[],[f31,f30])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4))),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f194,plain,(
% 0.21/0.49    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k1_tarski(sK3)) = k2_pre_topc(sK0,k1_tarski(sK3))),
% 0.21/0.49    inference(subsumption_resolution,[],[f192,f152])).
% 0.21/0.49  fof(f152,plain,(
% 0.21/0.49    m1_subset_1(k1_tarski(sK3),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    inference(backward_demodulation,[],[f137,f150])).
% 0.21/0.49  fof(f137,plain,(
% 0.21/0.49    m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK3)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    inference(subsumption_resolution,[],[f133,f44])).
% 0.21/0.49  fof(f133,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK3)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    inference(resolution,[],[f90,f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    m1_pre_topc(k1_tex_2(sK0,sK3),sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f89,f41])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    v2_struct_0(sK0) | m1_pre_topc(k1_tex_2(sK0,sK3),sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f86,f44])).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | m1_pre_topc(k1_tex_2(sK0,sK3),sK0)),
% 0.21/0.49    inference(resolution,[],[f56,f60])).
% 0.21/0.49  fof(f192,plain,(
% 0.21/0.49    ~m1_subset_1(k1_tarski(sK3),k1_zfmisc_1(u1_struct_0(sK0))) | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k1_tarski(sK3)) = k2_pre_topc(sK0,k1_tarski(sK3))),
% 0.21/0.49    inference(resolution,[],[f144,f125])).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f124,f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    v3_borsuk_1(sK2,sK0,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f124,plain,(
% 0.21/0.49    ( ! [X0] : (~v3_borsuk_1(sK2,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f123,f41])).
% 0.21/0.49  fof(f123,plain,(
% 0.21/0.49    ( ! [X0] : (v2_struct_0(sK0) | ~v3_borsuk_1(sK2,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f122,f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    v5_pre_topc(sK2,sK0,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f122,plain,(
% 0.21/0.49    ( ! [X0] : (~v5_pre_topc(sK2,sK0,sK1) | v2_struct_0(sK0) | ~v3_borsuk_1(sK2,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f121,f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f121,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,sK0,sK1) | v2_struct_0(sK0) | ~v3_borsuk_1(sK2,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f120,f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    v1_funct_1(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,sK0,sK1) | v2_struct_0(sK0) | ~v3_borsuk_1(sK2,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f119,f40])).
% 0.21/0.49  fof(f119,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_pre_topc(sK1,sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,sK0,sK1) | v2_struct_0(sK0) | ~v3_borsuk_1(sK2,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f118,f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    v4_tex_2(sK1,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f118,plain,(
% 0.21/0.49    ( ! [X0] : (~v4_tex_2(sK1,sK0) | ~m1_pre_topc(sK1,sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,sK0,sK1) | v2_struct_0(sK0) | ~v3_borsuk_1(sK2,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f117,f38])).
% 0.21/0.49  fof(f117,plain,(
% 0.21/0.49    ( ! [X0] : (v2_struct_0(sK1) | ~v4_tex_2(sK1,sK0) | ~m1_pre_topc(sK1,sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,sK0,sK1) | v2_struct_0(sK0) | ~v3_borsuk_1(sK2,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f116,f44])).
% 0.21/0.49  fof(f116,plain,(
% 0.21/0.49    ( ! [X0] : (~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v4_tex_2(sK1,sK0) | ~m1_pre_topc(sK1,sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,sK0,sK1) | v2_struct_0(sK0) | ~v3_borsuk_1(sK2,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f115,f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    v3_tdlat_3(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f115,plain,(
% 0.21/0.49    ( ! [X0] : (~v3_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v4_tex_2(sK1,sK0) | ~m1_pre_topc(sK1,sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,sK0,sK1) | v2_struct_0(sK0) | ~v3_borsuk_1(sK2,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f114,f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    v2_pre_topc(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f114,plain,(
% 0.21/0.49    ( ! [X0] : (~v2_pre_topc(sK0) | ~v3_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v4_tex_2(sK1,sK0) | ~m1_pre_topc(sK1,sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,sK0,sK1) | v2_struct_0(sK0) | ~v3_borsuk_1(sK2,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)) )),
% 0.21/0.49    inference(resolution,[],[f57,f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v5_pre_topc(X2,X0,X1) | v2_struct_0(X0) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X4) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) )),
% 0.21/0.49    inference(equality_resolution,[],[f49])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | X3 != X4 | k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : (! [X4] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4))))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tex_2)).
% 0.21/0.49  fof(f144,plain,(
% 0.21/0.49    m1_subset_1(k1_tarski(sK3),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.21/0.49    inference(backward_demodulation,[],[f130,f143])).
% 0.21/0.49  fof(f130,plain,(
% 0.21/0.49    m1_subset_1(u1_struct_0(k1_tex_2(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.21/0.49    inference(subsumption_resolution,[],[f127,f64])).
% 0.21/0.49  fof(f127,plain,(
% 0.21/0.49    ~l1_pre_topc(sK1) | m1_subset_1(u1_struct_0(k1_tex_2(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.21/0.49    inference(resolution,[],[f88,f47])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    m1_pre_topc(k1_tex_2(sK1,sK3),sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f87,f38])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    v2_struct_0(sK1) | m1_pre_topc(k1_tex_2(sK1,sK3),sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f85,f64])).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    ~l1_pre_topc(sK1) | v2_struct_0(sK1) | m1_pre_topc(k1_tex_2(sK1,sK3),sK1)),
% 0.21/0.49    inference(resolution,[],[f56,f32])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (569)------------------------------
% 0.21/0.49  % (569)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (569)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (569)Memory used [KB]: 1791
% 0.21/0.49  % (569)Time elapsed: 0.073 s
% 0.21/0.49  % (569)------------------------------
% 0.21/0.49  % (569)------------------------------
% 0.21/0.49  % (548)Success in time 0.13 s
%------------------------------------------------------------------------------
