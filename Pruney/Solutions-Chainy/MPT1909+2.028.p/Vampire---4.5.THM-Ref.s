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
% DateTime   : Thu Dec  3 13:22:31 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 721 expanded)
%              Number of leaves         :    9 ( 144 expanded)
%              Depth                    :   33
%              Number of atoms          :  440 (5375 expanded)
%              Number of equality atoms :   65 ( 708 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f138,plain,(
    $false ),
    inference(subsumption_resolution,[],[f137,f36])).

fof(f36,plain,(
    ~ v2_struct_0(sK0) ),
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

fof(f137,plain,(
    v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f136,f52])).

fof(f52,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f42,f39])).

fof(f39,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f42,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f136,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f135,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

fof(f135,plain,(
    v1_xboole_0(k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f134,f33])).

fof(f33,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f134,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f133,f61])).

fof(f61,plain,(
    l1_struct_0(sK1) ),
    inference(resolution,[],[f59,f42])).

fof(f59,plain,(
    l1_pre_topc(sK1) ),
    inference(resolution,[],[f58,f35])).

fof(f35,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f58,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | l1_pre_topc(X0) ) ),
    inference(resolution,[],[f43,f39])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f133,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f132,f45])).

fof(f132,plain,
    ( v1_xboole_0(k2_struct_0(sK1))
    | v1_xboole_0(k2_struct_0(sK0)) ),
    inference(resolution,[],[f131,f76])).

fof(f76,plain,
    ( m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(k2_struct_0(sK0)))
    | v1_xboole_0(k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f75,f54])).

fof(f54,plain,(
    m1_subset_1(sK4,k2_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f24,f53])).

fof(f53,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f41,f52])).

fof(f41,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f24,plain,(
    m1_subset_1(sK4,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f75,plain,
    ( m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK4,k2_struct_0(sK0))
    | v1_xboole_0(k2_struct_0(sK0)) ),
    inference(superposition,[],[f47,f73])).

fof(f73,plain,(
    k6_domain_1(k2_struct_0(sK0),sK4) = k2_tarski(sK4,sK4) ),
    inference(subsumption_resolution,[],[f72,f36])).

fof(f72,plain,
    ( k6_domain_1(k2_struct_0(sK0),sK4) = k2_tarski(sK4,sK4)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f71,f52])).

fof(f71,plain,
    ( k6_domain_1(k2_struct_0(sK0),sK4) = k2_tarski(sK4,sK4)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f67,f45])).

fof(f67,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | k6_domain_1(k2_struct_0(sK0),sK4) = k2_tarski(sK4,sK4) ),
    inference(resolution,[],[f50,f54])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | k6_domain_1(X0,X1) = k2_tarski(X1,X1) ) ),
    inference(definition_unfolding,[],[f46,f40])).

fof(f40,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
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

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

% (30660)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f131,plain,
    ( ~ m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(k2_struct_0(sK0)))
    | v1_xboole_0(k2_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f130,f81])).

fof(f81,plain,(
    k2_pre_topc(sK0,k2_tarski(sK4,sK4)) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_tarski(sK4,sK4)) ),
    inference(backward_demodulation,[],[f74,f80])).

fof(f80,plain,(
    k6_domain_1(k2_struct_0(sK1),sK4) = k2_tarski(sK4,sK4) ),
    inference(subsumption_resolution,[],[f79,f33])).

fof(f79,plain,
    ( k6_domain_1(k2_struct_0(sK1),sK4) = k2_tarski(sK4,sK4)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f78,f61])).

fof(f78,plain,
    ( k6_domain_1(k2_struct_0(sK1),sK4) = k2_tarski(sK4,sK4)
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f68,f45])).

fof(f68,plain,
    ( v1_xboole_0(k2_struct_0(sK1))
    | k6_domain_1(k2_struct_0(sK1),sK4) = k2_tarski(sK4,sK4) ),
    inference(resolution,[],[f50,f66])).

fof(f66,plain,(
    m1_subset_1(sK4,k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f48,f62])).

fof(f62,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(resolution,[],[f61,f41])).

fof(f48,plain,(
    m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(definition_unfolding,[],[f27,f25])).

fof(f25,plain,(
    sK3 = sK4 ),
    inference(cnf_transformation,[],[f12])).

fof(f27,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f74,plain,(
    k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k6_domain_1(k2_struct_0(sK1),sK4)) != k2_pre_topc(sK0,k2_tarski(sK4,sK4)) ),
    inference(backward_demodulation,[],[f65,f73])).

fof(f65,plain,(
    k2_pre_topc(sK0,k6_domain_1(k2_struct_0(sK0),sK4)) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k6_domain_1(k2_struct_0(sK1),sK4)) ),
    inference(backward_demodulation,[],[f55,f62])).

fof(f55,plain,(
    k2_pre_topc(sK0,k6_domain_1(k2_struct_0(sK0),sK4)) != k8_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK4)) ),
    inference(backward_demodulation,[],[f49,f53])).

fof(f49,plain,(
    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK4)) ),
    inference(definition_unfolding,[],[f26,f25])).

fof(f26,plain,(
    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) ),
    inference(cnf_transformation,[],[f12])).

fof(f130,plain,
    ( k2_pre_topc(sK0,k2_tarski(sK4,sK4)) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_tarski(sK4,sK4))
    | ~ m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(k2_struct_0(sK0)))
    | v1_xboole_0(k2_struct_0(sK1)) ),
    inference(resolution,[],[f128,f83])).

fof(f83,plain,
    ( m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(k2_struct_0(sK1)))
    | v1_xboole_0(k2_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f82,f66])).

fof(f82,plain,
    ( m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(k2_struct_0(sK1)))
    | ~ m1_subset_1(sK4,k2_struct_0(sK1))
    | v1_xboole_0(k2_struct_0(sK1)) ),
    inference(superposition,[],[f47,f80])).

fof(f128,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1)))
      | k2_pre_topc(sK0,X0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(forward_demodulation,[],[f127,f62])).

fof(f127,plain,(
    ! [X0] :
      ( k2_pre_topc(sK0,X0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(forward_demodulation,[],[f126,f62])).

fof(f126,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = k8_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(subsumption_resolution,[],[f125,f64])).

fof(f64,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f56,f62])).

fof(f56,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f29,f53])).

fof(f29,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f125,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = k8_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(forward_demodulation,[],[f124,f62])).

fof(f124,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1))
      | k2_pre_topc(sK0,X0) = k8_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(subsumption_resolution,[],[f123,f63])).

fof(f63,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f57,f62])).

fof(f57,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f31,f53])).

fof(f31,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f12])).

fof(f123,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1))
      | k2_pre_topc(sK0,X0) = k8_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(forward_demodulation,[],[f122,f62])).

fof(f122,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1))
      | k2_pre_topc(sK0,X0) = k8_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(subsumption_resolution,[],[f121,f30])).

fof(f30,plain,(
    v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f121,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1))
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | k2_pre_topc(sK0,X0) = k8_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(subsumption_resolution,[],[f120,f35])).

% (30651)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
fof(f120,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1))
      | ~ m1_pre_topc(sK1,sK0)
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | k2_pre_topc(sK0,X0) = k8_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(subsumption_resolution,[],[f119,f34])).

fof(f34,plain,(
    v4_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f119,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1))
      | ~ v4_tex_2(sK1,sK0)
      | ~ m1_pre_topc(sK1,sK0)
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | k2_pre_topc(sK0,X0) = k8_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(subsumption_resolution,[],[f118,f33])).

fof(f118,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1))
      | v2_struct_0(sK1)
      | ~ v4_tex_2(sK1,sK0)
      | ~ m1_pre_topc(sK1,sK0)
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | k2_pre_topc(sK0,X0) = k8_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(resolution,[],[f117,f32])).

fof(f32,plain,(
    v3_borsuk_1(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ v3_borsuk_1(sK2,sK0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ v4_tex_2(X0,sK0)
      | ~ m1_pre_topc(X0,sK0)
      | ~ v5_pre_topc(sK2,sK0,X0)
      | k2_pre_topc(sK0,X1) = k8_relset_1(k2_struct_0(sK0),u1_struct_0(X0),sK2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(forward_demodulation,[],[f116,f53])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ v4_tex_2(X0,sK0)
      | ~ m1_pre_topc(X0,sK0)
      | ~ v5_pre_topc(sK2,sK0,X0)
      | ~ v3_borsuk_1(sK2,sK0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(sK0,X1) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2,X1) ) ),
    inference(forward_demodulation,[],[f115,f53])).

fof(f115,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ v4_tex_2(X0,sK0)
      | ~ m1_pre_topc(X0,sK0)
      | ~ v5_pre_topc(sK2,sK0,X0)
      | ~ v3_borsuk_1(sK2,sK0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X1) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2,X1) ) ),
    inference(forward_demodulation,[],[f114,f53])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ v4_tex_2(X0,sK0)
      | ~ m1_pre_topc(X0,sK0)
      | ~ v5_pre_topc(sK2,sK0,X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v3_borsuk_1(sK2,sK0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X1) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2,X1) ) ),
    inference(forward_demodulation,[],[f113,f53])).

fof(f113,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v4_tex_2(X0,sK0)
      | ~ m1_pre_topc(X0,sK0)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v5_pre_topc(sK2,sK0,X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v3_borsuk_1(sK2,sK0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X1) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2,X1) ) ),
    inference(subsumption_resolution,[],[f112,f36])).

fof(f112,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v4_tex_2(X0,sK0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(sK0)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v5_pre_topc(sK2,sK0,X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v3_borsuk_1(sK2,sK0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X1) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2,X1) ) ),
    inference(subsumption_resolution,[],[f111,f39])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(X0)
      | ~ v4_tex_2(X0,sK0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(sK0)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v5_pre_topc(sK2,sK0,X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v3_borsuk_1(sK2,sK0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X1) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2,X1) ) ),
    inference(subsumption_resolution,[],[f110,f37])).

fof(f37,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X0)
      | ~ v4_tex_2(X0,sK0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(sK0)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v5_pre_topc(sK2,sK0,X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v3_borsuk_1(sK2,sK0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X1) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2,X1) ) ),
    inference(resolution,[],[f109,f38])).

fof(f38,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0)
      | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v5_pre_topc(sK2,X0,X1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v3_borsuk_1(sK2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X2) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,X2) ) ),
    inference(resolution,[],[f51,f28])).

fof(f28,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f51,plain,(
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
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
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
    inference(cnf_transformation,[],[f17])).

% (30644)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
fof(f17,plain,(
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
    inference(flattening,[],[f16])).

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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:25:46 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (30636)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.50  % (30634)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (30643)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (30636)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (30633)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (30645)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f138,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(subsumption_resolution,[],[f137,f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ~v2_struct_0(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (? [X4] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,negated_conjecture,(
% 0.21/0.51    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)))))))))),
% 0.21/0.51    inference(negated_conjecture,[],[f9])).
% 0.21/0.51  fof(f9,conjecture,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)))))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tex_2)).
% 0.21/0.51  fof(f137,plain,(
% 0.21/0.51    v2_struct_0(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f136,f52])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    l1_struct_0(sK0)),
% 0.21/0.51    inference(resolution,[],[f42,f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    l1_pre_topc(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.51  fof(f136,plain,(
% 0.21/0.51    ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.51    inference(resolution,[],[f135,f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).
% 0.21/0.51  fof(f135,plain,(
% 0.21/0.51    v1_xboole_0(k2_struct_0(sK0))),
% 0.21/0.51    inference(subsumption_resolution,[],[f134,f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ~v2_struct_0(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f134,plain,(
% 0.21/0.51    v1_xboole_0(k2_struct_0(sK0)) | v2_struct_0(sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f133,f61])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    l1_struct_0(sK1)),
% 0.21/0.51    inference(resolution,[],[f59,f42])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    l1_pre_topc(sK1)),
% 0.21/0.51    inference(resolution,[],[f58,f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    m1_pre_topc(sK1,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_pre_topc(X0,sK0) | l1_pre_topc(X0)) )),
% 0.21/0.51    inference(resolution,[],[f43,f39])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.51  fof(f133,plain,(
% 0.21/0.51    v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(sK1) | v2_struct_0(sK1)),
% 0.21/0.51    inference(resolution,[],[f132,f45])).
% 0.21/0.51  fof(f132,plain,(
% 0.21/0.51    v1_xboole_0(k2_struct_0(sK1)) | v1_xboole_0(k2_struct_0(sK0))),
% 0.21/0.51    inference(resolution,[],[f131,f76])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(k2_struct_0(sK0))) | v1_xboole_0(k2_struct_0(sK0))),
% 0.21/0.51    inference(subsumption_resolution,[],[f75,f54])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    m1_subset_1(sK4,k2_struct_0(sK0))),
% 0.21/0.51    inference(backward_demodulation,[],[f24,f53])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.21/0.51    inference(resolution,[],[f41,f52])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    m1_subset_1(sK4,u1_struct_0(sK0))),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(sK4,k2_struct_0(sK0)) | v1_xboole_0(k2_struct_0(sK0))),
% 0.21/0.51    inference(superposition,[],[f47,f73])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    k6_domain_1(k2_struct_0(sK0),sK4) = k2_tarski(sK4,sK4)),
% 0.21/0.51    inference(subsumption_resolution,[],[f72,f36])).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    k6_domain_1(k2_struct_0(sK0),sK4) = k2_tarski(sK4,sK4) | v2_struct_0(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f71,f52])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    k6_domain_1(k2_struct_0(sK0),sK4) = k2_tarski(sK4,sK4) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.51    inference(resolution,[],[f67,f45])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    v1_xboole_0(k2_struct_0(sK0)) | k6_domain_1(k2_struct_0(sK0),sK4) = k2_tarski(sK4,sK4)),
% 0.21/0.51    inference(resolution,[],[f50,f54])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X0) | k6_domain_1(X0,X1) = k2_tarski(X1,X1)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f46,f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.51    inference(flattening,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.51    inference(flattening,[],[f22])).
% 0.21/0.52  % (30660)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.21/0.52  fof(f131,plain,(
% 0.21/0.52    ~m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(k2_struct_0(sK0))) | v1_xboole_0(k2_struct_0(sK1))),
% 0.21/0.52    inference(subsumption_resolution,[],[f130,f81])).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    k2_pre_topc(sK0,k2_tarski(sK4,sK4)) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_tarski(sK4,sK4))),
% 0.21/0.52    inference(backward_demodulation,[],[f74,f80])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    k6_domain_1(k2_struct_0(sK1),sK4) = k2_tarski(sK4,sK4)),
% 0.21/0.52    inference(subsumption_resolution,[],[f79,f33])).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    k6_domain_1(k2_struct_0(sK1),sK4) = k2_tarski(sK4,sK4) | v2_struct_0(sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f78,f61])).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    k6_domain_1(k2_struct_0(sK1),sK4) = k2_tarski(sK4,sK4) | ~l1_struct_0(sK1) | v2_struct_0(sK1)),
% 0.21/0.52    inference(resolution,[],[f68,f45])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    v1_xboole_0(k2_struct_0(sK1)) | k6_domain_1(k2_struct_0(sK1),sK4) = k2_tarski(sK4,sK4)),
% 0.21/0.52    inference(resolution,[],[f50,f66])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    m1_subset_1(sK4,k2_struct_0(sK1))),
% 0.21/0.52    inference(backward_demodulation,[],[f48,f62])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.21/0.52    inference(resolution,[],[f61,f41])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    m1_subset_1(sK4,u1_struct_0(sK1))),
% 0.21/0.52    inference(definition_unfolding,[],[f27,f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    sK3 = sK4),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    m1_subset_1(sK3,u1_struct_0(sK1))),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k6_domain_1(k2_struct_0(sK1),sK4)) != k2_pre_topc(sK0,k2_tarski(sK4,sK4))),
% 0.21/0.52    inference(backward_demodulation,[],[f65,f73])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    k2_pre_topc(sK0,k6_domain_1(k2_struct_0(sK0),sK4)) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k6_domain_1(k2_struct_0(sK1),sK4))),
% 0.21/0.52    inference(backward_demodulation,[],[f55,f62])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    k2_pre_topc(sK0,k6_domain_1(k2_struct_0(sK0),sK4)) != k8_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK4))),
% 0.21/0.52    inference(backward_demodulation,[],[f49,f53])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK4))),
% 0.21/0.52    inference(definition_unfolding,[],[f26,f25])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4))),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f130,plain,(
% 0.21/0.52    k2_pre_topc(sK0,k2_tarski(sK4,sK4)) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_tarski(sK4,sK4)) | ~m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(k2_struct_0(sK0))) | v1_xboole_0(k2_struct_0(sK1))),
% 0.21/0.52    inference(resolution,[],[f128,f83])).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(k2_struct_0(sK1))) | v1_xboole_0(k2_struct_0(sK1))),
% 0.21/0.52    inference(subsumption_resolution,[],[f82,f66])).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(k2_struct_0(sK1))) | ~m1_subset_1(sK4,k2_struct_0(sK1)) | v1_xboole_0(k2_struct_0(sK1))),
% 0.21/0.52    inference(superposition,[],[f47,f80])).
% 0.21/0.52  fof(f128,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) | k2_pre_topc(sK0,X0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 0.21/0.52    inference(forward_demodulation,[],[f127,f62])).
% 0.21/0.52  fof(f127,plain,(
% 0.21/0.52    ( ! [X0] : (k2_pre_topc(sK0,X0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 0.21/0.52    inference(forward_demodulation,[],[f126,f62])).
% 0.21/0.52  fof(f126,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k8_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f125,f64])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.21/0.52    inference(backward_demodulation,[],[f56,f62])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.52    inference(backward_demodulation,[],[f29,f53])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f125,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k8_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 0.21/0.52    inference(forward_demodulation,[],[f124,f62])).
% 0.21/0.52  fof(f124,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1)) | k2_pre_topc(sK0,X0) = k8_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f123,f63])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.21/0.52    inference(backward_demodulation,[],[f57,f62])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.52    inference(backward_demodulation,[],[f31,f53])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f123,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1)) | k2_pre_topc(sK0,X0) = k8_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 0.21/0.52    inference(forward_demodulation,[],[f122,f62])).
% 0.21/0.52  fof(f122,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1)) | k2_pre_topc(sK0,X0) = k8_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f121,f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    v5_pre_topc(sK2,sK0,sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f121,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,sK0,sK1) | k2_pre_topc(sK0,X0) = k8_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f120,f35])).
% 0.21/0.52  % (30651)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  fof(f120,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1)) | ~m1_pre_topc(sK1,sK0) | ~v5_pre_topc(sK2,sK0,sK1) | k2_pre_topc(sK0,X0) = k8_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f119,f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    v4_tex_2(sK1,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f119,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1)) | ~v4_tex_2(sK1,sK0) | ~m1_pre_topc(sK1,sK0) | ~v5_pre_topc(sK2,sK0,sK1) | k2_pre_topc(sK0,X0) = k8_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f118,f33])).
% 0.21/0.52  fof(f118,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1)) | v2_struct_0(sK1) | ~v4_tex_2(sK1,sK0) | ~m1_pre_topc(sK1,sK0) | ~v5_pre_topc(sK2,sK0,sK1) | k2_pre_topc(sK0,X0) = k8_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 0.21/0.52    inference(resolution,[],[f117,f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    v3_borsuk_1(sK2,sK0,sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f117,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v3_borsuk_1(sK2,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(X0)) | v2_struct_0(X0) | ~v4_tex_2(X0,sK0) | ~m1_pre_topc(X0,sK0) | ~v5_pre_topc(sK2,sK0,X0) | k2_pre_topc(sK0,X1) = k8_relset_1(k2_struct_0(sK0),u1_struct_0(X0),sK2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.52    inference(forward_demodulation,[],[f116,f53])).
% 0.21/0.52  fof(f116,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(X0)) | v2_struct_0(X0) | ~v4_tex_2(X0,sK0) | ~m1_pre_topc(X0,sK0) | ~v5_pre_topc(sK2,sK0,X0) | ~v3_borsuk_1(sK2,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(sK0,X1) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2,X1)) )),
% 0.21/0.52    inference(forward_demodulation,[],[f115,f53])).
% 0.21/0.52  fof(f115,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(X0)) | v2_struct_0(X0) | ~v4_tex_2(X0,sK0) | ~m1_pre_topc(X0,sK0) | ~v5_pre_topc(sK2,sK0,X0) | ~v3_borsuk_1(sK2,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X1) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2,X1)) )),
% 0.21/0.52    inference(forward_demodulation,[],[f114,f53])).
% 0.21/0.52  fof(f114,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(X0)) | v2_struct_0(X0) | ~v4_tex_2(X0,sK0) | ~m1_pre_topc(X0,sK0) | ~v5_pre_topc(sK2,sK0,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v3_borsuk_1(sK2,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X1) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2,X1)) )),
% 0.21/0.52    inference(forward_demodulation,[],[f113,f53])).
% 0.21/0.52  fof(f113,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v2_struct_0(X0) | ~v4_tex_2(X0,sK0) | ~m1_pre_topc(X0,sK0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0)) | ~v5_pre_topc(sK2,sK0,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v3_borsuk_1(sK2,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X1) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2,X1)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f112,f36])).
% 0.21/0.52  fof(f112,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v2_struct_0(X0) | ~v4_tex_2(X0,sK0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(sK0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0)) | ~v5_pre_topc(sK2,sK0,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v3_borsuk_1(sK2,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X1) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2,X1)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f111,f39])).
% 0.21/0.52  fof(f111,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~l1_pre_topc(sK0) | v2_struct_0(X0) | ~v4_tex_2(X0,sK0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(sK0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0)) | ~v5_pre_topc(sK2,sK0,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v3_borsuk_1(sK2,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X1) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2,X1)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f110,f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    v2_pre_topc(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f110,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~v4_tex_2(X0,sK0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(sK0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0)) | ~v5_pre_topc(sK2,sK0,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v3_borsuk_1(sK2,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X1) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2,X1)) )),
% 0.21/0.52    inference(resolution,[],[f109,f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    v3_tdlat_3(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f109,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0) | ~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) | ~v5_pre_topc(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v3_borsuk_1(sK2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X2) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,X2)) )),
% 0.21/0.52    inference(resolution,[],[f51,f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    v1_funct_1(sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X1] : (~v1_funct_1(X2) | ~v2_pre_topc(X0) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X4) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) )),
% 0.21/0.52    inference(equality_resolution,[],[f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | X3 != X4 | k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  % (30644)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : (! [X4] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4))))))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tex_2)).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (30636)------------------------------
% 0.21/0.52  % (30636)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (30636)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (30636)Memory used [KB]: 6396
% 0.21/0.52  % (30636)Time elapsed: 0.090 s
% 0.21/0.52  % (30636)------------------------------
% 0.21/0.52  % (30636)------------------------------
% 0.21/0.52  % (30627)Success in time 0.159 s
%------------------------------------------------------------------------------
