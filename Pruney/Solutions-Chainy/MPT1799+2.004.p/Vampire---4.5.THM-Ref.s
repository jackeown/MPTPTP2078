%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:31 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 257 expanded)
%              Number of leaves         :    7 (  45 expanded)
%              Depth                    :   18
%              Number of atoms          :  308 (1607 expanded)
%              Number of equality atoms :   33 ( 170 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f117,plain,(
    $false ),
    inference(subsumption_resolution,[],[f116,f43])).

fof(f43,plain,(
    ~ v1_tsep_1(sK2,k8_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f22,f23])).

fof(f23,plain,(
    m1_pre_topc(sK2,k8_tmap_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,k8_tmap_1(X0,X1))
                | ~ v1_tsep_1(X2,k8_tmap_1(X0,X1)) )
              & u1_struct_0(X1) = u1_struct_0(X2)
              & m1_pre_topc(X2,k8_tmap_1(X0,X1)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,k8_tmap_1(X0,X1))
                | ~ v1_tsep_1(X2,k8_tmap_1(X0,X1)) )
              & u1_struct_0(X1) = u1_struct_0(X2)
              & m1_pre_topc(X2,k8_tmap_1(X0,X1)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_pre_topc(X2,k8_tmap_1(X0,X1))
               => ( u1_struct_0(X1) = u1_struct_0(X2)
                 => ( m1_pre_topc(X2,k8_tmap_1(X0,X1))
                    & v1_tsep_1(X2,k8_tmap_1(X0,X1)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_pre_topc(X2,k8_tmap_1(X0,X1))
             => ( u1_struct_0(X1) = u1_struct_0(X2)
               => ( m1_pre_topc(X2,k8_tmap_1(X0,X1))
                  & v1_tsep_1(X2,k8_tmap_1(X0,X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_tmap_1)).

fof(f22,plain,
    ( ~ v1_tsep_1(sK2,k8_tmap_1(sK0,sK1))
    | ~ m1_pre_topc(sK2,k8_tmap_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f116,plain,(
    v1_tsep_1(sK2,k8_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f115,f55])).

fof(f55,plain,(
    v2_pre_topc(k8_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f54,f27])).

fof(f27,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f54,plain,
    ( v2_struct_0(sK0)
    | v2_pre_topc(k8_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f53,f29])).

fof(f29,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f53,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v2_pre_topc(k8_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f51,f28])).

fof(f28,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f51,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v2_pre_topc(k8_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f38,f26])).

fof(f26,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_pre_topc(k8_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_tmap_1)).

fof(f115,plain,
    ( ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
    | v1_tsep_1(sK2,k8_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f114,f23])).

fof(f114,plain,
    ( ~ m1_pre_topc(sK2,k8_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
    | v1_tsep_1(sK2,k8_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f110,f61])).

fof(f61,plain,(
    l1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f60,f27])).

fof(f60,plain,
    ( v2_struct_0(sK0)
    | l1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f59,f29])).

fof(f59,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | l1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f57,f28])).

fof(f57,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | l1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f39,f26])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | l1_pre_topc(k8_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f110,plain,
    ( ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ m1_pre_topc(sK2,k8_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
    | v1_tsep_1(sK2,k8_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f108,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(u1_struct_0(sK1),X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK2,X0)
      | ~ v2_pre_topc(X0)
      | v1_tsep_1(sK2,X0) ) ),
    inference(superposition,[],[f45,f24])).

fof(f24,plain,(
    u1_struct_0(sK1) = u1_struct_0(sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(u1_struct_0(X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f41,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | ~ v3_pre_topc(X2,X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                <=> v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).

fof(f108,plain,(
    v3_pre_topc(u1_struct_0(sK1),k8_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f107,f49])).

fof(f49,plain,(
    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f47,f29])).

fof(f47,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f30,f26])).

fof(f107,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(u1_struct_0(sK1),k8_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f105,f95])).

fof(f95,plain,(
    r2_hidden(u1_struct_0(sK1),u1_pre_topc(k8_tmap_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f94,f85])).

fof(f85,plain,(
    u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f84,f27])).

fof(f84,plain,
    ( v2_struct_0(sK0)
    | u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f83,f25])).

fof(f25,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f83,plain,
    ( v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f82,f29])).

fof(f82,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f80,f28])).

fof(f80,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,u1_struct_0(sK1)) ),
    inference(resolution,[],[f44,f26])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f40,f30])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,u1_struct_0(X1)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ! [X2] :
                ( u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ! [X2] :
                ( u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ( ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) ) )
            & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_tmap_1)).

fof(f94,plain,(
    r2_hidden(u1_struct_0(sK1),k5_tmap_1(sK0,u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f93,f27])).

fof(f93,plain,
    ( v2_struct_0(sK0)
    | r2_hidden(u1_struct_0(sK1),k5_tmap_1(sK0,u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f92,f29])).

fof(f92,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | r2_hidden(u1_struct_0(sK1),k5_tmap_1(sK0,u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f89,f28])).

% (27591)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
fof(f89,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | r2_hidden(u1_struct_0(sK1),k5_tmap_1(sK0,u1_struct_0(sK1))) ),
    inference(resolution,[],[f49,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | r2_hidden(X1,k5_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k5_tmap_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k5_tmap_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r2_hidden(X1,k5_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_tmap_1)).

fof(f105,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,u1_pre_topc(k8_tmap_1(sK0,sK1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(X3,k8_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f101,f61])).

fof(f101,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
      | ~ r2_hidden(X3,u1_pre_topc(k8_tmap_1(sK0,sK1)))
      | v3_pre_topc(X3,k8_tmap_1(sK0,sK1)) ) ),
    inference(superposition,[],[f31,f75])).

fof(f75,plain,(
    u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f74,f27])).

fof(f74,plain,
    ( v2_struct_0(sK0)
    | u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f73,f25])).

fof(f73,plain,
    ( v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f72,f29])).

fof(f72,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f70,f28])).

fof(f70,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f35,f26])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:50:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.46  % (27580)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.19/0.46  % (27597)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.19/0.46  % (27590)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.19/0.46  % (27583)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.47  % (27590)Refutation not found, incomplete strategy% (27590)------------------------------
% 0.19/0.47  % (27590)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.47  % (27590)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.47  
% 0.19/0.47  % (27590)Memory used [KB]: 6268
% 0.19/0.47  % (27590)Time elapsed: 0.060 s
% 0.19/0.47  % (27590)------------------------------
% 0.19/0.47  % (27590)------------------------------
% 0.19/0.47  % (27597)Refutation found. Thanks to Tanya!
% 0.19/0.47  % SZS status Theorem for theBenchmark
% 0.19/0.47  % SZS output start Proof for theBenchmark
% 0.19/0.47  fof(f117,plain,(
% 0.19/0.47    $false),
% 0.19/0.47    inference(subsumption_resolution,[],[f116,f43])).
% 0.19/0.47  fof(f43,plain,(
% 0.19/0.47    ~v1_tsep_1(sK2,k8_tmap_1(sK0,sK1))),
% 0.19/0.47    inference(subsumption_resolution,[],[f22,f23])).
% 0.19/0.47  fof(f23,plain,(
% 0.19/0.47    m1_pre_topc(sK2,k8_tmap_1(sK0,sK1))),
% 0.19/0.47    inference(cnf_transformation,[],[f11])).
% 0.19/0.47  fof(f11,plain,(
% 0.19/0.47    ? [X0] : (? [X1] : (? [X2] : ((~m1_pre_topc(X2,k8_tmap_1(X0,X1)) | ~v1_tsep_1(X2,k8_tmap_1(X0,X1))) & u1_struct_0(X1) = u1_struct_0(X2) & m1_pre_topc(X2,k8_tmap_1(X0,X1))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.19/0.47    inference(flattening,[],[f10])).
% 0.19/0.47  fof(f10,plain,(
% 0.19/0.47    ? [X0] : (? [X1] : (? [X2] : (((~m1_pre_topc(X2,k8_tmap_1(X0,X1)) | ~v1_tsep_1(X2,k8_tmap_1(X0,X1))) & u1_struct_0(X1) = u1_struct_0(X2)) & m1_pre_topc(X2,k8_tmap_1(X0,X1))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.19/0.47    inference(ennf_transformation,[],[f8])).
% 0.19/0.47  fof(f8,negated_conjecture,(
% 0.19/0.47    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,k8_tmap_1(X0,X1)) => (u1_struct_0(X1) = u1_struct_0(X2) => (m1_pre_topc(X2,k8_tmap_1(X0,X1)) & v1_tsep_1(X2,k8_tmap_1(X0,X1)))))))),
% 0.19/0.47    inference(negated_conjecture,[],[f7])).
% 0.19/0.47  fof(f7,conjecture,(
% 0.19/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,k8_tmap_1(X0,X1)) => (u1_struct_0(X1) = u1_struct_0(X2) => (m1_pre_topc(X2,k8_tmap_1(X0,X1)) & v1_tsep_1(X2,k8_tmap_1(X0,X1)))))))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_tmap_1)).
% 0.19/0.47  fof(f22,plain,(
% 0.19/0.47    ~v1_tsep_1(sK2,k8_tmap_1(sK0,sK1)) | ~m1_pre_topc(sK2,k8_tmap_1(sK0,sK1))),
% 0.19/0.47    inference(cnf_transformation,[],[f11])).
% 0.19/0.47  fof(f116,plain,(
% 0.19/0.47    v1_tsep_1(sK2,k8_tmap_1(sK0,sK1))),
% 0.19/0.47    inference(subsumption_resolution,[],[f115,f55])).
% 0.19/0.47  fof(f55,plain,(
% 0.19/0.47    v2_pre_topc(k8_tmap_1(sK0,sK1))),
% 0.19/0.47    inference(subsumption_resolution,[],[f54,f27])).
% 0.19/0.47  fof(f27,plain,(
% 0.19/0.47    ~v2_struct_0(sK0)),
% 0.19/0.47    inference(cnf_transformation,[],[f11])).
% 0.19/0.47  fof(f54,plain,(
% 0.19/0.47    v2_struct_0(sK0) | v2_pre_topc(k8_tmap_1(sK0,sK1))),
% 0.19/0.47    inference(subsumption_resolution,[],[f53,f29])).
% 0.19/0.47  fof(f29,plain,(
% 0.19/0.47    l1_pre_topc(sK0)),
% 0.19/0.47    inference(cnf_transformation,[],[f11])).
% 0.19/0.47  fof(f53,plain,(
% 0.19/0.47    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v2_pre_topc(k8_tmap_1(sK0,sK1))),
% 0.19/0.47    inference(subsumption_resolution,[],[f51,f28])).
% 0.19/0.47  fof(f28,plain,(
% 0.19/0.47    v2_pre_topc(sK0)),
% 0.19/0.47    inference(cnf_transformation,[],[f11])).
% 0.19/0.47  fof(f51,plain,(
% 0.19/0.47    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v2_pre_topc(k8_tmap_1(sK0,sK1))),
% 0.19/0.47    inference(resolution,[],[f38,f26])).
% 0.19/0.47  fof(f26,plain,(
% 0.19/0.47    m1_pre_topc(sK1,sK0)),
% 0.19/0.47    inference(cnf_transformation,[],[f11])).
% 0.19/0.47  fof(f38,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v2_pre_topc(k8_tmap_1(X0,X1))) )),
% 0.19/0.47    inference(cnf_transformation,[],[f21])).
% 0.19/0.47  fof(f21,plain,(
% 0.19/0.47    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.47    inference(flattening,[],[f20])).
% 0.19/0.47  fof(f20,plain,(
% 0.19/0.47    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.19/0.47    inference(ennf_transformation,[],[f9])).
% 0.19/0.47  fof(f9,plain,(
% 0.19/0.47    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1))))),
% 0.19/0.47    inference(pure_predicate_removal,[],[f2])).
% 0.19/0.47  fof(f2,axiom,(
% 0.19/0.47    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_tmap_1)).
% 0.19/0.47  fof(f115,plain,(
% 0.19/0.47    ~v2_pre_topc(k8_tmap_1(sK0,sK1)) | v1_tsep_1(sK2,k8_tmap_1(sK0,sK1))),
% 0.19/0.47    inference(subsumption_resolution,[],[f114,f23])).
% 0.19/0.47  fof(f114,plain,(
% 0.19/0.47    ~m1_pre_topc(sK2,k8_tmap_1(sK0,sK1)) | ~v2_pre_topc(k8_tmap_1(sK0,sK1)) | v1_tsep_1(sK2,k8_tmap_1(sK0,sK1))),
% 0.19/0.47    inference(subsumption_resolution,[],[f110,f61])).
% 0.19/0.47  fof(f61,plain,(
% 0.19/0.47    l1_pre_topc(k8_tmap_1(sK0,sK1))),
% 0.19/0.47    inference(subsumption_resolution,[],[f60,f27])).
% 0.19/0.47  fof(f60,plain,(
% 0.19/0.47    v2_struct_0(sK0) | l1_pre_topc(k8_tmap_1(sK0,sK1))),
% 0.19/0.47    inference(subsumption_resolution,[],[f59,f29])).
% 0.19/0.47  fof(f59,plain,(
% 0.19/0.47    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | l1_pre_topc(k8_tmap_1(sK0,sK1))),
% 0.19/0.47    inference(subsumption_resolution,[],[f57,f28])).
% 0.19/0.47  fof(f57,plain,(
% 0.19/0.47    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | l1_pre_topc(k8_tmap_1(sK0,sK1))),
% 0.19/0.47    inference(resolution,[],[f39,f26])).
% 0.19/0.47  fof(f39,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | l1_pre_topc(k8_tmap_1(X0,X1))) )),
% 0.19/0.47    inference(cnf_transformation,[],[f21])).
% 0.19/0.47  fof(f110,plain,(
% 0.19/0.47    ~l1_pre_topc(k8_tmap_1(sK0,sK1)) | ~m1_pre_topc(sK2,k8_tmap_1(sK0,sK1)) | ~v2_pre_topc(k8_tmap_1(sK0,sK1)) | v1_tsep_1(sK2,k8_tmap_1(sK0,sK1))),
% 0.19/0.47    inference(resolution,[],[f108,f68])).
% 0.19/0.47  fof(f68,plain,(
% 0.19/0.47    ( ! [X0] : (~v3_pre_topc(u1_struct_0(sK1),X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK2,X0) | ~v2_pre_topc(X0) | v1_tsep_1(sK2,X0)) )),
% 0.19/0.47    inference(superposition,[],[f45,f24])).
% 0.19/0.47  fof(f24,plain,(
% 0.19/0.47    u1_struct_0(sK1) = u1_struct_0(sK2)),
% 0.19/0.47    inference(cnf_transformation,[],[f11])).
% 0.19/0.47  fof(f45,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~v3_pre_topc(u1_struct_0(X1),X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | v1_tsep_1(X1,X0)) )),
% 0.19/0.47    inference(subsumption_resolution,[],[f41,f30])).
% 0.19/0.47  fof(f30,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.19/0.47    inference(cnf_transformation,[],[f12])).
% 0.19/0.47  fof(f12,plain,(
% 0.19/0.47    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.19/0.47    inference(ennf_transformation,[],[f6])).
% 0.19/0.47  fof(f6,axiom,(
% 0.19/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.19/0.47  fof(f41,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(u1_struct_0(X1),X0) | v1_tsep_1(X1,X0)) )),
% 0.19/0.47    inference(equality_resolution,[],[f37])).
% 0.19/0.47  fof(f37,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | ~v3_pre_topc(X2,X0) | v1_tsep_1(X1,X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f19])).
% 0.19/0.47  fof(f19,plain,(
% 0.19/0.47    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.19/0.47    inference(flattening,[],[f18])).
% 0.19/0.47  fof(f18,plain,(
% 0.19/0.47    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.19/0.47    inference(ennf_transformation,[],[f5])).
% 0.19/0.47  fof(f5,axiom,(
% 0.19/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).
% 0.19/0.47  fof(f108,plain,(
% 0.19/0.47    v3_pre_topc(u1_struct_0(sK1),k8_tmap_1(sK0,sK1))),
% 0.19/0.47    inference(subsumption_resolution,[],[f107,f49])).
% 0.19/0.47  fof(f49,plain,(
% 0.19/0.47    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.47    inference(subsumption_resolution,[],[f47,f29])).
% 0.19/0.47  fof(f47,plain,(
% 0.19/0.47    ~l1_pre_topc(sK0) | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.47    inference(resolution,[],[f30,f26])).
% 0.19/0.47  fof(f107,plain,(
% 0.19/0.47    ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(u1_struct_0(sK1),k8_tmap_1(sK0,sK1))),
% 0.19/0.47    inference(resolution,[],[f105,f95])).
% 0.19/0.47  fof(f95,plain,(
% 0.19/0.47    r2_hidden(u1_struct_0(sK1),u1_pre_topc(k8_tmap_1(sK0,sK1)))),
% 0.19/0.47    inference(forward_demodulation,[],[f94,f85])).
% 0.19/0.47  fof(f85,plain,(
% 0.19/0.47    u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,u1_struct_0(sK1))),
% 0.19/0.47    inference(subsumption_resolution,[],[f84,f27])).
% 0.19/0.47  fof(f84,plain,(
% 0.19/0.47    v2_struct_0(sK0) | u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,u1_struct_0(sK1))),
% 0.19/0.47    inference(subsumption_resolution,[],[f83,f25])).
% 0.19/0.47  fof(f25,plain,(
% 0.19/0.47    ~v2_struct_0(sK1)),
% 0.19/0.47    inference(cnf_transformation,[],[f11])).
% 0.19/0.47  fof(f83,plain,(
% 0.19/0.47    v2_struct_0(sK1) | v2_struct_0(sK0) | u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,u1_struct_0(sK1))),
% 0.19/0.47    inference(subsumption_resolution,[],[f82,f29])).
% 0.19/0.47  fof(f82,plain,(
% 0.19/0.47    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,u1_struct_0(sK1))),
% 0.19/0.47    inference(subsumption_resolution,[],[f80,f28])).
% 0.19/0.47  fof(f80,plain,(
% 0.19/0.47    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,u1_struct_0(sK1))),
% 0.19/0.47    inference(resolution,[],[f44,f26])).
% 0.19/0.47  fof(f44,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | v2_struct_0(X0) | u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,u1_struct_0(X1))) )),
% 0.19/0.47    inference(subsumption_resolution,[],[f40,f30])).
% 0.19/0.47  fof(f40,plain,(
% 0.19/0.47    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,u1_struct_0(X1))) )),
% 0.19/0.47    inference(equality_resolution,[],[f34])).
% 0.19/0.47  fof(f34,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f17])).
% 0.19/0.47  fof(f17,plain,(
% 0.19/0.47    ! [X0] : (! [X1] : ((! [X2] : (u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.47    inference(flattening,[],[f16])).
% 0.19/0.47  fof(f16,plain,(
% 0.19/0.47    ! [X0] : (! [X1] : ((! [X2] : ((u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.19/0.47    inference(ennf_transformation,[],[f4])).
% 0.19/0.47  fof(f4,axiom,(
% 0.19/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2))) & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)))))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_tmap_1)).
% 0.19/0.47  fof(f94,plain,(
% 0.19/0.47    r2_hidden(u1_struct_0(sK1),k5_tmap_1(sK0,u1_struct_0(sK1)))),
% 0.19/0.47    inference(subsumption_resolution,[],[f93,f27])).
% 0.19/0.47  fof(f93,plain,(
% 0.19/0.47    v2_struct_0(sK0) | r2_hidden(u1_struct_0(sK1),k5_tmap_1(sK0,u1_struct_0(sK1)))),
% 0.19/0.47    inference(subsumption_resolution,[],[f92,f29])).
% 0.19/0.47  fof(f92,plain,(
% 0.19/0.47    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | r2_hidden(u1_struct_0(sK1),k5_tmap_1(sK0,u1_struct_0(sK1)))),
% 0.19/0.47    inference(subsumption_resolution,[],[f89,f28])).
% 0.19/0.47  % (27591)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.19/0.47  fof(f89,plain,(
% 0.19/0.47    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | r2_hidden(u1_struct_0(sK1),k5_tmap_1(sK0,u1_struct_0(sK1)))),
% 0.19/0.47    inference(resolution,[],[f49,f33])).
% 0.19/0.47  fof(f33,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | r2_hidden(X1,k5_tmap_1(X0,X1))) )),
% 0.19/0.47    inference(cnf_transformation,[],[f15])).
% 0.19/0.47  fof(f15,plain,(
% 0.19/0.47    ! [X0] : (! [X1] : (r2_hidden(X1,k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.47    inference(flattening,[],[f14])).
% 0.19/0.47  fof(f14,plain,(
% 0.19/0.47    ! [X0] : (! [X1] : (r2_hidden(X1,k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.19/0.47    inference(ennf_transformation,[],[f3])).
% 0.19/0.47  fof(f3,axiom,(
% 0.19/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r2_hidden(X1,k5_tmap_1(X0,X1))))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_tmap_1)).
% 0.19/0.47  fof(f105,plain,(
% 0.19/0.47    ( ! [X3] : (~r2_hidden(X3,u1_pre_topc(k8_tmap_1(sK0,sK1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(X3,k8_tmap_1(sK0,sK1))) )),
% 0.19/0.47    inference(subsumption_resolution,[],[f101,f61])).
% 0.19/0.47  fof(f101,plain,(
% 0.19/0.47    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(k8_tmap_1(sK0,sK1)) | ~r2_hidden(X3,u1_pre_topc(k8_tmap_1(sK0,sK1))) | v3_pre_topc(X3,k8_tmap_1(sK0,sK1))) )),
% 0.19/0.47    inference(superposition,[],[f31,f75])).
% 0.19/0.47  fof(f75,plain,(
% 0.19/0.47    u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1))),
% 0.19/0.47    inference(subsumption_resolution,[],[f74,f27])).
% 0.19/0.47  fof(f74,plain,(
% 0.19/0.47    v2_struct_0(sK0) | u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1))),
% 0.19/0.47    inference(subsumption_resolution,[],[f73,f25])).
% 0.19/0.47  fof(f73,plain,(
% 0.19/0.47    v2_struct_0(sK1) | v2_struct_0(sK0) | u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1))),
% 0.19/0.47    inference(subsumption_resolution,[],[f72,f29])).
% 0.19/0.47  fof(f72,plain,(
% 0.19/0.47    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1))),
% 0.19/0.47    inference(subsumption_resolution,[],[f70,f28])).
% 0.19/0.47  fof(f70,plain,(
% 0.19/0.47    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1))),
% 0.19/0.47    inference(resolution,[],[f35,f26])).
% 0.19/0.47  fof(f35,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | v2_struct_0(X0) | u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1))) )),
% 0.19/0.47    inference(cnf_transformation,[],[f17])).
% 0.19/0.47  fof(f31,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | v3_pre_topc(X1,X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f13])).
% 0.19/0.47  fof(f13,plain,(
% 0.19/0.47    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.47    inference(ennf_transformation,[],[f1])).
% 0.19/0.47  fof(f1,axiom,(
% 0.19/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).
% 0.19/0.47  % SZS output end Proof for theBenchmark
% 0.19/0.47  % (27597)------------------------------
% 0.19/0.47  % (27597)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.47  % (27597)Termination reason: Refutation
% 0.19/0.47  
% 0.19/0.47  % (27597)Memory used [KB]: 1663
% 0.19/0.47  % (27597)Time elapsed: 0.060 s
% 0.19/0.47  % (27597)------------------------------
% 0.19/0.47  % (27597)------------------------------
% 0.19/0.47  % (27579)Success in time 0.117 s
%------------------------------------------------------------------------------
