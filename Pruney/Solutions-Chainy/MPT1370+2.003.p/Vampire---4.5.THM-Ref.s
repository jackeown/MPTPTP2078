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
% DateTime   : Thu Dec  3 13:14:50 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 403 expanded)
%              Number of leaves         :   11 (  83 expanded)
%              Depth                    :   22
%              Number of atoms          :  336 (2897 expanded)
%              Number of equality atoms :   24 ( 260 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f201,plain,(
    $false ),
    inference(global_subsumption,[],[f33,f41,f199])).

% (5759)Refutation not found, incomplete strategy% (5759)------------------------------
% (5759)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f199,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v1_compts_1(sK0) ),
    inference(resolution,[],[f198,f47])).

fof(f47,plain,(
    ! [X0] :
      ( v2_compts_1(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v1_compts_1(X0)
      <=> v2_compts_1(k2_struct_0(X0),X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_compts_1(X0)
      <=> v2_compts_1(k2_struct_0(X0),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_compts_1)).

fof(f198,plain,(
    ~ v2_compts_1(k2_struct_0(sK0),sK0) ),
    inference(global_subsumption,[],[f76,f195])).

fof(f195,plain,
    ( ~ v2_compts_1(k2_struct_0(sK0),sK0)
    | ~ r1_tarski(sK3,k2_struct_0(sK0)) ),
    inference(resolution,[],[f194,f53])).

fof(f53,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f43,f42])).

fof(f42,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f43,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f194,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v2_compts_1(X0,sK0)
      | ~ r1_tarski(sK3,X0) ) ),
    inference(global_subsumption,[],[f40,f41,f28,f75,f193])).

fof(f193,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_compts_1(X0,sK0)
      | ~ r1_tarski(sK3,X0)
      | ~ v4_pre_topc(sK3,sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(forward_demodulation,[],[f192,f65])).

fof(f65,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f54,f41])).

fof(f54,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(resolution,[],[f44,f45])).

fof(f45,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f44,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f192,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_compts_1(X0,sK0)
      | ~ r1_tarski(sK3,X0)
      | ~ v4_pre_topc(sK3,sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(forward_demodulation,[],[f191,f65])).

fof(f191,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_compts_1(X0,sK0)
      | ~ r1_tarski(sK3,X0)
      | ~ v4_pre_topc(sK3,sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f190,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v2_compts_1(X2,X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_compts_1(X1,X0)
      | ~ r1_tarski(X2,X1)
      | ~ v4_pre_topc(X2,X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_compts_1(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ r1_tarski(X2,X1)
              | ~ v2_compts_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_compts_1(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ r1_tarski(X2,X1)
              | ~ v2_compts_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v4_pre_topc(X2,X0)
                  & r1_tarski(X2,X1)
                  & v2_compts_1(X1,X0) )
               => v2_compts_1(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_compts_1)).

fof(f190,plain,(
    ~ v2_compts_1(sK3,sK0) ),
    inference(global_subsumption,[],[f75,f189])).

fof(f189,plain,
    ( ~ v2_compts_1(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(resolution,[],[f188,f172])).

fof(f172,plain,(
    ~ v2_compts_1(k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK3),sK1) ),
    inference(global_subsumption,[],[f88,f171])).

fof(f171,plain,
    ( ~ v2_compts_1(k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK3),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(resolution,[],[f157,f92])).

fof(f92,plain,(
    ~ v4_pre_topc(k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK3),sK1) ),
    inference(forward_demodulation,[],[f70,f65])).

fof(f70,plain,(
    ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,sK3),sK1) ),
    inference(backward_demodulation,[],[f29,f64])).

fof(f64,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(resolution,[],[f54,f39])).

fof(f39,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                  & v4_pre_topc(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & v5_pre_topc(X2,X0,X1)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & v8_pre_topc(X1)
              & v1_compts_1(X0)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                  & v4_pre_topc(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & v5_pre_topc(X2,X0,X1)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & v8_pre_topc(X1)
              & v1_compts_1(X0)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( v5_pre_topc(X2,X0,X1)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                    & v8_pre_topc(X1)
                    & v1_compts_1(X0) )
                 => ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ( v4_pre_topc(X3,X0)
                       => v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v5_pre_topc(X2,X0,X1)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & v8_pre_topc(X1)
                  & v1_compts_1(X0) )
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( v4_pre_topc(X3,X0)
                     => v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_compts_1)).

fof(f29,plain,(
    ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f157,plain,(
    ! [X2,X0,X1] :
      ( v4_pre_topc(k7_relset_1(X0,k2_struct_0(sK1),X1,X2),sK1)
      | ~ v2_compts_1(k7_relset_1(X0,k2_struct_0(sK1),X1,X2),sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k2_struct_0(sK1)))) ) ),
    inference(global_subsumption,[],[f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_compts_1(k7_relset_1(X0,k2_struct_0(sK1),X1,X2),sK1)
      | v4_pre_topc(k7_relset_1(X0,k2_struct_0(sK1),X1,X2),sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k2_struct_0(sK1)))) ) ),
    inference(resolution,[],[f74,f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).

fof(f74,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1)))
      | ~ v2_compts_1(X0,sK1)
      | v4_pre_topc(X0,sK1) ) ),
    inference(global_subsumption,[],[f34,f38,f39,f73])).

fof(f73,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1)))
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ v8_pre_topc(sK1)
      | ~ v2_compts_1(X0,sK1)
      | v4_pre_topc(X0,sK1) ) ),
    inference(superposition,[],[f49,f64])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_compts_1(X1,X0)
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v2_compts_1(X1,X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v2_compts_1(X1,X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_compts_1(X1,X0)
              & v8_pre_topc(X0) )
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_compts_1)).

fof(f38,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f34,plain,(
    v8_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f88,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(forward_demodulation,[],[f71,f65])).

fof(f71,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f32,f64])).

fof(f32,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f15])).

fof(f188,plain,(
    ! [X0] :
      ( v2_compts_1(k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0),sK1)
      | ~ v2_compts_1(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(global_subsumption,[],[f30,f36,f77,f88,f187])).

fof(f187,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | ~ v2_compts_1(X0,sK0)
      | v2_compts_1(k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0),sK1) ) ),
    inference(trivial_inequality_removal,[],[f186])).

fof(f186,plain,(
    ! [X0] :
      ( k2_struct_0(sK1) != k2_struct_0(sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | ~ v2_compts_1(X0,sK0)
      | v2_compts_1(k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0),sK1) ) ),
    inference(superposition,[],[f178,f91])).

fof(f91,plain,(
    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(forward_demodulation,[],[f69,f65])).

fof(f69,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(backward_demodulation,[],[f35,f64])).

fof(f35,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f178,plain,(
    ! [X2,X3] :
      ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,k2_struct_0(sK0),k2_struct_0(sK1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
      | ~ v5_pre_topc(X2,sK0,sK1)
      | ~ v2_compts_1(X3,sK0)
      | v2_compts_1(k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X2,X3),sK1) ) ),
    inference(global_subsumption,[],[f41,f176])).

fof(f176,plain,(
    ! [X2,X3] :
      ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,k2_struct_0(sK0),k2_struct_0(sK1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
      | ~ v5_pre_topc(X2,sK0,sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_compts_1(X3,sK0)
      | v2_compts_1(k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X2,X3),sK1) ) ),
    inference(superposition,[],[f99,f65])).

% (5759)Termination reason: Refutation not found, incomplete strategy
fof(f99,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(sK1) != k2_relset_1(u1_struct_0(X0),k2_struct_0(sK1),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(X0),k2_struct_0(sK1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),k2_struct_0(sK1))))
      | ~ v5_pre_topc(X1,X0,sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_compts_1(X2,X0)
      | v2_compts_1(k7_relset_1(u1_struct_0(X0),k2_struct_0(sK1),X1,X2),sK1) ) ),
    inference(global_subsumption,[],[f37,f39,f95])).

% (5759)Memory used [KB]: 6140
% (5759)Time elapsed: 0.057 s
% (5759)------------------------------
% (5759)------------------------------
fof(f95,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(sK1) != k2_relset_1(u1_struct_0(X0),k2_struct_0(sK1),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(X0),k2_struct_0(sK1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),k2_struct_0(sK1))))
      | ~ v5_pre_topc(X1,X0,sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_compts_1(X2,X0)
      | v2_compts_1(k7_relset_1(u1_struct_0(X0),k2_struct_0(sK1),X1,X2),sK1) ) ),
    inference(superposition,[],[f48,f64])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3) != k2_struct_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X2)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
      | ~ v5_pre_topc(X3,X0,X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_compts_1(X1,X0)
      | v2_compts_1(k7_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3,X1),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v2_compts_1(k7_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3,X1),X2)
                  | ~ v2_compts_1(X1,X0)
                  | k2_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3) != k2_struct_0(X2)
                  | ~ v5_pre_topc(X3,X0,X2)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                  | ~ v1_funct_1(X3) )
              | ~ l1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v2_compts_1(k7_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3,X1),X2)
                  | ~ v2_compts_1(X1,X0)
                  | k2_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3) != k2_struct_0(X2)
                  | ~ v5_pre_topc(X3,X0,X2)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                  | ~ v1_funct_1(X3) )
              | ~ l1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                    & v1_funct_1(X3) )
                 => ( ( v2_compts_1(X1,X0)
                      & k2_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3) = k2_struct_0(X2)
                      & v5_pre_topc(X3,X0,X2) )
                   => v2_compts_1(k7_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3,X1),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_compts_1)).

fof(f37,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f77,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f72,f65])).

fof(f72,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f31,f64])).

fof(f31,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f36,plain,(
    v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f30,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f75,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f27,f65])).

fof(f27,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f28,plain,(
    v4_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f40,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f76,plain,(
    r1_tarski(sK3,k2_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f55,f65])).

fof(f55,plain,(
    r1_tarski(sK3,u1_struct_0(sK0)) ),
    inference(resolution,[],[f51,f27])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f41,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f33,plain,(
    v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:31:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.44  % (5751)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.45  % (5759)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.20/0.46  % (5751)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f201,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(global_subsumption,[],[f33,f41,f199])).
% 0.20/0.46  % (5759)Refutation not found, incomplete strategy% (5759)------------------------------
% 0.20/0.46  % (5759)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  fof(f199,plain,(
% 0.20/0.46    ~l1_pre_topc(sK0) | ~v1_compts_1(sK0)),
% 0.20/0.46    inference(resolution,[],[f198,f47])).
% 0.20/0.46  fof(f47,plain,(
% 0.20/0.46    ( ! [X0] : (v2_compts_1(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v1_compts_1(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f18])).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    ! [X0] : ((v1_compts_1(X0) <=> v2_compts_1(k2_struct_0(X0),X0)) | ~l1_pre_topc(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f7])).
% 0.20/0.46  fof(f7,axiom,(
% 0.20/0.46    ! [X0] : (l1_pre_topc(X0) => (v1_compts_1(X0) <=> v2_compts_1(k2_struct_0(X0),X0)))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_compts_1)).
% 0.20/0.46  fof(f198,plain,(
% 0.20/0.46    ~v2_compts_1(k2_struct_0(sK0),sK0)),
% 0.20/0.46    inference(global_subsumption,[],[f76,f195])).
% 0.20/0.46  fof(f195,plain,(
% 0.20/0.46    ~v2_compts_1(k2_struct_0(sK0),sK0) | ~r1_tarski(sK3,k2_struct_0(sK0))),
% 0.20/0.46    inference(resolution,[],[f194,f53])).
% 0.20/0.46  fof(f53,plain,(
% 0.20/0.46    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.20/0.46    inference(forward_demodulation,[],[f43,f42])).
% 0.20/0.46  fof(f42,plain,(
% 0.20/0.46    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.20/0.46    inference(cnf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0] : k2_subset_1(X0) = X0),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.20/0.46  fof(f43,plain,(
% 0.20/0.46    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.20/0.46  fof(f194,plain,(
% 0.20/0.46    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v2_compts_1(X0,sK0) | ~r1_tarski(sK3,X0)) )),
% 0.20/0.46    inference(global_subsumption,[],[f40,f41,f28,f75,f193])).
% 0.20/0.46  fof(f193,plain,(
% 0.20/0.46    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_compts_1(X0,sK0) | ~r1_tarski(sK3,X0) | ~v4_pre_topc(sK3,sK0) | ~v2_pre_topc(sK0)) )),
% 0.20/0.46    inference(forward_demodulation,[],[f192,f65])).
% 0.20/0.46  fof(f65,plain,(
% 0.20/0.46    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.20/0.46    inference(resolution,[],[f54,f41])).
% 0.20/0.46  fof(f54,plain,(
% 0.20/0.46    ( ! [X0] : (~l1_pre_topc(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.20/0.46    inference(resolution,[],[f44,f45])).
% 0.20/0.46  fof(f45,plain,(
% 0.20/0.46    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f17])).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f6])).
% 0.20/0.46  fof(f6,axiom,(
% 0.20/0.46    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.46  fof(f44,plain,(
% 0.20/0.46    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f16])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f5])).
% 0.20/0.46  fof(f5,axiom,(
% 0.20/0.46    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.46  fof(f192,plain,(
% 0.20/0.46    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_compts_1(X0,sK0) | ~r1_tarski(sK3,X0) | ~v4_pre_topc(sK3,sK0) | ~v2_pre_topc(sK0)) )),
% 0.20/0.46    inference(forward_demodulation,[],[f191,f65])).
% 0.20/0.46  fof(f191,plain,(
% 0.20/0.46    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_compts_1(X0,sK0) | ~r1_tarski(sK3,X0) | ~v4_pre_topc(sK3,sK0) | ~v2_pre_topc(sK0)) )),
% 0.20/0.46    inference(resolution,[],[f190,f50])).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (v2_compts_1(X2,X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_compts_1(X1,X0) | ~r1_tarski(X2,X1) | ~v4_pre_topc(X2,X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f24])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : (v2_compts_1(X2,X0) | ~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.47    inference(flattening,[],[f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : ((v2_compts_1(X2,X0) | (~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,axiom,(
% 0.20/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0)) => v2_compts_1(X2,X0)))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_compts_1)).
% 0.20/0.47  fof(f190,plain,(
% 0.20/0.47    ~v2_compts_1(sK3,sK0)),
% 0.20/0.47    inference(global_subsumption,[],[f75,f189])).
% 0.20/0.47  fof(f189,plain,(
% 0.20/0.47    ~v2_compts_1(sK3,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.20/0.47    inference(resolution,[],[f188,f172])).
% 0.20/0.47  fof(f172,plain,(
% 0.20/0.47    ~v2_compts_1(k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK3),sK1)),
% 0.20/0.47    inference(global_subsumption,[],[f88,f171])).
% 0.20/0.47  fof(f171,plain,(
% 0.20/0.47    ~v2_compts_1(k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK3),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.20/0.47    inference(resolution,[],[f157,f92])).
% 0.20/0.47  fof(f92,plain,(
% 0.20/0.47    ~v4_pre_topc(k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK3),sK1)),
% 0.20/0.47    inference(forward_demodulation,[],[f70,f65])).
% 0.20/0.47  fof(f70,plain,(
% 0.20/0.47    ~v4_pre_topc(k7_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,sK3),sK1)),
% 0.20/0.47    inference(backward_demodulation,[],[f29,f64])).
% 0.20/0.47  fof(f64,plain,(
% 0.20/0.47    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.20/0.47    inference(resolution,[],[f54,f39])).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    l1_pre_topc(sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v5_pre_topc(X2,X0,X1) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & v8_pre_topc(X1) & v1_compts_1(X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.47    inference(flattening,[],[f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : ((~v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) & v4_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & (v5_pre_topc(X2,X0,X1) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & v8_pre_topc(X1) & v1_compts_1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,negated_conjecture,(
% 0.20/0.47    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v5_pre_topc(X2,X0,X1) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & v8_pre_topc(X1) & v1_compts_1(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X3,X0) => v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)))))))),
% 0.20/0.47    inference(negated_conjecture,[],[f11])).
% 0.20/0.47  fof(f11,conjecture,(
% 0.20/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v5_pre_topc(X2,X0,X1) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & v8_pre_topc(X1) & v1_compts_1(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X3,X0) => v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)))))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_compts_1)).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ~v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f15])).
% 0.20/0.47  fof(f157,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (v4_pre_topc(k7_relset_1(X0,k2_struct_0(sK1),X1,X2),sK1) | ~v2_compts_1(k7_relset_1(X0,k2_struct_0(sK1),X1,X2),sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k2_struct_0(sK1))))) )),
% 0.20/0.47    inference(global_subsumption,[],[f109])).
% 0.20/0.47  fof(f109,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~v2_compts_1(k7_relset_1(X0,k2_struct_0(sK1),X1,X2),sK1) | v4_pre_topc(k7_relset_1(X0,k2_struct_0(sK1),X1,X2),sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k2_struct_0(sK1))))) )),
% 0.20/0.47    inference(resolution,[],[f74,f52])).
% 0.20/0.47  fof(f52,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f26])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(ennf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).
% 0.20/0.47  fof(f74,plain,(
% 0.20/0.47    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) | ~v2_compts_1(X0,sK1) | v4_pre_topc(X0,sK1)) )),
% 0.20/0.47    inference(global_subsumption,[],[f34,f38,f39,f73])).
% 0.20/0.47  fof(f73,plain,(
% 0.20/0.47    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~v8_pre_topc(sK1) | ~v2_compts_1(X0,sK1) | v4_pre_topc(X0,sK1)) )),
% 0.20/0.47    inference(superposition,[],[f49,f64])).
% 0.20/0.47  fof(f49,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~v8_pre_topc(X0) | ~v2_compts_1(X1,X0) | v4_pre_topc(X1,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v2_compts_1(X1,X0) | ~v8_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.47    inference(flattening,[],[f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | (~v2_compts_1(X1,X0) | ~v8_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,axiom,(
% 0.20/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v4_pre_topc(X1,X0))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_compts_1)).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    v2_pre_topc(sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f15])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    v8_pre_topc(sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f15])).
% 0.20/0.47  fof(f88,plain,(
% 0.20/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.20/0.47    inference(forward_demodulation,[],[f71,f65])).
% 0.20/0.47  fof(f71,plain,(
% 0.20/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))),
% 0.20/0.47    inference(backward_demodulation,[],[f32,f64])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.20/0.47    inference(cnf_transformation,[],[f15])).
% 0.20/0.47  fof(f188,plain,(
% 0.20/0.47    ( ! [X0] : (v2_compts_1(k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0),sK1) | ~v2_compts_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 0.20/0.47    inference(global_subsumption,[],[f30,f36,f77,f88,f187])).
% 0.20/0.47  fof(f187,plain,(
% 0.20/0.47    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v5_pre_topc(sK2,sK0,sK1) | ~v2_compts_1(X0,sK0) | v2_compts_1(k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0),sK1)) )),
% 0.20/0.47    inference(trivial_inequality_removal,[],[f186])).
% 0.20/0.47  fof(f186,plain,(
% 0.20/0.47    ( ! [X0] : (k2_struct_0(sK1) != k2_struct_0(sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v5_pre_topc(sK2,sK0,sK1) | ~v2_compts_1(X0,sK0) | v2_compts_1(k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0),sK1)) )),
% 0.20/0.47    inference(superposition,[],[f178,f91])).
% 0.20/0.47  fof(f91,plain,(
% 0.20/0.47    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.20/0.47    inference(forward_demodulation,[],[f69,f65])).
% 0.20/0.47  fof(f69,plain,(
% 0.20/0.47    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.20/0.47    inference(backward_demodulation,[],[f35,f64])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f15])).
% 0.20/0.47  fof(f178,plain,(
% 0.20/0.47    ( ! [X2,X3] : (k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v5_pre_topc(X2,sK0,sK1) | ~v2_compts_1(X3,sK0) | v2_compts_1(k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X2,X3),sK1)) )),
% 0.20/0.47    inference(global_subsumption,[],[f41,f176])).
% 0.20/0.47  fof(f176,plain,(
% 0.20/0.47    ( ! [X2,X3] : (k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v5_pre_topc(X2,sK0,sK1) | ~l1_pre_topc(sK0) | ~v2_compts_1(X3,sK0) | v2_compts_1(k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X2,X3),sK1)) )),
% 0.20/0.47    inference(superposition,[],[f99,f65])).
% 0.20/0.47  % (5759)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  fof(f99,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k2_struct_0(sK1) != k2_relset_1(u1_struct_0(X0),k2_struct_0(sK1),X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),k2_struct_0(sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),k2_struct_0(sK1)))) | ~v5_pre_topc(X1,X0,sK1) | ~l1_pre_topc(X0) | ~v2_compts_1(X2,X0) | v2_compts_1(k7_relset_1(u1_struct_0(X0),k2_struct_0(sK1),X1,X2),sK1)) )),
% 0.20/0.47    inference(global_subsumption,[],[f37,f39,f95])).
% 0.20/0.47  
% 0.20/0.47  % (5759)Memory used [KB]: 6140
% 0.20/0.47  % (5759)Time elapsed: 0.057 s
% 0.20/0.47  % (5759)------------------------------
% 0.20/0.47  % (5759)------------------------------
% 0.20/0.47  fof(f95,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k2_struct_0(sK1) != k2_relset_1(u1_struct_0(X0),k2_struct_0(sK1),X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),k2_struct_0(sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),k2_struct_0(sK1)))) | ~v5_pre_topc(X1,X0,sK1) | ~l1_pre_topc(X0) | ~v2_compts_1(X2,X0) | v2_compts_1(k7_relset_1(u1_struct_0(X0),k2_struct_0(sK1),X1,X2),sK1)) )),
% 0.20/0.47    inference(superposition,[],[f48,f64])).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (k2_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3) != k2_struct_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X2) | ~l1_pre_topc(X2) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) | ~v5_pre_topc(X3,X0,X2) | ~l1_pre_topc(X0) | ~v2_compts_1(X1,X0) | v2_compts_1(k7_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3,X1),X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v2_compts_1(k7_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3,X1),X2) | ~v2_compts_1(X1,X0) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3) != k2_struct_0(X2) | ~v5_pre_topc(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2)) | ~v1_funct_1(X3)) | ~l1_pre_topc(X2) | v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.47    inference(flattening,[],[f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v2_compts_1(k7_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3,X1),X2) | (~v2_compts_1(X1,X0) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3) != k2_struct_0(X2) | ~v5_pre_topc(X3,X0,X2))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2)) | ~v1_funct_1(X3))) | (~l1_pre_topc(X2) | v2_struct_0(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,axiom,(
% 0.20/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((l1_pre_topc(X2) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2)) & v1_funct_1(X3)) => ((v2_compts_1(X1,X0) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3) = k2_struct_0(X2) & v5_pre_topc(X3,X0,X2)) => v2_compts_1(k7_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3,X1),X2))))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_compts_1)).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    ~v2_struct_0(sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f15])).
% 0.20/0.47  fof(f77,plain,(
% 0.20/0.47    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.20/0.47    inference(backward_demodulation,[],[f72,f65])).
% 0.20/0.47  fof(f72,plain,(
% 0.20/0.47    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))),
% 0.20/0.47    inference(backward_demodulation,[],[f31,f64])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.20/0.47    inference(cnf_transformation,[],[f15])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    v5_pre_topc(sK2,sK0,sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f15])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    v1_funct_1(sK2)),
% 0.20/0.47    inference(cnf_transformation,[],[f15])).
% 0.20/0.47  fof(f75,plain,(
% 0.20/0.47    m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.20/0.47    inference(backward_demodulation,[],[f27,f65])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.47    inference(cnf_transformation,[],[f15])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    v4_pre_topc(sK3,sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f15])).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    v2_pre_topc(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f15])).
% 0.20/0.47  fof(f76,plain,(
% 0.20/0.47    r1_tarski(sK3,k2_struct_0(sK0))),
% 0.20/0.47    inference(backward_demodulation,[],[f55,f65])).
% 0.20/0.47  fof(f55,plain,(
% 0.20/0.47    r1_tarski(sK3,u1_struct_0(sK0))),
% 0.20/0.47    inference(resolution,[],[f51,f27])).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.20/0.47    inference(ennf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 0.20/0.47    inference(unused_predicate_definition_removal,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    l1_pre_topc(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f15])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    v1_compts_1(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f15])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (5751)------------------------------
% 0.20/0.47  % (5751)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (5751)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (5751)Memory used [KB]: 10874
% 0.20/0.47  % (5751)Time elapsed: 0.067 s
% 0.20/0.47  % (5751)------------------------------
% 0.20/0.47  % (5751)------------------------------
% 0.20/0.47  % (5738)Success in time 0.119 s
%------------------------------------------------------------------------------
