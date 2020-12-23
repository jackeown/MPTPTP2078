%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:26 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 245 expanded)
%              Number of leaves         :    3 (  42 expanded)
%              Depth                    :   21
%              Number of atoms          :  308 (1449 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f69,plain,(
    $false ),
    inference(subsumption_resolution,[],[f68,f13])).

fof(f13,plain,(
    ~ r1_borsuk_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_borsuk_1(X0,X1)
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_borsuk_1(X0,X1)
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => r1_borsuk_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => r1_borsuk_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_tex_2)).

fof(f68,plain,(
    r1_borsuk_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f67,f46])).

fof(f46,plain,(
    v3_borsuk_1(sK2(sK0,sK1),sK0,sK1) ),
    inference(subsumption_resolution,[],[f45,f14])).

fof(f14,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f45,plain,
    ( v2_struct_0(sK0)
    | v3_borsuk_1(sK2(sK0,sK1),sK0,sK1) ),
    inference(subsumption_resolution,[],[f44,f11])).

fof(f11,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f44,plain,
    ( v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | v3_borsuk_1(sK2(sK0,sK1),sK0,sK1) ),
    inference(subsumption_resolution,[],[f43,f17])).

fof(f17,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f43,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | v3_borsuk_1(sK2(sK0,sK1),sK0,sK1) ),
    inference(subsumption_resolution,[],[f42,f16])).

fof(f16,plain,(
    v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f42,plain,
    ( ~ v1_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | v3_borsuk_1(sK2(sK0,sK1),sK0,sK1) ),
    inference(subsumption_resolution,[],[f41,f15])).

fof(f15,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f41,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ v1_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | v3_borsuk_1(sK2(sK0,sK1),sK0,sK1) ),
    inference(resolution,[],[f22,f12])).

fof(f12,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | v3_borsuk_1(sK2(X0,X1),X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( v3_borsuk_1(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v5_pre_topc(X2,X0,X1)
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( v3_borsuk_1(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v5_pre_topc(X2,X0,X1)
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ? [X2] :
              ( v3_borsuk_1(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v5_pre_topc(X2,X0,X1)
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_tex_2)).

fof(f67,plain,
    ( ~ v3_borsuk_1(sK2(sK0,sK1),sK0,sK1)
    | r1_borsuk_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f66,f14])).

fof(f66,plain,
    ( v2_struct_0(sK0)
    | ~ v3_borsuk_1(sK2(sK0,sK1),sK0,sK1)
    | r1_borsuk_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f65,f40])).

fof(f40,plain,(
    v5_pre_topc(sK2(sK0,sK1),sK0,sK1) ),
    inference(subsumption_resolution,[],[f39,f14])).

fof(f39,plain,
    ( v2_struct_0(sK0)
    | v5_pre_topc(sK2(sK0,sK1),sK0,sK1) ),
    inference(subsumption_resolution,[],[f38,f11])).

fof(f38,plain,
    ( v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | v5_pre_topc(sK2(sK0,sK1),sK0,sK1) ),
    inference(subsumption_resolution,[],[f37,f17])).

fof(f37,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | v5_pre_topc(sK2(sK0,sK1),sK0,sK1) ),
    inference(subsumption_resolution,[],[f36,f16])).

fof(f36,plain,
    ( ~ v1_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | v5_pre_topc(sK2(sK0,sK1),sK0,sK1) ),
    inference(subsumption_resolution,[],[f35,f15])).

fof(f35,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ v1_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | v5_pre_topc(sK2(sK0,sK1),sK0,sK1) ),
    inference(resolution,[],[f20,f12])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | v5_pre_topc(sK2(X0,X1),X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f65,plain,
    ( ~ v5_pre_topc(sK2(sK0,sK1),sK0,sK1)
    | v2_struct_0(sK0)
    | ~ v3_borsuk_1(sK2(sK0,sK1),sK0,sK1)
    | r1_borsuk_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f64,f52])).

fof(f52,plain,(
    v1_funct_2(sK2(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f51,f14])).

fof(f51,plain,
    ( v2_struct_0(sK0)
    | v1_funct_2(sK2(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f50,f11])).

fof(f50,plain,
    ( v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | v1_funct_2(sK2(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f49,f17])).

fof(f49,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | v1_funct_2(sK2(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f48,f16])).

fof(f48,plain,
    ( ~ v1_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | v1_funct_2(sK2(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f47,f15])).

fof(f47,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ v1_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | v1_funct_2(sK2(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(resolution,[],[f19,f12])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | v1_funct_2(sK2(X0,X1),u1_struct_0(X0),u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f64,plain,
    ( ~ v1_funct_2(sK2(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2(sK0,sK1),sK0,sK1)
    | v2_struct_0(sK0)
    | ~ v3_borsuk_1(sK2(sK0,sK1),sK0,sK1)
    | r1_borsuk_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f63,f34])).

fof(f34,plain,(
    v1_funct_1(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f33,f14])).

fof(f33,plain,
    ( v2_struct_0(sK0)
    | v1_funct_1(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f32,f11])).

fof(f32,plain,
    ( v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | v1_funct_1(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f31,f17])).

fof(f31,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | v1_funct_1(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f30,f16])).

fof(f30,plain,
    ( ~ v1_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | v1_funct_1(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f29,f15])).

fof(f29,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ v1_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | v1_funct_1(sK2(sK0,sK1)) ),
    inference(resolution,[],[f18,f12])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | v1_funct_1(sK2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f63,plain,
    ( ~ v1_funct_1(sK2(sK0,sK1))
    | ~ v1_funct_2(sK2(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2(sK0,sK1),sK0,sK1)
    | v2_struct_0(sK0)
    | ~ v3_borsuk_1(sK2(sK0,sK1),sK0,sK1)
    | r1_borsuk_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f62,f12])).

fof(f62,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ v1_funct_1(sK2(sK0,sK1))
    | ~ v1_funct_2(sK2(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2(sK0,sK1),sK0,sK1)
    | v2_struct_0(sK0)
    | ~ v3_borsuk_1(sK2(sK0,sK1),sK0,sK1)
    | r1_borsuk_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f61,f11])).

fof(f61,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v1_funct_1(sK2(sK0,sK1))
    | ~ v1_funct_2(sK2(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2(sK0,sK1),sK0,sK1)
    | v2_struct_0(sK0)
    | ~ v3_borsuk_1(sK2(sK0,sK1),sK0,sK1)
    | r1_borsuk_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f60,f17])).

fof(f60,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v1_funct_1(sK2(sK0,sK1))
    | ~ v1_funct_2(sK2(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2(sK0,sK1),sK0,sK1)
    | v2_struct_0(sK0)
    | ~ v3_borsuk_1(sK2(sK0,sK1),sK0,sK1)
    | r1_borsuk_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f59,f15])).

fof(f59,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v1_funct_1(sK2(sK0,sK1))
    | ~ v1_funct_2(sK2(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2(sK0,sK1),sK0,sK1)
    | v2_struct_0(sK0)
    | ~ v3_borsuk_1(sK2(sK0,sK1),sK0,sK1)
    | r1_borsuk_1(sK0,sK1) ),
    inference(resolution,[],[f28,f58])).

fof(f58,plain,(
    m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f57,f14])).

fof(f57,plain,
    ( v2_struct_0(sK0)
    | m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f56,f11])).

fof(f56,plain,
    ( v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f55,f17])).

fof(f55,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f54,f16])).

fof(f54,plain,
    ( ~ v1_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f53,f15])).

fof(f53,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ v1_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(resolution,[],[f21,f12])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v5_pre_topc(X2,X0,X1)
      | v2_struct_0(X0)
      | ~ v3_borsuk_1(X2,X0,X1)
      | r1_borsuk_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_borsuk_1(X0,X1)
          <=> ? [X2] :
                ( v3_borsuk_1(X2,X0,X1)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v5_pre_topc(X2,X0,X1)
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) ) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_borsuk_1(X0,X1)
          <=> ? [X2] :
                ( v3_borsuk_1(X2,X0,X1)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v5_pre_topc(X2,X0,X1)
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) ) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ( r1_borsuk_1(X0,X1)
          <=> ? [X2] :
                ( v3_borsuk_1(X2,X0,X1)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v5_pre_topc(X2,X0,X1)
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_borsuk_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:17:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (12561)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.21/0.47  % (12563)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (12560)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.48  % (12569)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.21/0.48  % (12561)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(subsumption_resolution,[],[f68,f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ~r1_borsuk_1(sK0,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (~r1_borsuk_1(X0,X1) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f5])).
% 0.21/0.48  fof(f5,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (~r1_borsuk_1(X0,X1) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => r1_borsuk_1(X0,X1)))),
% 0.21/0.48    inference(negated_conjecture,[],[f3])).
% 0.21/0.48  fof(f3,conjecture,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => r1_borsuk_1(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_tex_2)).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    r1_borsuk_1(sK0,sK1)),
% 0.21/0.48    inference(subsumption_resolution,[],[f67,f46])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    v3_borsuk_1(sK2(sK0,sK1),sK0,sK1)),
% 0.21/0.48    inference(subsumption_resolution,[],[f45,f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ~v2_struct_0(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    v2_struct_0(sK0) | v3_borsuk_1(sK2(sK0,sK1),sK0,sK1)),
% 0.21/0.48    inference(subsumption_resolution,[],[f44,f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ~v2_struct_0(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    v2_struct_0(sK1) | v2_struct_0(sK0) | v3_borsuk_1(sK2(sK0,sK1),sK0,sK1)),
% 0.21/0.48    inference(subsumption_resolution,[],[f43,f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    l1_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | v3_borsuk_1(sK2(sK0,sK1),sK0,sK1)),
% 0.21/0.48    inference(subsumption_resolution,[],[f42,f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    v1_tdlat_3(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ~v1_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | v3_borsuk_1(sK2(sK0,sK1),sK0,sK1)),
% 0.21/0.48    inference(subsumption_resolution,[],[f41,f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    v2_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ~v2_pre_topc(sK0) | ~v1_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | v3_borsuk_1(sK2(sK0,sK1),sK0,sK1)),
% 0.21/0.48    inference(resolution,[],[f22,f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    m1_pre_topc(sK1,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | v2_struct_0(X0) | v3_borsuk_1(sK2(X0,X1),X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (? [X2] : (v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f7])).
% 0.21/0.48  fof(f7,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (? [X2] : (v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ? [X2] : (v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_tex_2)).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    ~v3_borsuk_1(sK2(sK0,sK1),sK0,sK1) | r1_borsuk_1(sK0,sK1)),
% 0.21/0.48    inference(subsumption_resolution,[],[f66,f14])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    v2_struct_0(sK0) | ~v3_borsuk_1(sK2(sK0,sK1),sK0,sK1) | r1_borsuk_1(sK0,sK1)),
% 0.21/0.48    inference(subsumption_resolution,[],[f65,f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    v5_pre_topc(sK2(sK0,sK1),sK0,sK1)),
% 0.21/0.48    inference(subsumption_resolution,[],[f39,f14])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    v2_struct_0(sK0) | v5_pre_topc(sK2(sK0,sK1),sK0,sK1)),
% 0.21/0.48    inference(subsumption_resolution,[],[f38,f11])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    v2_struct_0(sK1) | v2_struct_0(sK0) | v5_pre_topc(sK2(sK0,sK1),sK0,sK1)),
% 0.21/0.48    inference(subsumption_resolution,[],[f37,f17])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | v5_pre_topc(sK2(sK0,sK1),sK0,sK1)),
% 0.21/0.48    inference(subsumption_resolution,[],[f36,f16])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ~v1_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | v5_pre_topc(sK2(sK0,sK1),sK0,sK1)),
% 0.21/0.48    inference(subsumption_resolution,[],[f35,f15])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ~v2_pre_topc(sK0) | ~v1_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | v5_pre_topc(sK2(sK0,sK1),sK0,sK1)),
% 0.21/0.48    inference(resolution,[],[f20,f12])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | v2_struct_0(X0) | v5_pre_topc(sK2(X0,X1),X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    ~v5_pre_topc(sK2(sK0,sK1),sK0,sK1) | v2_struct_0(sK0) | ~v3_borsuk_1(sK2(sK0,sK1),sK0,sK1) | r1_borsuk_1(sK0,sK1)),
% 0.21/0.48    inference(subsumption_resolution,[],[f64,f52])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    v1_funct_2(sK2(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f51,f14])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    v2_struct_0(sK0) | v1_funct_2(sK2(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f50,f11])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    v2_struct_0(sK1) | v2_struct_0(sK0) | v1_funct_2(sK2(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f49,f17])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | v1_funct_2(sK2(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f48,f16])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ~v1_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | v1_funct_2(sK2(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f47,f15])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ~v2_pre_topc(sK0) | ~v1_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | v1_funct_2(sK2(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.48    inference(resolution,[],[f19,f12])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | v2_struct_0(X0) | v1_funct_2(sK2(X0,X1),u1_struct_0(X0),u1_struct_0(X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    ~v1_funct_2(sK2(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2(sK0,sK1),sK0,sK1) | v2_struct_0(sK0) | ~v3_borsuk_1(sK2(sK0,sK1),sK0,sK1) | r1_borsuk_1(sK0,sK1)),
% 0.21/0.48    inference(subsumption_resolution,[],[f63,f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    v1_funct_1(sK2(sK0,sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f33,f14])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    v2_struct_0(sK0) | v1_funct_1(sK2(sK0,sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f32,f11])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    v2_struct_0(sK1) | v2_struct_0(sK0) | v1_funct_1(sK2(sK0,sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f31,f17])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | v1_funct_1(sK2(sK0,sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f30,f16])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ~v1_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | v1_funct_1(sK2(sK0,sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f29,f15])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ~v2_pre_topc(sK0) | ~v1_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | v1_funct_1(sK2(sK0,sK1))),
% 0.21/0.48    inference(resolution,[],[f18,f12])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | v2_struct_0(X0) | v1_funct_1(sK2(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    ~v1_funct_1(sK2(sK0,sK1)) | ~v1_funct_2(sK2(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2(sK0,sK1),sK0,sK1) | v2_struct_0(sK0) | ~v3_borsuk_1(sK2(sK0,sK1),sK0,sK1) | r1_borsuk_1(sK0,sK1)),
% 0.21/0.48    inference(subsumption_resolution,[],[f62,f12])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    ~m1_pre_topc(sK1,sK0) | ~v1_funct_1(sK2(sK0,sK1)) | ~v1_funct_2(sK2(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2(sK0,sK1),sK0,sK1) | v2_struct_0(sK0) | ~v3_borsuk_1(sK2(sK0,sK1),sK0,sK1) | r1_borsuk_1(sK0,sK1)),
% 0.21/0.48    inference(subsumption_resolution,[],[f61,f11])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | ~v1_funct_1(sK2(sK0,sK1)) | ~v1_funct_2(sK2(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2(sK0,sK1),sK0,sK1) | v2_struct_0(sK0) | ~v3_borsuk_1(sK2(sK0,sK1),sK0,sK1) | r1_borsuk_1(sK0,sK1)),
% 0.21/0.48    inference(subsumption_resolution,[],[f60,f17])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | ~v1_funct_1(sK2(sK0,sK1)) | ~v1_funct_2(sK2(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2(sK0,sK1),sK0,sK1) | v2_struct_0(sK0) | ~v3_borsuk_1(sK2(sK0,sK1),sK0,sK1) | r1_borsuk_1(sK0,sK1)),
% 0.21/0.48    inference(subsumption_resolution,[],[f59,f15])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | ~v1_funct_1(sK2(sK0,sK1)) | ~v1_funct_2(sK2(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2(sK0,sK1),sK0,sK1) | v2_struct_0(sK0) | ~v3_borsuk_1(sK2(sK0,sK1),sK0,sK1) | r1_borsuk_1(sK0,sK1)),
% 0.21/0.48    inference(resolution,[],[f28,f58])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.48    inference(subsumption_resolution,[],[f57,f14])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    v2_struct_0(sK0) | m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.48    inference(subsumption_resolution,[],[f56,f11])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    v2_struct_0(sK1) | v2_struct_0(sK0) | m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.48    inference(subsumption_resolution,[],[f55,f17])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.48    inference(subsumption_resolution,[],[f54,f16])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ~v1_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.48    inference(subsumption_resolution,[],[f53,f15])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ~v2_pre_topc(sK0) | ~v1_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.48    inference(resolution,[],[f21,f12])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | v2_struct_0(X0) | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v5_pre_topc(X2,X0,X1) | v2_struct_0(X0) | ~v3_borsuk_1(X2,X0,X1) | r1_borsuk_1(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((r1_borsuk_1(X0,X1) <=> ? [X2] : (v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((r1_borsuk_1(X0,X1) <=> ? [X2] : (v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (r1_borsuk_1(X0,X1) <=> ? [X2] : (v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_borsuk_1)).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (12561)------------------------------
% 0.21/0.48  % (12561)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (12561)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (12561)Memory used [KB]: 5373
% 0.21/0.48  % (12561)Time elapsed: 0.062 s
% 0.21/0.48  % (12561)------------------------------
% 0.21/0.48  % (12561)------------------------------
% 0.21/0.48  % (12562)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.21/0.48  % (12554)Success in time 0.12 s
%------------------------------------------------------------------------------
