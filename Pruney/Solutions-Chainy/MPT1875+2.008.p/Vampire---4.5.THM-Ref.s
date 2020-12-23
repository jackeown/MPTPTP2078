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
% DateTime   : Thu Dec  3 13:21:32 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 361 expanded)
%              Number of leaves         :    7 (  65 expanded)
%              Depth                    :   23
%              Number of atoms          :  280 (1775 expanded)
%              Number of equality atoms :   15 (  44 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f177,plain,(
    $false ),
    inference(subsumption_resolution,[],[f176,f23])).

fof(f23,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v2_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).

fof(f176,plain,(
    ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f175,f111])).

fof(f111,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(resolution,[],[f101,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f101,plain,(
    r2_hidden(sK3(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f100,f23])).

fof(f100,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK3(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f99,f28])).

fof(f28,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f99,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK3(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f98,f26])).

fof(f26,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f98,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK3(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f93,f25])).

fof(f25,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f93,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK3(sK0,sK1),sK1) ),
    inference(resolution,[],[f24,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(sK3(X0,X1),X1)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ? [X2] :
              ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ? [X2] :
              ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = k6_domain_1(u1_struct_0(X0),X2)
                            & v3_pre_topc(X3,X0) ) )
                    & r2_hidden(X2,X1) ) )
           => v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_tex_2)).

fof(f24,plain,(
    ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f175,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f174,f28])).

fof(f174,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f173,f25])).

fof(f173,plain,
    ( v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f172,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_struct_0(sK2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_tsep_1)).

fof(f172,plain,(
    v2_struct_0(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f171,f24])).

fof(f171,plain,
    ( v2_struct_0(sK2(sK0,sK1))
    | v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f170,f28])).

fof(f170,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK2(sK0,sK1))
    | v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f169,f25])).

fof(f169,plain,
    ( v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK2(sK0,sK1))
    | v2_tex_2(sK1,sK0) ),
    inference(resolution,[],[f161,f120])).

fof(f120,plain,(
    m1_pre_topc(sK2(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f118,f111])).

fof(f118,plain,
    ( v1_xboole_0(sK1)
    | m1_pre_topc(sK2(sK0,sK1),sK0) ),
    inference(resolution,[],[f61,f23])).

fof(f61,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X2)
      | m1_pre_topc(sK2(sK0,X2),sK0) ) ),
    inference(subsumption_resolution,[],[f49,f28])).

fof(f49,plain,(
    ! [X2] :
      ( ~ l1_pre_topc(sK0)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_pre_topc(sK2(sK0,X2),sK0) ) ),
    inference(resolution,[],[f25,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_pre_topc(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f161,plain,(
    ! [X18] :
      ( ~ m1_pre_topc(sK2(sK0,sK1),X18)
      | v2_struct_0(X18)
      | ~ l1_pre_topc(X18)
      | v2_struct_0(sK2(sK0,sK1))
      | v2_tex_2(sK1,X18) ) ),
    inference(subsumption_resolution,[],[f160,f142])).

fof(f142,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK2(sK0,sK1),X0)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(superposition,[],[f30,f138])).

fof(f138,plain,(
    sK1 = u1_struct_0(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f136,f111])).

fof(f136,plain,
    ( v1_xboole_0(sK1)
    | sK1 = u1_struct_0(sK2(sK0,sK1)) ),
    inference(resolution,[],[f62,f23])).

fof(f62,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X3)
      | u1_struct_0(sK2(sK0,X3)) = X3 ) ),
    inference(subsumption_resolution,[],[f50,f28])).

fof(f50,plain,(
    ! [X3] :
      ( ~ l1_pre_topc(sK0)
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK2(sK0,X3)) = X3 ) ),
    inference(resolution,[],[f25,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(sK2(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f160,plain,(
    ! [X18] :
      ( v2_tex_2(sK1,X18)
      | v2_struct_0(X18)
      | ~ l1_pre_topc(X18)
      | v2_struct_0(sK2(sK0,sK1))
      | ~ m1_pre_topc(sK2(sK0,sK1),X18)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X18))) ) ),
    inference(subsumption_resolution,[],[f159,f121])).

fof(f121,plain,(
    v1_tdlat_3(sK2(sK0,sK1)) ),
    inference(resolution,[],[f120,f65])).

fof(f65,plain,(
    ! [X10] :
      ( ~ m1_pre_topc(X10,sK0)
      | v1_tdlat_3(X10) ) ),
    inference(subsumption_resolution,[],[f64,f28])).

fof(f64,plain,(
    ! [X10] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(X10,sK0)
      | v1_tdlat_3(X10) ) ),
    inference(subsumption_resolution,[],[f63,f27])).

fof(f27,plain,(
    v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f63,plain,(
    ! [X10] :
      ( ~ v1_tdlat_3(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(X10,sK0)
      | v1_tdlat_3(X10) ) ),
    inference(subsumption_resolution,[],[f56,f26])).

fof(f56,plain,(
    ! [X10] :
      ( ~ v2_pre_topc(sK0)
      | ~ v1_tdlat_3(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(X10,sK0)
      | v1_tdlat_3(X10) ) ),
    inference(resolution,[],[f25,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v1_tdlat_3(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tdlat_3(X1)
            & v1_tsep_1(X1,X0)
            & v1_borsuk_1(X1,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tdlat_3(X1)
            & v1_tsep_1(X1,X0)
            & v1_borsuk_1(X1,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tdlat_3(X1)
            & v1_tsep_1(X1,X0)
            & v1_borsuk_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_tdlat_3)).

fof(f159,plain,(
    ! [X18] :
      ( v2_tex_2(sK1,X18)
      | v2_struct_0(X18)
      | ~ l1_pre_topc(X18)
      | v2_struct_0(sK2(sK0,sK1))
      | ~ m1_pre_topc(sK2(sK0,sK1),X18)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X18)))
      | ~ v1_tdlat_3(sK2(sK0,sK1)) ) ),
    inference(superposition,[],[f46,f138])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X1)
      | v2_tex_2(u1_struct_0(X1),X0) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | ~ v1_tdlat_3(X1)
      | v2_tex_2(X2,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:41:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.47  % (13108)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.47  % (13101)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.47  % (13106)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.47  % (13114)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.48  % (13114)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f177,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(subsumption_resolution,[],[f176,f23])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.48    inference(cnf_transformation,[],[f11])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f10])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,negated_conjecture,(
% 0.22/0.48    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 0.22/0.48    inference(negated_conjecture,[],[f8])).
% 0.22/0.48  fof(f8,conjecture,(
% 0.22/0.48    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).
% 0.22/0.48  fof(f176,plain,(
% 0.22/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.48    inference(subsumption_resolution,[],[f175,f111])).
% 0.22/0.48  fof(f111,plain,(
% 0.22/0.48    ~v1_xboole_0(sK1)),
% 0.22/0.48    inference(resolution,[],[f101,f44])).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.48  fof(f101,plain,(
% 0.22/0.48    r2_hidden(sK3(sK0,sK1),sK1)),
% 0.22/0.48    inference(subsumption_resolution,[],[f100,f23])).
% 0.22/0.48  fof(f100,plain,(
% 0.22/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK3(sK0,sK1),sK1)),
% 0.22/0.48    inference(subsumption_resolution,[],[f99,f28])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    l1_pre_topc(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f11])).
% 0.22/0.48  fof(f99,plain,(
% 0.22/0.48    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK3(sK0,sK1),sK1)),
% 0.22/0.48    inference(subsumption_resolution,[],[f98,f26])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    v2_pre_topc(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f11])).
% 0.22/0.48  fof(f98,plain,(
% 0.22/0.48    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK3(sK0,sK1),sK1)),
% 0.22/0.48    inference(subsumption_resolution,[],[f93,f25])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ~v2_struct_0(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f11])).
% 0.22/0.48  fof(f93,plain,(
% 0.22/0.48    v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK3(sK0,sK1),sK1)),
% 0.22/0.48    inference(resolution,[],[f24,f39])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(sK3(X0,X1),X1) | v2_tex_2(X1,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f19])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) | ? [X2] : ((! [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),X2) | ~v3_pre_topc(X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,axiom,(
% 0.22/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = k6_domain_1(u1_struct_0(X0),X2) & v3_pre_topc(X3,X0))) & r2_hidden(X2,X1))) => v2_tex_2(X1,X0))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_tex_2)).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ~v2_tex_2(sK1,sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f11])).
% 0.22/0.48  fof(f175,plain,(
% 0.22/0.48    v1_xboole_0(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.48    inference(subsumption_resolution,[],[f174,f28])).
% 0.22/0.48  fof(f174,plain,(
% 0.22/0.48    ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.48    inference(subsumption_resolution,[],[f173,f25])).
% 0.22/0.48  fof(f173,plain,(
% 0.22/0.48    v2_struct_0(sK0) | ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.48    inference(resolution,[],[f172,f31])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_struct_0(sK2(X0,X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_tsep_1)).
% 0.22/0.48  fof(f172,plain,(
% 0.22/0.48    v2_struct_0(sK2(sK0,sK1))),
% 0.22/0.48    inference(subsumption_resolution,[],[f171,f24])).
% 0.22/0.48  fof(f171,plain,(
% 0.22/0.48    v2_struct_0(sK2(sK0,sK1)) | v2_tex_2(sK1,sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f170,f28])).
% 0.22/0.48  fof(f170,plain,(
% 0.22/0.48    ~l1_pre_topc(sK0) | v2_struct_0(sK2(sK0,sK1)) | v2_tex_2(sK1,sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f169,f25])).
% 0.22/0.48  fof(f169,plain,(
% 0.22/0.48    v2_struct_0(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK2(sK0,sK1)) | v2_tex_2(sK1,sK0)),
% 0.22/0.48    inference(resolution,[],[f161,f120])).
% 0.22/0.48  fof(f120,plain,(
% 0.22/0.48    m1_pre_topc(sK2(sK0,sK1),sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f118,f111])).
% 0.22/0.48  fof(f118,plain,(
% 0.22/0.48    v1_xboole_0(sK1) | m1_pre_topc(sK2(sK0,sK1),sK0)),
% 0.22/0.48    inference(resolution,[],[f61,f23])).
% 0.22/0.48  fof(f61,plain,(
% 0.22/0.48    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X2) | m1_pre_topc(sK2(sK0,X2),sK0)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f49,f28])).
% 0.22/0.48  fof(f49,plain,(
% 0.22/0.48    ( ! [X2] : (~l1_pre_topc(sK0) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | m1_pre_topc(sK2(sK0,X2),sK0)) )),
% 0.22/0.48    inference(resolution,[],[f25,f33])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_pre_topc(sK2(X0,X1),X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f16])).
% 0.22/0.48  fof(f161,plain,(
% 0.22/0.48    ( ! [X18] : (~m1_pre_topc(sK2(sK0,sK1),X18) | v2_struct_0(X18) | ~l1_pre_topc(X18) | v2_struct_0(sK2(sK0,sK1)) | v2_tex_2(sK1,X18)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f160,f142])).
% 0.22/0.48  fof(f142,plain,(
% 0.22/0.48    ( ! [X0] : (~m1_pre_topc(sK2(sK0,sK1),X0) | ~l1_pre_topc(X0) | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.22/0.48    inference(superposition,[],[f30,f138])).
% 0.22/0.48  fof(f138,plain,(
% 0.22/0.48    sK1 = u1_struct_0(sK2(sK0,sK1))),
% 0.22/0.48    inference(subsumption_resolution,[],[f136,f111])).
% 0.22/0.48  fof(f136,plain,(
% 0.22/0.48    v1_xboole_0(sK1) | sK1 = u1_struct_0(sK2(sK0,sK1))),
% 0.22/0.48    inference(resolution,[],[f62,f23])).
% 0.22/0.48  fof(f62,plain,(
% 0.22/0.48    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X3) | u1_struct_0(sK2(sK0,X3)) = X3) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f50,f28])).
% 0.22/0.48  fof(f50,plain,(
% 0.22/0.48    ( ! [X3] : (~l1_pre_topc(sK0) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK2(sK0,X3)) = X3) )),
% 0.22/0.48    inference(resolution,[],[f25,f34])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(sK2(X0,X1)) = X1) )),
% 0.22/0.48    inference(cnf_transformation,[],[f16])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.22/0.48  fof(f160,plain,(
% 0.22/0.48    ( ! [X18] : (v2_tex_2(sK1,X18) | v2_struct_0(X18) | ~l1_pre_topc(X18) | v2_struct_0(sK2(sK0,sK1)) | ~m1_pre_topc(sK2(sK0,sK1),X18) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X18)))) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f159,f121])).
% 0.22/0.48  fof(f121,plain,(
% 0.22/0.48    v1_tdlat_3(sK2(sK0,sK1))),
% 0.22/0.48    inference(resolution,[],[f120,f65])).
% 0.22/0.48  fof(f65,plain,(
% 0.22/0.48    ( ! [X10] : (~m1_pre_topc(X10,sK0) | v1_tdlat_3(X10)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f64,f28])).
% 0.22/0.48  fof(f64,plain,(
% 0.22/0.48    ( ! [X10] : (~l1_pre_topc(sK0) | ~m1_pre_topc(X10,sK0) | v1_tdlat_3(X10)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f63,f27])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    v1_tdlat_3(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f11])).
% 0.22/0.48  fof(f63,plain,(
% 0.22/0.48    ( ! [X10] : (~v1_tdlat_3(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(X10,sK0) | v1_tdlat_3(X10)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f56,f26])).
% 0.22/0.48  fof(f56,plain,(
% 0.22/0.48    ( ! [X10] : (~v2_pre_topc(sK0) | ~v1_tdlat_3(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(X10,sK0) | v1_tdlat_3(X10)) )),
% 0.22/0.48    inference(resolution,[],[f25,f42])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v1_tdlat_3(X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : ((v1_tdlat_3(X1) & v1_tsep_1(X1,X0) & v1_borsuk_1(X1,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : ((v1_tdlat_3(X1) & v1_tsep_1(X1,X0) & v1_borsuk_1(X1,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tdlat_3(X1) & v1_tsep_1(X1,X0) & v1_borsuk_1(X1,X0))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_tdlat_3)).
% 0.22/0.48  fof(f159,plain,(
% 0.22/0.48    ( ! [X18] : (v2_tex_2(sK1,X18) | v2_struct_0(X18) | ~l1_pre_topc(X18) | v2_struct_0(sK2(sK0,sK1)) | ~m1_pre_topc(sK2(sK0,sK1),X18) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X18))) | ~v1_tdlat_3(sK2(sK0,sK1))) )),
% 0.22/0.48    inference(superposition,[],[f46,f138])).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tdlat_3(X1) | v2_tex_2(u1_struct_0(X1),X0)) )),
% 0.22/0.48    inference(equality_resolution,[],[f35])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | ~v1_tdlat_3(X1) | v2_tex_2(X2,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v2_tex_2(X2,X0) <=> v1_tdlat_3(X1))))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tex_2)).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (13114)------------------------------
% 0.22/0.48  % (13114)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (13114)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (13114)Memory used [KB]: 1663
% 0.22/0.48  % (13114)Time elapsed: 0.064 s
% 0.22/0.48  % (13114)------------------------------
% 0.22/0.48  % (13114)------------------------------
% 0.22/0.48  % (13098)Success in time 0.121 s
%------------------------------------------------------------------------------
