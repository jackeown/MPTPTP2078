%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1885+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:51 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 142 expanded)
%              Number of leaves         :    3 (  24 expanded)
%              Depth                    :   22
%              Number of atoms          :  245 (1122 expanded)
%              Number of equality atoms :   32 ( 113 expanded)
%              Maximal formula depth    :   13 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f87,plain,(
    $false ),
    inference(subsumption_resolution,[],[f86,f48])).

fof(f48,plain,(
    ~ v2_struct_0(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f47,f12])).

fof(f12,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( u1_struct_0(X2) != X1
              | ~ v4_tex_2(X2,X0)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          & v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( u1_struct_0(X2) != X1
              | ~ v4_tex_2(X2,X0)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          & v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => ~ ( ! [X2] :
                    ( ( m1_pre_topc(X2,X0)
                      & v1_pre_topc(X2)
                      & ~ v2_struct_0(X2) )
                   => ~ ( u1_struct_0(X2) = X1
                        & v4_tex_2(X2,X0) ) )
                & v3_tex_2(X1,X0) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ~ ( ! [X2] :
                  ( ( m1_pre_topc(X2,X0)
                    & v1_pre_topc(X2)
                    & ~ v2_struct_0(X2) )
                 => ~ ( u1_struct_0(X2) = X1
                      & v4_tex_2(X2,X0) ) )
              & v3_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_tex_2)).

fof(f47,plain,
    ( v1_xboole_0(sK1)
    | ~ v2_struct_0(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f46,f17])).

fof(f17,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f46,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | ~ v2_struct_0(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f42,f15])).

fof(f15,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f42,plain,
    ( v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | ~ v2_struct_0(sK2(sK0,sK1)) ),
    inference(resolution,[],[f13,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_struct_0(sK2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f9,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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

fof(f13,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f6])).

fof(f86,plain,(
    v2_struct_0(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f85,f12])).

fof(f85,plain,
    ( v1_xboole_0(sK1)
    | v2_struct_0(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f84,f51])).

fof(f51,plain,(
    sK1 = u1_struct_0(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f50,f12])).

fof(f50,plain,
    ( v1_xboole_0(sK1)
    | sK1 = u1_struct_0(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f49,f17])).

fof(f49,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | sK1 = u1_struct_0(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f45,f15])).

fof(f45,plain,
    ( v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | sK1 = u1_struct_0(sK2(sK0,sK1)) ),
    inference(resolution,[],[f13,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(sK2(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f84,plain,
    ( sK1 != u1_struct_0(sK2(sK0,sK1))
    | v1_xboole_0(sK1)
    | v2_struct_0(sK2(sK0,sK1)) ),
    inference(resolution,[],[f83,f13])).

fof(f83,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK1 != u1_struct_0(sK2(sK0,X0))
      | v1_xboole_0(X0)
      | v2_struct_0(sK2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f82,f17])).

fof(f82,plain,(
    ! [X0] :
      ( v2_struct_0(sK2(sK0,X0))
      | sK1 != u1_struct_0(sK2(sK0,X0))
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f81,f15])).

fof(f81,plain,(
    ! [X0] :
      ( v2_struct_0(sK2(sK0,X0))
      | sK1 != u1_struct_0(sK2(sK0,X0))
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(duplicate_literal_removal,[],[f80])).

fof(f80,plain,(
    ! [X0] :
      ( v2_struct_0(sK2(sK0,X0))
      | sK1 != u1_struct_0(sK2(sK0,X0))
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f79,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_pre_topc(sK2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f79,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(sK2(sK0,X0))
      | v2_struct_0(sK2(sK0,X0))
      | sK1 != u1_struct_0(sK2(sK0,X0))
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f78,f17])).

fof(f78,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(sK2(sK0,X0))
      | v2_struct_0(sK2(sK0,X0))
      | sK1 != u1_struct_0(sK2(sK0,X0))
      | ~ l1_pre_topc(sK0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f77,f15])).

fof(f77,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(sK2(sK0,X0))
      | v2_struct_0(sK2(sK0,X0))
      | sK1 != u1_struct_0(sK2(sK0,X0))
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f76,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_pre_topc(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f76,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | ~ v1_pre_topc(X0)
      | v2_struct_0(X0)
      | u1_struct_0(X0) != sK1 ) ),
    inference(subsumption_resolution,[],[f75,f14])).

fof(f14,plain,(
    v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f75,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | u1_struct_0(X0) != sK1
      | ~ v3_tex_2(sK1,sK0) ) ),
    inference(subsumption_resolution,[],[f74,f13])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | u1_struct_0(X0) != sK1
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_tex_2(sK1,sK0) ) ),
    inference(inner_rewriting,[],[f73])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | u1_struct_0(X0) != sK1
      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_tex_2(u1_struct_0(X0),sK0) ) ),
    inference(subsumption_resolution,[],[f72,f17])).

fof(f72,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | u1_struct_0(X0) != sK1
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_tex_2(u1_struct_0(X0),sK0) ) ),
    inference(subsumption_resolution,[],[f71,f15])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | u1_struct_0(X0) != sK1
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_tex_2(u1_struct_0(X0),sK0) ) ),
    inference(duplicate_literal_removal,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | u1_struct_0(X0) != sK1
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_tex_2(u1_struct_0(X0),sK0) ) ),
    inference(resolution,[],[f11,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v4_tex_2(X1,X0)
      | ~ v3_tex_2(u1_struct_0(X1),X0) ) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | v4_tex_2(X1,X0)
      | ~ v3_tex_2(X2,X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_tex_2(X2,X0)
              <=> v4_tex_2(X1,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_tex_2(X2,X0)
              <=> v4_tex_2(X1,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v3_tex_2(X2,X0)
                <=> v4_tex_2(X1,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_tex_2)).

fof(f11,plain,(
    ! [X2] :
      ( ~ v4_tex_2(X2,sK0)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X2,sK0)
      | v2_struct_0(X2)
      | u1_struct_0(X2) != sK1 ) ),
    inference(cnf_transformation,[],[f6])).

%------------------------------------------------------------------------------
