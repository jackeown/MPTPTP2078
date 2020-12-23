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
% DateTime   : Thu Dec  3 13:21:31 EST 2020

% Result     : Theorem 1.55s
% Output     : Refutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 586 expanded)
%              Number of leaves         :   28 ( 174 expanded)
%              Depth                    :   25
%              Number of atoms          :  536 (2800 expanded)
%              Number of equality atoms :   51 (  96 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f910,plain,(
    $false ),
    inference(subsumption_resolution,[],[f909,f539])).

fof(f539,plain,(
    v4_pre_topc(k1_xboole_0,sK2) ),
    inference(resolution,[],[f533,f79])).

fof(f79,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f533,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | v4_pre_topc(X0,sK2) ) ),
    inference(subsumption_resolution,[],[f532,f76])).

fof(f76,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,
    ( ~ v2_tex_2(sK3,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2)
    & v1_tdlat_3(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f30,f59,f58])).

fof(f58,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ v2_tex_2(X1,sK2)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_pre_topc(sK2)
      & v1_tdlat_3(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( ? [X1] :
        ( ~ v2_tex_2(X1,sK2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
   => ( ~ v2_tex_2(sK3,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v2_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).

fof(f532,plain,(
    ! [X0] :
      ( v4_pre_topc(X0,sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_pre_topc(sK2) ) ),
    inference(duplicate_literal_removal,[],[f527])).

fof(f527,plain,(
    ! [X0] :
      ( v4_pre_topc(X0,sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_pre_topc(sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(resolution,[],[f87,f202])).

fof(f202,plain,(
    ! [X0] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(sK2),X0),sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(resolution,[],[f197,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f197,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | v3_pre_topc(X0,sK2) ) ),
    inference(subsumption_resolution,[],[f193,f76])).

fof(f193,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | v3_pre_topc(X0,sK2)
      | ~ l1_pre_topc(sK2) ) ),
    inference(resolution,[],[f117,f75])).

fof(f75,plain,(
    v1_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f60])).

fof(f117,plain,(
    ! [X2,X0] :
      ( ~ v1_tdlat_3(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(X2,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f101,f82])).

fof(f82,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tdlat_3)).

fof(f101,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ( ~ v3_pre_topc(sK6(X0),X0)
            & m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f70,f71])).

fof(f71,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK6(X0),X0)
        & m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tdlat_3)).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

fof(f909,plain,(
    ~ v4_pre_topc(k1_xboole_0,sK2) ),
    inference(subsumption_resolution,[],[f908,f436])).

fof(f436,plain,(
    ~ sP0(k1_xboole_0,sK2) ),
    inference(subsumption_resolution,[],[f149,f389])).

fof(f389,plain,(
    ~ v2_tex_2(k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f78,f387])).

fof(f387,plain,(
    k1_xboole_0 = sK3 ),
    inference(resolution,[],[f386,f80])).

fof(f80,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f386,plain,(
    v1_xboole_0(sK3) ),
    inference(subsumption_resolution,[],[f385,f178])).

fof(f178,plain,(
    l1_pre_topc(k1_pre_topc(sK2,sK3)) ),
    inference(resolution,[],[f170,f77])).

fof(f77,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f60])).

fof(f170,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | l1_pre_topc(k1_pre_topc(sK2,X2)) ) ),
    inference(subsumption_resolution,[],[f165,f76])).

fof(f165,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | l1_pre_topc(k1_pre_topc(sK2,X2))
      | ~ l1_pre_topc(sK2) ) ),
    inference(resolution,[],[f162,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f162,plain,(
    ! [X0] :
      ( m1_pre_topc(k1_pre_topc(sK2,X0),sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(resolution,[],[f109,f76])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_pre_topc(k1_pre_topc(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_pre_topc(k1_pre_topc(X0,X1),X0) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).

fof(f385,plain,
    ( v1_xboole_0(sK3)
    | ~ l1_pre_topc(k1_pre_topc(sK2,sK3)) ),
    inference(resolution,[],[f384,f81])).

fof(f81,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f384,plain,
    ( ~ l1_struct_0(k1_pre_topc(sK2,sK3))
    | v1_xboole_0(sK3) ),
    inference(forward_demodulation,[],[f383,f217])).

fof(f217,plain,(
    sK3 = u1_struct_0(k1_pre_topc(sK2,sK3)) ),
    inference(resolution,[],[f210,f77])).

fof(f210,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | u1_struct_0(k1_pre_topc(sK2,X0)) = X0 ) ),
    inference(resolution,[],[f85,f76])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).

fof(f383,plain,
    ( ~ l1_struct_0(k1_pre_topc(sK2,sK3))
    | v1_xboole_0(u1_struct_0(k1_pre_topc(sK2,sK3))) ),
    inference(resolution,[],[f382,f104])).

fof(f104,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v2_struct_0(X0) )
     => v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_struct_0)).

fof(f382,plain,(
    v2_struct_0(k1_pre_topc(sK2,sK3)) ),
    inference(subsumption_resolution,[],[f381,f77])).

fof(f381,plain,
    ( v2_struct_0(k1_pre_topc(sK2,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subsumption_resolution,[],[f378,f78])).

fof(f378,plain,
    ( v2_tex_2(sK3,sK2)
    | v2_struct_0(k1_pre_topc(sK2,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(superposition,[],[f275,f217])).

fof(f275,plain,(
    ! [X0] :
      ( v2_tex_2(u1_struct_0(k1_pre_topc(sK2,X0)),sK2)
      | v2_struct_0(k1_pre_topc(sK2,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(subsumption_resolution,[],[f274,f168])).

fof(f168,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | v1_tdlat_3(k1_pre_topc(sK2,X0)) ) ),
    inference(subsumption_resolution,[],[f167,f73])).

fof(f73,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f60])).

fof(f167,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | v1_tdlat_3(k1_pre_topc(sK2,X0))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f166,f75])).

fof(f166,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | v1_tdlat_3(k1_pre_topc(sK2,X0))
      | ~ v1_tdlat_3(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f163,f76])).

fof(f163,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | v1_tdlat_3(k1_pre_topc(sK2,X0))
      | ~ l1_pre_topc(sK2)
      | ~ v1_tdlat_3(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f162,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v1_tdlat_3(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f98,f82])).

fof(f98,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v1_tdlat_3(X1) ) ) ),
    inference(pure_predicate_removal,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tdlat_3(X1)
            & v1_borsuk_1(X1,X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f19,axiom,(
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

fof(f274,plain,(
    ! [X0] :
      ( ~ v1_tdlat_3(k1_pre_topc(sK2,X0))
      | v2_tex_2(u1_struct_0(k1_pre_topc(sK2,X0)),sK2)
      | v2_struct_0(k1_pre_topc(sK2,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(subsumption_resolution,[],[f273,f73])).

fof(f273,plain,(
    ! [X0] :
      ( ~ v1_tdlat_3(k1_pre_topc(sK2,X0))
      | v2_tex_2(u1_struct_0(k1_pre_topc(sK2,X0)),sK2)
      | v2_struct_0(k1_pre_topc(sK2,X0))
      | v2_struct_0(sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(subsumption_resolution,[],[f272,f76])).

fof(f272,plain,(
    ! [X0] :
      ( ~ v1_tdlat_3(k1_pre_topc(sK2,X0))
      | v2_tex_2(u1_struct_0(k1_pre_topc(sK2,X0)),sK2)
      | v2_struct_0(k1_pre_topc(sK2,X0))
      | ~ l1_pre_topc(sK2)
      | v2_struct_0(sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(resolution,[],[f115,f162])).

fof(f115,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v1_tdlat_3(X1)
      | v2_tex_2(u1_struct_0(X1),X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f112,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f112,plain,(
    ! [X0,X1] :
      ( v2_tex_2(u1_struct_0(X1),X0)
      | ~ v1_tdlat_3(X1)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(X2,X0)
      | ~ v1_tdlat_3(X1)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_tex_2(X2,X0)
                  | ~ v1_tdlat_3(X1) )
                & ( v1_tdlat_3(X1)
                  | ~ v2_tex_2(X2,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f44,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
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

fof(f78,plain,(
    ~ v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f60])).

fof(f149,plain,
    ( ~ sP0(k1_xboole_0,sK2)
    | v2_tex_2(k1_xboole_0,sK2) ),
    inference(resolution,[],[f146,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ sP0(X1,X0)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( ( v2_tex_2(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v2_tex_2(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( v2_tex_2(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f146,plain,(
    sP1(sK2,k1_xboole_0) ),
    inference(resolution,[],[f145,f79])).

fof(f145,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | sP1(sK2,X0) ) ),
    inference(resolution,[],[f96,f76])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f40,f56,f55])).

fof(f55,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ! [X2] :
          ( ? [X3] :
              ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
              & v4_pre_topc(X3,X0)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ r1_tarski(X2,X1)
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                            & v4_pre_topc(X3,X0) ) )
                    & r1_tarski(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tex_2)).

fof(f908,plain,
    ( sP0(k1_xboole_0,sK2)
    | ~ v4_pre_topc(k1_xboole_0,sK2) ),
    inference(trivial_inequality_removal,[],[f907])).

fof(f907,plain,
    ( k1_xboole_0 != k1_xboole_0
    | sP0(k1_xboole_0,sK2)
    | ~ v4_pre_topc(k1_xboole_0,sK2) ),
    inference(superposition,[],[f896,f435])).

fof(f435,plain,(
    k1_xboole_0 = sK4(k1_xboole_0,sK2) ),
    inference(subsumption_resolution,[],[f154,f389])).

fof(f154,plain,
    ( v2_tex_2(k1_xboole_0,sK2)
    | k1_xboole_0 = sK4(k1_xboole_0,sK2) ),
    inference(resolution,[],[f149,f121])).

fof(f121,plain,(
    ! [X0] :
      ( sP0(k1_xboole_0,X0)
      | k1_xboole_0 = sK4(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f94,f97])).

fof(f97,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f94,plain,(
    ! [X0,X1] :
      ( r1_tarski(sK4(X0,X1),X0)
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X1),X0,X3) != sK4(X0,X1)
              | ~ v4_pre_topc(X3,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          & r1_tarski(sK4(X0,X1),X0)
          & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) )
      & ( ! [X4] :
            ( ( k9_subset_1(u1_struct_0(X1),X0,sK5(X0,X1,X4)) = X4
              & v4_pre_topc(sK5(X0,X1,X4),X1)
              & m1_subset_1(sK5(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r1_tarski(X4,X0)
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f64,f66,f65])).

fof(f65,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X1),X0,X3) != X2
              | ~ v4_pre_topc(X3,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          & r1_tarski(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X1),X0,X3) != sK4(X0,X1)
            | ~ v4_pre_topc(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
        & r1_tarski(sK4(X0,X1),X0)
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( k9_subset_1(u1_struct_0(X1),X0,X5) = X4
          & v4_pre_topc(X5,X1)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X1),X0,sK5(X0,X1,X4)) = X4
        & v4_pre_topc(sK5(X0,X1,X4),X1)
        & m1_subset_1(sK5(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X1),X0,X3) != X2
                | ~ v4_pre_topc(X3,X1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            & r1_tarski(X2,X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ) )
      & ( ! [X4] :
            ( ? [X5] :
                ( k9_subset_1(u1_struct_0(X1),X0,X5) = X4
                & v4_pre_topc(X5,X1)
                & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r1_tarski(X4,X0)
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f63])).

fof(f63,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2] :
            ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
                | ~ v4_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & r1_tarski(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X2] :
            ( ? [X3] :
                ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                & v4_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r1_tarski(X2,X1)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f55])).

fof(f896,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != sK4(X1,X0)
      | sP0(X1,X0)
      | ~ v4_pre_topc(k1_xboole_0,X0) ) ),
    inference(subsumption_resolution,[],[f891,f79])).

fof(f891,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != sK4(X1,X0)
      | sP0(X1,X0)
      | ~ v4_pre_topc(k1_xboole_0,X0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(superposition,[],[f95,f192])).

fof(f192,plain,(
    ! [X0,X1] : k1_xboole_0 = k9_subset_1(X0,X1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f187,f128])).

fof(f128,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f126,f118])).

fof(f118,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f97,f105])).

fof(f105,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f126,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2) ),
    inference(superposition,[],[f122,f107])).

fof(f107,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f122,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(superposition,[],[f107,f106])).

fof(f106,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f187,plain,(
    ! [X0,X1] : k3_xboole_0(X1,k1_xboole_0) = k9_subset_1(X0,X1,k1_xboole_0) ),
    inference(resolution,[],[f110,f79])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f95,plain,(
    ! [X0,X3,X1] :
      ( k9_subset_1(u1_struct_0(X1),X0,X3) != sK4(X0,X1)
      | sP0(X0,X1)
      | ~ v4_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ),
    inference(cnf_transformation,[],[f67])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:58:14 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (13869)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.50  % (13846)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.50  % (13846)Refutation not found, incomplete strategy% (13846)------------------------------
% 0.21/0.50  % (13846)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (13846)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (13846)Memory used [KB]: 1663
% 0.21/0.50  % (13846)Time elapsed: 0.003 s
% 0.21/0.50  % (13846)------------------------------
% 0.21/0.50  % (13846)------------------------------
% 0.21/0.50  % (13858)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (13853)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (13868)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (13849)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (13874)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.51  % (13850)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (13857)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (13857)Refutation not found, incomplete strategy% (13857)------------------------------
% 0.21/0.52  % (13857)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (13857)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (13857)Memory used [KB]: 10618
% 0.21/0.52  % (13857)Time elapsed: 0.110 s
% 0.21/0.52  % (13857)------------------------------
% 0.21/0.52  % (13857)------------------------------
% 0.21/0.52  % (13859)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (13860)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (13873)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.52  % (13866)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (13855)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (13855)Refutation not found, incomplete strategy% (13855)------------------------------
% 0.21/0.53  % (13855)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (13855)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (13855)Memory used [KB]: 10618
% 0.21/0.53  % (13855)Time elapsed: 0.002 s
% 0.21/0.53  % (13855)------------------------------
% 0.21/0.53  % (13855)------------------------------
% 0.21/0.53  % (13848)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (13854)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (13847)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (13865)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (13875)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (13856)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (13867)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (13851)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.32/0.54  % (13870)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.32/0.54  % (13861)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.32/0.54  % (13868)Refutation not found, incomplete strategy% (13868)------------------------------
% 1.32/0.54  % (13868)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.54  % (13864)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.32/0.54  % (13862)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.32/0.54  % (13852)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.32/0.54  % (13871)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.32/0.54  % (13868)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.54  
% 1.32/0.54  % (13868)Memory used [KB]: 10746
% 1.32/0.54  % (13868)Time elapsed: 0.103 s
% 1.32/0.54  % (13868)------------------------------
% 1.32/0.54  % (13868)------------------------------
% 1.32/0.54  % (13863)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.32/0.54  % (13863)Refutation not found, incomplete strategy% (13863)------------------------------
% 1.32/0.54  % (13863)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.54  % (13863)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.54  
% 1.32/0.54  % (13863)Memory used [KB]: 10618
% 1.32/0.54  % (13863)Time elapsed: 0.142 s
% 1.32/0.54  % (13863)------------------------------
% 1.32/0.54  % (13863)------------------------------
% 1.32/0.55  % (13872)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.32/0.55  % (13848)Refutation not found, incomplete strategy% (13848)------------------------------
% 1.32/0.55  % (13848)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.55  % (13848)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.55  
% 1.32/0.55  % (13848)Memory used [KB]: 11001
% 1.32/0.55  % (13848)Time elapsed: 0.125 s
% 1.32/0.55  % (13848)------------------------------
% 1.32/0.55  % (13848)------------------------------
% 1.32/0.55  % (13856)Refutation not found, incomplete strategy% (13856)------------------------------
% 1.32/0.55  % (13856)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.55  % (13856)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.55  
% 1.32/0.55  % (13856)Memory used [KB]: 10618
% 1.32/0.55  % (13856)Time elapsed: 0.142 s
% 1.32/0.55  % (13856)------------------------------
% 1.32/0.55  % (13856)------------------------------
% 1.55/0.57  % (13853)Refutation found. Thanks to Tanya!
% 1.55/0.57  % SZS status Theorem for theBenchmark
% 1.55/0.57  % SZS output start Proof for theBenchmark
% 1.55/0.57  fof(f910,plain,(
% 1.55/0.57    $false),
% 1.55/0.57    inference(subsumption_resolution,[],[f909,f539])).
% 1.55/0.57  fof(f539,plain,(
% 1.55/0.57    v4_pre_topc(k1_xboole_0,sK2)),
% 1.55/0.57    inference(resolution,[],[f533,f79])).
% 1.55/0.57  fof(f79,plain,(
% 1.55/0.57    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.55/0.57    inference(cnf_transformation,[],[f8])).
% 1.55/0.57  fof(f8,axiom,(
% 1.55/0.57    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.55/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 1.55/0.57  fof(f533,plain,(
% 1.55/0.57    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | v4_pre_topc(X0,sK2)) )),
% 1.55/0.57    inference(subsumption_resolution,[],[f532,f76])).
% 1.55/0.57  fof(f76,plain,(
% 1.55/0.57    l1_pre_topc(sK2)),
% 1.55/0.57    inference(cnf_transformation,[],[f60])).
% 1.55/0.57  fof(f60,plain,(
% 1.55/0.57    (~v2_tex_2(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v1_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 1.55/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f30,f59,f58])).
% 1.55/0.57  fof(f58,plain,(
% 1.55/0.57    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (~v2_tex_2(X1,sK2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v1_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 1.55/0.57    introduced(choice_axiom,[])).
% 1.55/0.57  fof(f59,plain,(
% 1.55/0.57    ? [X1] : (~v2_tex_2(X1,sK2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) => (~v2_tex_2(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))))),
% 1.55/0.57    introduced(choice_axiom,[])).
% 1.55/0.57  fof(f30,plain,(
% 1.55/0.57    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.55/0.57    inference(flattening,[],[f29])).
% 1.55/0.57  fof(f29,plain,(
% 1.55/0.57    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.55/0.57    inference(ennf_transformation,[],[f24])).
% 1.55/0.57  fof(f24,negated_conjecture,(
% 1.55/0.57    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 1.55/0.57    inference(negated_conjecture,[],[f23])).
% 1.55/0.57  fof(f23,conjecture,(
% 1.55/0.57    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 1.55/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).
% 1.55/0.57  fof(f532,plain,(
% 1.55/0.57    ( ! [X0] : (v4_pre_topc(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2)) )),
% 1.55/0.57    inference(duplicate_literal_removal,[],[f527])).
% 1.55/0.57  fof(f527,plain,(
% 1.55/0.57    ( ! [X0] : (v4_pre_topc(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 1.55/0.57    inference(resolution,[],[f87,f202])).
% 1.55/0.57  fof(f202,plain,(
% 1.55/0.57    ( ! [X0] : (v3_pre_topc(k3_subset_1(u1_struct_0(sK2),X0),sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 1.55/0.57    inference(resolution,[],[f197,f108])).
% 1.55/0.57  fof(f108,plain,(
% 1.55/0.57    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.55/0.57    inference(cnf_transformation,[],[f50])).
% 1.55/0.57  fof(f50,plain,(
% 1.55/0.57    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.55/0.57    inference(ennf_transformation,[],[f6])).
% 1.55/0.57  fof(f6,axiom,(
% 1.55/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.55/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.55/0.57  fof(f197,plain,(
% 1.55/0.57    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | v3_pre_topc(X0,sK2)) )),
% 1.55/0.57    inference(subsumption_resolution,[],[f193,f76])).
% 1.55/0.58  fof(f193,plain,(
% 1.55/0.58    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | v3_pre_topc(X0,sK2) | ~l1_pre_topc(sK2)) )),
% 1.55/0.58    inference(resolution,[],[f117,f75])).
% 1.55/0.58  fof(f75,plain,(
% 1.55/0.58    v1_tdlat_3(sK2)),
% 1.55/0.58    inference(cnf_transformation,[],[f60])).
% 1.55/0.58  fof(f117,plain,(
% 1.55/0.58    ( ! [X2,X0] : (~v1_tdlat_3(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(X2,X0) | ~l1_pre_topc(X0)) )),
% 1.55/0.58    inference(subsumption_resolution,[],[f101,f82])).
% 1.55/0.58  fof(f82,plain,(
% 1.55/0.58    ( ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 1.55/0.58    inference(cnf_transformation,[],[f34])).
% 1.55/0.58  fof(f34,plain,(
% 1.55/0.58    ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 1.55/0.58    inference(flattening,[],[f33])).
% 1.55/0.58  fof(f33,plain,(
% 1.55/0.58    ! [X0] : ((v2_pre_topc(X0) | ~v1_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 1.55/0.58    inference(ennf_transformation,[],[f18])).
% 1.55/0.58  fof(f18,axiom,(
% 1.55/0.58    ! [X0] : (l1_pre_topc(X0) => (v1_tdlat_3(X0) => v2_pre_topc(X0)))),
% 1.55/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tdlat_3)).
% 1.55/0.58  fof(f101,plain,(
% 1.55/0.58    ( ! [X2,X0] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.55/0.58    inference(cnf_transformation,[],[f72])).
% 1.55/0.58  fof(f72,plain,(
% 1.55/0.58    ! [X0] : (((v1_tdlat_3(X0) | (~v3_pre_topc(sK6(X0),X0) & m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.55/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f70,f71])).
% 1.55/0.58  fof(f71,plain,(
% 1.55/0.58    ! [X0] : (? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK6(X0),X0) & m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.55/0.58    introduced(choice_axiom,[])).
% 1.55/0.58  fof(f70,plain,(
% 1.55/0.58    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.55/0.58    inference(rectify,[],[f69])).
% 1.55/0.58  fof(f69,plain,(
% 1.55/0.58    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.55/0.58    inference(nnf_transformation,[],[f47])).
% 1.55/0.58  fof(f47,plain,(
% 1.55/0.58    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.55/0.58    inference(flattening,[],[f46])).
% 1.55/0.58  fof(f46,plain,(
% 1.55/0.58    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.55/0.58    inference(ennf_transformation,[],[f21])).
% 1.55/0.58  fof(f21,axiom,(
% 1.55/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v1_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v3_pre_topc(X1,X0))))),
% 1.55/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tdlat_3)).
% 1.55/0.58  fof(f87,plain,(
% 1.55/0.58    ( ! [X0,X1] : (~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.55/0.58    inference(cnf_transformation,[],[f61])).
% 1.55/0.58  fof(f61,plain,(
% 1.55/0.58    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.55/0.58    inference(nnf_transformation,[],[f38])).
% 1.55/0.58  fof(f38,plain,(
% 1.55/0.58    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.55/0.58    inference(ennf_transformation,[],[f16])).
% 1.55/0.58  fof(f16,axiom,(
% 1.55/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 1.55/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).
% 1.55/0.58  fof(f909,plain,(
% 1.55/0.58    ~v4_pre_topc(k1_xboole_0,sK2)),
% 1.55/0.58    inference(subsumption_resolution,[],[f908,f436])).
% 1.55/0.58  fof(f436,plain,(
% 1.55/0.58    ~sP0(k1_xboole_0,sK2)),
% 1.55/0.58    inference(subsumption_resolution,[],[f149,f389])).
% 1.55/0.58  fof(f389,plain,(
% 1.55/0.58    ~v2_tex_2(k1_xboole_0,sK2)),
% 1.55/0.58    inference(backward_demodulation,[],[f78,f387])).
% 1.55/0.58  fof(f387,plain,(
% 1.55/0.58    k1_xboole_0 = sK3),
% 1.55/0.58    inference(resolution,[],[f386,f80])).
% 1.55/0.58  fof(f80,plain,(
% 1.55/0.58    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.55/0.58    inference(cnf_transformation,[],[f31])).
% 1.55/0.58  fof(f31,plain,(
% 1.55/0.58    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.55/0.58    inference(ennf_transformation,[],[f1])).
% 1.55/0.58  fof(f1,axiom,(
% 1.55/0.58    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.55/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.55/0.58  fof(f386,plain,(
% 1.55/0.58    v1_xboole_0(sK3)),
% 1.55/0.58    inference(subsumption_resolution,[],[f385,f178])).
% 1.55/0.58  fof(f178,plain,(
% 1.55/0.58    l1_pre_topc(k1_pre_topc(sK2,sK3))),
% 1.55/0.58    inference(resolution,[],[f170,f77])).
% 1.55/0.58  fof(f77,plain,(
% 1.55/0.58    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.55/0.58    inference(cnf_transformation,[],[f60])).
% 1.55/0.58  fof(f170,plain,(
% 1.55/0.58    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) | l1_pre_topc(k1_pre_topc(sK2,X2))) )),
% 1.55/0.58    inference(subsumption_resolution,[],[f165,f76])).
% 1.55/0.58  fof(f165,plain,(
% 1.55/0.58    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) | l1_pre_topc(k1_pre_topc(sK2,X2)) | ~l1_pre_topc(sK2)) )),
% 1.55/0.58    inference(resolution,[],[f162,f83])).
% 1.55/0.58  fof(f83,plain,(
% 1.55/0.58    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.55/0.58    inference(cnf_transformation,[],[f35])).
% 1.55/0.58  fof(f35,plain,(
% 1.55/0.58    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.55/0.58    inference(ennf_transformation,[],[f13])).
% 1.55/0.58  fof(f13,axiom,(
% 1.55/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.55/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.55/0.58  fof(f162,plain,(
% 1.55/0.58    ( ! [X0] : (m1_pre_topc(k1_pre_topc(sK2,X0),sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 1.55/0.58    inference(resolution,[],[f109,f76])).
% 1.55/0.58  fof(f109,plain,(
% 1.55/0.58    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_pre_topc(k1_pre_topc(X0,X1),X0)) )),
% 1.55/0.58    inference(cnf_transformation,[],[f52])).
% 1.55/0.58  fof(f52,plain,(
% 1.55/0.58    ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.55/0.58    inference(flattening,[],[f51])).
% 1.55/0.58  fof(f51,plain,(
% 1.55/0.58    ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.55/0.58    inference(ennf_transformation,[],[f27])).
% 1.55/0.58  fof(f27,plain,(
% 1.55/0.58    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_pre_topc(k1_pre_topc(X0,X1),X0))),
% 1.55/0.58    inference(pure_predicate_removal,[],[f11])).
% 1.55/0.58  fof(f11,axiom,(
% 1.55/0.58    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 1.55/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).
% 1.55/0.58  fof(f385,plain,(
% 1.55/0.58    v1_xboole_0(sK3) | ~l1_pre_topc(k1_pre_topc(sK2,sK3))),
% 1.55/0.58    inference(resolution,[],[f384,f81])).
% 1.55/0.58  fof(f81,plain,(
% 1.55/0.58    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.55/0.58    inference(cnf_transformation,[],[f32])).
% 1.55/0.58  fof(f32,plain,(
% 1.55/0.58    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.55/0.58    inference(ennf_transformation,[],[f12])).
% 1.55/0.58  fof(f12,axiom,(
% 1.55/0.58    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.55/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.55/0.58  fof(f384,plain,(
% 1.55/0.58    ~l1_struct_0(k1_pre_topc(sK2,sK3)) | v1_xboole_0(sK3)),
% 1.55/0.58    inference(forward_demodulation,[],[f383,f217])).
% 1.55/0.58  fof(f217,plain,(
% 1.55/0.58    sK3 = u1_struct_0(k1_pre_topc(sK2,sK3))),
% 1.55/0.58    inference(resolution,[],[f210,f77])).
% 1.55/0.58  fof(f210,plain,(
% 1.55/0.58    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | u1_struct_0(k1_pre_topc(sK2,X0)) = X0) )),
% 1.55/0.58    inference(resolution,[],[f85,f76])).
% 1.55/0.58  fof(f85,plain,(
% 1.55/0.58    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(k1_pre_topc(X0,X1)) = X1) )),
% 1.55/0.58    inference(cnf_transformation,[],[f37])).
% 1.55/0.58  fof(f37,plain,(
% 1.55/0.58    ! [X0] : (! [X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.55/0.58    inference(ennf_transformation,[],[f15])).
% 1.55/0.58  fof(f15,axiom,(
% 1.55/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => u1_struct_0(k1_pre_topc(X0,X1)) = X1))),
% 1.55/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).
% 1.55/0.58  fof(f383,plain,(
% 1.55/0.58    ~l1_struct_0(k1_pre_topc(sK2,sK3)) | v1_xboole_0(u1_struct_0(k1_pre_topc(sK2,sK3)))),
% 1.55/0.58    inference(resolution,[],[f382,f104])).
% 1.55/0.58  fof(f104,plain,(
% 1.55/0.58    ( ! [X0] : (~v2_struct_0(X0) | ~l1_struct_0(X0) | v1_xboole_0(u1_struct_0(X0))) )),
% 1.55/0.58    inference(cnf_transformation,[],[f49])).
% 1.55/0.58  fof(f49,plain,(
% 1.55/0.58    ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v2_struct_0(X0))),
% 1.55/0.58    inference(flattening,[],[f48])).
% 1.55/0.58  fof(f48,plain,(
% 1.55/0.58    ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v2_struct_0(X0)))),
% 1.55/0.58    inference(ennf_transformation,[],[f14])).
% 1.55/0.58  fof(f14,axiom,(
% 1.55/0.58    ! [X0] : ((l1_struct_0(X0) & v2_struct_0(X0)) => v1_xboole_0(u1_struct_0(X0)))),
% 1.55/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_struct_0)).
% 1.55/0.58  fof(f382,plain,(
% 1.55/0.58    v2_struct_0(k1_pre_topc(sK2,sK3))),
% 1.55/0.58    inference(subsumption_resolution,[],[f381,f77])).
% 1.55/0.58  fof(f381,plain,(
% 1.55/0.58    v2_struct_0(k1_pre_topc(sK2,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.55/0.58    inference(subsumption_resolution,[],[f378,f78])).
% 1.55/0.58  fof(f378,plain,(
% 1.55/0.58    v2_tex_2(sK3,sK2) | v2_struct_0(k1_pre_topc(sK2,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.55/0.58    inference(superposition,[],[f275,f217])).
% 1.55/0.58  fof(f275,plain,(
% 1.55/0.58    ( ! [X0] : (v2_tex_2(u1_struct_0(k1_pre_topc(sK2,X0)),sK2) | v2_struct_0(k1_pre_topc(sK2,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 1.55/0.58    inference(subsumption_resolution,[],[f274,f168])).
% 1.55/0.58  fof(f168,plain,(
% 1.55/0.58    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | v1_tdlat_3(k1_pre_topc(sK2,X0))) )),
% 1.55/0.58    inference(subsumption_resolution,[],[f167,f73])).
% 1.55/0.58  fof(f73,plain,(
% 1.55/0.58    ~v2_struct_0(sK2)),
% 1.55/0.58    inference(cnf_transformation,[],[f60])).
% 1.55/0.58  fof(f167,plain,(
% 1.55/0.58    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | v1_tdlat_3(k1_pre_topc(sK2,X0)) | v2_struct_0(sK2)) )),
% 1.55/0.58    inference(subsumption_resolution,[],[f166,f75])).
% 1.55/0.58  fof(f166,plain,(
% 1.55/0.58    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | v1_tdlat_3(k1_pre_topc(sK2,X0)) | ~v1_tdlat_3(sK2) | v2_struct_0(sK2)) )),
% 1.55/0.58    inference(subsumption_resolution,[],[f163,f76])).
% 1.55/0.58  fof(f163,plain,(
% 1.55/0.58    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | v1_tdlat_3(k1_pre_topc(sK2,X0)) | ~l1_pre_topc(sK2) | ~v1_tdlat_3(sK2) | v2_struct_0(sK2)) )),
% 1.55/0.58    inference(resolution,[],[f162,f114])).
% 1.55/0.58  fof(f114,plain,(
% 1.55/0.58    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v1_tdlat_3(X1) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | v2_struct_0(X0)) )),
% 1.55/0.58    inference(subsumption_resolution,[],[f98,f82])).
% 1.55/0.58  fof(f98,plain,(
% 1.55/0.58    ( ! [X0,X1] : (v1_tdlat_3(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.55/0.58    inference(cnf_transformation,[],[f43])).
% 1.55/0.58  fof(f43,plain,(
% 1.55/0.58    ! [X0] : (! [X1] : (v1_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.55/0.58    inference(flattening,[],[f42])).
% 1.55/0.58  fof(f42,plain,(
% 1.55/0.58    ! [X0] : (! [X1] : (v1_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.55/0.58    inference(ennf_transformation,[],[f26])).
% 1.55/0.58  fof(f26,plain,(
% 1.55/0.58    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v1_tdlat_3(X1)))),
% 1.55/0.58    inference(pure_predicate_removal,[],[f25])).
% 1.55/0.58  fof(f25,plain,(
% 1.55/0.58    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tdlat_3(X1) & v1_borsuk_1(X1,X0))))),
% 1.55/0.58    inference(pure_predicate_removal,[],[f19])).
% 1.55/0.58  fof(f19,axiom,(
% 1.55/0.58    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tdlat_3(X1) & v1_tsep_1(X1,X0) & v1_borsuk_1(X1,X0))))),
% 1.55/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_tdlat_3)).
% 1.55/0.58  fof(f274,plain,(
% 1.55/0.58    ( ! [X0] : (~v1_tdlat_3(k1_pre_topc(sK2,X0)) | v2_tex_2(u1_struct_0(k1_pre_topc(sK2,X0)),sK2) | v2_struct_0(k1_pre_topc(sK2,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 1.55/0.58    inference(subsumption_resolution,[],[f273,f73])).
% 1.55/0.58  fof(f273,plain,(
% 1.55/0.58    ( ! [X0] : (~v1_tdlat_3(k1_pre_topc(sK2,X0)) | v2_tex_2(u1_struct_0(k1_pre_topc(sK2,X0)),sK2) | v2_struct_0(k1_pre_topc(sK2,X0)) | v2_struct_0(sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 1.55/0.58    inference(subsumption_resolution,[],[f272,f76])).
% 1.55/0.58  fof(f272,plain,(
% 1.55/0.58    ( ! [X0] : (~v1_tdlat_3(k1_pre_topc(sK2,X0)) | v2_tex_2(u1_struct_0(k1_pre_topc(sK2,X0)),sK2) | v2_struct_0(k1_pre_topc(sK2,X0)) | ~l1_pre_topc(sK2) | v2_struct_0(sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 1.55/0.58    inference(resolution,[],[f115,f162])).
% 1.55/0.58  fof(f115,plain,(
% 1.55/0.58    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v1_tdlat_3(X1) | v2_tex_2(u1_struct_0(X1),X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.55/0.58    inference(subsumption_resolution,[],[f112,f84])).
% 1.55/0.58  fof(f84,plain,(
% 1.55/0.58    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.55/0.58    inference(cnf_transformation,[],[f36])).
% 1.55/0.58  fof(f36,plain,(
% 1.55/0.58    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.55/0.58    inference(ennf_transformation,[],[f17])).
% 1.55/0.58  fof(f17,axiom,(
% 1.55/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.55/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 1.55/0.58  fof(f112,plain,(
% 1.55/0.58    ( ! [X0,X1] : (v2_tex_2(u1_struct_0(X1),X0) | ~v1_tdlat_3(X1) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.55/0.58    inference(equality_resolution,[],[f100])).
% 1.55/0.58  fof(f100,plain,(
% 1.55/0.58    ( ! [X2,X0,X1] : (v2_tex_2(X2,X0) | ~v1_tdlat_3(X1) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.55/0.58    inference(cnf_transformation,[],[f68])).
% 1.55/0.58  fof(f68,plain,(
% 1.55/0.58    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) | ~v1_tdlat_3(X1)) & (v1_tdlat_3(X1) | ~v2_tex_2(X2,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.55/0.58    inference(nnf_transformation,[],[f45])).
% 1.55/0.58  fof(f45,plain,(
% 1.55/0.58    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.55/0.58    inference(flattening,[],[f44])).
% 1.55/0.58  fof(f44,plain,(
% 1.55/0.58    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.55/0.58    inference(ennf_transformation,[],[f22])).
% 1.55/0.58  fof(f22,axiom,(
% 1.55/0.58    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v2_tex_2(X2,X0) <=> v1_tdlat_3(X1))))))),
% 1.55/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tex_2)).
% 1.55/0.58  fof(f78,plain,(
% 1.55/0.58    ~v2_tex_2(sK3,sK2)),
% 1.55/0.58    inference(cnf_transformation,[],[f60])).
% 1.55/0.58  fof(f149,plain,(
% 1.55/0.58    ~sP0(k1_xboole_0,sK2) | v2_tex_2(k1_xboole_0,sK2)),
% 1.55/0.58    inference(resolution,[],[f146,f89])).
% 1.55/0.58  fof(f89,plain,(
% 1.55/0.58    ( ! [X0,X1] : (~sP1(X0,X1) | ~sP0(X1,X0) | v2_tex_2(X1,X0)) )),
% 1.55/0.58    inference(cnf_transformation,[],[f62])).
% 1.55/0.58  fof(f62,plain,(
% 1.55/0.58    ! [X0,X1] : (((v2_tex_2(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~v2_tex_2(X1,X0))) | ~sP1(X0,X1))),
% 1.55/0.58    inference(nnf_transformation,[],[f56])).
% 1.55/0.58  fof(f56,plain,(
% 1.55/0.58    ! [X0,X1] : ((v2_tex_2(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 1.55/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.55/0.58  fof(f146,plain,(
% 1.55/0.58    sP1(sK2,k1_xboole_0)),
% 1.55/0.58    inference(resolution,[],[f145,f79])).
% 1.55/0.58  fof(f145,plain,(
% 1.55/0.58    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | sP1(sK2,X0)) )),
% 1.55/0.58    inference(resolution,[],[f96,f76])).
% 1.55/0.58  fof(f96,plain,(
% 1.55/0.58    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | sP1(X0,X1)) )),
% 1.55/0.58    inference(cnf_transformation,[],[f57])).
% 1.55/0.58  fof(f57,plain,(
% 1.55/0.58    ! [X0] : (! [X1] : (sP1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.55/0.58    inference(definition_folding,[],[f40,f56,f55])).
% 1.55/0.58  fof(f55,plain,(
% 1.55/0.58    ! [X1,X0] : (sP0(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.55/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.55/0.58  fof(f40,plain,(
% 1.55/0.58    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.55/0.58    inference(flattening,[],[f39])).
% 1.55/0.58  fof(f39,plain,(
% 1.55/0.58    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.55/0.58    inference(ennf_transformation,[],[f20])).
% 1.55/0.58  fof(f20,axiom,(
% 1.55/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 1.55/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tex_2)).
% 1.55/0.58  fof(f908,plain,(
% 1.55/0.58    sP0(k1_xboole_0,sK2) | ~v4_pre_topc(k1_xboole_0,sK2)),
% 1.55/0.58    inference(trivial_inequality_removal,[],[f907])).
% 1.55/0.58  fof(f907,plain,(
% 1.55/0.58    k1_xboole_0 != k1_xboole_0 | sP0(k1_xboole_0,sK2) | ~v4_pre_topc(k1_xboole_0,sK2)),
% 1.55/0.58    inference(superposition,[],[f896,f435])).
% 1.55/0.58  fof(f435,plain,(
% 1.55/0.58    k1_xboole_0 = sK4(k1_xboole_0,sK2)),
% 1.55/0.58    inference(subsumption_resolution,[],[f154,f389])).
% 1.55/0.58  fof(f154,plain,(
% 1.55/0.58    v2_tex_2(k1_xboole_0,sK2) | k1_xboole_0 = sK4(k1_xboole_0,sK2)),
% 1.55/0.58    inference(resolution,[],[f149,f121])).
% 1.55/0.58  fof(f121,plain,(
% 1.55/0.58    ( ! [X0] : (sP0(k1_xboole_0,X0) | k1_xboole_0 = sK4(k1_xboole_0,X0)) )),
% 1.55/0.58    inference(resolution,[],[f94,f97])).
% 1.55/0.58  fof(f97,plain,(
% 1.55/0.58    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.55/0.58    inference(cnf_transformation,[],[f41])).
% 1.55/0.58  fof(f41,plain,(
% 1.55/0.58    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 1.55/0.58    inference(ennf_transformation,[],[f3])).
% 1.55/0.58  fof(f3,axiom,(
% 1.55/0.58    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 1.55/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 1.55/0.58  fof(f94,plain,(
% 1.55/0.58    ( ! [X0,X1] : (r1_tarski(sK4(X0,X1),X0) | sP0(X0,X1)) )),
% 1.55/0.58    inference(cnf_transformation,[],[f67])).
% 1.55/0.58  fof(f67,plain,(
% 1.55/0.58    ! [X0,X1] : ((sP0(X0,X1) | (! [X3] : (k9_subset_1(u1_struct_0(X1),X0,X3) != sK4(X0,X1) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(sK4(X0,X1),X0) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : ((k9_subset_1(u1_struct_0(X1),X0,sK5(X0,X1,X4)) = X4 & v4_pre_topc(sK5(X0,X1,X4),X1) & m1_subset_1(sK5(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~sP0(X0,X1)))),
% 1.55/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f64,f66,f65])).
% 1.55/0.58  fof(f65,plain,(
% 1.55/0.58    ! [X1,X0] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X1),X0,X3) != X2 | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) => (! [X3] : (k9_subset_1(u1_struct_0(X1),X0,X3) != sK4(X0,X1) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(sK4(X0,X1),X0) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))),
% 1.55/0.58    introduced(choice_axiom,[])).
% 1.55/0.58  fof(f66,plain,(
% 1.55/0.58    ! [X4,X1,X0] : (? [X5] : (k9_subset_1(u1_struct_0(X1),X0,X5) = X4 & v4_pre_topc(X5,X1) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X1),X0,sK5(X0,X1,X4)) = X4 & v4_pre_topc(sK5(X0,X1,X4),X1) & m1_subset_1(sK5(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1)))))),
% 1.55/0.58    introduced(choice_axiom,[])).
% 1.55/0.58  fof(f64,plain,(
% 1.55/0.58    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X1),X0,X3) != X2 | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (? [X5] : (k9_subset_1(u1_struct_0(X1),X0,X5) = X4 & v4_pre_topc(X5,X1) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~sP0(X0,X1)))),
% 1.55/0.58    inference(rectify,[],[f63])).
% 1.55/0.58  fof(f63,plain,(
% 1.55/0.58    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X1,X0)))),
% 1.55/0.58    inference(nnf_transformation,[],[f55])).
% 1.55/0.58  fof(f896,plain,(
% 1.55/0.58    ( ! [X0,X1] : (k1_xboole_0 != sK4(X1,X0) | sP0(X1,X0) | ~v4_pre_topc(k1_xboole_0,X0)) )),
% 1.55/0.58    inference(subsumption_resolution,[],[f891,f79])).
% 1.55/0.58  fof(f891,plain,(
% 1.55/0.58    ( ! [X0,X1] : (k1_xboole_0 != sK4(X1,X0) | sP0(X1,X0) | ~v4_pre_topc(k1_xboole_0,X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.55/0.58    inference(superposition,[],[f95,f192])).
% 1.55/0.58  fof(f192,plain,(
% 1.55/0.58    ( ! [X0,X1] : (k1_xboole_0 = k9_subset_1(X0,X1,k1_xboole_0)) )),
% 1.55/0.58    inference(forward_demodulation,[],[f187,f128])).
% 1.55/0.58  fof(f128,plain,(
% 1.55/0.58    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.55/0.58    inference(superposition,[],[f126,f118])).
% 1.55/0.58  fof(f118,plain,(
% 1.55/0.58    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 1.55/0.58    inference(resolution,[],[f97,f105])).
% 1.55/0.58  fof(f105,plain,(
% 1.55/0.58    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.55/0.58    inference(cnf_transformation,[],[f2])).
% 1.55/0.58  fof(f2,axiom,(
% 1.55/0.58    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.55/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.55/0.58  fof(f126,plain,(
% 1.55/0.58    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) )),
% 1.55/0.58    inference(superposition,[],[f122,f107])).
% 1.55/0.58  fof(f107,plain,(
% 1.55/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.55/0.58    inference(cnf_transformation,[],[f9])).
% 1.55/0.58  fof(f9,axiom,(
% 1.55/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.55/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.55/0.58  fof(f122,plain,(
% 1.55/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) )),
% 1.55/0.58    inference(superposition,[],[f107,f106])).
% 1.55/0.58  fof(f106,plain,(
% 1.55/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.55/0.58    inference(cnf_transformation,[],[f4])).
% 1.55/0.58  fof(f4,axiom,(
% 1.55/0.58    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.55/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.55/0.58  fof(f187,plain,(
% 1.55/0.58    ( ! [X0,X1] : (k3_xboole_0(X1,k1_xboole_0) = k9_subset_1(X0,X1,k1_xboole_0)) )),
% 1.55/0.58    inference(resolution,[],[f110,f79])).
% 1.55/0.58  fof(f110,plain,(
% 1.55/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 1.55/0.58    inference(cnf_transformation,[],[f53])).
% 1.55/0.58  fof(f53,plain,(
% 1.55/0.58    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.55/0.58    inference(ennf_transformation,[],[f7])).
% 1.55/0.58  fof(f7,axiom,(
% 1.55/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 1.55/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 1.55/0.58  fof(f95,plain,(
% 1.55/0.58    ( ! [X0,X3,X1] : (k9_subset_1(u1_struct_0(X1),X0,X3) != sK4(X0,X1) | sP0(X0,X1) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) )),
% 1.55/0.58    inference(cnf_transformation,[],[f67])).
% 1.55/0.58  % SZS output end Proof for theBenchmark
% 1.55/0.58  % (13853)------------------------------
% 1.55/0.58  % (13853)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.58  % (13853)Termination reason: Refutation
% 1.55/0.58  
% 1.55/0.58  % (13853)Memory used [KB]: 7036
% 1.55/0.58  % (13853)Time elapsed: 0.169 s
% 1.55/0.58  % (13853)------------------------------
% 1.55/0.58  % (13853)------------------------------
% 1.55/0.59  % (13845)Success in time 0.221 s
%------------------------------------------------------------------------------
