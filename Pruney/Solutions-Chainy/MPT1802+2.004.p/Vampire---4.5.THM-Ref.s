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
% DateTime   : Thu Dec  3 13:19:36 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  188 (1312 expanded)
%              Number of leaves         :   20 ( 246 expanded)
%              Depth                    :   28
%              Number of atoms          :  833 (8829 expanded)
%              Number of equality atoms :   57 ( 409 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1235,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f452,f469,f659,f1156,f1174,f1234])).

fof(f1234,plain,
    ( ~ spl6_34
    | ~ spl6_46 ),
    inference(avatar_contradiction_clause,[],[f1233])).

fof(f1233,plain,
    ( $false
    | ~ spl6_34
    | ~ spl6_46 ),
    inference(subsumption_resolution,[],[f1232,f42])).

fof(f42,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3)
                  & m1_subset_1(X3,u1_struct_0(X2)) )
              & r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3)
                  & m1_subset_1(X3,u1_struct_0(X2)) )
              & r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( r1_tsep_1(X1,X2)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X2))
                     => r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( r1_tsep_1(X1,X2)
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X2))
                   => r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_tmap_1)).

fof(f1232,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ spl6_34
    | ~ spl6_46 ),
    inference(resolution,[],[f1185,f43])).

fof(f43,plain,(
    ~ r1_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f1185,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK2)) )
    | ~ spl6_34
    | ~ spl6_46 ),
    inference(backward_demodulation,[],[f1014,f993])).

fof(f993,plain,
    ( k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl6_46 ),
    inference(avatar_component_clause,[],[f991])).

fof(f991,plain,
    ( spl6_46
  <=> k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f1014,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),sK2),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK2)) )
    | ~ spl6_34 ),
    inference(subsumption_resolution,[],[f1013,f45])).

fof(f45,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f1013,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,sK0)
        | r1_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),sK2),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK2)) )
    | ~ spl6_34 ),
    inference(subsumption_resolution,[],[f1011,f44])).

fof(f44,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f1011,plain,
    ( ! [X0] :
        ( v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,sK0)
        | r1_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),sK2),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK2)) )
    | ~ spl6_34 ),
    inference(resolution,[],[f898,f108])).

fof(f108,plain,(
    r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(resolution,[],[f106,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f106,plain,(
    r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f105,f97])).

fof(f97,plain,(
    l1_pre_topc(sK1) ),
    inference(resolution,[],[f95,f48])).

fof(f48,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f95,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | l1_pre_topc(X0) ) ),
    inference(resolution,[],[f55,f51])).

fof(f51,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f105,plain,
    ( r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f103,f46])).

fof(f46,plain,(
    r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f103,plain,(
    ! [X1] :
      ( ~ r1_tsep_1(X1,sK2)
      | r1_xboole_0(u1_struct_0(X1),u1_struct_0(sK2))
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f101,f96])).

fof(f96,plain,(
    l1_pre_topc(sK2) ),
    inference(resolution,[],[f95,f45])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ r1_tsep_1(X0,X1)
      | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f100,f54])).

fof(f54,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f53,f54])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0)
      | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ r1_tsep_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).

fof(f898,plain,
    ( ! [X8,X9] :
        ( ~ r1_xboole_0(u1_struct_0(X8),u1_struct_0(sK1))
        | v2_struct_0(X8)
        | ~ m1_pre_topc(X8,sK0)
        | r1_tmap_1(X8,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X8),X9)
        | ~ m1_subset_1(X9,u1_struct_0(X8)) )
    | ~ spl6_34 ),
    inference(forward_demodulation,[],[f879,f232])).

fof(f232,plain,(
    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) ),
    inference(resolution,[],[f230,f48])).

fof(f230,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | k8_tmap_1(sK0,X0) = k6_tmap_1(sK0,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f229,f51])).

fof(f229,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | k8_tmap_1(sK0,X0) = k6_tmap_1(sK0,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f226,f49])).

fof(f49,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f226,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | k8_tmap_1(sK0,X0) = k6_tmap_1(sK0,u1_struct_0(X0)) ) ),
    inference(resolution,[],[f91,f50])).

fof(f50,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f90,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v1_pre_topc(k8_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_tmap_1)).

fof(f90,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_pre_topc(k8_tmap_1(X0,X1))
      | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f89,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(k8_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f89,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ v2_pre_topc(k8_tmap_1(X0,X1))
      | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f87,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(k8_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f87,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ l1_pre_topc(k8_tmap_1(X0,X1))
      | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f82,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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

fof(f82,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | k6_tmap_1(X0,u1_struct_0(X1)) = X2
      | k8_tmap_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X3
      | k6_tmap_1(X0,X3) = X2
      | k8_tmap_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( k6_tmap_1(X0,X3) = X2
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( k6_tmap_1(X0,X3) = X2
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2)
                & v1_pre_topc(X2) )
             => ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( u1_struct_0(X1) = X3
                     => k6_tmap_1(X0,X3) = X2 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_tmap_1)).

fof(f879,plain,
    ( ! [X8,X9] :
        ( v2_struct_0(X8)
        | ~ m1_pre_topc(X8,sK0)
        | ~ r1_xboole_0(u1_struct_0(X8),u1_struct_0(sK1))
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | r1_tmap_1(X8,k6_tmap_1(sK0,u1_struct_0(sK1)),k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),X8),X9) )
    | ~ spl6_34 ),
    inference(resolution,[],[f875,f446])).

fof(f446,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f445])).

fof(f445,plain,
    ( spl6_34
  <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f875,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,sK0)
      | ~ r1_xboole_0(u1_struct_0(X1),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | r1_tmap_1(X1,k6_tmap_1(sK0,X0),k2_tmap_1(sK0,k6_tmap_1(sK0,X0),k7_tmap_1(sK0,X0),X1),X2) ) ),
    inference(subsumption_resolution,[],[f874,f51])).

fof(f874,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,sK0)
      | ~ r1_xboole_0(u1_struct_0(X1),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | r1_tmap_1(X1,k6_tmap_1(sK0,X0),k2_tmap_1(sK0,k6_tmap_1(sK0,X0),k7_tmap_1(sK0,X0),X1),X2) ) ),
    inference(subsumption_resolution,[],[f872,f49])).

fof(f872,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,sK0)
      | ~ r1_xboole_0(u1_struct_0(X1),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | r1_tmap_1(X1,k6_tmap_1(sK0,X0),k2_tmap_1(sK0,k6_tmap_1(sK0,X0),k7_tmap_1(sK0,X0),X1),X2) ) ),
    inference(resolution,[],[f68,f50])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ r1_xboole_0(u1_struct_0(X2),X1)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X2)) )
              | ~ r1_xboole_0(u1_struct_0(X2),X1)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X2)) )
              | ~ r1_xboole_0(u1_struct_0(X2),X1)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( r1_xboole_0(u1_struct_0(X2),X1)
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X2))
                   => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_tmap_1)).

fof(f1174,plain,
    ( spl6_38
    | ~ spl6_49 ),
    inference(avatar_contradiction_clause,[],[f1173])).

fof(f1173,plain,
    ( $false
    | spl6_38
    | ~ spl6_49 ),
    inference(subsumption_resolution,[],[f1172,f410])).

fof(f410,plain,(
    v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f409,f49])).

fof(f409,plain,
    ( v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f408,f48])).

fof(f408,plain,
    ( v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f407,f51])).

fof(f407,plain,
    ( v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f402,f50])).

fof(f402,plain,
    ( v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f74,f244])).

fof(f244,plain,(
    u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f241,f232])).

fof(f241,plain,(
    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))) ),
    inference(resolution,[],[f239,f48])).

fof(f239,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0))) ) ),
    inference(subsumption_resolution,[],[f238,f51])).

fof(f238,plain,(
    ! [X0] :
      ( u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0)))
      | ~ m1_pre_topc(X0,sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f237,f56])).

fof(f237,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f236,f51])).

fof(f236,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f233,f49])).

fof(f233,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X0)) ) ),
    inference(resolution,[],[f66,f50])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).

fof(f74,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_tmap_1)).

fof(f1172,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
    | spl6_38
    | ~ spl6_49 ),
    inference(forward_demodulation,[],[f1171,f244])).

fof(f1171,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | spl6_38
    | ~ spl6_49 ),
    inference(subsumption_resolution,[],[f1170,f637])).

fof(f637,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl6_38 ),
    inference(avatar_component_clause,[],[f636])).

fof(f636,plain,
    ( spl6_38
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f1170,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ spl6_49 ),
    inference(forward_demodulation,[],[f1169,f244])).

fof(f1169,plain,
    ( v1_xboole_0(u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ spl6_49 ),
    inference(subsumption_resolution,[],[f1168,f614])).

fof(f614,plain,(
    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1))) ),
    inference(forward_demodulation,[],[f613,f244])).

fof(f613,plain,(
    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1))) ),
    inference(forward_demodulation,[],[f612,f232])).

fof(f612,plain,(
    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f611,f49])).

fof(f611,plain,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f610,f48])).

fof(f610,plain,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f609,f51])).

fof(f609,plain,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f598,f50])).

fof(f598,plain,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f94,f244])).

fof(f94,plain,(
    ! [X0,X1] :
      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f93,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v1_funct_1(k9_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f93,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(k9_tmap_1(X0,X1))
      | r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1))) ) ),
    inference(subsumption_resolution,[],[f92,f74])).

fof(f92,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(k9_tmap_1(X0,X1))
      | ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1))) ) ),
    inference(subsumption_resolution,[],[f88,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f88,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(k9_tmap_1(X0,X1))
      | ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1))) ) ),
    inference(subsumption_resolution,[],[f84,f56])).

fof(f84,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(k9_tmap_1(X0,X1))
      | ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1))) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),X2,k7_tmap_1(X0,u1_struct_0(X1)))
      | k9_tmap_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X3
      | r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
      | k9_tmap_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k9_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k9_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
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
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
                & v1_funct_1(X2) )
             => ( k9_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( u1_struct_0(X1) = X3
                     => r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_tmap_1)).

fof(f1168,plain,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ spl6_49 ),
    inference(forward_demodulation,[],[f1167,f244])).

fof(f1167,plain,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ spl6_49 ),
    inference(subsumption_resolution,[],[f1166,f49])).

fof(f1166,plain,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | v2_struct_0(sK0)
    | ~ spl6_49 ),
    inference(subsumption_resolution,[],[f1165,f48])).

fof(f1165,plain,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl6_49 ),
    inference(subsumption_resolution,[],[f1164,f51])).

fof(f1164,plain,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl6_49 ),
    inference(subsumption_resolution,[],[f1159,f50])).

fof(f1159,plain,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl6_49 ),
    inference(resolution,[],[f1155,f75])).

fof(f1155,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ r1_funct_2(X0,X1,u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)))
        | v1_xboole_0(X1)
        | ~ v1_funct_2(k9_tmap_1(sK0,sK1),X0,X1) )
    | ~ spl6_49 ),
    inference(avatar_component_clause,[],[f1154])).

fof(f1154,plain,
    ( spl6_49
  <=> ! [X1,X0] :
        ( ~ v1_funct_2(k9_tmap_1(sK0,sK1),X0,X1)
        | ~ r1_funct_2(X0,X1,u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)))
        | v1_xboole_0(X1)
        | ~ m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).

fof(f1156,plain,
    ( spl6_46
    | spl6_49
    | ~ spl6_34
    | ~ spl6_35
    | spl6_38 ),
    inference(avatar_split_clause,[],[f1150,f636,f449,f445,f1154,f991])).

fof(f449,plain,
    ( spl6_35
  <=> v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f1150,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(k9_tmap_1(sK0,sK1),X0,X1)
        | ~ m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_xboole_0(X1)
        | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
        | ~ r1_funct_2(X0,X1,u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1))) )
    | ~ spl6_34
    | ~ spl6_35
    | spl6_38 ),
    inference(resolution,[],[f1137,f216])).

fof(f216,plain,(
    v1_funct_1(k9_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f214,f48])).

fof(f214,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | v1_funct_1(k9_tmap_1(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f213,f51])).

fof(f213,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | v1_funct_1(k9_tmap_1(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f210,f49])).

fof(f210,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | v1_funct_1(k9_tmap_1(sK0,X0)) ) ),
    inference(resolution,[],[f73,f50])).

fof(f1137,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,X1,X2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | v1_xboole_0(X2)
        | k7_tmap_1(sK0,u1_struct_0(sK1)) = X0
        | ~ r1_funct_2(X1,X2,u1_struct_0(sK0),u1_struct_0(sK0),X0,k7_tmap_1(sK0,u1_struct_0(sK1))) )
    | ~ spl6_34
    | ~ spl6_35
    | spl6_38 ),
    inference(subsumption_resolution,[],[f1136,f637])).

fof(f1136,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,X1,X2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | v1_xboole_0(X2)
        | v1_xboole_0(u1_struct_0(sK0))
        | k7_tmap_1(sK0,u1_struct_0(sK1)) = X0
        | ~ r1_funct_2(X1,X2,u1_struct_0(sK0),u1_struct_0(sK0),X0,k7_tmap_1(sK0,u1_struct_0(sK1))) )
    | ~ spl6_34
    | ~ spl6_35 ),
    inference(subsumption_resolution,[],[f1134,f451])).

fof(f451,plain,
    ( v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl6_35 ),
    inference(avatar_component_clause,[],[f449])).

fof(f1134,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,X1,X2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | v1_xboole_0(X2)
        | ~ v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0))
        | v1_xboole_0(u1_struct_0(sK0))
        | k7_tmap_1(sK0,u1_struct_0(sK1)) = X0
        | ~ r1_funct_2(X1,X2,u1_struct_0(sK0),u1_struct_0(sK0),X0,k7_tmap_1(sK0,u1_struct_0(sK1))) )
    | ~ spl6_34 ),
    inference(resolution,[],[f699,f488])).

fof(f488,plain,
    ( m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl6_34 ),
    inference(forward_demodulation,[],[f487,f244])).

fof(f487,plain,
    ( m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ spl6_34 ),
    inference(subsumption_resolution,[],[f486,f49])).

fof(f486,plain,
    ( m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | v2_struct_0(sK0)
    | ~ spl6_34 ),
    inference(subsumption_resolution,[],[f485,f446])).

fof(f485,plain,
    ( m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f484,f51])).

fof(f484,plain,
    ( m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f478,f50])).

fof(f478,plain,
    ( m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f78,f232])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_tmap_1)).

fof(f699,plain,(
    ! [X19,X17,X15,X18,X16] :
      ( ~ m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(X19,X15)))
      | ~ v1_funct_1(X16)
      | ~ v1_funct_2(X16,X17,X18)
      | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))
      | v1_xboole_0(X18)
      | ~ v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),X19,X15)
      | v1_xboole_0(X15)
      | k7_tmap_1(sK0,u1_struct_0(sK1)) = X16
      | ~ r1_funct_2(X17,X18,X19,X15,X16,k7_tmap_1(sK0,u1_struct_0(sK1))) ) ),
    inference(resolution,[],[f80,f225])).

fof(f225,plain,(
    v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) ),
    inference(resolution,[],[f223,f48])).

fof(f223,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | v1_funct_1(k7_tmap_1(sK0,u1_struct_0(X0))) ) ),
    inference(subsumption_resolution,[],[f222,f51])).

fof(f222,plain,(
    ! [X0] :
      ( v1_funct_1(k7_tmap_1(sK0,u1_struct_0(X0)))
      | ~ m1_pre_topc(X0,sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f221,f56])).

fof(f221,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_funct_1(k7_tmap_1(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f220,f51])).

fof(f220,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_funct_1(k7_tmap_1(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f217,f49])).

fof(f217,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_funct_1(k7_tmap_1(sK0,X0)) ) ),
    inference(resolution,[],[f76,f50])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_funct_1(k7_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f80,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X5)
      | v1_xboole_0(X3)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X0,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | ~ v1_funct_2(X5,X2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | X4 = X5
      | ~ r1_funct_2(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_2(X5,X2,X3)
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4)
        & ~ v1_xboole_0(X3)
        & ~ v1_xboole_0(X1) )
     => ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

fof(f659,plain,(
    ~ spl6_38 ),
    inference(avatar_contradiction_clause,[],[f658])).

fof(f658,plain,
    ( $false
    | ~ spl6_38 ),
    inference(subsumption_resolution,[],[f657,f51])).

fof(f657,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl6_38 ),
    inference(resolution,[],[f656,f54])).

fof(f656,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl6_38 ),
    inference(subsumption_resolution,[],[f655,f49])).

fof(f655,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_38 ),
    inference(resolution,[],[f638,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f638,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl6_38 ),
    inference(avatar_component_clause,[],[f636])).

fof(f469,plain,(
    spl6_34 ),
    inference(avatar_contradiction_clause,[],[f468])).

fof(f468,plain,
    ( $false
    | spl6_34 ),
    inference(subsumption_resolution,[],[f467,f51])).

fof(f467,plain,
    ( ~ l1_pre_topc(sK0)
    | spl6_34 ),
    inference(subsumption_resolution,[],[f466,f48])).

fof(f466,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | spl6_34 ),
    inference(resolution,[],[f447,f56])).

fof(f447,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_34 ),
    inference(avatar_component_clause,[],[f445])).

fof(f452,plain,
    ( ~ spl6_34
    | spl6_35 ),
    inference(avatar_split_clause,[],[f443,f449,f445])).

fof(f443,plain,
    ( v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f442,f244])).

fof(f442,plain,
    ( v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f441,f49])).

fof(f441,plain,
    ( v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f440,f51])).

fof(f440,plain,
    ( v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f426,f50])).

fof(f426,plain,
    ( v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f77,f232])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 14:17:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.52  % (11483)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.52  % (11485)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.52  % (11476)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.52  % (11475)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.52  % (11491)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.52  % (11477)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.53  % (11490)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.53  % (11478)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.53  % (11492)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.53  % (11493)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.53  % (11483)Refutation not found, incomplete strategy% (11483)------------------------------
% 0.20/0.53  % (11483)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (11494)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.53  % (11483)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (11483)Memory used [KB]: 10746
% 0.20/0.53  % (11483)Time elapsed: 0.089 s
% 0.20/0.53  % (11483)------------------------------
% 0.20/0.53  % (11483)------------------------------
% 0.20/0.54  % (11484)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.54  % (11485)Refutation not found, incomplete strategy% (11485)------------------------------
% 0.20/0.54  % (11485)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (11485)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (11485)Memory used [KB]: 6396
% 0.20/0.54  % (11485)Time elapsed: 0.132 s
% 0.20/0.54  % (11485)------------------------------
% 0.20/0.54  % (11485)------------------------------
% 0.20/0.54  % (11479)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.54  % (11486)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.54  % (11477)Refutation not found, incomplete strategy% (11477)------------------------------
% 0.20/0.54  % (11477)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (11477)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (11477)Memory used [KB]: 6396
% 0.20/0.54  % (11477)Time elapsed: 0.113 s
% 0.20/0.54  % (11477)------------------------------
% 0.20/0.54  % (11477)------------------------------
% 0.20/0.54  % (11487)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.55  % (11478)Refutation not found, incomplete strategy% (11478)------------------------------
% 0.20/0.55  % (11478)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (11478)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (11478)Memory used [KB]: 10746
% 0.20/0.55  % (11478)Time elapsed: 0.121 s
% 0.20/0.55  % (11478)------------------------------
% 0.20/0.55  % (11478)------------------------------
% 0.20/0.55  % (11472)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.56  % (11495)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.56  % (11482)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.57  % (11479)Refutation not found, incomplete strategy% (11479)------------------------------
% 0.20/0.57  % (11479)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (11479)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.57  
% 0.20/0.57  % (11479)Memory used [KB]: 1918
% 0.20/0.57  % (11479)Time elapsed: 0.122 s
% 0.20/0.57  % (11479)------------------------------
% 0.20/0.57  % (11479)------------------------------
% 0.20/0.57  % (11489)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.57  % (11480)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.57  % (11496)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.58  % (11473)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.58  % (11472)Refutation not found, incomplete strategy% (11472)------------------------------
% 0.20/0.58  % (11472)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.58  % (11472)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.58  
% 0.20/0.58  % (11472)Memory used [KB]: 10618
% 0.20/0.58  % (11472)Time elapsed: 0.142 s
% 0.20/0.58  % (11472)------------------------------
% 0.20/0.58  % (11472)------------------------------
% 0.20/0.58  % (11494)Refutation found. Thanks to Tanya!
% 0.20/0.58  % SZS status Theorem for theBenchmark
% 0.20/0.58  % SZS output start Proof for theBenchmark
% 0.20/0.58  fof(f1235,plain,(
% 0.20/0.58    $false),
% 0.20/0.58    inference(avatar_sat_refutation,[],[f452,f469,f659,f1156,f1174,f1234])).
% 0.20/0.58  fof(f1234,plain,(
% 0.20/0.58    ~spl6_34 | ~spl6_46),
% 0.20/0.58    inference(avatar_contradiction_clause,[],[f1233])).
% 0.20/0.58  fof(f1233,plain,(
% 0.20/0.58    $false | (~spl6_34 | ~spl6_46)),
% 0.20/0.58    inference(subsumption_resolution,[],[f1232,f42])).
% 0.20/0.58  fof(f42,plain,(
% 0.20/0.58    m1_subset_1(sK3,u1_struct_0(sK2))),
% 0.20/0.58    inference(cnf_transformation,[],[f18])).
% 0.20/0.58  fof(f18,plain,(
% 0.20/0.58    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.58    inference(flattening,[],[f17])).
% 0.20/0.58  fof(f17,plain,(
% 0.20/0.58    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (~r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_tsep_1(X1,X2)) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.58    inference(ennf_transformation,[],[f16])).
% 0.20/0.58  fof(f16,negated_conjecture,(
% 0.20/0.58    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_tsep_1(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X2)) => r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3))))))),
% 0.20/0.58    inference(negated_conjecture,[],[f15])).
% 0.20/0.58  fof(f15,conjecture,(
% 0.20/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_tsep_1(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X2)) => r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3))))))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_tmap_1)).
% 0.20/0.58  fof(f1232,plain,(
% 0.20/0.58    ~m1_subset_1(sK3,u1_struct_0(sK2)) | (~spl6_34 | ~spl6_46)),
% 0.20/0.58    inference(resolution,[],[f1185,f43])).
% 0.20/0.58  fof(f43,plain,(
% 0.20/0.58    ~r1_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),sK3)),
% 0.20/0.58    inference(cnf_transformation,[],[f18])).
% 0.20/0.58  fof(f1185,plain,(
% 0.20/0.58    ( ! [X0] : (r1_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),X0) | ~m1_subset_1(X0,u1_struct_0(sK2))) ) | (~spl6_34 | ~spl6_46)),
% 0.20/0.58    inference(backward_demodulation,[],[f1014,f993])).
% 0.20/0.58  fof(f993,plain,(
% 0.20/0.58    k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | ~spl6_46),
% 0.20/0.58    inference(avatar_component_clause,[],[f991])).
% 0.20/0.58  fof(f991,plain,(
% 0.20/0.58    spl6_46 <=> k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).
% 0.20/0.58  fof(f1014,plain,(
% 0.20/0.58    ( ! [X0] : (r1_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),sK2),X0) | ~m1_subset_1(X0,u1_struct_0(sK2))) ) | ~spl6_34),
% 0.20/0.58    inference(subsumption_resolution,[],[f1013,f45])).
% 0.20/0.58  fof(f45,plain,(
% 0.20/0.58    m1_pre_topc(sK2,sK0)),
% 0.20/0.58    inference(cnf_transformation,[],[f18])).
% 0.20/0.58  fof(f1013,plain,(
% 0.20/0.58    ( ! [X0] : (~m1_pre_topc(sK2,sK0) | r1_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),sK2),X0) | ~m1_subset_1(X0,u1_struct_0(sK2))) ) | ~spl6_34),
% 0.20/0.58    inference(subsumption_resolution,[],[f1011,f44])).
% 0.20/0.58  fof(f44,plain,(
% 0.20/0.58    ~v2_struct_0(sK2)),
% 0.20/0.58    inference(cnf_transformation,[],[f18])).
% 0.20/0.58  fof(f1011,plain,(
% 0.20/0.58    ( ! [X0] : (v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | r1_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),sK2),X0) | ~m1_subset_1(X0,u1_struct_0(sK2))) ) | ~spl6_34),
% 0.20/0.58    inference(resolution,[],[f898,f108])).
% 0.20/0.58  fof(f108,plain,(
% 0.20/0.58    r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1))),
% 0.20/0.58    inference(resolution,[],[f106,f69])).
% 0.20/0.58  fof(f69,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f33])).
% 0.20/0.58  fof(f33,plain,(
% 0.20/0.58    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.20/0.58    inference(ennf_transformation,[],[f1])).
% 0.20/0.58  fof(f1,axiom,(
% 0.20/0.58    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.20/0.58  fof(f106,plain,(
% 0.20/0.58    r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))),
% 0.20/0.58    inference(subsumption_resolution,[],[f105,f97])).
% 0.20/0.58  fof(f97,plain,(
% 0.20/0.58    l1_pre_topc(sK1)),
% 0.20/0.58    inference(resolution,[],[f95,f48])).
% 0.20/0.58  fof(f48,plain,(
% 0.20/0.58    m1_pre_topc(sK1,sK0)),
% 0.20/0.58    inference(cnf_transformation,[],[f18])).
% 0.20/0.58  fof(f95,plain,(
% 0.20/0.58    ( ! [X0] : (~m1_pre_topc(X0,sK0) | l1_pre_topc(X0)) )),
% 0.20/0.58    inference(resolution,[],[f55,f51])).
% 0.20/0.58  fof(f51,plain,(
% 0.20/0.58    l1_pre_topc(sK0)),
% 0.20/0.58    inference(cnf_transformation,[],[f18])).
% 0.20/0.58  fof(f55,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f21])).
% 0.20/0.58  fof(f21,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.58    inference(ennf_transformation,[],[f3])).
% 0.20/0.58  fof(f3,axiom,(
% 0.20/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.20/0.58  fof(f105,plain,(
% 0.20/0.58    r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) | ~l1_pre_topc(sK1)),
% 0.20/0.58    inference(resolution,[],[f103,f46])).
% 0.20/0.58  fof(f46,plain,(
% 0.20/0.58    r1_tsep_1(sK1,sK2)),
% 0.20/0.58    inference(cnf_transformation,[],[f18])).
% 0.20/0.58  fof(f103,plain,(
% 0.20/0.58    ( ! [X1] : (~r1_tsep_1(X1,sK2) | r1_xboole_0(u1_struct_0(X1),u1_struct_0(sK2)) | ~l1_pre_topc(X1)) )),
% 0.20/0.58    inference(resolution,[],[f101,f96])).
% 0.20/0.58  fof(f96,plain,(
% 0.20/0.58    l1_pre_topc(sK2)),
% 0.20/0.58    inference(resolution,[],[f95,f45])).
% 0.20/0.58  fof(f101,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~l1_pre_topc(X1) | ~r1_tsep_1(X0,X1) | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X0)) )),
% 0.20/0.58    inference(resolution,[],[f100,f54])).
% 0.20/0.58  fof(f54,plain,(
% 0.20/0.58    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f20])).
% 0.20/0.58  fof(f20,plain,(
% 0.20/0.58    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.58    inference(ennf_transformation,[],[f2])).
% 0.20/0.58  fof(f2,axiom,(
% 0.20/0.58    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.58  fof(f100,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~l1_struct_0(X0) | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1) | ~l1_pre_topc(X1)) )),
% 0.20/0.58    inference(resolution,[],[f53,f54])).
% 0.20/0.58  fof(f53,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~l1_struct_0(X1) | ~l1_struct_0(X0) | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f19])).
% 0.20/0.58  fof(f19,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : ((r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.20/0.58    inference(ennf_transformation,[],[f8])).
% 0.20/0.58  fof(f8,axiom,(
% 0.20/0.58    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => (r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)))))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).
% 0.20/0.58  fof(f898,plain,(
% 0.20/0.58    ( ! [X8,X9] : (~r1_xboole_0(u1_struct_0(X8),u1_struct_0(sK1)) | v2_struct_0(X8) | ~m1_pre_topc(X8,sK0) | r1_tmap_1(X8,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X8),X9) | ~m1_subset_1(X9,u1_struct_0(X8))) ) | ~spl6_34),
% 0.20/0.58    inference(forward_demodulation,[],[f879,f232])).
% 0.20/0.58  fof(f232,plain,(
% 0.20/0.58    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))),
% 0.20/0.58    inference(resolution,[],[f230,f48])).
% 0.20/0.58  fof(f230,plain,(
% 0.20/0.58    ( ! [X0] : (~m1_pre_topc(X0,sK0) | k8_tmap_1(sK0,X0) = k6_tmap_1(sK0,u1_struct_0(X0))) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f229,f51])).
% 0.20/0.58  fof(f229,plain,(
% 0.20/0.58    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | k8_tmap_1(sK0,X0) = k6_tmap_1(sK0,u1_struct_0(X0))) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f226,f49])).
% 0.20/0.58  fof(f49,plain,(
% 0.20/0.58    ~v2_struct_0(sK0)),
% 0.20/0.58    inference(cnf_transformation,[],[f18])).
% 0.20/0.58  fof(f226,plain,(
% 0.20/0.58    ( ! [X0] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | k8_tmap_1(sK0,X0) = k6_tmap_1(sK0,u1_struct_0(X0))) )),
% 0.20/0.58    inference(resolution,[],[f91,f50])).
% 0.20/0.58  fof(f50,plain,(
% 0.20/0.58    v2_pre_topc(sK0)),
% 0.20/0.58    inference(cnf_transformation,[],[f18])).
% 0.20/0.58  fof(f91,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f90,f70])).
% 0.20/0.58  fof(f70,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v1_pre_topc(k8_tmap_1(X0,X1))) )),
% 0.20/0.58    inference(cnf_transformation,[],[f35])).
% 0.20/0.58  fof(f35,plain,(
% 0.20/0.58    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.58    inference(flattening,[],[f34])).
% 0.20/0.58  fof(f34,plain,(
% 0.20/0.58    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.58    inference(ennf_transformation,[],[f10])).
% 0.20/0.58  fof(f10,axiom,(
% 0.20/0.58    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_tmap_1)).
% 0.20/0.58  fof(f90,plain,(
% 0.20/0.58    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v1_pre_topc(k8_tmap_1(X0,X1)) | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f89,f71])).
% 0.20/0.58  fof(f71,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_pre_topc(k8_tmap_1(X0,X1))) )),
% 0.20/0.58    inference(cnf_transformation,[],[f35])).
% 0.20/0.58  fof(f89,plain,(
% 0.20/0.58    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v1_pre_topc(k8_tmap_1(X0,X1)) | ~v2_pre_topc(k8_tmap_1(X0,X1)) | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f87,f72])).
% 0.20/0.58  fof(f72,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(k8_tmap_1(X0,X1))) )),
% 0.20/0.58    inference(cnf_transformation,[],[f35])).
% 0.20/0.58  fof(f87,plain,(
% 0.20/0.58    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v1_pre_topc(k8_tmap_1(X0,X1)) | ~v2_pre_topc(k8_tmap_1(X0,X1)) | ~l1_pre_topc(k8_tmap_1(X0,X1)) | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f82,f56])).
% 0.20/0.58  fof(f56,plain,(
% 0.20/0.58    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f22])).
% 0.20/0.58  fof(f22,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.58    inference(ennf_transformation,[],[f14])).
% 0.20/0.58  fof(f14,axiom,(
% 0.20/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.20/0.58  fof(f82,plain,(
% 0.20/0.58    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v1_pre_topc(k8_tmap_1(X0,X1)) | ~v2_pre_topc(k8_tmap_1(X0,X1)) | ~l1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))) )),
% 0.20/0.58    inference(equality_resolution,[],[f81])).
% 0.20/0.58  fof(f81,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k6_tmap_1(X0,u1_struct_0(X1)) = X2 | k8_tmap_1(X0,X1) != X2) )),
% 0.20/0.58    inference(equality_resolution,[],[f58])).
% 0.20/0.58  fof(f58,plain,(
% 0.20/0.58    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X3 | k6_tmap_1(X0,X3) = X2 | k8_tmap_1(X0,X1) != X2) )),
% 0.20/0.58    inference(cnf_transformation,[],[f26])).
% 0.20/0.58  fof(f26,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.58    inference(flattening,[],[f25])).
% 0.20/0.58  fof(f25,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : ((k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.58    inference(ennf_transformation,[],[f6])).
% 0.20/0.58  fof(f6,axiom,(
% 0.20/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & v1_pre_topc(X2)) => (k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => k6_tmap_1(X0,X3) = X2))))))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_tmap_1)).
% 0.20/0.58  fof(f879,plain,(
% 0.20/0.58    ( ! [X8,X9] : (v2_struct_0(X8) | ~m1_pre_topc(X8,sK0) | ~r1_xboole_0(u1_struct_0(X8),u1_struct_0(sK1)) | ~m1_subset_1(X9,u1_struct_0(X8)) | r1_tmap_1(X8,k6_tmap_1(sK0,u1_struct_0(sK1)),k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),X8),X9)) ) | ~spl6_34),
% 0.20/0.58    inference(resolution,[],[f875,f446])).
% 0.20/0.58  fof(f446,plain,(
% 0.20/0.58    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_34),
% 0.20/0.58    inference(avatar_component_clause,[],[f445])).
% 0.20/0.58  fof(f445,plain,(
% 0.20/0.58    spl6_34 <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).
% 0.20/0.58  fof(f875,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | ~r1_xboole_0(u1_struct_0(X1),X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | r1_tmap_1(X1,k6_tmap_1(sK0,X0),k2_tmap_1(sK0,k6_tmap_1(sK0,X0),k7_tmap_1(sK0,X0),X1),X2)) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f874,f51])).
% 0.20/0.58  fof(f874,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | ~r1_xboole_0(u1_struct_0(X1),X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | r1_tmap_1(X1,k6_tmap_1(sK0,X0),k2_tmap_1(sK0,k6_tmap_1(sK0,X0),k7_tmap_1(sK0,X0),X1),X2)) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f872,f49])).
% 0.20/0.58  fof(f872,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | ~r1_xboole_0(u1_struct_0(X1),X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | r1_tmap_1(X1,k6_tmap_1(sK0,X0),k2_tmap_1(sK0,k6_tmap_1(sK0,X0),k7_tmap_1(sK0,X0),X1),X2)) )),
% 0.20/0.58    inference(resolution,[],[f68,f50])).
% 0.20/0.58  fof(f68,plain,(
% 0.20/0.58    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~r1_xboole_0(u1_struct_0(X2),X1) | ~m1_subset_1(X3,u1_struct_0(X2)) | r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f32])).
% 0.20/0.58  fof(f32,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X3,u1_struct_0(X2))) | ~r1_xboole_0(u1_struct_0(X2),X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.58    inference(flattening,[],[f31])).
% 0.20/0.58  fof(f31,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : (r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X3,u1_struct_0(X2))) | ~r1_xboole_0(u1_struct_0(X2),X1)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.58    inference(ennf_transformation,[],[f13])).
% 0.20/0.58  fof(f13,axiom,(
% 0.20/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_xboole_0(u1_struct_0(X2),X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X2)) => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3))))))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_tmap_1)).
% 0.20/0.58  fof(f1174,plain,(
% 0.20/0.58    spl6_38 | ~spl6_49),
% 0.20/0.58    inference(avatar_contradiction_clause,[],[f1173])).
% 0.20/0.58  fof(f1173,plain,(
% 0.20/0.58    $false | (spl6_38 | ~spl6_49)),
% 0.20/0.58    inference(subsumption_resolution,[],[f1172,f410])).
% 0.20/0.58  fof(f410,plain,(
% 0.20/0.58    v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))),
% 0.20/0.58    inference(subsumption_resolution,[],[f409,f49])).
% 0.20/0.58  fof(f409,plain,(
% 0.20/0.58    v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) | v2_struct_0(sK0)),
% 0.20/0.58    inference(subsumption_resolution,[],[f408,f48])).
% 0.20/0.58  fof(f408,plain,(
% 0.20/0.58    v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0)),
% 0.20/0.58    inference(subsumption_resolution,[],[f407,f51])).
% 0.20/0.58  fof(f407,plain,(
% 0.20/0.58    v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0)),
% 0.20/0.58    inference(subsumption_resolution,[],[f402,f50])).
% 0.20/0.58  fof(f402,plain,(
% 0.20/0.58    v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0)),
% 0.20/0.58    inference(superposition,[],[f74,f244])).
% 0.20/0.58  fof(f244,plain,(
% 0.20/0.58    u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1))),
% 0.20/0.58    inference(forward_demodulation,[],[f241,f232])).
% 0.20/0.58  fof(f241,plain,(
% 0.20/0.58    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))),
% 0.20/0.58    inference(resolution,[],[f239,f48])).
% 0.20/0.58  fof(f239,plain,(
% 0.20/0.58    ( ! [X0] : (~m1_pre_topc(X0,sK0) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0)))) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f238,f51])).
% 0.20/0.58  fof(f238,plain,(
% 0.20/0.58    ( ! [X0] : (u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0))) | ~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0)) )),
% 0.20/0.58    inference(resolution,[],[f237,f56])).
% 0.20/0.58  fof(f237,plain,(
% 0.20/0.58    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X0))) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f236,f51])).
% 0.20/0.58  fof(f236,plain,(
% 0.20/0.58    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X0))) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f233,f49])).
% 0.20/0.58  fof(f233,plain,(
% 0.20/0.58    ( ! [X0] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X0))) )),
% 0.20/0.58    inference(resolution,[],[f66,f50])).
% 0.20/0.58  fof(f66,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) )),
% 0.20/0.58    inference(cnf_transformation,[],[f30])).
% 0.20/0.58  fof(f30,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.58    inference(flattening,[],[f29])).
% 0.20/0.58  fof(f29,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.58    inference(ennf_transformation,[],[f12])).
% 0.20/0.58  fof(f12,axiom,(
% 0.20/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).
% 0.20/0.58  fof(f74,plain,(
% 0.20/0.58    ( ! [X0,X1] : (v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f37])).
% 0.20/0.58  fof(f37,plain,(
% 0.20/0.58    ! [X0,X1] : ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.58    inference(flattening,[],[f36])).
% 0.20/0.58  fof(f36,plain,(
% 0.20/0.58    ! [X0,X1] : ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.58    inference(ennf_transformation,[],[f11])).
% 0.20/0.58  fof(f11,axiom,(
% 0.20/0.58    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_tmap_1)).
% 0.20/0.58  fof(f1172,plain,(
% 0.20/0.58    ~v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) | (spl6_38 | ~spl6_49)),
% 0.20/0.58    inference(forward_demodulation,[],[f1171,f244])).
% 0.20/0.58  fof(f1171,plain,(
% 0.20/0.58    ~v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | (spl6_38 | ~spl6_49)),
% 0.20/0.58    inference(subsumption_resolution,[],[f1170,f637])).
% 0.20/0.58  fof(f637,plain,(
% 0.20/0.58    ~v1_xboole_0(u1_struct_0(sK0)) | spl6_38),
% 0.20/0.58    inference(avatar_component_clause,[],[f636])).
% 0.20/0.58  fof(f636,plain,(
% 0.20/0.58    spl6_38 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).
% 0.20/0.58  fof(f1170,plain,(
% 0.20/0.58    v1_xboole_0(u1_struct_0(sK0)) | ~v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~spl6_49),
% 0.20/0.58    inference(forward_demodulation,[],[f1169,f244])).
% 0.20/0.58  fof(f1169,plain,(
% 0.20/0.58    v1_xboole_0(u1_struct_0(k8_tmap_1(sK0,sK1))) | ~v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~spl6_49),
% 0.20/0.58    inference(subsumption_resolution,[],[f1168,f614])).
% 0.20/0.58  fof(f614,plain,(
% 0.20/0.58    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)))),
% 0.20/0.58    inference(forward_demodulation,[],[f613,f244])).
% 0.20/0.58  fof(f613,plain,(
% 0.20/0.58    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)))),
% 0.20/0.58    inference(forward_demodulation,[],[f612,f232])).
% 0.20/0.58  fof(f612,plain,(
% 0.20/0.58    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)))),
% 0.20/0.58    inference(subsumption_resolution,[],[f611,f49])).
% 0.20/0.58  fof(f611,plain,(
% 0.20/0.58    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1))) | v2_struct_0(sK0)),
% 0.20/0.58    inference(subsumption_resolution,[],[f610,f48])).
% 0.20/0.58  fof(f610,plain,(
% 0.20/0.58    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1))) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0)),
% 0.20/0.58    inference(subsumption_resolution,[],[f609,f51])).
% 0.20/0.58  fof(f609,plain,(
% 0.20/0.58    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1))) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0)),
% 0.20/0.58    inference(subsumption_resolution,[],[f598,f50])).
% 0.20/0.58  fof(f598,plain,(
% 0.20/0.58    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0)),
% 0.20/0.58    inference(superposition,[],[f94,f244])).
% 0.20/0.58  fof(f94,plain,(
% 0.20/0.58    ( ! [X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0)) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f93,f73])).
% 0.20/0.58  fof(f73,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v1_funct_1(k9_tmap_1(X0,X1))) )),
% 0.20/0.58    inference(cnf_transformation,[],[f37])).
% 0.20/0.58  fof(f93,plain,(
% 0.20/0.58    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(k9_tmap_1(X0,X1)) | r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f92,f74])).
% 0.20/0.58  fof(f92,plain,(
% 0.20/0.58    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(k9_tmap_1(X0,X1)) | ~v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f88,f75])).
% 0.20/0.58  fof(f75,plain,(
% 0.20/0.58    ( ! [X0,X1] : (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f37])).
% 0.20/0.58  fof(f88,plain,(
% 0.20/0.58    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(k9_tmap_1(X0,X1)) | ~v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f84,f56])).
% 0.20/0.58  fof(f84,plain,(
% 0.20/0.58    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(k9_tmap_1(X0,X1)) | ~v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))) )),
% 0.20/0.58    inference(equality_resolution,[],[f83])).
% 0.20/0.58  fof(f83,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),X2,k7_tmap_1(X0,u1_struct_0(X1))) | k9_tmap_1(X0,X1) != X2) )),
% 0.20/0.58    inference(equality_resolution,[],[f62])).
% 0.20/0.58  fof(f62,plain,(
% 0.20/0.58    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X3 | r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | k9_tmap_1(X0,X1) != X2) )),
% 0.20/0.58    inference(cnf_transformation,[],[f28])).
% 0.20/0.58  fof(f28,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : (! [X2] : ((k9_tmap_1(X0,X1) = X2 <=> ! [X3] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.58    inference(flattening,[],[f27])).
% 0.20/0.58  fof(f27,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : (! [X2] : ((k9_tmap_1(X0,X1) = X2 <=> ! [X3] : ((r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.58    inference(ennf_transformation,[],[f7])).
% 0.20/0.58  fof(f7,axiom,(
% 0.20/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(X2)) => (k9_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))))))))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_tmap_1)).
% 0.20/0.58  fof(f1168,plain,(
% 0.20/0.58    ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1))) | v1_xboole_0(u1_struct_0(k8_tmap_1(sK0,sK1))) | ~v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~spl6_49),
% 0.20/0.58    inference(forward_demodulation,[],[f1167,f244])).
% 0.20/0.58  fof(f1167,plain,(
% 0.20/0.58    ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1))) | v1_xboole_0(u1_struct_0(k8_tmap_1(sK0,sK1))) | ~v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~spl6_49),
% 0.20/0.58    inference(subsumption_resolution,[],[f1166,f49])).
% 0.20/0.58  fof(f1166,plain,(
% 0.20/0.58    ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1))) | v1_xboole_0(u1_struct_0(k8_tmap_1(sK0,sK1))) | ~v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | v2_struct_0(sK0) | ~spl6_49),
% 0.20/0.58    inference(subsumption_resolution,[],[f1165,f48])).
% 0.20/0.58  fof(f1165,plain,(
% 0.20/0.58    ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1))) | v1_xboole_0(u1_struct_0(k8_tmap_1(sK0,sK1))) | ~v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0) | ~spl6_49),
% 0.20/0.58    inference(subsumption_resolution,[],[f1164,f51])).
% 0.20/0.58  fof(f1164,plain,(
% 0.20/0.58    ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1))) | v1_xboole_0(u1_struct_0(k8_tmap_1(sK0,sK1))) | ~v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0) | ~spl6_49),
% 0.20/0.58    inference(subsumption_resolution,[],[f1159,f50])).
% 0.20/0.58  fof(f1159,plain,(
% 0.20/0.58    ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1))) | v1_xboole_0(u1_struct_0(k8_tmap_1(sK0,sK1))) | ~v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0) | ~spl6_49),
% 0.20/0.58    inference(resolution,[],[f1155,f75])).
% 0.20/0.58  fof(f1155,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_funct_2(X0,X1,u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1))) | v1_xboole_0(X1) | ~v1_funct_2(k9_tmap_1(sK0,sK1),X0,X1)) ) | ~spl6_49),
% 0.20/0.58    inference(avatar_component_clause,[],[f1154])).
% 0.20/0.58  fof(f1154,plain,(
% 0.20/0.58    spl6_49 <=> ! [X1,X0] : (~v1_funct_2(k9_tmap_1(sK0,sK1),X0,X1) | ~r1_funct_2(X0,X1,u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1))) | v1_xboole_0(X1) | ~m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).
% 0.20/0.58  fof(f1156,plain,(
% 0.20/0.58    spl6_46 | spl6_49 | ~spl6_34 | ~spl6_35 | spl6_38),
% 0.20/0.58    inference(avatar_split_clause,[],[f1150,f636,f449,f445,f1154,f991])).
% 0.20/0.58  fof(f449,plain,(
% 0.20/0.58    spl6_35 <=> v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).
% 0.20/0.58  fof(f1150,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~v1_funct_2(k9_tmap_1(sK0,sK1),X0,X1) | ~m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | ~r1_funct_2(X0,X1,u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)))) ) | (~spl6_34 | ~spl6_35 | spl6_38)),
% 0.20/0.58    inference(resolution,[],[f1137,f216])).
% 0.20/0.58  fof(f216,plain,(
% 0.20/0.58    v1_funct_1(k9_tmap_1(sK0,sK1))),
% 0.20/0.58    inference(resolution,[],[f214,f48])).
% 0.20/0.58  fof(f214,plain,(
% 0.20/0.58    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v1_funct_1(k9_tmap_1(sK0,X0))) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f213,f51])).
% 0.20/0.58  fof(f213,plain,(
% 0.20/0.58    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | v1_funct_1(k9_tmap_1(sK0,X0))) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f210,f49])).
% 0.20/0.58  fof(f210,plain,(
% 0.20/0.58    ( ! [X0] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | v1_funct_1(k9_tmap_1(sK0,X0))) )),
% 0.20/0.58    inference(resolution,[],[f73,f50])).
% 0.20/0.58  fof(f1137,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (~v1_funct_1(X0) | ~v1_funct_2(X0,X1,X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_xboole_0(X2) | k7_tmap_1(sK0,u1_struct_0(sK1)) = X0 | ~r1_funct_2(X1,X2,u1_struct_0(sK0),u1_struct_0(sK0),X0,k7_tmap_1(sK0,u1_struct_0(sK1)))) ) | (~spl6_34 | ~spl6_35 | spl6_38)),
% 0.20/0.58    inference(subsumption_resolution,[],[f1136,f637])).
% 0.20/0.58  fof(f1136,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (~v1_funct_1(X0) | ~v1_funct_2(X0,X1,X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_xboole_0(X2) | v1_xboole_0(u1_struct_0(sK0)) | k7_tmap_1(sK0,u1_struct_0(sK1)) = X0 | ~r1_funct_2(X1,X2,u1_struct_0(sK0),u1_struct_0(sK0),X0,k7_tmap_1(sK0,u1_struct_0(sK1)))) ) | (~spl6_34 | ~spl6_35)),
% 0.20/0.58    inference(subsumption_resolution,[],[f1134,f451])).
% 0.20/0.58  fof(f451,plain,(
% 0.20/0.58    v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~spl6_35),
% 0.20/0.58    inference(avatar_component_clause,[],[f449])).
% 0.20/0.58  fof(f1134,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (~v1_funct_1(X0) | ~v1_funct_2(X0,X1,X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_xboole_0(X2) | ~v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | k7_tmap_1(sK0,u1_struct_0(sK1)) = X0 | ~r1_funct_2(X1,X2,u1_struct_0(sK0),u1_struct_0(sK0),X0,k7_tmap_1(sK0,u1_struct_0(sK1)))) ) | ~spl6_34),
% 0.20/0.58    inference(resolution,[],[f699,f488])).
% 0.20/0.58  fof(f488,plain,(
% 0.20/0.58    m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~spl6_34),
% 0.20/0.58    inference(forward_demodulation,[],[f487,f244])).
% 0.20/0.58  fof(f487,plain,(
% 0.20/0.58    m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~spl6_34),
% 0.20/0.58    inference(subsumption_resolution,[],[f486,f49])).
% 0.20/0.58  fof(f486,plain,(
% 0.20/0.58    m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | v2_struct_0(sK0) | ~spl6_34),
% 0.20/0.58    inference(subsumption_resolution,[],[f485,f446])).
% 0.20/0.58  fof(f485,plain,(
% 0.20/0.58    m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)),
% 0.20/0.58    inference(subsumption_resolution,[],[f484,f51])).
% 0.20/0.58  fof(f484,plain,(
% 0.20/0.58    m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~l1_pre_topc(sK0) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)),
% 0.20/0.58    inference(subsumption_resolution,[],[f478,f50])).
% 0.20/0.58  fof(f478,plain,(
% 0.20/0.58    m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)),
% 0.20/0.58    inference(superposition,[],[f78,f232])).
% 0.20/0.58  fof(f78,plain,(
% 0.20/0.58    ( ! [X0,X1] : (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f39])).
% 0.20/0.58  fof(f39,plain,(
% 0.20/0.58    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.58    inference(flattening,[],[f38])).
% 0.20/0.58  fof(f38,plain,(
% 0.20/0.58    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.58    inference(ennf_transformation,[],[f9])).
% 0.20/0.58  fof(f9,axiom,(
% 0.20/0.58    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_tmap_1)).
% 0.20/0.58  fof(f699,plain,(
% 0.20/0.58    ( ! [X19,X17,X15,X18,X16] : (~m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(X19,X15))) | ~v1_funct_1(X16) | ~v1_funct_2(X16,X17,X18) | ~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) | v1_xboole_0(X18) | ~v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),X19,X15) | v1_xboole_0(X15) | k7_tmap_1(sK0,u1_struct_0(sK1)) = X16 | ~r1_funct_2(X17,X18,X19,X15,X16,k7_tmap_1(sK0,u1_struct_0(sK1)))) )),
% 0.20/0.58    inference(resolution,[],[f80,f225])).
% 0.20/0.58  fof(f225,plain,(
% 0.20/0.58    v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))),
% 0.20/0.58    inference(resolution,[],[f223,f48])).
% 0.20/0.58  fof(f223,plain,(
% 0.20/0.58    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v1_funct_1(k7_tmap_1(sK0,u1_struct_0(X0)))) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f222,f51])).
% 0.20/0.58  fof(f222,plain,(
% 0.20/0.58    ( ! [X0] : (v1_funct_1(k7_tmap_1(sK0,u1_struct_0(X0))) | ~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0)) )),
% 0.20/0.58    inference(resolution,[],[f221,f56])).
% 0.20/0.58  fof(f221,plain,(
% 0.20/0.58    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_funct_1(k7_tmap_1(sK0,X0))) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f220,f51])).
% 0.20/0.58  fof(f220,plain,(
% 0.20/0.58    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_funct_1(k7_tmap_1(sK0,X0))) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f217,f49])).
% 0.20/0.58  fof(f217,plain,(
% 0.20/0.58    ( ! [X0] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_funct_1(k7_tmap_1(sK0,X0))) )),
% 0.20/0.58    inference(resolution,[],[f76,f50])).
% 0.20/0.58  fof(f76,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_funct_1(k7_tmap_1(X0,X1))) )),
% 0.20/0.58    inference(cnf_transformation,[],[f39])).
% 0.20/0.58  fof(f80,plain,(
% 0.20/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X5) | v1_xboole_0(X3) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X0,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_2(X5,X2,X3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f41])).
% 0.20/0.58  fof(f41,plain,(
% 0.20/0.58    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 0.20/0.58    inference(flattening,[],[f40])).
% 0.20/0.58  fof(f40,plain,(
% 0.20/0.58    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 0.20/0.58    inference(ennf_transformation,[],[f5])).
% 0.20/0.58  fof(f5,axiom,(
% 0.20/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_funct_2)).
% 0.20/0.58  fof(f659,plain,(
% 0.20/0.58    ~spl6_38),
% 0.20/0.58    inference(avatar_contradiction_clause,[],[f658])).
% 0.20/0.58  fof(f658,plain,(
% 0.20/0.58    $false | ~spl6_38),
% 0.20/0.58    inference(subsumption_resolution,[],[f657,f51])).
% 0.20/0.58  fof(f657,plain,(
% 0.20/0.58    ~l1_pre_topc(sK0) | ~spl6_38),
% 0.20/0.58    inference(resolution,[],[f656,f54])).
% 0.20/0.58  fof(f656,plain,(
% 0.20/0.58    ~l1_struct_0(sK0) | ~spl6_38),
% 0.20/0.58    inference(subsumption_resolution,[],[f655,f49])).
% 0.20/0.58  fof(f655,plain,(
% 0.20/0.58    ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl6_38),
% 0.20/0.58    inference(resolution,[],[f638,f57])).
% 0.20/0.58  fof(f57,plain,(
% 0.20/0.58    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f24])).
% 0.20/0.58  fof(f24,plain,(
% 0.20/0.58    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.58    inference(flattening,[],[f23])).
% 0.20/0.58  fof(f23,plain,(
% 0.20/0.58    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.58    inference(ennf_transformation,[],[f4])).
% 0.20/0.58  fof(f4,axiom,(
% 0.20/0.58    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.20/0.58  fof(f638,plain,(
% 0.20/0.58    v1_xboole_0(u1_struct_0(sK0)) | ~spl6_38),
% 0.20/0.58    inference(avatar_component_clause,[],[f636])).
% 0.20/0.58  fof(f469,plain,(
% 0.20/0.58    spl6_34),
% 0.20/0.58    inference(avatar_contradiction_clause,[],[f468])).
% 0.20/0.58  fof(f468,plain,(
% 0.20/0.58    $false | spl6_34),
% 0.20/0.58    inference(subsumption_resolution,[],[f467,f51])).
% 0.20/0.58  fof(f467,plain,(
% 0.20/0.58    ~l1_pre_topc(sK0) | spl6_34),
% 0.20/0.58    inference(subsumption_resolution,[],[f466,f48])).
% 0.20/0.58  fof(f466,plain,(
% 0.20/0.58    ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | spl6_34),
% 0.20/0.58    inference(resolution,[],[f447,f56])).
% 0.20/0.58  fof(f447,plain,(
% 0.20/0.58    ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl6_34),
% 0.20/0.58    inference(avatar_component_clause,[],[f445])).
% 0.20/0.58  fof(f452,plain,(
% 0.20/0.58    ~spl6_34 | spl6_35),
% 0.20/0.58    inference(avatar_split_clause,[],[f443,f449,f445])).
% 0.20/0.58  fof(f443,plain,(
% 0.20/0.58    v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.58    inference(forward_demodulation,[],[f442,f244])).
% 0.20/0.58  fof(f442,plain,(
% 0.20/0.58    v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.58    inference(subsumption_resolution,[],[f441,f49])).
% 0.20/0.58  fof(f441,plain,(
% 0.20/0.58    v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)),
% 0.20/0.58    inference(subsumption_resolution,[],[f440,f51])).
% 0.20/0.58  fof(f440,plain,(
% 0.20/0.58    v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~l1_pre_topc(sK0) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)),
% 0.20/0.58    inference(subsumption_resolution,[],[f426,f50])).
% 0.20/0.58  fof(f426,plain,(
% 0.20/0.58    v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)),
% 0.20/0.58    inference(superposition,[],[f77,f232])).
% 0.20/0.58  fof(f77,plain,(
% 0.20/0.58    ( ! [X0,X1] : (v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f39])).
% 0.20/0.58  % SZS output end Proof for theBenchmark
% 0.20/0.58  % (11494)------------------------------
% 0.20/0.58  % (11494)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.58  % (11494)Termination reason: Refutation
% 0.20/0.58  
% 0.20/0.58  % (11494)Memory used [KB]: 11385
% 0.20/0.58  % (11494)Time elapsed: 0.151 s
% 0.20/0.58  % (11494)------------------------------
% 0.20/0.58  % (11494)------------------------------
% 0.20/0.58  % (11473)Refutation not found, incomplete strategy% (11473)------------------------------
% 0.20/0.58  % (11473)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.58  % (11473)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.58  
% 0.20/0.58  % (11473)Memory used [KB]: 10746
% 0.20/0.58  % (11473)Time elapsed: 0.162 s
% 0.20/0.58  % (11473)------------------------------
% 0.20/0.58  % (11473)------------------------------
% 0.20/0.58  % (11469)Success in time 0.225 s
%------------------------------------------------------------------------------
