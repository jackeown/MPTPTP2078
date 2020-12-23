%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:15 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 868 expanded)
%              Number of leaves         :   20 ( 177 expanded)
%              Depth                    :   18
%              Number of atoms          :  445 (6460 expanded)
%              Number of equality atoms :   34 ( 458 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f377,plain,(
    $false ),
    inference(subsumption_resolution,[],[f376,f278])).

fof(f278,plain,(
    r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3) ),
    inference(unit_resulting_resolution,[],[f53,f108,f108,f54,f55,f54,f55,f95])).

fof(f95,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X5)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1)
      | ~ v1_funct_2(X5,X0,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | r1_funct_2(X0,X1,X2,X3,X5,X5) ) ),
    inference(duplicate_literal_removal,[],[f94])).

fof(f94,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( v1_xboole_0(X1)
      | v1_xboole_0(X3)
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X0,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | r1_funct_2(X0,X1,X2,X3,X5,X5) ) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_xboole_0(X1)
      | v1_xboole_0(X3)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X0,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | X4 != X5
      | r1_funct_2(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
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
    inference(flattening,[],[f51])).

fof(f51,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f55,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2))
                  & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2))
                  & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X1)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                      & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                      & v1_funct_1(X3) )
                   => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                     => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X1)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                    & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                    & v1_funct_1(X3) )
                 => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                   => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_tmap_1)).

fof(f54,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f108,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f63,f99,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f99,plain,(
    l1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f65,f67])).

fof(f67,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f65,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f63,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f53,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f376,plain,(
    ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3) ),
    inference(forward_demodulation,[],[f373,f136])).

fof(f136,plain,(
    sK3 = k7_relat_1(sK3,u1_struct_0(sK1)) ),
    inference(unit_resulting_resolution,[],[f111,f130,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f130,plain,(
    v4_relat_1(sK3,u1_struct_0(sK1)) ),
    inference(unit_resulting_resolution,[],[f55,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f111,plain,(
    v1_relat_1(sK3) ),
    inference(unit_resulting_resolution,[],[f80,f55,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f80,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f373,plain,(
    ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,k7_relat_1(sK3,u1_struct_0(sK1))) ),
    inference(backward_demodulation,[],[f296,f367])).

fof(f367,plain,(
    u1_struct_0(sK1) = u1_struct_0(sK2) ),
    inference(unit_resulting_resolution,[],[f161,f341,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

% (20256)Refutation not found, incomplete strategy% (20256)------------------------------
% (20256)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

% (20256)Termination reason: Refutation not found, incomplete strategy
fof(f341,plain,(
    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f338,f240])).

% (20256)Memory used [KB]: 10746
fof(f240,plain,(
    u1_struct_0(sK1) = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(unit_resulting_resolution,[],[f164,f210,f85])).

% (20256)Time elapsed: 0.114 s
% (20256)------------------------------
% (20256)------------------------------
fof(f210,plain,(
    r1_tarski(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(unit_resulting_resolution,[],[f61,f62,f100,f144,f184,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X2)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

fof(f184,plain,(
    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(unit_resulting_resolution,[],[f62,f61,f122,f128,f134,f96])).

fof(f96,plain,(
    ! [X2,X0] :
      ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0) ) ),
    inference(subsumption_resolution,[],[f90,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f90,plain,(
    ! [X2,X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0) ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
      | m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X0)
              <=> m1_pre_topc(X2,X0) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X0)
              <=> m1_pre_topc(X2,X0) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2) )
             => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1
               => ( m1_pre_topc(X1,X0)
                <=> m1_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_tmap_1)).

fof(f134,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(forward_demodulation,[],[f133,f56])).

fof(f56,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f133,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(unit_resulting_resolution,[],[f115,f102,f76])).

fof(f76,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).

fof(f102,plain,(
    l1_pre_topc(sK2) ),
    inference(unit_resulting_resolution,[],[f59,f62,f70])).

fof(f59,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f115,plain,(
    v2_pre_topc(sK2) ),
    inference(unit_resulting_resolution,[],[f59,f61,f62,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f128,plain,(
    m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(unit_resulting_resolution,[],[f122,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f122,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(forward_demodulation,[],[f121,f56])).

fof(f121,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(unit_resulting_resolution,[],[f114,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f114,plain,(
    m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(unit_resulting_resolution,[],[f102,f69])).

fof(f69,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f144,plain,(
    m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1) ),
    inference(unit_resulting_resolution,[],[f62,f128,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | m1_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

fof(f100,plain,(
    m1_pre_topc(sK1,sK1) ),
    inference(unit_resulting_resolution,[],[f62,f68])).

fof(f62,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f61,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f164,plain,(
    r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK1)) ),
    inference(unit_resulting_resolution,[],[f62,f100,f144,f144,f61,f78])).

fof(f338,plain,(
    r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) ),
    inference(unit_resulting_resolution,[],[f115,f102,f105,f327,f327,f78])).

fof(f327,plain,(
    m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) ),
    inference(unit_resulting_resolution,[],[f102,f105,f236])).

fof(f236,plain,(
    ! [X0] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0)
      | ~ m1_pre_topc(sK2,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f235,f115])).

fof(f235,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(sK2)
      | ~ m1_pre_topc(sK2,X0)
      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) ) ),
    inference(subsumption_resolution,[],[f234,f134])).

fof(f234,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(sK2)
      | ~ m1_pre_topc(sK2,X0)
      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) ) ),
    inference(subsumption_resolution,[],[f233,f122])).

fof(f233,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(sK2)
      | ~ m1_pre_topc(sK2,X0)
      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) ) ),
    inference(superposition,[],[f97,f56])).

fof(f97,plain,(
    ! [X2,X0] :
      ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X2)
      | ~ m1_pre_topc(X2,X0)
      | m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0) ) ),
    inference(subsumption_resolution,[],[f91,f70])).

fof(f91,plain,(
    ! [X2,X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | ~ m1_pre_topc(X2,X0)
      | m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
      | ~ m1_pre_topc(X2,X0)
      | m1_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f105,plain,(
    m1_pre_topc(sK2,sK2) ),
    inference(unit_resulting_resolution,[],[f102,f68])).

fof(f161,plain,(
    r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(unit_resulting_resolution,[],[f62,f59,f100,f59,f61,f78])).

fof(f296,plain,(
    ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k7_relat_1(sK3,u1_struct_0(sK2))) ),
    inference(backward_demodulation,[],[f57,f295])).

fof(f295,plain,(
    k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f287,f149])).

fof(f149,plain,(
    ! [X0] : k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(unit_resulting_resolution,[],[f53,f55,f87])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f287,plain,(
    k2_tmap_1(sK1,sK0,sK3,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) ),
    inference(unit_resulting_resolution,[],[f65,f59,f61,f62,f53,f60,f64,f63,f54,f55,f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X0)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X0)
      | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f64,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f60,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f57,plain,(
    ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:36:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.48  % (20257)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.49  % (20257)Refutation not found, incomplete strategy% (20257)------------------------------
% 0.20/0.49  % (20257)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (20273)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.49  % (20257)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (20257)Memory used [KB]: 10746
% 0.20/0.49  % (20257)Time elapsed: 0.072 s
% 0.20/0.49  % (20257)------------------------------
% 0.20/0.49  % (20257)------------------------------
% 0.20/0.49  % (20261)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.49  % (20265)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.49  % (20261)Refutation not found, incomplete strategy% (20261)------------------------------
% 0.20/0.49  % (20261)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (20261)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (20261)Memory used [KB]: 6268
% 0.20/0.49  % (20261)Time elapsed: 0.084 s
% 0.20/0.49  % (20261)------------------------------
% 0.20/0.49  % (20261)------------------------------
% 0.20/0.50  % (20259)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.50  % (20269)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (20264)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.50  % (20263)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.51  % (20262)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.51  % (20271)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.51  % (20277)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.51  % (20270)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.51  % (20267)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.52  % (20258)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.52  % (20279)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.52  % (20256)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.52  % (20268)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.52  % (20260)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.52  % (20276)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.53  % (20275)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.53  % (20262)Refutation not found, incomplete strategy% (20262)------------------------------
% 0.20/0.53  % (20262)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (20262)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (20262)Memory used [KB]: 10746
% 0.20/0.53  % (20262)Time elapsed: 0.107 s
% 0.20/0.53  % (20262)------------------------------
% 0.20/0.53  % (20262)------------------------------
% 0.20/0.53  % (20269)Refutation not found, incomplete strategy% (20269)------------------------------
% 0.20/0.53  % (20269)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (20269)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (20269)Memory used [KB]: 6780
% 0.20/0.53  % (20269)Time elapsed: 0.111 s
% 0.20/0.53  % (20269)------------------------------
% 0.20/0.53  % (20269)------------------------------
% 0.20/0.53  % (20263)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % (20280)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f377,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(subsumption_resolution,[],[f376,f278])).
% 0.20/0.53  fof(f278,plain,(
% 0.20/0.53    r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f53,f108,f108,f54,f55,f54,f55,f95])).
% 0.20/0.53  fof(f95,plain,(
% 0.20/0.53    ( ! [X2,X0,X5,X3,X1] : (~v1_funct_1(X5) | v1_xboole_0(X3) | v1_xboole_0(X1) | ~v1_funct_2(X5,X0,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X5,X2,X3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | r1_funct_2(X0,X1,X2,X3,X5,X5)) )),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f94])).
% 0.20/0.53  fof(f94,plain,(
% 0.20/0.53    ( ! [X2,X0,X5,X3,X1] : (v1_xboole_0(X1) | v1_xboole_0(X3) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X0,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X2,X3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | r1_funct_2(X0,X1,X2,X3,X5,X5)) )),
% 0.20/0.53    inference(equality_resolution,[],[f88])).
% 0.20/0.53  fof(f88,plain,(
% 0.20/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X1) | v1_xboole_0(X3) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X0,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X2,X3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | X4 != X5 | r1_funct_2(X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f52])).
% 0.20/0.53  fof(f52,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 0.20/0.53    inference(flattening,[],[f51])).
% 0.20/0.53  fof(f51,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 0.20/0.53    inference(ennf_transformation,[],[f15])).
% 0.20/0.53  fof(f15,axiom,(
% 0.20/0.53    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_funct_2)).
% 0.20/0.53  fof(f55,plain,(
% 0.20/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.20/0.53    inference(cnf_transformation,[],[f26])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f25])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f21])).
% 0.20/0.53  fof(f21,negated_conjecture,(
% 0.20/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)))))))),
% 0.20/0.53    inference(negated_conjecture,[],[f20])).
% 0.20/0.53  fof(f20,conjecture,(
% 0.20/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)))))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_tmap_1)).
% 0.20/0.53  fof(f54,plain,(
% 0.20/0.53    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.20/0.53    inference(cnf_transformation,[],[f26])).
% 0.20/0.53  fof(f108,plain,(
% 0.20/0.53    ~v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f63,f99,f74])).
% 0.20/0.53  fof(f74,plain,(
% 0.20/0.53    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f36])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f35])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f12])).
% 0.20/0.53  fof(f12,axiom,(
% 0.20/0.53    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.20/0.53  fof(f99,plain,(
% 0.20/0.53    l1_struct_0(sK0)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f65,f67])).
% 0.20/0.53  fof(f67,plain,(
% 0.20/0.53    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f28])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,axiom,(
% 0.20/0.53    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.53  fof(f65,plain,(
% 0.20/0.53    l1_pre_topc(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f26])).
% 0.20/0.53  fof(f63,plain,(
% 0.20/0.53    ~v2_struct_0(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f26])).
% 0.20/0.53  fof(f53,plain,(
% 0.20/0.53    v1_funct_1(sK3)),
% 0.20/0.53    inference(cnf_transformation,[],[f26])).
% 0.20/0.53  fof(f376,plain,(
% 0.20/0.53    ~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3)),
% 0.20/0.53    inference(forward_demodulation,[],[f373,f136])).
% 0.20/0.53  fof(f136,plain,(
% 0.20/0.53    sK3 = k7_relat_1(sK3,u1_struct_0(sK1))),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f111,f130,f82])).
% 0.20/0.53  fof(f82,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1) )),
% 0.20/0.53    inference(cnf_transformation,[],[f47])).
% 0.20/0.53  fof(f47,plain,(
% 0.20/0.53    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.53    inference(flattening,[],[f46])).
% 0.20/0.53  fof(f46,plain,(
% 0.20/0.53    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.53    inference(ennf_transformation,[],[f4])).
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 0.20/0.53  fof(f130,plain,(
% 0.20/0.53    v4_relat_1(sK3,u1_struct_0(sK1))),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f55,f86])).
% 0.20/0.53  fof(f86,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f48])).
% 0.20/0.53  fof(f48,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f24])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.20/0.53    inference(pure_predicate_removal,[],[f5])).
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.53  fof(f111,plain,(
% 0.20/0.53    v1_relat_1(sK3)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f80,f55,f66])).
% 0.20/0.53  fof(f66,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f27])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.53  fof(f80,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.53  fof(f373,plain,(
% 0.20/0.53    ~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,k7_relat_1(sK3,u1_struct_0(sK1)))),
% 0.20/0.53    inference(backward_demodulation,[],[f296,f367])).
% 0.20/0.53  fof(f367,plain,(
% 0.20/0.53    u1_struct_0(sK1) = u1_struct_0(sK2)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f161,f341,f85])).
% 0.20/0.53  fof(f85,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.20/0.53    inference(cnf_transformation,[],[f1])).
% 0.20/0.53  % (20256)Refutation not found, incomplete strategy% (20256)------------------------------
% 0.20/0.53  % (20256)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.53  % (20256)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  fof(f341,plain,(
% 0.20/0.53    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))),
% 0.20/0.53    inference(forward_demodulation,[],[f338,f240])).
% 0.20/0.53  
% 0.20/0.53  % (20256)Memory used [KB]: 10746
% 0.20/0.53  fof(f240,plain,(
% 0.20/0.53    u1_struct_0(sK1) = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f164,f210,f85])).
% 0.20/0.53  % (20256)Time elapsed: 0.114 s
% 0.20/0.53  % (20256)------------------------------
% 0.20/0.53  % (20256)------------------------------
% 0.20/0.53  fof(f210,plain,(
% 0.20/0.53    r1_tarski(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f61,f62,f100,f144,f184,f78])).
% 0.20/0.53  fof(f78,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X2) | r1_tarski(u1_struct_0(X1),u1_struct_0(X2))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f44])).
% 0.20/0.53  fof(f44,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.53    inference(flattening,[],[f43])).
% 0.20/0.53  fof(f43,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f19])).
% 0.20/0.53  fof(f19,axiom,(
% 0.20/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).
% 0.20/0.53  fof(f184,plain,(
% 0.20/0.53    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f62,f61,f122,f128,f134,f96])).
% 0.20/0.53  fof(f96,plain,(
% 0.20/0.53    ( ! [X2,X0] : (~v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | m1_pre_topc(X2,X0) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f90,f70])).
% 0.20/0.53  fof(f70,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f31])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f10])).
% 0.20/0.53  fof(f10,axiom,(
% 0.20/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.20/0.53  fof(f90,plain,(
% 0.20/0.53    ( ! [X2,X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | m1_pre_topc(X2,X0) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0)) )),
% 0.20/0.53    inference(equality_resolution,[],[f73])).
% 0.20/0.53  fof(f73,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f34])).
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(flattening,[],[f33])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f17])).
% 0.20/0.53  fof(f17,axiom,(
% 0.20/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1 => (m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0))))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_tmap_1)).
% 0.20/0.53  fof(f134,plain,(
% 0.20/0.53    v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 0.20/0.53    inference(forward_demodulation,[],[f133,f56])).
% 0.20/0.53  fof(f56,plain,(
% 0.20/0.53    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),
% 0.20/0.53    inference(cnf_transformation,[],[f26])).
% 0.20/0.53  fof(f133,plain,(
% 0.20/0.53    v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f115,f102,f76])).
% 0.20/0.53  fof(f76,plain,(
% 0.20/0.53    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f40])).
% 0.20/0.53  fof(f40,plain,(
% 0.20/0.53    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.53    inference(flattening,[],[f39])).
% 0.20/0.53  fof(f39,plain,(
% 0.20/0.53    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f23])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),
% 0.20/0.53    inference(pure_predicate_removal,[],[f13])).
% 0.20/0.53  fof(f13,axiom,(
% 0.20/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).
% 0.20/0.53  fof(f102,plain,(
% 0.20/0.53    l1_pre_topc(sK2)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f59,f62,f70])).
% 0.20/0.53  fof(f59,plain,(
% 0.20/0.53    m1_pre_topc(sK2,sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f26])).
% 0.20/0.53  fof(f115,plain,(
% 0.20/0.53    v2_pre_topc(sK2)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f59,f61,f62,f77])).
% 0.20/0.53  fof(f77,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_pre_topc(X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f42])).
% 0.20/0.53  fof(f42,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.53    inference(flattening,[],[f41])).
% 0.20/0.53  fof(f41,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f7])).
% 0.20/0.53  fof(f7,axiom,(
% 0.20/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.20/0.53  fof(f128,plain,(
% 0.20/0.53    m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f122,f68])).
% 0.20/0.53  fof(f68,plain,(
% 0.20/0.53    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f29])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f18])).
% 0.20/0.53  fof(f18,axiom,(
% 0.20/0.53    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.20/0.53  fof(f122,plain,(
% 0.20/0.53    l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 0.20/0.53    inference(forward_demodulation,[],[f121,f56])).
% 0.20/0.53  fof(f121,plain,(
% 0.20/0.53    l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f114,f81])).
% 0.20/0.53  fof(f81,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | l1_pre_topc(g1_pre_topc(X0,X1))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f45])).
% 0.20/0.53  fof(f45,plain,(
% 0.20/0.53    ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.53    inference(ennf_transformation,[],[f22])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => l1_pre_topc(g1_pre_topc(X0,X1)))),
% 0.20/0.53    inference(pure_predicate_removal,[],[f8])).
% 0.20/0.53  fof(f8,axiom,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).
% 0.20/0.53  fof(f114,plain,(
% 0.20/0.53    m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f102,f69])).
% 0.20/0.53  fof(f69,plain,(
% 0.20/0.53    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f30])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f11])).
% 0.20/0.53  fof(f11,axiom,(
% 0.20/0.53    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 0.20/0.53  fof(f144,plain,(
% 0.20/0.53    m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f62,f128,f71])).
% 0.20/0.53  fof(f71,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | m1_pre_topc(X1,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f32])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f14])).
% 0.20/0.53  fof(f14,axiom,(
% 0.20/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).
% 0.20/0.53  fof(f100,plain,(
% 0.20/0.53    m1_pre_topc(sK1,sK1)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f62,f68])).
% 0.20/0.53  fof(f62,plain,(
% 0.20/0.53    l1_pre_topc(sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f26])).
% 0.20/0.53  fof(f61,plain,(
% 0.20/0.53    v2_pre_topc(sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f26])).
% 0.20/0.53  fof(f164,plain,(
% 0.20/0.53    r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK1))),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f62,f100,f144,f144,f61,f78])).
% 0.20/0.53  fof(f338,plain,(
% 0.20/0.53    r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f115,f102,f105,f327,f327,f78])).
% 0.20/0.53  fof(f327,plain,(
% 0.20/0.53    m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f102,f105,f236])).
% 0.20/0.53  fof(f236,plain,(
% 0.20/0.53    ( ! [X0] : (m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) | ~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f235,f115])).
% 0.20/0.53  fof(f235,plain,(
% 0.20/0.53    ( ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(sK2) | ~m1_pre_topc(sK2,X0) | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f234,f134])).
% 0.20/0.53  fof(f234,plain,(
% 0.20/0.53    ( ! [X0] : (~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(X0) | ~v2_pre_topc(sK2) | ~m1_pre_topc(sK2,X0) | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f233,f122])).
% 0.20/0.53  fof(f233,plain,(
% 0.20/0.53    ( ! [X0] : (~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(X0) | ~v2_pre_topc(sK2) | ~m1_pre_topc(sK2,X0) | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0)) )),
% 0.20/0.53    inference(superposition,[],[f97,f56])).
% 0.20/0.53  fof(f97,plain,(
% 0.20/0.53    ( ! [X2,X0] : (~l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X2) | ~m1_pre_topc(X2,X0) | m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f91,f70])).
% 0.20/0.53  fof(f91,plain,(
% 0.20/0.53    ( ! [X2,X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~m1_pre_topc(X2,X0) | m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0)) )),
% 0.20/0.53    inference(equality_resolution,[],[f72])).
% 0.20/0.53  fof(f72,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~m1_pre_topc(X2,X0) | m1_pre_topc(X1,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f34])).
% 0.20/0.53  fof(f105,plain,(
% 0.20/0.53    m1_pre_topc(sK2,sK2)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f102,f68])).
% 0.20/0.53  fof(f161,plain,(
% 0.20/0.53    r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1))),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f62,f59,f100,f59,f61,f78])).
% 0.20/0.53  fof(f296,plain,(
% 0.20/0.53    ~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k7_relat_1(sK3,u1_struct_0(sK2)))),
% 0.20/0.53    inference(backward_demodulation,[],[f57,f295])).
% 0.20/0.53  fof(f295,plain,(
% 0.20/0.53    k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2))),
% 0.20/0.53    inference(forward_demodulation,[],[f287,f149])).
% 0.20/0.53  fof(f149,plain,(
% 0.20/0.53    ( ! [X0] : (k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = k7_relat_1(sK3,X0)) )),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f53,f55,f87])).
% 0.20/0.53  fof(f87,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f50])).
% 0.20/0.53  fof(f50,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.20/0.53    inference(flattening,[],[f49])).
% 0.20/0.53  fof(f49,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.20/0.53    inference(ennf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.20/0.53  fof(f287,plain,(
% 0.20/0.53    k2_tmap_1(sK1,sK0,sK3,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2))),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f65,f59,f61,f62,f53,f60,f64,f63,f54,f55,f75])).
% 0.20/0.53  fof(f75,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | v2_struct_0(X0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f38])).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f37])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f16])).
% 0.20/0.53  fof(f16,axiom,(
% 0.20/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).
% 0.20/0.53  fof(f64,plain,(
% 0.20/0.53    v2_pre_topc(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f26])).
% 0.20/0.53  fof(f60,plain,(
% 0.20/0.53    ~v2_struct_0(sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f26])).
% 0.20/0.53  fof(f57,plain,(
% 0.20/0.53    ~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2))),
% 0.20/0.53    inference(cnf_transformation,[],[f26])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (20263)------------------------------
% 0.20/0.53  % (20263)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (20263)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (20263)Memory used [KB]: 1918
% 0.20/0.53  % (20263)Time elapsed: 0.101 s
% 0.20/0.53  % (20263)------------------------------
% 0.20/0.53  % (20263)------------------------------
% 0.20/0.53  % (20255)Success in time 0.18 s
%------------------------------------------------------------------------------
