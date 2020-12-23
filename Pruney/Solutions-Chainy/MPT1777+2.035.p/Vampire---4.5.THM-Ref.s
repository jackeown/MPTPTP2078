%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:07 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  235 (15472 expanded)
%              Number of leaves         :   15 (3130 expanded)
%              Depth                    :   52
%              Number of atoms          : 1275 (133036 expanded)
%              Number of equality atoms :   81 (14013 expanded)
%              Maximal formula depth    :   28 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f992,plain,(
    $false ),
    inference(subsumption_resolution,[],[f991,f93])).

fof(f93,plain,(
    l1_pre_topc(sK2) ),
    inference(resolution,[],[f90,f50])).

fof(f50,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X3,X1,X4,X5)
                              & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
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
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X3,X1,X4,X5)
                              & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
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
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X3))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X2))
                                 => ( ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                      & X5 = X6 )
                                   => r1_tmap_1(X3,X1,X4,X5) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                    & X5 = X6 )
                                 => r1_tmap_1(X3,X1,X4,X5) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tmap_1)).

fof(f90,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK0)
      | l1_pre_topc(X1) ) ),
    inference(resolution,[],[f62,f56])).

fof(f56,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f991,plain,(
    ~ l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f990,f125])).

fof(f125,plain,(
    v2_pre_topc(sK2) ),
    inference(resolution,[],[f122,f50])).

fof(f122,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f118,f55])).

fof(f55,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f118,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_pre_topc(X0) ) ),
    inference(resolution,[],[f69,f56])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f990,plain,
    ( ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f989,f49])).

fof(f49,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f989,plain,
    ( v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f988,f548])).

fof(f548,plain,(
    v1_tsep_1(sK3,sK2) ),
    inference(subsumption_resolution,[],[f547,f315])).

fof(f315,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(resolution,[],[f313,f96])).

fof(f96,plain,(
    m1_pre_topc(sK3,sK3) ),
    inference(resolution,[],[f92,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f92,plain,(
    l1_pre_topc(sK3) ),
    inference(resolution,[],[f90,f48])).

fof(f48,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f313,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK3)
      | m1_pre_topc(X2,sK2) ) ),
    inference(subsumption_resolution,[],[f312,f95])).

fof(f95,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | l1_pre_topc(X0) ) ),
    inference(resolution,[],[f92,f62])).

fof(f312,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK3)
      | ~ l1_pre_topc(X2)
      | m1_pre_topc(X2,sK2) ) ),
    inference(forward_demodulation,[],[f311,f108])).

fof(f108,plain,(
    sK3 = g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(backward_demodulation,[],[f46,f103])).

fof(f103,plain,(
    u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(resolution,[],[f88,f93])).

fof(f88,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(resolution,[],[f57,f58])).

fof(f58,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f57,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f46,plain,(
    sK3 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f311,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)))
      | ~ l1_pre_topc(X2)
      | m1_pre_topc(X2,sK2) ) ),
    inference(forward_demodulation,[],[f307,f103])).

fof(f307,plain,(
    ! [X2] :
      ( ~ l1_pre_topc(X2)
      | ~ m1_pre_topc(X2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
      | m1_pre_topc(X2,sK2) ) ),
    inference(resolution,[],[f60,f93])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | m1_pre_topc(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f547,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | v1_tsep_1(sK3,sK2) ),
    inference(subsumption_resolution,[],[f544,f130])).

fof(f130,plain,(
    v3_pre_topc(k2_struct_0(sK2),sK2) ),
    inference(subsumption_resolution,[],[f114,f125])).

fof(f114,plain,
    ( v3_pre_topc(k2_struct_0(sK2),sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(resolution,[],[f68,f93])).

fof(f68,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v3_pre_topc(k2_struct_0(X0),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

fof(f544,plain,
    ( ~ v3_pre_topc(k2_struct_0(sK2),sK2)
    | ~ m1_pre_topc(sK3,sK2)
    | v1_tsep_1(sK3,sK2) ),
    inference(superposition,[],[f525,f381])).

fof(f381,plain,(
    u1_struct_0(sK3) = k2_struct_0(sK2) ),
    inference(backward_demodulation,[],[f104,f380])).

fof(f380,plain,(
    k2_struct_0(sK2) = k2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f374,f98])).

fof(f98,plain,(
    m1_pre_topc(sK2,sK2) ),
    inference(resolution,[],[f93,f59])).

fof(f374,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | k2_struct_0(sK2) = k2_struct_0(sK3) ),
    inference(resolution,[],[f363,f319])).

fof(f319,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | k2_struct_0(sK2) = k2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f183,f318])).

fof(f318,plain,(
    r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f166,f315])).

fof(f166,plain,
    ( r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2))
    | ~ m1_pre_topc(sK3,sK2) ),
    inference(superposition,[],[f146,f104])).

fof(f146,plain,(
    ! [X2] :
      ( r1_tarski(u1_struct_0(X2),k2_struct_0(sK2))
      | ~ m1_pre_topc(X2,sK2) ) ),
    inference(subsumption_resolution,[],[f142,f93])).

fof(f142,plain,(
    ! [X2] :
      ( r1_tarski(u1_struct_0(X2),k2_struct_0(sK2))
      | ~ m1_pre_topc(X2,sK2)
      | ~ l1_pre_topc(sK2) ) ),
    inference(superposition,[],[f63,f103])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).

fof(f183,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2))
    | k2_struct_0(sK2) = k2_struct_0(sK3) ),
    inference(resolution,[],[f170,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f170,plain,
    ( r1_tarski(k2_struct_0(sK2),k2_struct_0(sK3))
    | ~ m1_pre_topc(sK2,sK3) ),
    inference(superposition,[],[f147,f103])).

fof(f147,plain,(
    ! [X3] :
      ( r1_tarski(u1_struct_0(X3),k2_struct_0(sK3))
      | ~ m1_pre_topc(X3,sK3) ) ),
    inference(subsumption_resolution,[],[f143,f92])).

fof(f143,plain,(
    ! [X3] :
      ( r1_tarski(u1_struct_0(X3),k2_struct_0(sK3))
      | ~ m1_pre_topc(X3,sK3)
      | ~ l1_pre_topc(sK3) ) ),
    inference(superposition,[],[f63,f104])).

fof(f363,plain,(
    ! [X2] :
      ( m1_pre_topc(X2,sK3)
      | ~ m1_pre_topc(X2,sK2) ) ),
    inference(forward_demodulation,[],[f362,f108])).

fof(f362,plain,(
    ! [X2] :
      ( m1_pre_topc(X2,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)))
      | ~ m1_pre_topc(X2,sK2) ) ),
    inference(forward_demodulation,[],[f361,f103])).

fof(f361,plain,(
    ! [X2] :
      ( m1_pre_topc(X2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
      | ~ m1_pre_topc(X2,sK2) ) ),
    inference(subsumption_resolution,[],[f355,f97])).

fof(f97,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | l1_pre_topc(X0) ) ),
    inference(resolution,[],[f93,f62])).

fof(f355,plain,(
    ! [X2] :
      ( ~ l1_pre_topc(X2)
      | m1_pre_topc(X2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
      | ~ m1_pre_topc(X2,sK2) ) ),
    inference(resolution,[],[f61,f93])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f104,plain,(
    u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(resolution,[],[f88,f92])).

fof(f525,plain,(
    ! [X2] :
      ( ~ v3_pre_topc(u1_struct_0(X2),sK2)
      | ~ m1_pre_topc(X2,sK2)
      | v1_tsep_1(X2,sK2) ) ),
    inference(subsumption_resolution,[],[f521,f125])).

fof(f521,plain,(
    ! [X2] :
      ( ~ v2_pre_topc(sK2)
      | ~ m1_pre_topc(X2,sK2)
      | ~ v3_pre_topc(u1_struct_0(X2),sK2)
      | v1_tsep_1(X2,sK2) ) ),
    inference(resolution,[],[f84,f93])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f78,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | ~ v3_pre_topc(X2,X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f988,plain,
    ( ~ v1_tsep_1(sK3,sK2)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f987,f315])).

fof(f987,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | ~ v1_tsep_1(sK3,sK2)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f974,f949])).

fof(f949,plain,(
    r1_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK2,sK2,sK4),sK5) ),
    inference(subsumption_resolution,[],[f948,f49])).

fof(f948,plain,
    ( r1_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK2,sK2,sK4),sK5)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f947,f93])).

fof(f947,plain,
    ( r1_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK2,sK2,sK4),sK5)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f946,f125])).

fof(f946,plain,
    ( r1_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK2,sK2,sK4),sK5)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f945,f548])).

fof(f945,plain,
    ( r1_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK2,sK2,sK4),sK5)
    | ~ v1_tsep_1(sK3,sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f939,f98])).

fof(f939,plain,
    ( r1_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK2,sK2,sK4),sK5)
    | ~ m1_pre_topc(sK2,sK2)
    | ~ v1_tsep_1(sK3,sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(superposition,[],[f934,f715])).

fof(f715,plain,(
    k3_tmap_1(sK0,sK1,sK2,sK2,sK4) = k3_tmap_1(sK2,sK1,sK2,sK3,sK4) ),
    inference(forward_demodulation,[],[f714,f707])).

fof(f707,plain,(
    k3_tmap_1(sK0,sK1,sK2,sK2,sK4) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,k2_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f705,f103])).

fof(f705,plain,(
    k3_tmap_1(sK0,sK1,sK2,sK2,sK4) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(sK2)) ),
    inference(resolution,[],[f697,f98])).

fof(f697,plain,(
    ! [X3] :
      ( ~ m1_pre_topc(X3,sK2)
      | k3_tmap_1(sK0,sK1,sK2,X3,sK4) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3)) ) ),
    inference(subsumption_resolution,[],[f696,f55])).

fof(f696,plain,(
    ! [X3] :
      ( ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(X3,sK2)
      | k3_tmap_1(sK0,sK1,sK2,X3,sK4) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3)) ) ),
    inference(subsumption_resolution,[],[f695,f54])).

fof(f54,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f695,plain,(
    ! [X3] :
      ( v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(X3,sK2)
      | k3_tmap_1(sK0,sK1,sK2,X3,sK4) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3)) ) ),
    inference(subsumption_resolution,[],[f691,f56])).

fof(f691,plain,(
    ! [X3] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(X3,sK2)
      | k3_tmap_1(sK0,sK1,sK2,X3,sK4) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3)) ) ),
    inference(resolution,[],[f685,f50])).

fof(f685,plain,(
    ! [X4,X5] :
      ( ~ m1_pre_topc(sK2,X4)
      | ~ l1_pre_topc(X4)
      | v2_struct_0(X4)
      | ~ v2_pre_topc(X4)
      | ~ m1_pre_topc(X5,sK2)
      | k3_tmap_1(X4,sK1,sK2,X5,sK4) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X5)) ) ),
    inference(subsumption_resolution,[],[f684,f383])).

fof(f383,plain,(
    v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f110,f380])).

fof(f110,plain,(
    v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f105,f104])).

fof(f105,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f44,f102])).

fof(f102,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(resolution,[],[f88,f53])).

fof(f53,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f44,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f684,plain,(
    ! [X4,X5] :
      ( ~ l1_pre_topc(X4)
      | ~ m1_pre_topc(sK2,X4)
      | v2_struct_0(X4)
      | ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1))
      | ~ v2_pre_topc(X4)
      | ~ m1_pre_topc(X5,sK2)
      | k3_tmap_1(X4,sK1,sK2,X5,sK4) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X5)) ) ),
    inference(subsumption_resolution,[],[f682,f382])).

fof(f382,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f109,f380])).

fof(f109,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f106,f104])).

fof(f106,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f45,f102])).

fof(f45,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f18])).

fof(f682,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1))))
      | ~ l1_pre_topc(X4)
      | ~ m1_pre_topc(sK2,X4)
      | v2_struct_0(X4)
      | ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1))
      | ~ v2_pre_topc(X4)
      | ~ m1_pre_topc(X5,sK2)
      | k3_tmap_1(X4,sK1,sK2,X5,sK4) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X5)) ) ),
    inference(superposition,[],[f669,f103])).

fof(f669,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK1))))
      | ~ l1_pre_topc(X4)
      | ~ m1_pre_topc(X3,X4)
      | v2_struct_0(X4)
      | ~ v1_funct_2(sK4,u1_struct_0(X3),k2_struct_0(sK1))
      | ~ v2_pre_topc(X4)
      | ~ m1_pre_topc(X5,X3)
      | k3_tmap_1(X4,sK1,X3,X5,sK4) = k2_partfun1(u1_struct_0(X3),k2_struct_0(sK1),sK4,u1_struct_0(X5)) ) ),
    inference(subsumption_resolution,[],[f668,f53])).

fof(f668,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK1))))
      | ~ l1_pre_topc(X4)
      | ~ l1_pre_topc(sK1)
      | ~ m1_pre_topc(X3,X4)
      | v2_struct_0(X4)
      | ~ v1_funct_2(sK4,u1_struct_0(X3),k2_struct_0(sK1))
      | ~ v2_pre_topc(X4)
      | ~ m1_pre_topc(X5,X3)
      | k3_tmap_1(X4,sK1,X3,X5,sK4) = k2_partfun1(u1_struct_0(X3),k2_struct_0(sK1),sK4,u1_struct_0(X5)) ) ),
    inference(subsumption_resolution,[],[f667,f52])).

fof(f52,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f667,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK1))))
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ m1_pre_topc(X3,X4)
      | v2_struct_0(X4)
      | ~ v1_funct_2(sK4,u1_struct_0(X3),k2_struct_0(sK1))
      | ~ v2_pre_topc(X4)
      | ~ m1_pre_topc(X5,X3)
      | k3_tmap_1(X4,sK1,X3,X5,sK4) = k2_partfun1(u1_struct_0(X3),k2_struct_0(sK1),sK4,u1_struct_0(X5)) ) ),
    inference(subsumption_resolution,[],[f661,f51])).

fof(f51,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f661,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK1))))
      | ~ l1_pre_topc(X4)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ m1_pre_topc(X3,X4)
      | v2_struct_0(X4)
      | ~ v1_funct_2(sK4,u1_struct_0(X3),k2_struct_0(sK1))
      | ~ v2_pre_topc(X4)
      | ~ m1_pre_topc(X5,X3)
      | k3_tmap_1(X4,sK1,X3,X5,sK4) = k2_partfun1(u1_struct_0(X3),k2_struct_0(sK1),sK4,u1_struct_0(X5)) ) ),
    inference(superposition,[],[f634,f102])).

fof(f634,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0)
      | ~ v1_funct_2(sK4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X3,X2)
      | k3_tmap_1(X0,X1,X2,X3,sK4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),sK4,u1_struct_0(X3)) ) ),
    inference(subsumption_resolution,[],[f633,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X1)
      | m1_pre_topc(X2,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f633,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X0)
      | ~ v1_funct_2(sK4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X2)
      | k3_tmap_1(X0,X1,X2,X3,sK4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),sK4,u1_struct_0(X3)) ) ),
    inference(resolution,[],[f65,f43])).

fof(f43,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f18])).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X0)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X2)
      | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X3,X2)
                       => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).

fof(f714,plain,(
    k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,k2_struct_0(sK2)) = k3_tmap_1(sK2,sK1,sK2,sK3,sK4) ),
    inference(forward_demodulation,[],[f711,f381])).

fof(f711,plain,(
    k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(sK2,sK1,sK2,sK3,sK4) ),
    inference(resolution,[],[f700,f315])).

fof(f700,plain,(
    ! [X4] :
      ( ~ m1_pre_topc(X4,sK2)
      | k3_tmap_1(sK2,sK1,sK2,X4,sK4) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f699,f125])).

fof(f699,plain,(
    ! [X4] :
      ( ~ v2_pre_topc(sK2)
      | ~ m1_pre_topc(X4,sK2)
      | k3_tmap_1(sK2,sK1,sK2,X4,sK4) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f698,f49])).

fof(f698,plain,(
    ! [X4] :
      ( v2_struct_0(sK2)
      | ~ v2_pre_topc(sK2)
      | ~ m1_pre_topc(X4,sK2)
      | k3_tmap_1(sK2,sK1,sK2,X4,sK4) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f692,f93])).

fof(f692,plain,(
    ! [X4] :
      ( ~ l1_pre_topc(sK2)
      | v2_struct_0(sK2)
      | ~ v2_pre_topc(sK2)
      | ~ m1_pre_topc(X4,sK2)
      | k3_tmap_1(sK2,sK1,sK2,X4,sK4) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X4)) ) ),
    inference(resolution,[],[f685,f98])).

fof(f934,plain,(
    ! [X3] :
      ( r1_tmap_1(sK3,sK1,k3_tmap_1(X3,sK1,sK2,sK3,sK4),sK5)
      | ~ m1_pre_topc(sK2,X3)
      | ~ v1_tsep_1(sK3,X3)
      | ~ v2_pre_topc(X3)
      | ~ l1_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f933,f315])).

fof(f933,plain,(
    ! [X3] :
      ( ~ l1_pre_topc(X3)
      | ~ m1_pre_topc(sK2,X3)
      | ~ v1_tsep_1(sK3,X3)
      | ~ m1_pre_topc(sK3,sK2)
      | ~ v2_pre_topc(X3)
      | r1_tmap_1(sK3,sK1,k3_tmap_1(X3,sK1,sK2,sK3,sK4),sK5)
      | v2_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f932,f47])).

fof(f47,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f932,plain,(
    ! [X3] :
      ( ~ l1_pre_topc(X3)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK2,X3)
      | ~ v1_tsep_1(sK3,X3)
      | ~ m1_pre_topc(sK3,sK2)
      | ~ v2_pre_topc(X3)
      | r1_tmap_1(sK3,sK1,k3_tmap_1(X3,sK1,sK2,sK3,sK4),sK5)
      | v2_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f923,f107])).

fof(f107,plain,(
    m1_subset_1(sK5,k2_struct_0(sK2)) ),
    inference(backward_demodulation,[],[f83,f103])).

fof(f83,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f38,f39])).

fof(f39,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f18])).

fof(f38,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f923,plain,(
    ! [X3] :
      ( ~ m1_subset_1(sK5,k2_struct_0(sK2))
      | ~ l1_pre_topc(X3)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK2,X3)
      | ~ v1_tsep_1(sK3,X3)
      | ~ m1_pre_topc(sK3,sK2)
      | ~ v2_pre_topc(X3)
      | r1_tmap_1(sK3,sK1,k3_tmap_1(X3,sK1,sK2,sK3,sK4),sK5)
      | v2_struct_0(X3) ) ),
    inference(superposition,[],[f914,f381])).

fof(f914,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK5,u1_struct_0(X1))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(sK2,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,sK2)
      | ~ v2_pre_topc(X0)
      | r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK2,X1,sK4),sK5)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f913,f107])).

fof(f913,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(sK2,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,sK2)
      | ~ m1_subset_1(sK5,k2_struct_0(sK2))
      | ~ m1_subset_1(sK5,u1_struct_0(X1))
      | r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK2,X1,sK4),sK5)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f912,f839])).

fof(f839,plain,(
    ! [X6,X8,X7] :
      ( ~ r1_tmap_1(sK2,sK1,sK4,X8)
      | ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | v2_struct_0(X7)
      | ~ m1_pre_topc(sK2,X6)
      | ~ v1_tsep_1(X7,X6)
      | ~ m1_pre_topc(X7,sK2)
      | ~ m1_subset_1(X8,k2_struct_0(sK2))
      | ~ m1_subset_1(X8,u1_struct_0(X7))
      | r1_tmap_1(X7,sK1,k3_tmap_1(X6,sK1,sK2,X7,sK4),X8)
      | v2_struct_0(X6) ) ),
    inference(subsumption_resolution,[],[f838,f383])).

fof(f838,plain,(
    ! [X6,X8,X7] :
      ( v2_struct_0(X6)
      | ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | v2_struct_0(X7)
      | ~ m1_pre_topc(sK2,X6)
      | ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1))
      | ~ v1_tsep_1(X7,X6)
      | ~ m1_pre_topc(X7,sK2)
      | ~ m1_subset_1(X8,k2_struct_0(sK2))
      | ~ m1_subset_1(X8,u1_struct_0(X7))
      | r1_tmap_1(X7,sK1,k3_tmap_1(X6,sK1,sK2,X7,sK4),X8)
      | ~ r1_tmap_1(sK2,sK1,sK4,X8) ) ),
    inference(subsumption_resolution,[],[f837,f49])).

fof(f837,plain,(
    ! [X6,X8,X7] :
      ( v2_struct_0(X6)
      | ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | v2_struct_0(X7)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,X6)
      | ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1))
      | ~ v1_tsep_1(X7,X6)
      | ~ m1_pre_topc(X7,sK2)
      | ~ m1_subset_1(X8,k2_struct_0(sK2))
      | ~ m1_subset_1(X8,u1_struct_0(X7))
      | r1_tmap_1(X7,sK1,k3_tmap_1(X6,sK1,sK2,X7,sK4),X8)
      | ~ r1_tmap_1(sK2,sK1,sK4,X8) ) ),
    inference(subsumption_resolution,[],[f833,f382])).

fof(f833,plain,(
    ! [X6,X8,X7] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1))))
      | v2_struct_0(X6)
      | ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | v2_struct_0(X7)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,X6)
      | ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1))
      | ~ v1_tsep_1(X7,X6)
      | ~ m1_pre_topc(X7,sK2)
      | ~ m1_subset_1(X8,k2_struct_0(sK2))
      | ~ m1_subset_1(X8,u1_struct_0(X7))
      | r1_tmap_1(X7,sK1,k3_tmap_1(X6,sK1,sK2,X7,sK4),X8)
      | ~ r1_tmap_1(sK2,sK1,sK4,X8) ) ),
    inference(superposition,[],[f816,f103])).

fof(f816,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),k2_struct_0(sK1))))
      | v2_struct_0(X5)
      | ~ v2_pre_topc(X5)
      | ~ l1_pre_topc(X5)
      | v2_struct_0(X6)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X4,X5)
      | ~ v1_funct_2(sK4,u1_struct_0(X4),k2_struct_0(sK1))
      | ~ v1_tsep_1(X6,X5)
      | ~ m1_pre_topc(X6,X4)
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | r1_tmap_1(X6,sK1,k3_tmap_1(X5,sK1,X4,X6,sK4),X7)
      | ~ r1_tmap_1(X4,sK1,sK4,X7) ) ),
    inference(subsumption_resolution,[],[f815,f52])).

fof(f815,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),k2_struct_0(sK1))))
      | v2_struct_0(X5)
      | ~ v2_pre_topc(X5)
      | ~ l1_pre_topc(X5)
      | v2_struct_0(X6)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X4,X5)
      | ~ v1_funct_2(sK4,u1_struct_0(X4),k2_struct_0(sK1))
      | ~ v2_pre_topc(sK1)
      | ~ v1_tsep_1(X6,X5)
      | ~ m1_pre_topc(X6,X4)
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | r1_tmap_1(X6,sK1,k3_tmap_1(X5,sK1,X4,X6,sK4),X7)
      | ~ r1_tmap_1(X4,sK1,sK4,X7) ) ),
    inference(subsumption_resolution,[],[f814,f51])).

fof(f814,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),k2_struct_0(sK1))))
      | v2_struct_0(X5)
      | ~ v2_pre_topc(X5)
      | ~ l1_pre_topc(X5)
      | v2_struct_0(X6)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X4,X5)
      | v2_struct_0(sK1)
      | ~ v1_funct_2(sK4,u1_struct_0(X4),k2_struct_0(sK1))
      | ~ v2_pre_topc(sK1)
      | ~ v1_tsep_1(X6,X5)
      | ~ m1_pre_topc(X6,X4)
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | r1_tmap_1(X6,sK1,k3_tmap_1(X5,sK1,X4,X6,sK4),X7)
      | ~ r1_tmap_1(X4,sK1,sK4,X7) ) ),
    inference(subsumption_resolution,[],[f804,f53])).

fof(f804,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),k2_struct_0(sK1))))
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(X5)
      | ~ v2_pre_topc(X5)
      | ~ l1_pre_topc(X5)
      | v2_struct_0(X6)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X4,X5)
      | v2_struct_0(sK1)
      | ~ v1_funct_2(sK4,u1_struct_0(X4),k2_struct_0(sK1))
      | ~ v2_pre_topc(sK1)
      | ~ v1_tsep_1(X6,X5)
      | ~ m1_pre_topc(X6,X4)
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | r1_tmap_1(X6,sK1,k3_tmap_1(X5,sK1,X4,X6,sK4),X7)
      | ~ r1_tmap_1(X4,sK1,sK4,X7) ) ),
    inference(superposition,[],[f723,f102])).

fof(f723,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X0)
      | ~ v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | ~ v1_tsep_1(X2,X1)
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X2))
      | r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK4),X4)
      | ~ r1_tmap_1(X3,X0,sK4,X4) ) ),
    inference(subsumption_resolution,[],[f722,f70])).

fof(f722,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X0)
      | ~ v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X0))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
      | ~ v1_tsep_1(X2,X1)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X2))
      | r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK4),X4)
      | ~ r1_tmap_1(X3,X0,sK4,X4) ) ),
    inference(resolution,[],[f76,f43])).

fof(f76,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X0)
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
      | ~ v1_tsep_1(X2,X1)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
      | ~ r1_tmap_1(X3,X0,X4,X6) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X1)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
      | ~ v1_tsep_1(X2,X1)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | X5 != X6
      | r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
      | ~ r1_tmap_1(X3,X0,X4,X5) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X3,X0,X4,X5)
                              <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_pre_topc(X2,X1)
                      | ~ v1_tsep_1(X2,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X1)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X3,X0,X4,X5)
                              <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_pre_topc(X2,X1)
                      | ~ v1_tsep_1(X2,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X1)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                     => ( ( m1_pre_topc(X2,X3)
                          & m1_pre_topc(X2,X1)
                          & v1_tsep_1(X2,X1) )
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( X5 = X6
                                 => ( r1_tmap_1(X3,X0,X4,X5)
                                  <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_tmap_1)).

fof(f912,plain,(
    r1_tmap_1(sK2,sK1,sK4,sK5) ),
    inference(subsumption_resolution,[],[f911,f93])).

fof(f911,plain,
    ( ~ l1_pre_topc(sK2)
    | r1_tmap_1(sK2,sK1,sK4,sK5) ),
    inference(subsumption_resolution,[],[f910,f125])).

fof(f910,plain,
    ( ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | r1_tmap_1(sK2,sK1,sK4,sK5) ),
    inference(subsumption_resolution,[],[f909,f49])).

fof(f909,plain,
    ( v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | r1_tmap_1(sK2,sK1,sK4,sK5) ),
    inference(subsumption_resolution,[],[f908,f546])).

fof(f546,plain,(
    v1_tsep_1(sK2,sK2) ),
    inference(subsumption_resolution,[],[f545,f98])).

% (982)Refutation not found, incomplete strategy% (982)------------------------------
% (982)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (982)Termination reason: Refutation not found, incomplete strategy

% (982)Memory used [KB]: 11001
% (982)Time elapsed: 0.121 s
% (982)------------------------------
% (982)------------------------------
fof(f545,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | v1_tsep_1(sK2,sK2) ),
    inference(subsumption_resolution,[],[f543,f130])).

fof(f543,plain,
    ( ~ v3_pre_topc(k2_struct_0(sK2),sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | v1_tsep_1(sK2,sK2) ),
    inference(superposition,[],[f525,f103])).

fof(f908,plain,
    ( ~ v1_tsep_1(sK2,sK2)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | r1_tmap_1(sK2,sK1,sK4,sK5) ),
    inference(subsumption_resolution,[],[f907,f98])).

fof(f907,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | ~ v1_tsep_1(sK2,sK2)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | r1_tmap_1(sK2,sK1,sK4,sK5) ),
    inference(subsumption_resolution,[],[f901,f758])).

fof(f758,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK2,sK2,sK4),sK5) ),
    inference(backward_demodulation,[],[f82,f757])).

fof(f757,plain,(
    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k3_tmap_1(sK0,sK1,sK2,sK2,sK4) ),
    inference(forward_demodulation,[],[f756,f707])).

fof(f756,plain,(
    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,k2_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f754,f103])).

fof(f754,plain,(
    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(sK2)) ),
    inference(resolution,[],[f743,f98])).

fof(f743,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK4) ) ),
    inference(resolution,[],[f735,f363])).

fof(f735,plain,(
    ! [X3] :
      ( ~ m1_pre_topc(X3,sK3)
      | k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3)) = k3_tmap_1(sK0,sK1,sK3,X3,sK4) ) ),
    inference(subsumption_resolution,[],[f734,f55])).

fof(f734,plain,(
    ! [X3] :
      ( ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(X3,sK3)
      | k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3)) = k3_tmap_1(sK0,sK1,sK3,X3,sK4) ) ),
    inference(subsumption_resolution,[],[f733,f54])).

fof(f733,plain,(
    ! [X3] :
      ( v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(X3,sK3)
      | k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3)) = k3_tmap_1(sK0,sK1,sK3,X3,sK4) ) ),
    inference(subsumption_resolution,[],[f727,f56])).

fof(f727,plain,(
    ! [X3] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(X3,sK3)
      | k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3)) = k3_tmap_1(sK0,sK1,sK3,X3,sK4) ) ),
    inference(resolution,[],[f687,f48])).

fof(f687,plain,(
    ! [X6,X7] :
      ( ~ m1_pre_topc(sK3,X6)
      | ~ l1_pre_topc(X6)
      | v2_struct_0(X6)
      | ~ v2_pre_topc(X6)
      | ~ m1_pre_topc(X7,sK3)
      | k3_tmap_1(X6,sK1,sK3,X7,sK4) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X7)) ) ),
    inference(subsumption_resolution,[],[f686,f383])).

fof(f686,plain,(
    ! [X6,X7] :
      ( ~ l1_pre_topc(X6)
      | ~ m1_pre_topc(sK3,X6)
      | v2_struct_0(X6)
      | ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1))
      | ~ v2_pre_topc(X6)
      | ~ m1_pre_topc(X7,sK3)
      | k3_tmap_1(X6,sK1,sK3,X7,sK4) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X7)) ) ),
    inference(subsumption_resolution,[],[f683,f382])).

fof(f683,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1))))
      | ~ l1_pre_topc(X6)
      | ~ m1_pre_topc(sK3,X6)
      | v2_struct_0(X6)
      | ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1))
      | ~ v2_pre_topc(X6)
      | ~ m1_pre_topc(X7,sK3)
      | k3_tmap_1(X6,sK1,sK3,X7,sK4) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X7)) ) ),
    inference(superposition,[],[f669,f381])).

fof(f82,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(backward_demodulation,[],[f40,f39])).

fof(f40,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f18])).

fof(f901,plain,
    ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK2,sK2,sK4),sK5)
    | ~ m1_pre_topc(sK2,sK2)
    | ~ v1_tsep_1(sK2,sK2)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | r1_tmap_1(sK2,sK1,sK4,sK5) ),
    inference(superposition,[],[f896,f713])).

fof(f713,plain,(
    k3_tmap_1(sK0,sK1,sK2,sK2,sK4) = k3_tmap_1(sK2,sK1,sK2,sK2,sK4) ),
    inference(forward_demodulation,[],[f712,f707])).

fof(f712,plain,(
    k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,k2_struct_0(sK2)) = k3_tmap_1(sK2,sK1,sK2,sK2,sK4) ),
    inference(forward_demodulation,[],[f710,f103])).

fof(f710,plain,(
    k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(sK2,sK1,sK2,sK2,sK4) ),
    inference(resolution,[],[f700,f98])).

fof(f896,plain,(
    ! [X2] :
      ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(X2,sK1,sK2,sK2,sK4),sK5)
      | ~ m1_pre_topc(sK2,X2)
      | ~ v1_tsep_1(sK2,X2)
      | v2_struct_0(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | r1_tmap_1(sK2,sK1,sK4,sK5) ) ),
    inference(subsumption_resolution,[],[f895,f98])).

fof(f895,plain,(
    ! [X2] :
      ( ~ l1_pre_topc(X2)
      | ~ m1_pre_topc(sK2,X2)
      | ~ v1_tsep_1(sK2,X2)
      | ~ m1_pre_topc(sK2,sK2)
      | v2_struct_0(X2)
      | ~ v2_pre_topc(X2)
      | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(X2,sK1,sK2,sK2,sK4),sK5)
      | r1_tmap_1(sK2,sK1,sK4,sK5) ) ),
    inference(subsumption_resolution,[],[f894,f49])).

fof(f894,plain,(
    ! [X2] :
      ( ~ l1_pre_topc(X2)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,X2)
      | ~ v1_tsep_1(sK2,X2)
      | ~ m1_pre_topc(sK2,sK2)
      | v2_struct_0(X2)
      | ~ v2_pre_topc(X2)
      | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(X2,sK1,sK2,sK2,sK4),sK5)
      | r1_tmap_1(sK2,sK1,sK4,sK5) ) ),
    inference(subsumption_resolution,[],[f890,f107])).

fof(f890,plain,(
    ! [X2] :
      ( ~ m1_subset_1(sK5,k2_struct_0(sK2))
      | ~ l1_pre_topc(X2)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,X2)
      | ~ v1_tsep_1(sK2,X2)
      | ~ m1_pre_topc(sK2,sK2)
      | v2_struct_0(X2)
      | ~ v2_pre_topc(X2)
      | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(X2,sK1,sK2,sK2,sK4),sK5)
      | r1_tmap_1(sK2,sK1,sK4,sK5) ) ),
    inference(superposition,[],[f887,f103])).

fof(f887,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK5,u1_struct_0(X1))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(sK2,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK2,X1,sK4),sK5)
      | r1_tmap_1(sK2,sK1,sK4,sK5) ) ),
    inference(resolution,[],[f883,f107])).

fof(f883,plain,(
    ! [X6,X8,X7] :
      ( ~ m1_subset_1(X8,k2_struct_0(sK2))
      | ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | v2_struct_0(X7)
      | ~ m1_pre_topc(sK2,X6)
      | ~ v1_tsep_1(X7,X6)
      | ~ m1_pre_topc(X7,sK2)
      | v2_struct_0(X6)
      | ~ m1_subset_1(X8,u1_struct_0(X7))
      | ~ r1_tmap_1(X7,sK1,k3_tmap_1(X6,sK1,sK2,X7,sK4),X8)
      | r1_tmap_1(sK2,sK1,sK4,X8) ) ),
    inference(subsumption_resolution,[],[f882,f383])).

fof(f882,plain,(
    ! [X6,X8,X7] :
      ( v2_struct_0(X6)
      | ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | v2_struct_0(X7)
      | ~ m1_pre_topc(sK2,X6)
      | ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1))
      | ~ v1_tsep_1(X7,X6)
      | ~ m1_pre_topc(X7,sK2)
      | ~ m1_subset_1(X8,k2_struct_0(sK2))
      | ~ m1_subset_1(X8,u1_struct_0(X7))
      | ~ r1_tmap_1(X7,sK1,k3_tmap_1(X6,sK1,sK2,X7,sK4),X8)
      | r1_tmap_1(sK2,sK1,sK4,X8) ) ),
    inference(subsumption_resolution,[],[f881,f49])).

fof(f881,plain,(
    ! [X6,X8,X7] :
      ( v2_struct_0(X6)
      | ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | v2_struct_0(X7)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,X6)
      | ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1))
      | ~ v1_tsep_1(X7,X6)
      | ~ m1_pre_topc(X7,sK2)
      | ~ m1_subset_1(X8,k2_struct_0(sK2))
      | ~ m1_subset_1(X8,u1_struct_0(X7))
      | ~ r1_tmap_1(X7,sK1,k3_tmap_1(X6,sK1,sK2,X7,sK4),X8)
      | r1_tmap_1(sK2,sK1,sK4,X8) ) ),
    inference(subsumption_resolution,[],[f877,f382])).

fof(f877,plain,(
    ! [X6,X8,X7] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1))))
      | v2_struct_0(X6)
      | ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | v2_struct_0(X7)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,X6)
      | ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1))
      | ~ v1_tsep_1(X7,X6)
      | ~ m1_pre_topc(X7,sK2)
      | ~ m1_subset_1(X8,k2_struct_0(sK2))
      | ~ m1_subset_1(X8,u1_struct_0(X7))
      | ~ r1_tmap_1(X7,sK1,k3_tmap_1(X6,sK1,sK2,X7,sK4),X8)
      | r1_tmap_1(sK2,sK1,sK4,X8) ) ),
    inference(superposition,[],[f860,f103])).

fof(f860,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),k2_struct_0(sK1))))
      | v2_struct_0(X5)
      | ~ v2_pre_topc(X5)
      | ~ l1_pre_topc(X5)
      | v2_struct_0(X6)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X4,X5)
      | ~ v1_funct_2(sK4,u1_struct_0(X4),k2_struct_0(sK1))
      | ~ v1_tsep_1(X6,X5)
      | ~ m1_pre_topc(X6,X4)
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ r1_tmap_1(X6,sK1,k3_tmap_1(X5,sK1,X4,X6,sK4),X7)
      | r1_tmap_1(X4,sK1,sK4,X7) ) ),
    inference(subsumption_resolution,[],[f859,f52])).

fof(f859,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),k2_struct_0(sK1))))
      | v2_struct_0(X5)
      | ~ v2_pre_topc(X5)
      | ~ l1_pre_topc(X5)
      | v2_struct_0(X6)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X4,X5)
      | ~ v1_funct_2(sK4,u1_struct_0(X4),k2_struct_0(sK1))
      | ~ v2_pre_topc(sK1)
      | ~ v1_tsep_1(X6,X5)
      | ~ m1_pre_topc(X6,X4)
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ r1_tmap_1(X6,sK1,k3_tmap_1(X5,sK1,X4,X6,sK4),X7)
      | r1_tmap_1(X4,sK1,sK4,X7) ) ),
    inference(subsumption_resolution,[],[f858,f51])).

fof(f858,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),k2_struct_0(sK1))))
      | v2_struct_0(X5)
      | ~ v2_pre_topc(X5)
      | ~ l1_pre_topc(X5)
      | v2_struct_0(X6)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X4,X5)
      | v2_struct_0(sK1)
      | ~ v1_funct_2(sK4,u1_struct_0(X4),k2_struct_0(sK1))
      | ~ v2_pre_topc(sK1)
      | ~ v1_tsep_1(X6,X5)
      | ~ m1_pre_topc(X6,X4)
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ r1_tmap_1(X6,sK1,k3_tmap_1(X5,sK1,X4,X6,sK4),X7)
      | r1_tmap_1(X4,sK1,sK4,X7) ) ),
    inference(subsumption_resolution,[],[f848,f53])).

fof(f848,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),k2_struct_0(sK1))))
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(X5)
      | ~ v2_pre_topc(X5)
      | ~ l1_pre_topc(X5)
      | v2_struct_0(X6)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X4,X5)
      | v2_struct_0(sK1)
      | ~ v1_funct_2(sK4,u1_struct_0(X4),k2_struct_0(sK1))
      | ~ v2_pre_topc(sK1)
      | ~ v1_tsep_1(X6,X5)
      | ~ m1_pre_topc(X6,X4)
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ r1_tmap_1(X6,sK1,k3_tmap_1(X5,sK1,X4,X6,sK4),X7)
      | r1_tmap_1(X4,sK1,sK4,X7) ) ),
    inference(superposition,[],[f782,f102])).

fof(f782,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X0)
      | ~ v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | ~ v1_tsep_1(X2,X1)
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X2))
      | ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK4),X4)
      | r1_tmap_1(X3,X0,sK4,X4) ) ),
    inference(subsumption_resolution,[],[f781,f70])).

fof(f781,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X0)
      | ~ v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X0))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
      | ~ v1_tsep_1(X2,X1)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X2))
      | ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK4),X4)
      | r1_tmap_1(X3,X0,sK4,X4) ) ),
    inference(resolution,[],[f77,f43])).

fof(f77,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X0)
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
      | ~ v1_tsep_1(X2,X1)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
      | r1_tmap_1(X3,X0,X4,X6) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X1)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
      | ~ v1_tsep_1(X2,X1)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | X5 != X6
      | ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
      | r1_tmap_1(X3,X0,X4,X5) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f974,plain,
    ( ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK2,sK2,sK4),sK5)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ v1_tsep_1(sK3,sK2)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(superposition,[],[f962,f749])).

fof(f749,plain,(
    k3_tmap_1(sK0,sK1,sK2,sK2,sK4) = k3_tmap_1(sK2,sK1,sK3,sK3,sK4) ),
    inference(forward_demodulation,[],[f748,f707])).

fof(f748,plain,(
    k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,k2_struct_0(sK2)) = k3_tmap_1(sK2,sK1,sK3,sK3,sK4) ),
    inference(forward_demodulation,[],[f746,f381])).

fof(f746,plain,(
    k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(sK2,sK1,sK3,sK3,sK4) ),
    inference(resolution,[],[f738,f96])).

fof(f738,plain,(
    ! [X4] :
      ( ~ m1_pre_topc(X4,sK3)
      | k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X4)) = k3_tmap_1(sK2,sK1,sK3,X4,sK4) ) ),
    inference(subsumption_resolution,[],[f737,f125])).

fof(f737,plain,(
    ! [X4] :
      ( ~ v2_pre_topc(sK2)
      | ~ m1_pre_topc(X4,sK3)
      | k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X4)) = k3_tmap_1(sK2,sK1,sK3,X4,sK4) ) ),
    inference(subsumption_resolution,[],[f736,f49])).

fof(f736,plain,(
    ! [X4] :
      ( v2_struct_0(sK2)
      | ~ v2_pre_topc(sK2)
      | ~ m1_pre_topc(X4,sK3)
      | k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X4)) = k3_tmap_1(sK2,sK1,sK3,X4,sK4) ) ),
    inference(subsumption_resolution,[],[f728,f93])).

fof(f728,plain,(
    ! [X4] :
      ( ~ l1_pre_topc(sK2)
      | v2_struct_0(sK2)
      | ~ v2_pre_topc(sK2)
      | ~ m1_pre_topc(X4,sK3)
      | k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X4)) = k3_tmap_1(sK2,sK1,sK3,X4,sK4) ) ),
    inference(resolution,[],[f687,f315])).

fof(f962,plain,(
    ! [X3] :
      ( ~ r1_tmap_1(sK3,sK1,k3_tmap_1(X3,sK1,sK3,sK3,sK4),sK5)
      | ~ m1_pre_topc(sK3,X3)
      | ~ v1_tsep_1(sK3,X3)
      | v2_struct_0(X3)
      | ~ v2_pre_topc(X3)
      | ~ l1_pre_topc(X3) ) ),
    inference(subsumption_resolution,[],[f961,f96])).

fof(f961,plain,(
    ! [X3] :
      ( ~ l1_pre_topc(X3)
      | ~ m1_pre_topc(sK3,X3)
      | ~ v1_tsep_1(sK3,X3)
      | ~ m1_pre_topc(sK3,sK3)
      | v2_struct_0(X3)
      | ~ v2_pre_topc(X3)
      | ~ r1_tmap_1(sK3,sK1,k3_tmap_1(X3,sK1,sK3,sK3,sK4),sK5) ) ),
    inference(subsumption_resolution,[],[f960,f47])).

fof(f960,plain,(
    ! [X3] :
      ( ~ l1_pre_topc(X3)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,X3)
      | ~ v1_tsep_1(sK3,X3)
      | ~ m1_pre_topc(sK3,sK3)
      | v2_struct_0(X3)
      | ~ v2_pre_topc(X3)
      | ~ r1_tmap_1(sK3,sK1,k3_tmap_1(X3,sK1,sK3,sK3,sK4),sK5) ) ),
    inference(subsumption_resolution,[],[f955,f107])).

fof(f955,plain,(
    ! [X3] :
      ( ~ m1_subset_1(sK5,k2_struct_0(sK2))
      | ~ l1_pre_topc(X3)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,X3)
      | ~ v1_tsep_1(sK3,X3)
      | ~ m1_pre_topc(sK3,sK3)
      | v2_struct_0(X3)
      | ~ v2_pre_topc(X3)
      | ~ r1_tmap_1(sK3,sK1,k3_tmap_1(X3,sK1,sK3,sK3,sK4),sK5) ) ),
    inference(superposition,[],[f951,f381])).

fof(f951,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK5,u1_struct_0(X1))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(sK3,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,sK3)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5) ) ),
    inference(subsumption_resolution,[],[f950,f41])).

fof(f41,plain,(
    ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f18])).

fof(f950,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(sK3,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,sK3)
      | v2_struct_0(X0)
      | ~ m1_subset_1(sK5,u1_struct_0(X1))
      | ~ r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5)
      | r1_tmap_1(sK3,sK1,sK4,sK5) ) ),
    inference(resolution,[],[f886,f107])).

fof(f886,plain,(
    ! [X10,X11,X9] :
      ( ~ m1_subset_1(X11,k2_struct_0(sK2))
      | ~ v2_pre_topc(X9)
      | ~ l1_pre_topc(X9)
      | v2_struct_0(X10)
      | ~ m1_pre_topc(sK3,X9)
      | ~ v1_tsep_1(X10,X9)
      | ~ m1_pre_topc(X10,sK3)
      | v2_struct_0(X9)
      | ~ m1_subset_1(X11,u1_struct_0(X10))
      | ~ r1_tmap_1(X10,sK1,k3_tmap_1(X9,sK1,sK3,X10,sK4),X11)
      | r1_tmap_1(sK3,sK1,sK4,X11) ) ),
    inference(subsumption_resolution,[],[f885,f383])).

fof(f885,plain,(
    ! [X10,X11,X9] :
      ( v2_struct_0(X9)
      | ~ v2_pre_topc(X9)
      | ~ l1_pre_topc(X9)
      | v2_struct_0(X10)
      | ~ m1_pre_topc(sK3,X9)
      | ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1))
      | ~ v1_tsep_1(X10,X9)
      | ~ m1_pre_topc(X10,sK3)
      | ~ m1_subset_1(X11,k2_struct_0(sK2))
      | ~ m1_subset_1(X11,u1_struct_0(X10))
      | ~ r1_tmap_1(X10,sK1,k3_tmap_1(X9,sK1,sK3,X10,sK4),X11)
      | r1_tmap_1(sK3,sK1,sK4,X11) ) ),
    inference(subsumption_resolution,[],[f884,f47])).

fof(f884,plain,(
    ! [X10,X11,X9] :
      ( v2_struct_0(X9)
      | ~ v2_pre_topc(X9)
      | ~ l1_pre_topc(X9)
      | v2_struct_0(X10)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,X9)
      | ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1))
      | ~ v1_tsep_1(X10,X9)
      | ~ m1_pre_topc(X10,sK3)
      | ~ m1_subset_1(X11,k2_struct_0(sK2))
      | ~ m1_subset_1(X11,u1_struct_0(X10))
      | ~ r1_tmap_1(X10,sK1,k3_tmap_1(X9,sK1,sK3,X10,sK4),X11)
      | r1_tmap_1(sK3,sK1,sK4,X11) ) ),
    inference(subsumption_resolution,[],[f878,f382])).

fof(f878,plain,(
    ! [X10,X11,X9] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1))))
      | v2_struct_0(X9)
      | ~ v2_pre_topc(X9)
      | ~ l1_pre_topc(X9)
      | v2_struct_0(X10)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,X9)
      | ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1))
      | ~ v1_tsep_1(X10,X9)
      | ~ m1_pre_topc(X10,sK3)
      | ~ m1_subset_1(X11,k2_struct_0(sK2))
      | ~ m1_subset_1(X11,u1_struct_0(X10))
      | ~ r1_tmap_1(X10,sK1,k3_tmap_1(X9,sK1,sK3,X10,sK4),X11)
      | r1_tmap_1(sK3,sK1,sK4,X11) ) ),
    inference(superposition,[],[f860,f381])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n019.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 20:13:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.47  % (989)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.47  % (989)Refutation not found, incomplete strategy% (989)------------------------------
% 0.22/0.47  % (989)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (1004)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.47  % (989)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (989)Memory used [KB]: 6268
% 0.22/0.47  % (989)Time elapsed: 0.054 s
% 0.22/0.47  % (989)------------------------------
% 0.22/0.47  % (989)------------------------------
% 0.22/0.49  % (995)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.49  % (996)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.50  % (983)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.50  % (1003)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.50  % (1002)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.50  % (984)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.50  % (985)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.50  % (986)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.51  % (990)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.51  % (982)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.51  % (1005)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.51  % (994)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.52  % (1000)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.52  % (998)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.52  % (1007)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.52  % (1001)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.52  % (1006)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.52  % (1008)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.53  % (991)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.53  % (991)Refutation not found, incomplete strategy% (991)------------------------------
% 0.22/0.53  % (991)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (991)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (991)Memory used [KB]: 1791
% 0.22/0.53  % (991)Time elapsed: 0.098 s
% 0.22/0.53  % (991)------------------------------
% 0.22/0.53  % (991)------------------------------
% 0.22/0.53  % (993)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.53  % (992)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.53  % (1009)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.53  % (997)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.55  % (999)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.56  % (1003)Refutation found. Thanks to Tanya!
% 0.22/0.56  % SZS status Theorem for theBenchmark
% 0.22/0.56  % SZS output start Proof for theBenchmark
% 0.22/0.56  fof(f992,plain,(
% 0.22/0.56    $false),
% 0.22/0.56    inference(subsumption_resolution,[],[f991,f93])).
% 0.22/0.56  fof(f93,plain,(
% 0.22/0.56    l1_pre_topc(sK2)),
% 0.22/0.56    inference(resolution,[],[f90,f50])).
% 0.22/0.56  fof(f50,plain,(
% 0.22/0.56    m1_pre_topc(sK2,sK0)),
% 0.22/0.56    inference(cnf_transformation,[],[f18])).
% 0.22/0.56  fof(f18,plain,(
% 0.22/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.56    inference(flattening,[],[f17])).
% 0.22/0.56  fof(f17,plain,(
% 0.22/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f16])).
% 0.22/0.56  fof(f16,negated_conjecture,(
% 0.22/0.56    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 0.22/0.56    inference(negated_conjecture,[],[f15])).
% 0.22/0.56  fof(f15,conjecture,(
% 0.22/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tmap_1)).
% 0.22/0.56  fof(f90,plain,(
% 0.22/0.56    ( ! [X1] : (~m1_pre_topc(X1,sK0) | l1_pre_topc(X1)) )),
% 0.22/0.56    inference(resolution,[],[f62,f56])).
% 0.22/0.56  fof(f56,plain,(
% 0.22/0.56    l1_pre_topc(sK0)),
% 0.22/0.56    inference(cnf_transformation,[],[f18])).
% 0.22/0.56  fof(f62,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f23])).
% 0.22/0.56  fof(f23,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f5])).
% 0.22/0.56  fof(f5,axiom,(
% 0.22/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.22/0.56  fof(f991,plain,(
% 0.22/0.56    ~l1_pre_topc(sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f990,f125])).
% 0.22/0.56  fof(f125,plain,(
% 0.22/0.56    v2_pre_topc(sK2)),
% 0.22/0.56    inference(resolution,[],[f122,f50])).
% 0.22/0.56  fof(f122,plain,(
% 0.22/0.56    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v2_pre_topc(X0)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f118,f55])).
% 0.22/0.56  fof(f55,plain,(
% 0.22/0.56    v2_pre_topc(sK0)),
% 0.22/0.56    inference(cnf_transformation,[],[f18])).
% 0.22/0.56  fof(f118,plain,(
% 0.22/0.56    ( ! [X0] : (~v2_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | v2_pre_topc(X0)) )),
% 0.22/0.56    inference(resolution,[],[f69,f56])).
% 0.22/0.56  fof(f69,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_pre_topc(X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f33])).
% 0.22/0.56  fof(f33,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.56    inference(flattening,[],[f32])).
% 0.22/0.56  fof(f32,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f2])).
% 0.22/0.56  fof(f2,axiom,(
% 0.22/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.22/0.56  fof(f990,plain,(
% 0.22/0.56    ~v2_pre_topc(sK2) | ~l1_pre_topc(sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f989,f49])).
% 0.22/0.56  fof(f49,plain,(
% 0.22/0.56    ~v2_struct_0(sK2)),
% 0.22/0.56    inference(cnf_transformation,[],[f18])).
% 0.22/0.56  fof(f989,plain,(
% 0.22/0.56    v2_struct_0(sK2) | ~v2_pre_topc(sK2) | ~l1_pre_topc(sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f988,f548])).
% 0.22/0.56  fof(f548,plain,(
% 0.22/0.56    v1_tsep_1(sK3,sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f547,f315])).
% 0.22/0.56  fof(f315,plain,(
% 0.22/0.56    m1_pre_topc(sK3,sK2)),
% 0.22/0.56    inference(resolution,[],[f313,f96])).
% 0.22/0.56  fof(f96,plain,(
% 0.22/0.56    m1_pre_topc(sK3,sK3)),
% 0.22/0.56    inference(resolution,[],[f92,f59])).
% 0.22/0.56  fof(f59,plain,(
% 0.22/0.56    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f21])).
% 0.22/0.56  fof(f21,plain,(
% 0.22/0.56    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f11])).
% 0.22/0.56  fof(f11,axiom,(
% 0.22/0.56    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.22/0.56  fof(f92,plain,(
% 0.22/0.56    l1_pre_topc(sK3)),
% 0.22/0.56    inference(resolution,[],[f90,f48])).
% 0.22/0.56  fof(f48,plain,(
% 0.22/0.56    m1_pre_topc(sK3,sK0)),
% 0.22/0.56    inference(cnf_transformation,[],[f18])).
% 0.22/0.56  fof(f313,plain,(
% 0.22/0.56    ( ! [X2] : (~m1_pre_topc(X2,sK3) | m1_pre_topc(X2,sK2)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f312,f95])).
% 0.22/0.56  fof(f95,plain,(
% 0.22/0.56    ( ! [X0] : (~m1_pre_topc(X0,sK3) | l1_pre_topc(X0)) )),
% 0.22/0.56    inference(resolution,[],[f92,f62])).
% 0.22/0.56  fof(f312,plain,(
% 0.22/0.56    ( ! [X2] : (~m1_pre_topc(X2,sK3) | ~l1_pre_topc(X2) | m1_pre_topc(X2,sK2)) )),
% 0.22/0.56    inference(forward_demodulation,[],[f311,f108])).
% 0.22/0.56  fof(f108,plain,(
% 0.22/0.56    sK3 = g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))),
% 0.22/0.56    inference(backward_demodulation,[],[f46,f103])).
% 0.22/0.56  fof(f103,plain,(
% 0.22/0.56    u1_struct_0(sK2) = k2_struct_0(sK2)),
% 0.22/0.56    inference(resolution,[],[f88,f93])).
% 0.22/0.56  fof(f88,plain,(
% 0.22/0.56    ( ! [X0] : (~l1_pre_topc(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.56    inference(resolution,[],[f57,f58])).
% 0.22/0.56  fof(f58,plain,(
% 0.22/0.56    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f20])).
% 0.22/0.56  fof(f20,plain,(
% 0.22/0.56    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f4])).
% 0.22/0.56  fof(f4,axiom,(
% 0.22/0.56    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.56  fof(f57,plain,(
% 0.22/0.56    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f19])).
% 0.22/0.56  fof(f19,plain,(
% 0.22/0.56    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f3])).
% 0.22/0.56  fof(f3,axiom,(
% 0.22/0.56    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.56  fof(f46,plain,(
% 0.22/0.56    sK3 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 0.22/0.56    inference(cnf_transformation,[],[f18])).
% 0.22/0.56  fof(f311,plain,(
% 0.22/0.56    ( ! [X2] : (~m1_pre_topc(X2,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))) | ~l1_pre_topc(X2) | m1_pre_topc(X2,sK2)) )),
% 0.22/0.56    inference(forward_demodulation,[],[f307,f103])).
% 0.22/0.56  fof(f307,plain,(
% 0.22/0.56    ( ! [X2] : (~l1_pre_topc(X2) | ~m1_pre_topc(X2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | m1_pre_topc(X2,sK2)) )),
% 0.22/0.56    inference(resolution,[],[f60,f93])).
% 0.22/0.56  fof(f60,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | m1_pre_topc(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f22])).
% 0.22/0.56  fof(f22,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f6])).
% 0.22/0.56  fof(f6,axiom,(
% 0.22/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).
% 0.22/0.56  fof(f547,plain,(
% 0.22/0.56    ~m1_pre_topc(sK3,sK2) | v1_tsep_1(sK3,sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f544,f130])).
% 0.22/0.56  fof(f130,plain,(
% 0.22/0.56    v3_pre_topc(k2_struct_0(sK2),sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f114,f125])).
% 0.22/0.56  fof(f114,plain,(
% 0.22/0.56    v3_pre_topc(k2_struct_0(sK2),sK2) | ~v2_pre_topc(sK2)),
% 0.22/0.56    inference(resolution,[],[f68,f93])).
% 0.22/0.56  fof(f68,plain,(
% 0.22/0.56    ( ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v3_pre_topc(k2_struct_0(X0),X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f31])).
% 0.22/0.56  fof(f31,plain,(
% 0.22/0.56    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.56    inference(flattening,[],[f30])).
% 0.22/0.56  fof(f30,plain,(
% 0.22/0.56    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f7])).
% 0.22/0.56  fof(f7,axiom,(
% 0.22/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).
% 0.22/0.56  fof(f544,plain,(
% 0.22/0.56    ~v3_pre_topc(k2_struct_0(sK2),sK2) | ~m1_pre_topc(sK3,sK2) | v1_tsep_1(sK3,sK2)),
% 0.22/0.56    inference(superposition,[],[f525,f381])).
% 0.22/0.56  fof(f381,plain,(
% 0.22/0.56    u1_struct_0(sK3) = k2_struct_0(sK2)),
% 0.22/0.56    inference(backward_demodulation,[],[f104,f380])).
% 0.22/0.56  fof(f380,plain,(
% 0.22/0.56    k2_struct_0(sK2) = k2_struct_0(sK3)),
% 0.22/0.56    inference(subsumption_resolution,[],[f374,f98])).
% 0.22/0.56  fof(f98,plain,(
% 0.22/0.56    m1_pre_topc(sK2,sK2)),
% 0.22/0.56    inference(resolution,[],[f93,f59])).
% 0.22/0.56  fof(f374,plain,(
% 0.22/0.56    ~m1_pre_topc(sK2,sK2) | k2_struct_0(sK2) = k2_struct_0(sK3)),
% 0.22/0.56    inference(resolution,[],[f363,f319])).
% 0.22/0.56  fof(f319,plain,(
% 0.22/0.56    ~m1_pre_topc(sK2,sK3) | k2_struct_0(sK2) = k2_struct_0(sK3)),
% 0.22/0.56    inference(subsumption_resolution,[],[f183,f318])).
% 0.22/0.56  fof(f318,plain,(
% 0.22/0.56    r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2))),
% 0.22/0.56    inference(subsumption_resolution,[],[f166,f315])).
% 0.22/0.56  fof(f166,plain,(
% 0.22/0.56    r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) | ~m1_pre_topc(sK3,sK2)),
% 0.22/0.56    inference(superposition,[],[f146,f104])).
% 0.22/0.56  fof(f146,plain,(
% 0.22/0.56    ( ! [X2] : (r1_tarski(u1_struct_0(X2),k2_struct_0(sK2)) | ~m1_pre_topc(X2,sK2)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f142,f93])).
% 0.22/0.56  fof(f142,plain,(
% 0.22/0.56    ( ! [X2] : (r1_tarski(u1_struct_0(X2),k2_struct_0(sK2)) | ~m1_pre_topc(X2,sK2) | ~l1_pre_topc(sK2)) )),
% 0.22/0.56    inference(superposition,[],[f63,f103])).
% 0.22/0.56  fof(f63,plain,(
% 0.22/0.56    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f24])).
% 0.22/0.56  fof(f24,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f12])).
% 0.22/0.56  fof(f12,axiom,(
% 0.22/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).
% 0.22/0.56  fof(f183,plain,(
% 0.22/0.56    ~m1_pre_topc(sK2,sK3) | ~r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) | k2_struct_0(sK2) = k2_struct_0(sK3)),
% 0.22/0.56    inference(resolution,[],[f170,f75])).
% 0.22/0.56  fof(f75,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.22/0.56    inference(cnf_transformation,[],[f1])).
% 0.22/0.56  fof(f1,axiom,(
% 0.22/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.56  fof(f170,plain,(
% 0.22/0.56    r1_tarski(k2_struct_0(sK2),k2_struct_0(sK3)) | ~m1_pre_topc(sK2,sK3)),
% 0.22/0.56    inference(superposition,[],[f147,f103])).
% 0.22/0.56  fof(f147,plain,(
% 0.22/0.56    ( ! [X3] : (r1_tarski(u1_struct_0(X3),k2_struct_0(sK3)) | ~m1_pre_topc(X3,sK3)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f143,f92])).
% 0.22/0.56  fof(f143,plain,(
% 0.22/0.56    ( ! [X3] : (r1_tarski(u1_struct_0(X3),k2_struct_0(sK3)) | ~m1_pre_topc(X3,sK3) | ~l1_pre_topc(sK3)) )),
% 0.22/0.56    inference(superposition,[],[f63,f104])).
% 0.22/0.56  fof(f363,plain,(
% 0.22/0.56    ( ! [X2] : (m1_pre_topc(X2,sK3) | ~m1_pre_topc(X2,sK2)) )),
% 0.22/0.56    inference(forward_demodulation,[],[f362,f108])).
% 0.22/0.56  fof(f362,plain,(
% 0.22/0.56    ( ! [X2] : (m1_pre_topc(X2,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))) | ~m1_pre_topc(X2,sK2)) )),
% 0.22/0.56    inference(forward_demodulation,[],[f361,f103])).
% 0.22/0.56  fof(f361,plain,(
% 0.22/0.56    ( ! [X2] : (m1_pre_topc(X2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~m1_pre_topc(X2,sK2)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f355,f97])).
% 0.22/0.56  fof(f97,plain,(
% 0.22/0.56    ( ! [X0] : (~m1_pre_topc(X0,sK2) | l1_pre_topc(X0)) )),
% 0.22/0.56    inference(resolution,[],[f93,f62])).
% 0.22/0.56  fof(f355,plain,(
% 0.22/0.56    ( ! [X2] : (~l1_pre_topc(X2) | m1_pre_topc(X2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~m1_pre_topc(X2,sK2)) )),
% 0.22/0.56    inference(resolution,[],[f61,f93])).
% 0.22/0.56  fof(f61,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~l1_pre_topc(X1) | ~l1_pre_topc(X0) | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f22])).
% 0.22/0.56  fof(f104,plain,(
% 0.22/0.56    u1_struct_0(sK3) = k2_struct_0(sK3)),
% 0.22/0.56    inference(resolution,[],[f88,f92])).
% 0.22/0.56  fof(f525,plain,(
% 0.22/0.56    ( ! [X2] : (~v3_pre_topc(u1_struct_0(X2),sK2) | ~m1_pre_topc(X2,sK2) | v1_tsep_1(X2,sK2)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f521,f125])).
% 0.22/0.56  fof(f521,plain,(
% 0.22/0.56    ( ! [X2] : (~v2_pre_topc(sK2) | ~m1_pre_topc(X2,sK2) | ~v3_pre_topc(u1_struct_0(X2),sK2) | v1_tsep_1(X2,sK2)) )),
% 0.22/0.56    inference(resolution,[],[f84,f93])).
% 0.22/0.56  fof(f84,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v3_pre_topc(u1_struct_0(X1),X0) | v1_tsep_1(X1,X0)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f78,f64])).
% 0.22/0.56  fof(f64,plain,(
% 0.22/0.56    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f25])).
% 0.22/0.56  fof(f25,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f10])).
% 0.22/0.56  fof(f10,axiom,(
% 0.22/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.22/0.56  fof(f78,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(u1_struct_0(X1),X0) | v1_tsep_1(X1,X0)) )),
% 0.22/0.56    inference(equality_resolution,[],[f72])).
% 0.22/0.56  fof(f72,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | ~v3_pre_topc(X2,X0) | v1_tsep_1(X1,X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f37])).
% 0.22/0.56  fof(f37,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.56    inference(flattening,[],[f36])).
% 0.22/0.56  fof(f36,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f9])).
% 0.22/0.56  fof(f9,axiom,(
% 0.22/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).
% 0.22/0.56  fof(f988,plain,(
% 0.22/0.56    ~v1_tsep_1(sK3,sK2) | v2_struct_0(sK2) | ~v2_pre_topc(sK2) | ~l1_pre_topc(sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f987,f315])).
% 0.22/0.56  fof(f987,plain,(
% 0.22/0.56    ~m1_pre_topc(sK3,sK2) | ~v1_tsep_1(sK3,sK2) | v2_struct_0(sK2) | ~v2_pre_topc(sK2) | ~l1_pre_topc(sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f974,f949])).
% 0.22/0.56  fof(f949,plain,(
% 0.22/0.56    r1_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK2,sK2,sK4),sK5)),
% 0.22/0.56    inference(subsumption_resolution,[],[f948,f49])).
% 0.22/0.56  fof(f948,plain,(
% 0.22/0.56    r1_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK2,sK2,sK4),sK5) | v2_struct_0(sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f947,f93])).
% 0.22/0.56  fof(f947,plain,(
% 0.22/0.56    r1_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK2,sK2,sK4),sK5) | ~l1_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f946,f125])).
% 0.22/0.56  fof(f946,plain,(
% 0.22/0.56    r1_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK2,sK2,sK4),sK5) | ~v2_pre_topc(sK2) | ~l1_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f945,f548])).
% 0.22/0.56  fof(f945,plain,(
% 0.22/0.56    r1_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK2,sK2,sK4),sK5) | ~v1_tsep_1(sK3,sK2) | ~v2_pre_topc(sK2) | ~l1_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f939,f98])).
% 0.22/0.56  fof(f939,plain,(
% 0.22/0.56    r1_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK2,sK2,sK4),sK5) | ~m1_pre_topc(sK2,sK2) | ~v1_tsep_1(sK3,sK2) | ~v2_pre_topc(sK2) | ~l1_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.22/0.56    inference(superposition,[],[f934,f715])).
% 0.22/0.56  fof(f715,plain,(
% 0.22/0.56    k3_tmap_1(sK0,sK1,sK2,sK2,sK4) = k3_tmap_1(sK2,sK1,sK2,sK3,sK4)),
% 0.22/0.56    inference(forward_demodulation,[],[f714,f707])).
% 0.22/0.56  fof(f707,plain,(
% 0.22/0.56    k3_tmap_1(sK0,sK1,sK2,sK2,sK4) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,k2_struct_0(sK2))),
% 0.22/0.56    inference(forward_demodulation,[],[f705,f103])).
% 0.22/0.56  fof(f705,plain,(
% 0.22/0.56    k3_tmap_1(sK0,sK1,sK2,sK2,sK4) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(sK2))),
% 0.22/0.56    inference(resolution,[],[f697,f98])).
% 0.22/0.56  fof(f697,plain,(
% 0.22/0.56    ( ! [X3] : (~m1_pre_topc(X3,sK2) | k3_tmap_1(sK0,sK1,sK2,X3,sK4) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3))) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f696,f55])).
% 0.22/0.56  fof(f696,plain,(
% 0.22/0.56    ( ! [X3] : (~v2_pre_topc(sK0) | ~m1_pre_topc(X3,sK2) | k3_tmap_1(sK0,sK1,sK2,X3,sK4) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3))) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f695,f54])).
% 0.22/0.56  fof(f54,plain,(
% 0.22/0.56    ~v2_struct_0(sK0)),
% 0.22/0.56    inference(cnf_transformation,[],[f18])).
% 0.22/0.56  fof(f695,plain,(
% 0.22/0.56    ( ! [X3] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_pre_topc(X3,sK2) | k3_tmap_1(sK0,sK1,sK2,X3,sK4) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3))) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f691,f56])).
% 0.22/0.56  fof(f691,plain,(
% 0.22/0.56    ( ! [X3] : (~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_pre_topc(X3,sK2) | k3_tmap_1(sK0,sK1,sK2,X3,sK4) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3))) )),
% 0.22/0.56    inference(resolution,[],[f685,f50])).
% 0.22/0.56  fof(f685,plain,(
% 0.22/0.56    ( ! [X4,X5] : (~m1_pre_topc(sK2,X4) | ~l1_pre_topc(X4) | v2_struct_0(X4) | ~v2_pre_topc(X4) | ~m1_pre_topc(X5,sK2) | k3_tmap_1(X4,sK1,sK2,X5,sK4) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X5))) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f684,f383])).
% 0.22/0.56  fof(f383,plain,(
% 0.22/0.56    v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1))),
% 0.22/0.56    inference(backward_demodulation,[],[f110,f380])).
% 0.22/0.56  fof(f110,plain,(
% 0.22/0.56    v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1))),
% 0.22/0.56    inference(backward_demodulation,[],[f105,f104])).
% 0.22/0.56  fof(f105,plain,(
% 0.22/0.56    v1_funct_2(sK4,u1_struct_0(sK3),k2_struct_0(sK1))),
% 0.22/0.56    inference(backward_demodulation,[],[f44,f102])).
% 0.22/0.56  fof(f102,plain,(
% 0.22/0.56    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.22/0.56    inference(resolution,[],[f88,f53])).
% 0.22/0.56  fof(f53,plain,(
% 0.22/0.56    l1_pre_topc(sK1)),
% 0.22/0.56    inference(cnf_transformation,[],[f18])).
% 0.22/0.56  fof(f44,plain,(
% 0.22/0.56    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.22/0.56    inference(cnf_transformation,[],[f18])).
% 0.22/0.56  fof(f684,plain,(
% 0.22/0.56    ( ! [X4,X5] : (~l1_pre_topc(X4) | ~m1_pre_topc(sK2,X4) | v2_struct_0(X4) | ~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1)) | ~v2_pre_topc(X4) | ~m1_pre_topc(X5,sK2) | k3_tmap_1(X4,sK1,sK2,X5,sK4) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X5))) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f682,f382])).
% 0.22/0.56  fof(f382,plain,(
% 0.22/0.56    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1))))),
% 0.22/0.56    inference(backward_demodulation,[],[f109,f380])).
% 0.22/0.56  fof(f109,plain,(
% 0.22/0.56    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1))))),
% 0.22/0.56    inference(backward_demodulation,[],[f106,f104])).
% 0.22/0.56  fof(f106,plain,(
% 0.22/0.56    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1))))),
% 0.22/0.56    inference(backward_demodulation,[],[f45,f102])).
% 0.22/0.56  fof(f45,plain,(
% 0.22/0.56    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.22/0.56    inference(cnf_transformation,[],[f18])).
% 0.22/0.56  fof(f682,plain,(
% 0.22/0.56    ( ! [X4,X5] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1)))) | ~l1_pre_topc(X4) | ~m1_pre_topc(sK2,X4) | v2_struct_0(X4) | ~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1)) | ~v2_pre_topc(X4) | ~m1_pre_topc(X5,sK2) | k3_tmap_1(X4,sK1,sK2,X5,sK4) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X5))) )),
% 0.22/0.56    inference(superposition,[],[f669,f103])).
% 0.22/0.56  fof(f669,plain,(
% 0.22/0.56    ( ! [X4,X5,X3] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK1)))) | ~l1_pre_topc(X4) | ~m1_pre_topc(X3,X4) | v2_struct_0(X4) | ~v1_funct_2(sK4,u1_struct_0(X3),k2_struct_0(sK1)) | ~v2_pre_topc(X4) | ~m1_pre_topc(X5,X3) | k3_tmap_1(X4,sK1,X3,X5,sK4) = k2_partfun1(u1_struct_0(X3),k2_struct_0(sK1),sK4,u1_struct_0(X5))) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f668,f53])).
% 0.22/0.56  fof(f668,plain,(
% 0.22/0.56    ( ! [X4,X5,X3] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK1)))) | ~l1_pre_topc(X4) | ~l1_pre_topc(sK1) | ~m1_pre_topc(X3,X4) | v2_struct_0(X4) | ~v1_funct_2(sK4,u1_struct_0(X3),k2_struct_0(sK1)) | ~v2_pre_topc(X4) | ~m1_pre_topc(X5,X3) | k3_tmap_1(X4,sK1,X3,X5,sK4) = k2_partfun1(u1_struct_0(X3),k2_struct_0(sK1),sK4,u1_struct_0(X5))) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f667,f52])).
% 0.22/0.56  fof(f52,plain,(
% 0.22/0.56    v2_pre_topc(sK1)),
% 0.22/0.56    inference(cnf_transformation,[],[f18])).
% 0.22/0.56  fof(f667,plain,(
% 0.22/0.56    ( ! [X4,X5,X3] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK1)))) | ~l1_pre_topc(X4) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_pre_topc(X3,X4) | v2_struct_0(X4) | ~v1_funct_2(sK4,u1_struct_0(X3),k2_struct_0(sK1)) | ~v2_pre_topc(X4) | ~m1_pre_topc(X5,X3) | k3_tmap_1(X4,sK1,X3,X5,sK4) = k2_partfun1(u1_struct_0(X3),k2_struct_0(sK1),sK4,u1_struct_0(X5))) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f661,f51])).
% 0.22/0.56  fof(f51,plain,(
% 0.22/0.56    ~v2_struct_0(sK1)),
% 0.22/0.56    inference(cnf_transformation,[],[f18])).
% 0.22/0.56  fof(f661,plain,(
% 0.22/0.56    ( ! [X4,X5,X3] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK1)))) | ~l1_pre_topc(X4) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_pre_topc(X3,X4) | v2_struct_0(X4) | ~v1_funct_2(sK4,u1_struct_0(X3),k2_struct_0(sK1)) | ~v2_pre_topc(X4) | ~m1_pre_topc(X5,X3) | k3_tmap_1(X4,sK1,X3,X5,sK4) = k2_partfun1(u1_struct_0(X3),k2_struct_0(sK1),sK4,u1_struct_0(X5))) )),
% 0.22/0.56    inference(superposition,[],[f634,f102])).
% 0.22/0.56  fof(f634,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(X2),u1_struct_0(X1)) | ~v2_pre_topc(X0) | ~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,sK4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),sK4,u1_struct_0(X3))) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f633,f70])).
% 0.22/0.56  fof(f70,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X1) | m1_pre_topc(X2,X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f35])).
% 0.22/0.56  fof(f35,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.56    inference(flattening,[],[f34])).
% 0.22/0.56  fof(f34,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f13])).
% 0.22/0.56  fof(f13,axiom,(
% 0.22/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).
% 0.22/0.56  fof(f633,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X3,X0) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,sK4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),sK4,u1_struct_0(X3))) )),
% 0.22/0.56    inference(resolution,[],[f65,f43])).
% 0.22/0.56  fof(f43,plain,(
% 0.22/0.56    v1_funct_1(sK4)),
% 0.22/0.56    inference(cnf_transformation,[],[f18])).
% 0.22/0.56  fof(f65,plain,(
% 0.22/0.56    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X4) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X3,X0) | v2_struct_0(X0) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f27])).
% 0.22/0.56  fof(f27,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.56    inference(flattening,[],[f26])).
% 0.22/0.56  fof(f26,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f8])).
% 0.22/0.56  fof(f8,axiom,(
% 0.22/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).
% 0.22/0.56  fof(f714,plain,(
% 0.22/0.56    k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,k2_struct_0(sK2)) = k3_tmap_1(sK2,sK1,sK2,sK3,sK4)),
% 0.22/0.56    inference(forward_demodulation,[],[f711,f381])).
% 0.22/0.56  fof(f711,plain,(
% 0.22/0.56    k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(sK2,sK1,sK2,sK3,sK4)),
% 0.22/0.56    inference(resolution,[],[f700,f315])).
% 0.22/0.56  fof(f700,plain,(
% 0.22/0.56    ( ! [X4] : (~m1_pre_topc(X4,sK2) | k3_tmap_1(sK2,sK1,sK2,X4,sK4) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X4))) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f699,f125])).
% 0.22/0.56  fof(f699,plain,(
% 0.22/0.56    ( ! [X4] : (~v2_pre_topc(sK2) | ~m1_pre_topc(X4,sK2) | k3_tmap_1(sK2,sK1,sK2,X4,sK4) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X4))) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f698,f49])).
% 0.22/0.56  fof(f698,plain,(
% 0.22/0.56    ( ! [X4] : (v2_struct_0(sK2) | ~v2_pre_topc(sK2) | ~m1_pre_topc(X4,sK2) | k3_tmap_1(sK2,sK1,sK2,X4,sK4) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X4))) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f692,f93])).
% 0.22/0.56  fof(f692,plain,(
% 0.22/0.56    ( ! [X4] : (~l1_pre_topc(sK2) | v2_struct_0(sK2) | ~v2_pre_topc(sK2) | ~m1_pre_topc(X4,sK2) | k3_tmap_1(sK2,sK1,sK2,X4,sK4) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X4))) )),
% 0.22/0.56    inference(resolution,[],[f685,f98])).
% 0.22/0.56  fof(f934,plain,(
% 0.22/0.56    ( ! [X3] : (r1_tmap_1(sK3,sK1,k3_tmap_1(X3,sK1,sK2,sK3,sK4),sK5) | ~m1_pre_topc(sK2,X3) | ~v1_tsep_1(sK3,X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | v2_struct_0(X3)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f933,f315])).
% 0.22/0.56  fof(f933,plain,(
% 0.22/0.56    ( ! [X3] : (~l1_pre_topc(X3) | ~m1_pre_topc(sK2,X3) | ~v1_tsep_1(sK3,X3) | ~m1_pre_topc(sK3,sK2) | ~v2_pre_topc(X3) | r1_tmap_1(sK3,sK1,k3_tmap_1(X3,sK1,sK2,sK3,sK4),sK5) | v2_struct_0(X3)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f932,f47])).
% 0.22/0.56  fof(f47,plain,(
% 0.22/0.56    ~v2_struct_0(sK3)),
% 0.22/0.56    inference(cnf_transformation,[],[f18])).
% 0.22/0.56  fof(f932,plain,(
% 0.22/0.56    ( ! [X3] : (~l1_pre_topc(X3) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,X3) | ~v1_tsep_1(sK3,X3) | ~m1_pre_topc(sK3,sK2) | ~v2_pre_topc(X3) | r1_tmap_1(sK3,sK1,k3_tmap_1(X3,sK1,sK2,sK3,sK4),sK5) | v2_struct_0(X3)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f923,f107])).
% 0.22/0.56  fof(f107,plain,(
% 0.22/0.56    m1_subset_1(sK5,k2_struct_0(sK2))),
% 0.22/0.56    inference(backward_demodulation,[],[f83,f103])).
% 0.22/0.56  fof(f83,plain,(
% 0.22/0.56    m1_subset_1(sK5,u1_struct_0(sK2))),
% 0.22/0.56    inference(forward_demodulation,[],[f38,f39])).
% 0.22/0.56  fof(f39,plain,(
% 0.22/0.56    sK5 = sK6),
% 0.22/0.56    inference(cnf_transformation,[],[f18])).
% 0.22/0.56  fof(f38,plain,(
% 0.22/0.56    m1_subset_1(sK6,u1_struct_0(sK2))),
% 0.22/0.56    inference(cnf_transformation,[],[f18])).
% 0.22/0.56  fof(f923,plain,(
% 0.22/0.56    ( ! [X3] : (~m1_subset_1(sK5,k2_struct_0(sK2)) | ~l1_pre_topc(X3) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,X3) | ~v1_tsep_1(sK3,X3) | ~m1_pre_topc(sK3,sK2) | ~v2_pre_topc(X3) | r1_tmap_1(sK3,sK1,k3_tmap_1(X3,sK1,sK2,sK3,sK4),sK5) | v2_struct_0(X3)) )),
% 0.22/0.56    inference(superposition,[],[f914,f381])).
% 0.22/0.56  fof(f914,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~m1_subset_1(sK5,u1_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(sK2,X0) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,sK2) | ~v2_pre_topc(X0) | r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK2,X1,sK4),sK5) | v2_struct_0(X0)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f913,f107])).
% 0.22/0.56  fof(f913,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(sK2,X0) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,sK2) | ~m1_subset_1(sK5,k2_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(X1)) | r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK2,X1,sK4),sK5) | v2_struct_0(X0)) )),
% 0.22/0.56    inference(resolution,[],[f912,f839])).
% 0.22/0.56  fof(f839,plain,(
% 0.22/0.56    ( ! [X6,X8,X7] : (~r1_tmap_1(sK2,sK1,sK4,X8) | ~v2_pre_topc(X6) | ~l1_pre_topc(X6) | v2_struct_0(X7) | ~m1_pre_topc(sK2,X6) | ~v1_tsep_1(X7,X6) | ~m1_pre_topc(X7,sK2) | ~m1_subset_1(X8,k2_struct_0(sK2)) | ~m1_subset_1(X8,u1_struct_0(X7)) | r1_tmap_1(X7,sK1,k3_tmap_1(X6,sK1,sK2,X7,sK4),X8) | v2_struct_0(X6)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f838,f383])).
% 0.22/0.56  fof(f838,plain,(
% 0.22/0.56    ( ! [X6,X8,X7] : (v2_struct_0(X6) | ~v2_pre_topc(X6) | ~l1_pre_topc(X6) | v2_struct_0(X7) | ~m1_pre_topc(sK2,X6) | ~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1)) | ~v1_tsep_1(X7,X6) | ~m1_pre_topc(X7,sK2) | ~m1_subset_1(X8,k2_struct_0(sK2)) | ~m1_subset_1(X8,u1_struct_0(X7)) | r1_tmap_1(X7,sK1,k3_tmap_1(X6,sK1,sK2,X7,sK4),X8) | ~r1_tmap_1(sK2,sK1,sK4,X8)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f837,f49])).
% 0.22/0.56  fof(f837,plain,(
% 0.22/0.56    ( ! [X6,X8,X7] : (v2_struct_0(X6) | ~v2_pre_topc(X6) | ~l1_pre_topc(X6) | v2_struct_0(X7) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,X6) | ~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1)) | ~v1_tsep_1(X7,X6) | ~m1_pre_topc(X7,sK2) | ~m1_subset_1(X8,k2_struct_0(sK2)) | ~m1_subset_1(X8,u1_struct_0(X7)) | r1_tmap_1(X7,sK1,k3_tmap_1(X6,sK1,sK2,X7,sK4),X8) | ~r1_tmap_1(sK2,sK1,sK4,X8)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f833,f382])).
% 0.22/0.56  fof(f833,plain,(
% 0.22/0.56    ( ! [X6,X8,X7] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1)))) | v2_struct_0(X6) | ~v2_pre_topc(X6) | ~l1_pre_topc(X6) | v2_struct_0(X7) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,X6) | ~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1)) | ~v1_tsep_1(X7,X6) | ~m1_pre_topc(X7,sK2) | ~m1_subset_1(X8,k2_struct_0(sK2)) | ~m1_subset_1(X8,u1_struct_0(X7)) | r1_tmap_1(X7,sK1,k3_tmap_1(X6,sK1,sK2,X7,sK4),X8) | ~r1_tmap_1(sK2,sK1,sK4,X8)) )),
% 0.22/0.56    inference(superposition,[],[f816,f103])).
% 0.22/0.56  fof(f816,plain,(
% 0.22/0.56    ( ! [X6,X4,X7,X5] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),k2_struct_0(sK1)))) | v2_struct_0(X5) | ~v2_pre_topc(X5) | ~l1_pre_topc(X5) | v2_struct_0(X6) | v2_struct_0(X4) | ~m1_pre_topc(X4,X5) | ~v1_funct_2(sK4,u1_struct_0(X4),k2_struct_0(sK1)) | ~v1_tsep_1(X6,X5) | ~m1_pre_topc(X6,X4) | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X7,u1_struct_0(X6)) | r1_tmap_1(X6,sK1,k3_tmap_1(X5,sK1,X4,X6,sK4),X7) | ~r1_tmap_1(X4,sK1,sK4,X7)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f815,f52])).
% 0.22/0.56  fof(f815,plain,(
% 0.22/0.56    ( ! [X6,X4,X7,X5] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),k2_struct_0(sK1)))) | v2_struct_0(X5) | ~v2_pre_topc(X5) | ~l1_pre_topc(X5) | v2_struct_0(X6) | v2_struct_0(X4) | ~m1_pre_topc(X4,X5) | ~v1_funct_2(sK4,u1_struct_0(X4),k2_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~v1_tsep_1(X6,X5) | ~m1_pre_topc(X6,X4) | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X7,u1_struct_0(X6)) | r1_tmap_1(X6,sK1,k3_tmap_1(X5,sK1,X4,X6,sK4),X7) | ~r1_tmap_1(X4,sK1,sK4,X7)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f814,f51])).
% 0.22/0.56  fof(f814,plain,(
% 0.22/0.56    ( ! [X6,X4,X7,X5] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),k2_struct_0(sK1)))) | v2_struct_0(X5) | ~v2_pre_topc(X5) | ~l1_pre_topc(X5) | v2_struct_0(X6) | v2_struct_0(X4) | ~m1_pre_topc(X4,X5) | v2_struct_0(sK1) | ~v1_funct_2(sK4,u1_struct_0(X4),k2_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~v1_tsep_1(X6,X5) | ~m1_pre_topc(X6,X4) | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X7,u1_struct_0(X6)) | r1_tmap_1(X6,sK1,k3_tmap_1(X5,sK1,X4,X6,sK4),X7) | ~r1_tmap_1(X4,sK1,sK4,X7)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f804,f53])).
% 0.22/0.56  fof(f804,plain,(
% 0.22/0.56    ( ! [X6,X4,X7,X5] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),k2_struct_0(sK1)))) | ~l1_pre_topc(sK1) | v2_struct_0(X5) | ~v2_pre_topc(X5) | ~l1_pre_topc(X5) | v2_struct_0(X6) | v2_struct_0(X4) | ~m1_pre_topc(X4,X5) | v2_struct_0(sK1) | ~v1_funct_2(sK4,u1_struct_0(X4),k2_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~v1_tsep_1(X6,X5) | ~m1_pre_topc(X6,X4) | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X7,u1_struct_0(X6)) | r1_tmap_1(X6,sK1,k3_tmap_1(X5,sK1,X4,X6,sK4),X7) | ~r1_tmap_1(X4,sK1,sK4,X7)) )),
% 0.22/0.56    inference(superposition,[],[f723,f102])).
% 0.22/0.56  fof(f723,plain,(
% 0.22/0.56    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~v1_tsep_1(X2,X1) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X2)) | r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK4),X4) | ~r1_tmap_1(X3,X0,sK4,X4)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f722,f70])).
% 0.22/0.56  fof(f722,plain,(
% 0.22/0.56    ( ! [X4,X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v1_tsep_1(X2,X1) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X2)) | r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK4),X4) | ~r1_tmap_1(X3,X0,sK4,X4)) )),
% 0.22/0.56    inference(resolution,[],[f76,f43])).
% 0.22/0.56  fof(f76,plain,(
% 0.22/0.56    ( ! [X6,X4,X2,X0,X3,X1] : (~v1_funct_1(X4) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | v2_struct_0(X0) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v1_tsep_1(X2,X1) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X6)) )),
% 0.22/0.56    inference(equality_resolution,[],[f67])).
% 0.22/0.56  fof(f67,plain,(
% 0.22/0.56    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v1_tsep_1(X2,X1) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | X5 != X6 | r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f29])).
% 0.22/0.56  fof(f29,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X0,X4,X5) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_pre_topc(X2,X1) | ~v1_tsep_1(X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.56    inference(flattening,[],[f28])).
% 0.22/0.56  fof(f28,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (((r1_tmap_1(X3,X0,X4,X5) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)) | X5 != X6) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | (~m1_pre_topc(X2,X3) | ~m1_pre_topc(X2,X1) | ~v1_tsep_1(X2,X1))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X1) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f14])).
% 0.22/0.56  fof(f14,axiom,(
% 0.22/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X0,X4,X5) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)))))))))))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_tmap_1)).
% 0.22/0.56  fof(f912,plain,(
% 0.22/0.56    r1_tmap_1(sK2,sK1,sK4,sK5)),
% 0.22/0.56    inference(subsumption_resolution,[],[f911,f93])).
% 0.22/0.56  fof(f911,plain,(
% 0.22/0.56    ~l1_pre_topc(sK2) | r1_tmap_1(sK2,sK1,sK4,sK5)),
% 0.22/0.56    inference(subsumption_resolution,[],[f910,f125])).
% 0.22/0.56  fof(f910,plain,(
% 0.22/0.56    ~v2_pre_topc(sK2) | ~l1_pre_topc(sK2) | r1_tmap_1(sK2,sK1,sK4,sK5)),
% 0.22/0.56    inference(subsumption_resolution,[],[f909,f49])).
% 0.22/0.56  fof(f909,plain,(
% 0.22/0.56    v2_struct_0(sK2) | ~v2_pre_topc(sK2) | ~l1_pre_topc(sK2) | r1_tmap_1(sK2,sK1,sK4,sK5)),
% 0.22/0.56    inference(subsumption_resolution,[],[f908,f546])).
% 0.22/0.56  fof(f546,plain,(
% 0.22/0.56    v1_tsep_1(sK2,sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f545,f98])).
% 0.22/0.56  % (982)Refutation not found, incomplete strategy% (982)------------------------------
% 0.22/0.56  % (982)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (982)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (982)Memory used [KB]: 11001
% 0.22/0.56  % (982)Time elapsed: 0.121 s
% 0.22/0.56  % (982)------------------------------
% 0.22/0.56  % (982)------------------------------
% 0.22/0.58  fof(f545,plain,(
% 0.22/0.58    ~m1_pre_topc(sK2,sK2) | v1_tsep_1(sK2,sK2)),
% 0.22/0.58    inference(subsumption_resolution,[],[f543,f130])).
% 0.22/0.58  fof(f543,plain,(
% 0.22/0.58    ~v3_pre_topc(k2_struct_0(sK2),sK2) | ~m1_pre_topc(sK2,sK2) | v1_tsep_1(sK2,sK2)),
% 0.22/0.58    inference(superposition,[],[f525,f103])).
% 0.22/0.58  fof(f908,plain,(
% 0.22/0.58    ~v1_tsep_1(sK2,sK2) | v2_struct_0(sK2) | ~v2_pre_topc(sK2) | ~l1_pre_topc(sK2) | r1_tmap_1(sK2,sK1,sK4,sK5)),
% 0.22/0.58    inference(subsumption_resolution,[],[f907,f98])).
% 0.22/0.58  fof(f907,plain,(
% 0.22/0.58    ~m1_pre_topc(sK2,sK2) | ~v1_tsep_1(sK2,sK2) | v2_struct_0(sK2) | ~v2_pre_topc(sK2) | ~l1_pre_topc(sK2) | r1_tmap_1(sK2,sK1,sK4,sK5)),
% 0.22/0.58    inference(subsumption_resolution,[],[f901,f758])).
% 0.22/0.58  fof(f758,plain,(
% 0.22/0.58    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK2,sK2,sK4),sK5)),
% 0.22/0.58    inference(backward_demodulation,[],[f82,f757])).
% 0.22/0.58  fof(f757,plain,(
% 0.22/0.58    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k3_tmap_1(sK0,sK1,sK2,sK2,sK4)),
% 0.22/0.58    inference(forward_demodulation,[],[f756,f707])).
% 0.22/0.58  fof(f756,plain,(
% 0.22/0.58    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,k2_struct_0(sK2))),
% 0.22/0.58    inference(forward_demodulation,[],[f754,f103])).
% 0.22/0.58  fof(f754,plain,(
% 0.22/0.58    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(sK2))),
% 0.22/0.58    inference(resolution,[],[f743,f98])).
% 0.22/0.58  fof(f743,plain,(
% 0.22/0.58    ( ! [X0] : (~m1_pre_topc(X0,sK2) | k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK4)) )),
% 0.22/0.58    inference(resolution,[],[f735,f363])).
% 0.22/0.58  fof(f735,plain,(
% 0.22/0.58    ( ! [X3] : (~m1_pre_topc(X3,sK3) | k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3)) = k3_tmap_1(sK0,sK1,sK3,X3,sK4)) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f734,f55])).
% 0.22/0.58  fof(f734,plain,(
% 0.22/0.58    ( ! [X3] : (~v2_pre_topc(sK0) | ~m1_pre_topc(X3,sK3) | k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3)) = k3_tmap_1(sK0,sK1,sK3,X3,sK4)) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f733,f54])).
% 0.22/0.58  fof(f733,plain,(
% 0.22/0.58    ( ! [X3] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_pre_topc(X3,sK3) | k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3)) = k3_tmap_1(sK0,sK1,sK3,X3,sK4)) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f727,f56])).
% 0.22/0.58  fof(f727,plain,(
% 0.22/0.58    ( ! [X3] : (~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_pre_topc(X3,sK3) | k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3)) = k3_tmap_1(sK0,sK1,sK3,X3,sK4)) )),
% 0.22/0.58    inference(resolution,[],[f687,f48])).
% 0.22/0.58  fof(f687,plain,(
% 0.22/0.58    ( ! [X6,X7] : (~m1_pre_topc(sK3,X6) | ~l1_pre_topc(X6) | v2_struct_0(X6) | ~v2_pre_topc(X6) | ~m1_pre_topc(X7,sK3) | k3_tmap_1(X6,sK1,sK3,X7,sK4) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X7))) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f686,f383])).
% 0.22/0.58  fof(f686,plain,(
% 0.22/0.58    ( ! [X6,X7] : (~l1_pre_topc(X6) | ~m1_pre_topc(sK3,X6) | v2_struct_0(X6) | ~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1)) | ~v2_pre_topc(X6) | ~m1_pre_topc(X7,sK3) | k3_tmap_1(X6,sK1,sK3,X7,sK4) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X7))) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f683,f382])).
% 0.22/0.58  fof(f683,plain,(
% 0.22/0.58    ( ! [X6,X7] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1)))) | ~l1_pre_topc(X6) | ~m1_pre_topc(sK3,X6) | v2_struct_0(X6) | ~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1)) | ~v2_pre_topc(X6) | ~m1_pre_topc(X7,sK3) | k3_tmap_1(X6,sK1,sK3,X7,sK4) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X7))) )),
% 0.22/0.58    inference(superposition,[],[f669,f381])).
% 0.22/0.58  fof(f82,plain,(
% 0.22/0.58    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)),
% 0.22/0.58    inference(backward_demodulation,[],[f40,f39])).
% 0.22/0.58  fof(f40,plain,(
% 0.22/0.58    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 0.22/0.58    inference(cnf_transformation,[],[f18])).
% 0.22/0.58  fof(f901,plain,(
% 0.22/0.58    ~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK2,sK2,sK4),sK5) | ~m1_pre_topc(sK2,sK2) | ~v1_tsep_1(sK2,sK2) | v2_struct_0(sK2) | ~v2_pre_topc(sK2) | ~l1_pre_topc(sK2) | r1_tmap_1(sK2,sK1,sK4,sK5)),
% 0.22/0.58    inference(superposition,[],[f896,f713])).
% 0.22/0.58  fof(f713,plain,(
% 0.22/0.58    k3_tmap_1(sK0,sK1,sK2,sK2,sK4) = k3_tmap_1(sK2,sK1,sK2,sK2,sK4)),
% 0.22/0.58    inference(forward_demodulation,[],[f712,f707])).
% 0.22/0.58  fof(f712,plain,(
% 0.22/0.58    k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,k2_struct_0(sK2)) = k3_tmap_1(sK2,sK1,sK2,sK2,sK4)),
% 0.22/0.58    inference(forward_demodulation,[],[f710,f103])).
% 0.22/0.58  fof(f710,plain,(
% 0.22/0.58    k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(sK2,sK1,sK2,sK2,sK4)),
% 0.22/0.58    inference(resolution,[],[f700,f98])).
% 0.22/0.58  fof(f896,plain,(
% 0.22/0.58    ( ! [X2] : (~r1_tmap_1(sK2,sK1,k3_tmap_1(X2,sK1,sK2,sK2,sK4),sK5) | ~m1_pre_topc(sK2,X2) | ~v1_tsep_1(sK2,X2) | v2_struct_0(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | r1_tmap_1(sK2,sK1,sK4,sK5)) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f895,f98])).
% 0.22/0.58  fof(f895,plain,(
% 0.22/0.58    ( ! [X2] : (~l1_pre_topc(X2) | ~m1_pre_topc(sK2,X2) | ~v1_tsep_1(sK2,X2) | ~m1_pre_topc(sK2,sK2) | v2_struct_0(X2) | ~v2_pre_topc(X2) | ~r1_tmap_1(sK2,sK1,k3_tmap_1(X2,sK1,sK2,sK2,sK4),sK5) | r1_tmap_1(sK2,sK1,sK4,sK5)) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f894,f49])).
% 0.22/0.58  fof(f894,plain,(
% 0.22/0.58    ( ! [X2] : (~l1_pre_topc(X2) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,X2) | ~v1_tsep_1(sK2,X2) | ~m1_pre_topc(sK2,sK2) | v2_struct_0(X2) | ~v2_pre_topc(X2) | ~r1_tmap_1(sK2,sK1,k3_tmap_1(X2,sK1,sK2,sK2,sK4),sK5) | r1_tmap_1(sK2,sK1,sK4,sK5)) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f890,f107])).
% 0.22/0.58  fof(f890,plain,(
% 0.22/0.58    ( ! [X2] : (~m1_subset_1(sK5,k2_struct_0(sK2)) | ~l1_pre_topc(X2) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,X2) | ~v1_tsep_1(sK2,X2) | ~m1_pre_topc(sK2,sK2) | v2_struct_0(X2) | ~v2_pre_topc(X2) | ~r1_tmap_1(sK2,sK1,k3_tmap_1(X2,sK1,sK2,sK2,sK4),sK5) | r1_tmap_1(sK2,sK1,sK4,sK5)) )),
% 0.22/0.58    inference(superposition,[],[f887,f103])).
% 0.22/0.58  fof(f887,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~m1_subset_1(sK5,u1_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(sK2,X0) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,sK2) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK2,X1,sK4),sK5) | r1_tmap_1(sK2,sK1,sK4,sK5)) )),
% 0.22/0.58    inference(resolution,[],[f883,f107])).
% 0.22/0.58  fof(f883,plain,(
% 0.22/0.58    ( ! [X6,X8,X7] : (~m1_subset_1(X8,k2_struct_0(sK2)) | ~v2_pre_topc(X6) | ~l1_pre_topc(X6) | v2_struct_0(X7) | ~m1_pre_topc(sK2,X6) | ~v1_tsep_1(X7,X6) | ~m1_pre_topc(X7,sK2) | v2_struct_0(X6) | ~m1_subset_1(X8,u1_struct_0(X7)) | ~r1_tmap_1(X7,sK1,k3_tmap_1(X6,sK1,sK2,X7,sK4),X8) | r1_tmap_1(sK2,sK1,sK4,X8)) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f882,f383])).
% 0.22/0.58  fof(f882,plain,(
% 0.22/0.58    ( ! [X6,X8,X7] : (v2_struct_0(X6) | ~v2_pre_topc(X6) | ~l1_pre_topc(X6) | v2_struct_0(X7) | ~m1_pre_topc(sK2,X6) | ~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1)) | ~v1_tsep_1(X7,X6) | ~m1_pre_topc(X7,sK2) | ~m1_subset_1(X8,k2_struct_0(sK2)) | ~m1_subset_1(X8,u1_struct_0(X7)) | ~r1_tmap_1(X7,sK1,k3_tmap_1(X6,sK1,sK2,X7,sK4),X8) | r1_tmap_1(sK2,sK1,sK4,X8)) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f881,f49])).
% 0.22/0.58  fof(f881,plain,(
% 0.22/0.58    ( ! [X6,X8,X7] : (v2_struct_0(X6) | ~v2_pre_topc(X6) | ~l1_pre_topc(X6) | v2_struct_0(X7) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,X6) | ~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1)) | ~v1_tsep_1(X7,X6) | ~m1_pre_topc(X7,sK2) | ~m1_subset_1(X8,k2_struct_0(sK2)) | ~m1_subset_1(X8,u1_struct_0(X7)) | ~r1_tmap_1(X7,sK1,k3_tmap_1(X6,sK1,sK2,X7,sK4),X8) | r1_tmap_1(sK2,sK1,sK4,X8)) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f877,f382])).
% 0.22/0.58  fof(f877,plain,(
% 0.22/0.58    ( ! [X6,X8,X7] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1)))) | v2_struct_0(X6) | ~v2_pre_topc(X6) | ~l1_pre_topc(X6) | v2_struct_0(X7) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,X6) | ~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1)) | ~v1_tsep_1(X7,X6) | ~m1_pre_topc(X7,sK2) | ~m1_subset_1(X8,k2_struct_0(sK2)) | ~m1_subset_1(X8,u1_struct_0(X7)) | ~r1_tmap_1(X7,sK1,k3_tmap_1(X6,sK1,sK2,X7,sK4),X8) | r1_tmap_1(sK2,sK1,sK4,X8)) )),
% 0.22/0.58    inference(superposition,[],[f860,f103])).
% 0.22/0.58  fof(f860,plain,(
% 0.22/0.58    ( ! [X6,X4,X7,X5] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),k2_struct_0(sK1)))) | v2_struct_0(X5) | ~v2_pre_topc(X5) | ~l1_pre_topc(X5) | v2_struct_0(X6) | v2_struct_0(X4) | ~m1_pre_topc(X4,X5) | ~v1_funct_2(sK4,u1_struct_0(X4),k2_struct_0(sK1)) | ~v1_tsep_1(X6,X5) | ~m1_pre_topc(X6,X4) | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X7,u1_struct_0(X6)) | ~r1_tmap_1(X6,sK1,k3_tmap_1(X5,sK1,X4,X6,sK4),X7) | r1_tmap_1(X4,sK1,sK4,X7)) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f859,f52])).
% 0.22/0.58  fof(f859,plain,(
% 0.22/0.58    ( ! [X6,X4,X7,X5] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),k2_struct_0(sK1)))) | v2_struct_0(X5) | ~v2_pre_topc(X5) | ~l1_pre_topc(X5) | v2_struct_0(X6) | v2_struct_0(X4) | ~m1_pre_topc(X4,X5) | ~v1_funct_2(sK4,u1_struct_0(X4),k2_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~v1_tsep_1(X6,X5) | ~m1_pre_topc(X6,X4) | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X7,u1_struct_0(X6)) | ~r1_tmap_1(X6,sK1,k3_tmap_1(X5,sK1,X4,X6,sK4),X7) | r1_tmap_1(X4,sK1,sK4,X7)) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f858,f51])).
% 0.22/0.58  fof(f858,plain,(
% 0.22/0.58    ( ! [X6,X4,X7,X5] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),k2_struct_0(sK1)))) | v2_struct_0(X5) | ~v2_pre_topc(X5) | ~l1_pre_topc(X5) | v2_struct_0(X6) | v2_struct_0(X4) | ~m1_pre_topc(X4,X5) | v2_struct_0(sK1) | ~v1_funct_2(sK4,u1_struct_0(X4),k2_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~v1_tsep_1(X6,X5) | ~m1_pre_topc(X6,X4) | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X7,u1_struct_0(X6)) | ~r1_tmap_1(X6,sK1,k3_tmap_1(X5,sK1,X4,X6,sK4),X7) | r1_tmap_1(X4,sK1,sK4,X7)) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f848,f53])).
% 0.22/0.58  fof(f848,plain,(
% 0.22/0.58    ( ! [X6,X4,X7,X5] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),k2_struct_0(sK1)))) | ~l1_pre_topc(sK1) | v2_struct_0(X5) | ~v2_pre_topc(X5) | ~l1_pre_topc(X5) | v2_struct_0(X6) | v2_struct_0(X4) | ~m1_pre_topc(X4,X5) | v2_struct_0(sK1) | ~v1_funct_2(sK4,u1_struct_0(X4),k2_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~v1_tsep_1(X6,X5) | ~m1_pre_topc(X6,X4) | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X7,u1_struct_0(X6)) | ~r1_tmap_1(X6,sK1,k3_tmap_1(X5,sK1,X4,X6,sK4),X7) | r1_tmap_1(X4,sK1,sK4,X7)) )),
% 0.22/0.58    inference(superposition,[],[f782,f102])).
% 0.22/0.58  fof(f782,plain,(
% 0.22/0.58    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~v1_tsep_1(X2,X1) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X2)) | ~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK4),X4) | r1_tmap_1(X3,X0,sK4,X4)) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f781,f70])).
% 0.22/0.58  fof(f781,plain,(
% 0.22/0.58    ( ! [X4,X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v1_tsep_1(X2,X1) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X2)) | ~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK4),X4) | r1_tmap_1(X3,X0,sK4,X4)) )),
% 0.22/0.58    inference(resolution,[],[f77,f43])).
% 0.22/0.58  fof(f77,plain,(
% 0.22/0.58    ( ! [X6,X4,X2,X0,X3,X1] : (~v1_funct_1(X4) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | v2_struct_0(X0) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v1_tsep_1(X2,X1) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X6)) )),
% 0.22/0.58    inference(equality_resolution,[],[f66])).
% 0.22/0.58  fof(f66,plain,(
% 0.22/0.58    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v1_tsep_1(X2,X1) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | X5 != X6 | ~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f29])).
% 0.22/0.58  fof(f974,plain,(
% 0.22/0.58    ~r1_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK2,sK2,sK4),sK5) | ~m1_pre_topc(sK3,sK2) | ~v1_tsep_1(sK3,sK2) | v2_struct_0(sK2) | ~v2_pre_topc(sK2) | ~l1_pre_topc(sK2)),
% 0.22/0.58    inference(superposition,[],[f962,f749])).
% 0.22/0.58  fof(f749,plain,(
% 0.22/0.58    k3_tmap_1(sK0,sK1,sK2,sK2,sK4) = k3_tmap_1(sK2,sK1,sK3,sK3,sK4)),
% 0.22/0.58    inference(forward_demodulation,[],[f748,f707])).
% 0.22/0.58  fof(f748,plain,(
% 0.22/0.58    k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,k2_struct_0(sK2)) = k3_tmap_1(sK2,sK1,sK3,sK3,sK4)),
% 0.22/0.58    inference(forward_demodulation,[],[f746,f381])).
% 0.22/0.58  fof(f746,plain,(
% 0.22/0.58    k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(sK2,sK1,sK3,sK3,sK4)),
% 0.22/0.58    inference(resolution,[],[f738,f96])).
% 0.22/0.58  fof(f738,plain,(
% 0.22/0.58    ( ! [X4] : (~m1_pre_topc(X4,sK3) | k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X4)) = k3_tmap_1(sK2,sK1,sK3,X4,sK4)) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f737,f125])).
% 0.22/0.58  fof(f737,plain,(
% 0.22/0.58    ( ! [X4] : (~v2_pre_topc(sK2) | ~m1_pre_topc(X4,sK3) | k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X4)) = k3_tmap_1(sK2,sK1,sK3,X4,sK4)) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f736,f49])).
% 0.22/0.58  fof(f736,plain,(
% 0.22/0.58    ( ! [X4] : (v2_struct_0(sK2) | ~v2_pre_topc(sK2) | ~m1_pre_topc(X4,sK3) | k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X4)) = k3_tmap_1(sK2,sK1,sK3,X4,sK4)) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f728,f93])).
% 0.22/0.58  fof(f728,plain,(
% 0.22/0.58    ( ! [X4] : (~l1_pre_topc(sK2) | v2_struct_0(sK2) | ~v2_pre_topc(sK2) | ~m1_pre_topc(X4,sK3) | k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X4)) = k3_tmap_1(sK2,sK1,sK3,X4,sK4)) )),
% 0.22/0.58    inference(resolution,[],[f687,f315])).
% 0.22/0.58  fof(f962,plain,(
% 0.22/0.58    ( ! [X3] : (~r1_tmap_1(sK3,sK1,k3_tmap_1(X3,sK1,sK3,sK3,sK4),sK5) | ~m1_pre_topc(sK3,X3) | ~v1_tsep_1(sK3,X3) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3)) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f961,f96])).
% 0.22/0.58  fof(f961,plain,(
% 0.22/0.58    ( ! [X3] : (~l1_pre_topc(X3) | ~m1_pre_topc(sK3,X3) | ~v1_tsep_1(sK3,X3) | ~m1_pre_topc(sK3,sK3) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~r1_tmap_1(sK3,sK1,k3_tmap_1(X3,sK1,sK3,sK3,sK4),sK5)) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f960,f47])).
% 0.22/0.58  fof(f960,plain,(
% 0.22/0.58    ( ! [X3] : (~l1_pre_topc(X3) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,X3) | ~v1_tsep_1(sK3,X3) | ~m1_pre_topc(sK3,sK3) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~r1_tmap_1(sK3,sK1,k3_tmap_1(X3,sK1,sK3,sK3,sK4),sK5)) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f955,f107])).
% 0.22/0.58  fof(f955,plain,(
% 0.22/0.58    ( ! [X3] : (~m1_subset_1(sK5,k2_struct_0(sK2)) | ~l1_pre_topc(X3) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,X3) | ~v1_tsep_1(sK3,X3) | ~m1_pre_topc(sK3,sK3) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~r1_tmap_1(sK3,sK1,k3_tmap_1(X3,sK1,sK3,sK3,sK4),sK5)) )),
% 0.22/0.58    inference(superposition,[],[f951,f381])).
% 0.22/0.58  fof(f951,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~m1_subset_1(sK5,u1_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(sK3,X0) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,sK3) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5)) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f950,f41])).
% 0.22/0.58  fof(f41,plain,(
% 0.22/0.58    ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.22/0.58    inference(cnf_transformation,[],[f18])).
% 0.22/0.58  fof(f950,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(sK3,X0) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,sK3) | v2_struct_0(X0) | ~m1_subset_1(sK5,u1_struct_0(X1)) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5) | r1_tmap_1(sK3,sK1,sK4,sK5)) )),
% 0.22/0.58    inference(resolution,[],[f886,f107])).
% 0.22/0.58  fof(f886,plain,(
% 0.22/0.58    ( ! [X10,X11,X9] : (~m1_subset_1(X11,k2_struct_0(sK2)) | ~v2_pre_topc(X9) | ~l1_pre_topc(X9) | v2_struct_0(X10) | ~m1_pre_topc(sK3,X9) | ~v1_tsep_1(X10,X9) | ~m1_pre_topc(X10,sK3) | v2_struct_0(X9) | ~m1_subset_1(X11,u1_struct_0(X10)) | ~r1_tmap_1(X10,sK1,k3_tmap_1(X9,sK1,sK3,X10,sK4),X11) | r1_tmap_1(sK3,sK1,sK4,X11)) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f885,f383])).
% 0.22/0.58  fof(f885,plain,(
% 0.22/0.58    ( ! [X10,X11,X9] : (v2_struct_0(X9) | ~v2_pre_topc(X9) | ~l1_pre_topc(X9) | v2_struct_0(X10) | ~m1_pre_topc(sK3,X9) | ~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1)) | ~v1_tsep_1(X10,X9) | ~m1_pre_topc(X10,sK3) | ~m1_subset_1(X11,k2_struct_0(sK2)) | ~m1_subset_1(X11,u1_struct_0(X10)) | ~r1_tmap_1(X10,sK1,k3_tmap_1(X9,sK1,sK3,X10,sK4),X11) | r1_tmap_1(sK3,sK1,sK4,X11)) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f884,f47])).
% 0.22/0.58  fof(f884,plain,(
% 0.22/0.58    ( ! [X10,X11,X9] : (v2_struct_0(X9) | ~v2_pre_topc(X9) | ~l1_pre_topc(X9) | v2_struct_0(X10) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,X9) | ~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1)) | ~v1_tsep_1(X10,X9) | ~m1_pre_topc(X10,sK3) | ~m1_subset_1(X11,k2_struct_0(sK2)) | ~m1_subset_1(X11,u1_struct_0(X10)) | ~r1_tmap_1(X10,sK1,k3_tmap_1(X9,sK1,sK3,X10,sK4),X11) | r1_tmap_1(sK3,sK1,sK4,X11)) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f878,f382])).
% 0.22/0.58  fof(f878,plain,(
% 0.22/0.58    ( ! [X10,X11,X9] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1)))) | v2_struct_0(X9) | ~v2_pre_topc(X9) | ~l1_pre_topc(X9) | v2_struct_0(X10) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,X9) | ~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1)) | ~v1_tsep_1(X10,X9) | ~m1_pre_topc(X10,sK3) | ~m1_subset_1(X11,k2_struct_0(sK2)) | ~m1_subset_1(X11,u1_struct_0(X10)) | ~r1_tmap_1(X10,sK1,k3_tmap_1(X9,sK1,sK3,X10,sK4),X11) | r1_tmap_1(sK3,sK1,sK4,X11)) )),
% 0.22/0.58    inference(superposition,[],[f860,f381])).
% 0.22/0.58  % SZS output end Proof for theBenchmark
% 0.22/0.58  % (1003)------------------------------
% 0.22/0.58  % (1003)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (1003)Termination reason: Refutation
% 0.22/0.58  
% 0.22/0.58  % (1003)Memory used [KB]: 2302
% 0.22/0.58  % (1003)Time elapsed: 0.137 s
% 0.22/0.58  % (1003)------------------------------
% 0.22/0.58  % (1003)------------------------------
% 1.70/0.58  % (979)Success in time 0.218 s
%------------------------------------------------------------------------------
