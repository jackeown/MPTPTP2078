%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:04 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 858 expanded)
%              Number of leaves         :   15 ( 159 expanded)
%              Depth                    :   27
%              Number of atoms          :  717 (8936 expanded)
%              Number of equality atoms :   68 ( 934 expanded)
%              Maximal formula depth    :   28 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f639,plain,(
    $false ),
    inference(subsumption_resolution,[],[f638,f419])).

fof(f419,plain,(
    ~ v1_tsep_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f172,f418])).

fof(f418,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f417,f52])).

fof(f52,plain,(
    sK3 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

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
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
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

fof(f417,plain,
    ( sK3 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f411,f99])).

fof(f99,plain,(
    l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f97,f62])).

fof(f62,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f97,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2) ),
    inference(resolution,[],[f68,f56])).

fof(f56,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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

fof(f411,plain,
    ( ~ l1_pre_topc(sK2)
    | sK3 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | m1_pre_topc(sK2,sK3) ),
    inference(duplicate_literal_removal,[],[f408])).

fof(f408,plain,
    ( ~ l1_pre_topc(sK2)
    | sK3 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | sK3 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | m1_pre_topc(sK2,sK3) ),
    inference(resolution,[],[f328,f175])).

fof(f175,plain,(
    m1_pre_topc(sK2,sK2) ),
    inference(resolution,[],[f99,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f328,plain,(
    ! [X4,X5] :
      ( ~ m1_pre_topc(X5,X4)
      | ~ l1_pre_topc(X4)
      | sK3 != g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4))
      | sK3 != g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5))
      | m1_pre_topc(sK2,sK3) ) ),
    inference(forward_demodulation,[],[f326,f52])).

fof(f326,plain,(
    ! [X4,X5] :
      ( ~ l1_pre_topc(X4)
      | sK3 != g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4))
      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5))
      | ~ m1_pre_topc(X5,X4)
      | m1_pre_topc(sK2,sK3) ) ),
    inference(resolution,[],[f247,f99])).

fof(f247,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X2)
      | ~ l1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK3
      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
      | ~ m1_pre_topc(X1,X0)
      | m1_pre_topc(X2,sK3) ) ),
    inference(backward_demodulation,[],[f144,f244])).

fof(f244,plain,(
    sK3 = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) ),
    inference(subsumption_resolution,[],[f243,f98])).

fof(f98,plain,(
    l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f96,f62])).

fof(f96,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK3) ),
    inference(resolution,[],[f68,f54])).

fof(f54,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f19])).

% (8196)Refutation not found, incomplete strategy% (8196)------------------------------
% (8196)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (8196)Termination reason: Refutation not found, incomplete strategy

% (8196)Memory used [KB]: 10618
% (8196)Time elapsed: 0.099 s
% (8196)------------------------------
% (8196)------------------------------
fof(f243,plain,
    ( ~ l1_pre_topc(sK3)
    | sK3 = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) ),
    inference(resolution,[],[f180,f66])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f180,plain,(
    v1_pre_topc(sK3) ),
    inference(forward_demodulation,[],[f179,f52])).

fof(f179,plain,(
    v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(subsumption_resolution,[],[f174,f55])).

fof(f55,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f174,plain,
    ( v2_struct_0(sK2)
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(resolution,[],[f99,f75])).

fof(f75,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & ~ v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & ~ v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & ~ v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_pre_topc)).

fof(f144,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X2)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
      | ~ m1_pre_topc(X1,X0)
      | m1_pre_topc(X2,sK3) ) ),
    inference(subsumption_resolution,[],[f140,f68])).

fof(f140,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X2)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
      | ~ m1_pre_topc(X1,X0)
      | m1_pre_topc(X2,sK3) ) ),
    inference(resolution,[],[f98,f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X2)
      | ~ l1_pre_topc(X3)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
      | ~ m1_pre_topc(X2,X0)
      | m1_pre_topc(X3,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( m1_pre_topc(X3,X1)
                  | ~ m1_pre_topc(X2,X0)
                  | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                  | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  | ~ l1_pre_topc(X3) )
              | ~ l1_pre_topc(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( m1_pre_topc(X3,X1)
                  | ~ m1_pre_topc(X2,X0)
                  | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                  | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  | ~ l1_pre_topc(X3) )
              | ~ l1_pre_topc(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( l1_pre_topc(X2)
             => ! [X3] :
                  ( l1_pre_topc(X3)
                 => ( ( m1_pre_topc(X2,X0)
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                      & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                   => m1_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_pre_topc)).

fof(f172,plain,
    ( ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f171,f47])).

fof(f47,plain,(
    ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f19])).

fof(f171,plain,
    ( ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(subsumption_resolution,[],[f170,f60])).

fof(f60,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f170,plain,
    ( ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | v2_struct_0(sK0)
    | r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(subsumption_resolution,[],[f169,f87])).

fof(f87,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f44,f45])).

fof(f45,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f19])).

fof(f44,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f169,plain,
    ( ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(subsumption_resolution,[],[f168,f48])).

fof(f48,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f19])).

fof(f168,plain,
    ( ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(subsumption_resolution,[],[f167,f51])).

fof(f51,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f19])).

fof(f167,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(subsumption_resolution,[],[f166,f50])).

fof(f50,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f166,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(subsumption_resolution,[],[f165,f49])).

fof(f49,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f19])).

fof(f165,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(subsumption_resolution,[],[f164,f54])).

fof(f164,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(subsumption_resolution,[],[f163,f53])).

fof(f53,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f163,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(subsumption_resolution,[],[f162,f56])).

fof(f162,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(subsumption_resolution,[],[f161,f55])).

fof(f161,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(subsumption_resolution,[],[f160,f59])).

fof(f59,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f160,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(subsumption_resolution,[],[f159,f58])).

fof(f58,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f159,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(subsumption_resolution,[],[f158,f57])).

fof(f57,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f158,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(subsumption_resolution,[],[f157,f62])).

fof(f157,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(subsumption_resolution,[],[f156,f61])).

fof(f61,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f156,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(resolution,[],[f83,f86])).

fof(f86,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(backward_demodulation,[],[f46,f45])).

fof(f46,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f19])).

fof(f83,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_tsep_1(X2,X3)
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | v2_struct_0(X0)
      | r1_tmap_1(X3,X1,X4,X6) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_tsep_1(X2,X3)
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | X5 != X6
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
      | r1_tmap_1(X3,X1,X4,X5) ) ),
    inference(cnf_transformation,[],[f33])).

% (8175)Refutation not found, incomplete strategy% (8175)------------------------------
% (8175)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X3,X1,X4,X5)
                              <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ v1_tsep_1(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X3,X1,X4,X5)
                              <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ v1_tsep_1(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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
                     => ( ( m1_pre_topc(X2,X3)
                          & v1_tsep_1(X2,X3) )
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( X5 = X6
                                 => ( r1_tmap_1(X3,X1,X4,X5)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tmap_1)).

fof(f638,plain,(
    v1_tsep_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f637,f108])).

fof(f108,plain,(
    v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f107,f61])).

fof(f107,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f105,f62])).

fof(f105,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK3) ),
    inference(resolution,[],[f77,f54])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
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

fof(f637,plain,
    ( ~ v2_pre_topc(sK3)
    | v1_tsep_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f636,f418])).

fof(f636,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ v2_pre_topc(sK3)
    | v1_tsep_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f635,f98])).

fof(f635,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ v2_pre_topc(sK3)
    | v1_tsep_1(sK2,sK3) ),
    inference(resolution,[],[f619,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(u1_struct_0(X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f84,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | ~ v3_pre_topc(X2,X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f619,plain,(
    v3_pre_topc(u1_struct_0(sK2),sK3) ),
    inference(subsumption_resolution,[],[f618,f222])).

fof(f222,plain,(
    v3_pre_topc(u1_struct_0(sK2),sK2) ),
    inference(backward_demodulation,[],[f184,f221])).

fof(f221,plain,(
    u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(resolution,[],[f176,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f176,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f99,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f184,plain,(
    v3_pre_topc(k2_struct_0(sK2),sK2) ),
    inference(subsumption_resolution,[],[f183,f99])).

fof(f183,plain,
    ( ~ l1_pre_topc(sK2)
    | v3_pre_topc(k2_struct_0(sK2),sK2) ),
    inference(resolution,[],[f110,f76])).

fof(f76,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v3_pre_topc(k2_struct_0(X0),X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

fof(f110,plain,(
    v2_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f109,f61])).

fof(f109,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f106,f62])).

% (8175)Termination reason: Refutation not found, incomplete strategy

% (8175)Memory used [KB]: 6780
% (8177)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
fof(f106,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK2) ),
    inference(resolution,[],[f77,f56])).

fof(f618,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK2),sK2)
    | v3_pre_topc(u1_struct_0(sK2),sK3) ),
    inference(resolution,[],[f518,f572])).

fof(f572,plain,(
    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subsumption_resolution,[],[f556,f98])).

fof(f556,plain,
    ( ~ l1_pre_topc(sK3)
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(resolution,[],[f418,f69])).

fof(f518,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ v3_pre_topc(X6,sK2)
      | v3_pre_topc(X6,sK3) ) ),
    inference(subsumption_resolution,[],[f499,f99])).

fof(f499,plain,(
    ! [X6] :
      ( ~ l1_pre_topc(sK2)
      | ~ v3_pre_topc(X6,sK2)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK3)))
      | v3_pre_topc(X6,sK3) ) ),
    inference(resolution,[],[f403,f88])).

fof(f88,plain,(
    ! [X2,X0,X3] :
      ( ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | v3_pre_topc(X3,X2) ) ),
    inference(subsumption_resolution,[],[f81,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

fof(f81,plain,(
    ! [X2,X0,X3] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X2,X0)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | v3_pre_topc(X3,X2) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X2,X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | X1 != X3
      | v3_pre_topc(X3,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v3_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v3_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v3_pre_topc(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X1 = X3
                     => v3_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tops_2)).

fof(f403,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(subsumption_resolution,[],[f402,f52])).

fof(f402,plain,
    ( sK3 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | m1_pre_topc(sK3,sK2) ),
    inference(subsumption_resolution,[],[f396,f99])).

fof(f396,plain,
    ( ~ l1_pre_topc(sK2)
    | sK3 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | m1_pre_topc(sK3,sK2) ),
    inference(duplicate_literal_removal,[],[f393])).

fof(f393,plain,
    ( ~ l1_pre_topc(sK2)
    | sK3 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | sK3 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | m1_pre_topc(sK3,sK2) ),
    inference(resolution,[],[f322,f175])).

fof(f322,plain,(
    ! [X6,X7] :
      ( ~ m1_pre_topc(X7,X6)
      | ~ l1_pre_topc(X6)
      | sK3 != g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6))
      | sK3 != g1_pre_topc(u1_struct_0(X7),u1_pre_topc(X7))
      | m1_pre_topc(sK3,sK2) ) ),
    inference(forward_demodulation,[],[f321,f244])).

fof(f321,plain,(
    ! [X6,X7] :
      ( ~ l1_pre_topc(X6)
      | sK3 != g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6))
      | g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != g1_pre_topc(u1_struct_0(X7),u1_pre_topc(X7))
      | ~ m1_pre_topc(X7,X6)
      | m1_pre_topc(sK3,sK2) ) ),
    inference(resolution,[],[f178,f98])).

fof(f178,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X2)
      | ~ l1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK3
      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
      | ~ m1_pre_topc(X1,X0)
      | m1_pre_topc(X2,sK2) ) ),
    inference(forward_demodulation,[],[f177,f52])).

fof(f177,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X2)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
      | ~ m1_pre_topc(X1,X0)
      | m1_pre_topc(X2,sK2) ) ),
    inference(subsumption_resolution,[],[f173,f68])).

fof(f173,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X2)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
      | ~ m1_pre_topc(X1,X0)
      | m1_pre_topc(X2,sK2) ) ),
    inference(resolution,[],[f99,f67])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:02:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (8176)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.47  % (8175)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.48  % (8192)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.48  % (8178)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.48  % (8188)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.49  % (8193)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.49  % (8196)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.49  % (8182)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.50  % (8184)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.50  % (8179)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.50  % (8187)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.50  % (8191)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.50  % (8185)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.51  % (8183)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.51  % (8190)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.51  % (8193)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f639,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(subsumption_resolution,[],[f638,f419])).
% 0.22/0.51  fof(f419,plain,(
% 0.22/0.51    ~v1_tsep_1(sK2,sK3)),
% 0.22/0.51    inference(subsumption_resolution,[],[f172,f418])).
% 0.22/0.51  fof(f418,plain,(
% 0.22/0.51    m1_pre_topc(sK2,sK3)),
% 0.22/0.51    inference(subsumption_resolution,[],[f417,f52])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    sK3 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f17])).
% 0.22/0.51  fof(f17,negated_conjecture,(
% 0.22/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 0.22/0.51    inference(negated_conjecture,[],[f16])).
% 0.22/0.51  fof(f16,conjecture,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tmap_1)).
% 0.22/0.51  fof(f417,plain,(
% 0.22/0.51    sK3 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) | m1_pre_topc(sK2,sK3)),
% 0.22/0.51    inference(subsumption_resolution,[],[f411,f99])).
% 0.22/0.51  fof(f99,plain,(
% 0.22/0.51    l1_pre_topc(sK2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f97,f62])).
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    l1_pre_topc(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f97,plain,(
% 0.22/0.51    ~l1_pre_topc(sK0) | l1_pre_topc(sK2)),
% 0.22/0.51    inference(resolution,[],[f68,f56])).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    m1_pre_topc(sK2,sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f68,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.22/0.51  fof(f411,plain,(
% 0.22/0.51    ~l1_pre_topc(sK2) | sK3 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) | m1_pre_topc(sK2,sK3)),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f408])).
% 0.22/0.51  fof(f408,plain,(
% 0.22/0.51    ~l1_pre_topc(sK2) | sK3 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) | sK3 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) | m1_pre_topc(sK2,sK3)),
% 0.22/0.51    inference(resolution,[],[f328,f175])).
% 0.22/0.51  fof(f175,plain,(
% 0.22/0.51    m1_pre_topc(sK2,sK2)),
% 0.22/0.51    inference(resolution,[],[f99,f65])).
% 0.22/0.51  fof(f65,plain,(
% 0.22/0.51    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.22/0.51  fof(f328,plain,(
% 0.22/0.51    ( ! [X4,X5] : (~m1_pre_topc(X5,X4) | ~l1_pre_topc(X4) | sK3 != g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4)) | sK3 != g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5)) | m1_pre_topc(sK2,sK3)) )),
% 0.22/0.51    inference(forward_demodulation,[],[f326,f52])).
% 0.22/0.51  fof(f326,plain,(
% 0.22/0.51    ( ! [X4,X5] : (~l1_pre_topc(X4) | sK3 != g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4)) | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5)) | ~m1_pre_topc(X5,X4) | m1_pre_topc(sK2,sK3)) )),
% 0.22/0.51    inference(resolution,[],[f247,f99])).
% 0.22/0.51  fof(f247,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~l1_pre_topc(X2) | ~l1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK3 | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) | ~m1_pre_topc(X1,X0) | m1_pre_topc(X2,sK3)) )),
% 0.22/0.51    inference(backward_demodulation,[],[f144,f244])).
% 0.22/0.51  fof(f244,plain,(
% 0.22/0.51    sK3 = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),
% 0.22/0.51    inference(subsumption_resolution,[],[f243,f98])).
% 0.22/0.51  fof(f98,plain,(
% 0.22/0.51    l1_pre_topc(sK3)),
% 0.22/0.51    inference(subsumption_resolution,[],[f96,f62])).
% 0.22/0.51  fof(f96,plain,(
% 0.22/0.51    ~l1_pre_topc(sK0) | l1_pre_topc(sK3)),
% 0.22/0.51    inference(resolution,[],[f68,f54])).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    m1_pre_topc(sK3,sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  % (8196)Refutation not found, incomplete strategy% (8196)------------------------------
% 0.22/0.51  % (8196)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (8196)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (8196)Memory used [KB]: 10618
% 0.22/0.51  % (8196)Time elapsed: 0.099 s
% 0.22/0.51  % (8196)------------------------------
% 0.22/0.51  % (8196)------------------------------
% 0.22/0.51  fof(f243,plain,(
% 0.22/0.51    ~l1_pre_topc(sK3) | sK3 = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),
% 0.22/0.51    inference(resolution,[],[f180,f66])).
% 0.22/0.51  fof(f66,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_pre_topc(X0) | ~l1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(flattening,[],[f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).
% 0.22/0.51  fof(f180,plain,(
% 0.22/0.51    v1_pre_topc(sK3)),
% 0.22/0.51    inference(forward_demodulation,[],[f179,f52])).
% 0.22/0.51  fof(f179,plain,(
% 0.22/0.51    v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),
% 0.22/0.51    inference(subsumption_resolution,[],[f174,f55])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    ~v2_struct_0(sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f174,plain,(
% 0.22/0.51    v2_struct_0(sK2) | v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),
% 0.22/0.51    inference(resolution,[],[f99,f75])).
% 0.22/0.51  fof(f75,plain,(
% 0.22/0.51    ( ! [X0] : (~l1_pre_topc(X0) | v2_struct_0(X0) | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f35])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ! [X0] : ((v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & ~v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f34])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ! [X0] : ((v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & ~v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & ~v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_pre_topc)).
% 0.22/0.51  fof(f144,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~l1_pre_topc(X2) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) | ~m1_pre_topc(X1,X0) | m1_pre_topc(X2,sK3)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f140,f68])).
% 0.22/0.51  fof(f140,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~l1_pre_topc(X1) | ~l1_pre_topc(X2) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) | ~m1_pre_topc(X1,X0) | m1_pre_topc(X2,sK3)) )),
% 0.22/0.51    inference(resolution,[],[f98,f67])).
% 0.22/0.51  fof(f67,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~l1_pre_topc(X2) | ~l1_pre_topc(X3) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) | ~m1_pre_topc(X2,X0) | m1_pre_topc(X3,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (m1_pre_topc(X3,X1) | ~m1_pre_topc(X2,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~l1_pre_topc(X3)) | ~l1_pre_topc(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(flattening,[],[f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((m1_pre_topc(X3,X1) | (~m1_pre_topc(X2,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X3)) | ~l1_pre_topc(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (l1_pre_topc(X2) => ! [X3] : (l1_pre_topc(X3) => ((m1_pre_topc(X2,X0) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => m1_pre_topc(X3,X1))))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_pre_topc)).
% 0.22/0.51  fof(f172,plain,(
% 0.22/0.51    ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3)),
% 0.22/0.51    inference(subsumption_resolution,[],[f171,f47])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f171,plain,(
% 0.22/0.51    ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.22/0.51    inference(subsumption_resolution,[],[f170,f60])).
% 0.22/0.51  fof(f60,plain,(
% 0.22/0.51    ~v2_struct_0(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f170,plain,(
% 0.22/0.51    ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.22/0.51    inference(subsumption_resolution,[],[f169,f87])).
% 0.22/0.51  fof(f87,plain,(
% 0.22/0.51    m1_subset_1(sK5,u1_struct_0(sK2))),
% 0.22/0.51    inference(forward_demodulation,[],[f44,f45])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    sK5 = sK6),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    m1_subset_1(sK6,u1_struct_0(sK2))),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f169,plain,(
% 0.22/0.51    ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.22/0.51    inference(subsumption_resolution,[],[f168,f48])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f168,plain,(
% 0.22/0.51    ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.22/0.51    inference(subsumption_resolution,[],[f167,f51])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f167,plain,(
% 0.22/0.51    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.22/0.51    inference(subsumption_resolution,[],[f166,f50])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f166,plain,(
% 0.22/0.51    ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.22/0.51    inference(subsumption_resolution,[],[f165,f49])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    v1_funct_1(sK4)),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f165,plain,(
% 0.22/0.51    ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.22/0.51    inference(subsumption_resolution,[],[f164,f54])).
% 0.22/0.51  fof(f164,plain,(
% 0.22/0.51    ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.22/0.51    inference(subsumption_resolution,[],[f163,f53])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    ~v2_struct_0(sK3)),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f163,plain,(
% 0.22/0.51    v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.22/0.51    inference(subsumption_resolution,[],[f162,f56])).
% 0.22/0.51  fof(f162,plain,(
% 0.22/0.51    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.22/0.51    inference(subsumption_resolution,[],[f161,f55])).
% 0.22/0.51  fof(f161,plain,(
% 0.22/0.51    v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.22/0.51    inference(subsumption_resolution,[],[f160,f59])).
% 0.22/0.51  fof(f59,plain,(
% 0.22/0.51    l1_pre_topc(sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f160,plain,(
% 0.22/0.51    ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.22/0.51    inference(subsumption_resolution,[],[f159,f58])).
% 0.22/0.51  fof(f58,plain,(
% 0.22/0.51    v2_pre_topc(sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f159,plain,(
% 0.22/0.51    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.22/0.51    inference(subsumption_resolution,[],[f158,f57])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    ~v2_struct_0(sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f158,plain,(
% 0.22/0.51    v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.22/0.51    inference(subsumption_resolution,[],[f157,f62])).
% 0.22/0.51  fof(f157,plain,(
% 0.22/0.51    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.22/0.51    inference(subsumption_resolution,[],[f156,f61])).
% 0.22/0.51  fof(f61,plain,(
% 0.22/0.51    v2_pre_topc(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f156,plain,(
% 0.22/0.51    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.22/0.51    inference(resolution,[],[f83,f86])).
% 0.22/0.51  fof(f86,plain,(
% 0.22/0.51    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)),
% 0.22/0.51    inference(backward_demodulation,[],[f46,f45])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f83,plain,(
% 0.22/0.51    ( ! [X6,X4,X2,X0,X3,X1] : (~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_tsep_1(X2,X3) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | v2_struct_0(X0) | r1_tmap_1(X3,X1,X4,X6)) )),
% 0.22/0.51    inference(equality_resolution,[],[f72])).
% 0.22/0.51  fof(f72,plain,(
% 0.22/0.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_tsep_1(X2,X3) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | X5 != X6 | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f33])).
% 0.22/0.51  % (8175)Refutation not found, incomplete strategy% (8175)------------------------------
% 0.22/0.51  % (8175)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | (~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tmap_1)).
% 0.22/0.51  fof(f638,plain,(
% 0.22/0.51    v1_tsep_1(sK2,sK3)),
% 0.22/0.51    inference(subsumption_resolution,[],[f637,f108])).
% 0.22/0.51  fof(f108,plain,(
% 0.22/0.51    v2_pre_topc(sK3)),
% 0.22/0.51    inference(subsumption_resolution,[],[f107,f61])).
% 0.22/0.51  fof(f107,plain,(
% 0.22/0.51    ~v2_pre_topc(sK0) | v2_pre_topc(sK3)),
% 0.22/0.51    inference(subsumption_resolution,[],[f105,f62])).
% 0.22/0.51  fof(f105,plain,(
% 0.22/0.51    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_pre_topc(sK3)),
% 0.22/0.51    inference(resolution,[],[f77,f54])).
% 0.22/0.51  fof(f77,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_pre_topc(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f39])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.51    inference(flattening,[],[f38])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.22/0.51  fof(f637,plain,(
% 0.22/0.51    ~v2_pre_topc(sK3) | v1_tsep_1(sK2,sK3)),
% 0.22/0.51    inference(subsumption_resolution,[],[f636,f418])).
% 0.22/0.51  fof(f636,plain,(
% 0.22/0.51    ~m1_pre_topc(sK2,sK3) | ~v2_pre_topc(sK3) | v1_tsep_1(sK2,sK3)),
% 0.22/0.51    inference(subsumption_resolution,[],[f635,f98])).
% 0.22/0.51  fof(f635,plain,(
% 0.22/0.51    ~l1_pre_topc(sK3) | ~m1_pre_topc(sK2,sK3) | ~v2_pre_topc(sK3) | v1_tsep_1(sK2,sK3)),
% 0.22/0.51    inference(resolution,[],[f619,f89])).
% 0.22/0.51  fof(f89,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v3_pre_topc(u1_struct_0(X1),X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | v1_tsep_1(X1,X0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f84,f69])).
% 0.22/0.51  fof(f69,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.22/0.51  fof(f84,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(u1_struct_0(X1),X0) | v1_tsep_1(X1,X0)) )),
% 0.22/0.51    inference(equality_resolution,[],[f80])).
% 0.22/0.51  fof(f80,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | ~v3_pre_topc(X2,X0) | v1_tsep_1(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f43])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.51    inference(flattening,[],[f42])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).
% 0.22/0.51  fof(f619,plain,(
% 0.22/0.51    v3_pre_topc(u1_struct_0(sK2),sK3)),
% 0.22/0.51    inference(subsumption_resolution,[],[f618,f222])).
% 0.22/0.51  fof(f222,plain,(
% 0.22/0.51    v3_pre_topc(u1_struct_0(sK2),sK2)),
% 0.22/0.51    inference(backward_demodulation,[],[f184,f221])).
% 0.22/0.51  fof(f221,plain,(
% 0.22/0.51    u1_struct_0(sK2) = k2_struct_0(sK2)),
% 0.22/0.51    inference(resolution,[],[f176,f63])).
% 0.22/0.51  fof(f63,plain,(
% 0.22/0.51    ( ! [X0] : (~l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.51  fof(f176,plain,(
% 0.22/0.51    l1_struct_0(sK2)),
% 0.22/0.51    inference(resolution,[],[f99,f64])).
% 0.22/0.51  fof(f64,plain,(
% 0.22/0.51    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.51  fof(f184,plain,(
% 0.22/0.51    v3_pre_topc(k2_struct_0(sK2),sK2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f183,f99])).
% 0.22/0.51  fof(f183,plain,(
% 0.22/0.51    ~l1_pre_topc(sK2) | v3_pre_topc(k2_struct_0(sK2),sK2)),
% 0.22/0.51    inference(resolution,[],[f110,f76])).
% 0.22/0.51  fof(f76,plain,(
% 0.22/0.51    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v3_pre_topc(k2_struct_0(X0),X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f37])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.51    inference(flattening,[],[f36])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).
% 0.22/0.51  fof(f110,plain,(
% 0.22/0.51    v2_pre_topc(sK2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f109,f61])).
% 0.22/0.51  fof(f109,plain,(
% 0.22/0.51    ~v2_pre_topc(sK0) | v2_pre_topc(sK2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f106,f62])).
% 0.22/0.51  % (8175)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (8175)Memory used [KB]: 6780
% 0.22/0.51  % (8177)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.51  fof(f106,plain,(
% 0.22/0.51    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_pre_topc(sK2)),
% 0.22/0.51    inference(resolution,[],[f77,f56])).
% 0.22/0.51  fof(f618,plain,(
% 0.22/0.51    ~v3_pre_topc(u1_struct_0(sK2),sK2) | v3_pre_topc(u1_struct_0(sK2),sK3)),
% 0.22/0.51    inference(resolution,[],[f518,f572])).
% 0.22/0.51  fof(f572,plain,(
% 0.22/0.51    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.22/0.51    inference(subsumption_resolution,[],[f556,f98])).
% 0.22/0.51  fof(f556,plain,(
% 0.22/0.51    ~l1_pre_topc(sK3) | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.22/0.51    inference(resolution,[],[f418,f69])).
% 0.22/0.51  fof(f518,plain,(
% 0.22/0.51    ( ! [X6] : (~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK3))) | ~v3_pre_topc(X6,sK2) | v3_pre_topc(X6,sK3)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f499,f99])).
% 0.22/0.51  fof(f499,plain,(
% 0.22/0.51    ( ! [X6] : (~l1_pre_topc(sK2) | ~v3_pre_topc(X6,sK2) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK3))) | v3_pre_topc(X6,sK3)) )),
% 0.22/0.51    inference(resolution,[],[f403,f88])).
% 0.22/0.51  fof(f88,plain,(
% 0.22/0.51    ( ! [X2,X0,X3] : (~m1_pre_topc(X2,X0) | ~l1_pre_topc(X0) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | v3_pre_topc(X3,X2)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f81,f70])).
% 0.22/0.51  fof(f70,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).
% 0.22/0.51  fof(f81,plain,(
% 0.22/0.51    ( ! [X2,X0,X3] : (~l1_pre_topc(X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X2,X0) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | v3_pre_topc(X3,X2)) )),
% 0.22/0.51    inference(equality_resolution,[],[f71])).
% 0.22/0.51  fof(f71,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X2,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | X1 != X3 | v3_pre_topc(X3,X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(flattening,[],[f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v3_pre_topc(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v3_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v3_pre_topc(X3,X2)))))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tops_2)).
% 0.22/0.51  fof(f403,plain,(
% 0.22/0.51    m1_pre_topc(sK3,sK2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f402,f52])).
% 0.22/0.51  fof(f402,plain,(
% 0.22/0.51    sK3 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) | m1_pre_topc(sK3,sK2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f396,f99])).
% 0.22/0.51  fof(f396,plain,(
% 0.22/0.51    ~l1_pre_topc(sK2) | sK3 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) | m1_pre_topc(sK3,sK2)),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f393])).
% 0.22/0.51  fof(f393,plain,(
% 0.22/0.51    ~l1_pre_topc(sK2) | sK3 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) | sK3 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) | m1_pre_topc(sK3,sK2)),
% 0.22/0.51    inference(resolution,[],[f322,f175])).
% 0.22/0.51  fof(f322,plain,(
% 0.22/0.51    ( ! [X6,X7] : (~m1_pre_topc(X7,X6) | ~l1_pre_topc(X6) | sK3 != g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6)) | sK3 != g1_pre_topc(u1_struct_0(X7),u1_pre_topc(X7)) | m1_pre_topc(sK3,sK2)) )),
% 0.22/0.51    inference(forward_demodulation,[],[f321,f244])).
% 0.22/0.51  fof(f321,plain,(
% 0.22/0.51    ( ! [X6,X7] : (~l1_pre_topc(X6) | sK3 != g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6)) | g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != g1_pre_topc(u1_struct_0(X7),u1_pre_topc(X7)) | ~m1_pre_topc(X7,X6) | m1_pre_topc(sK3,sK2)) )),
% 0.22/0.51    inference(resolution,[],[f178,f98])).
% 0.22/0.51  fof(f178,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~l1_pre_topc(X2) | ~l1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK3 | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) | ~m1_pre_topc(X1,X0) | m1_pre_topc(X2,sK2)) )),
% 0.22/0.51    inference(forward_demodulation,[],[f177,f52])).
% 0.22/0.51  fof(f177,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~l1_pre_topc(X2) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) | ~m1_pre_topc(X1,X0) | m1_pre_topc(X2,sK2)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f173,f68])).
% 0.22/0.51  fof(f173,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~l1_pre_topc(X1) | ~l1_pre_topc(X2) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) | ~m1_pre_topc(X1,X0) | m1_pre_topc(X2,sK2)) )),
% 0.22/0.51    inference(resolution,[],[f99,f67])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (8193)------------------------------
% 0.22/0.51  % (8193)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (8193)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (8193)Memory used [KB]: 1918
% 0.22/0.51  % (8193)Time elapsed: 0.083 s
% 0.22/0.51  % (8193)------------------------------
% 0.22/0.51  % (8193)------------------------------
% 0.22/0.51  % (8173)Success in time 0.152 s
%------------------------------------------------------------------------------
