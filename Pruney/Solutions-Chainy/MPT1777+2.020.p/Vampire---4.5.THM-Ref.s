%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:04 EST 2020

% Result     : Theorem 1.84s
% Output     : Refutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 672 expanded)
%              Number of leaves         :   16 ( 124 expanded)
%              Depth                    :   24
%              Number of atoms          :  745 (7210 expanded)
%              Number of equality atoms :   50 ( 717 expanded)
%              Maximal formula depth    :   28 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f972,plain,(
    $false ),
    inference(subsumption_resolution,[],[f971,f652])).

fof(f652,plain,(
    ~ v1_tsep_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f191,f651])).

fof(f651,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f650,f55])).

fof(f55,plain,(
    sK3 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

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
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
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

fof(f650,plain,
    ( sK3 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f643,f105])).

fof(f105,plain,(
    l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f103,f65])).

fof(f65,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f103,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2) ),
    inference(resolution,[],[f71,f59])).

fof(f59,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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

fof(f643,plain,
    ( ~ l1_pre_topc(sK2)
    | sK3 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | m1_pre_topc(sK2,sK3) ),
    inference(duplicate_literal_removal,[],[f639])).

fof(f639,plain,
    ( ~ l1_pre_topc(sK2)
    | sK3 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | sK3 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | m1_pre_topc(sK2,sK3) ),
    inference(resolution,[],[f512,f194])).

fof(f194,plain,(
    m1_pre_topc(sK2,sK2) ),
    inference(resolution,[],[f105,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f512,plain,(
    ! [X4,X5] :
      ( ~ m1_pre_topc(X5,X4)
      | ~ l1_pre_topc(X4)
      | sK3 != g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4))
      | sK3 != g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5))
      | m1_pre_topc(sK2,sK3) ) ),
    inference(forward_demodulation,[],[f510,f55])).

fof(f510,plain,(
    ! [X4,X5] :
      ( ~ l1_pre_topc(X4)
      | sK3 != g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4))
      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5))
      | ~ m1_pre_topc(X5,X4)
      | m1_pre_topc(sK2,sK3) ) ),
    inference(resolution,[],[f206,f105])).

fof(f206,plain,(
    ! [X6,X8,X7] :
      ( ~ l1_pre_topc(X8)
      | ~ l1_pre_topc(X6)
      | sK3 != g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6))
      | g1_pre_topc(u1_struct_0(X7),u1_pre_topc(X7)) != g1_pre_topc(u1_struct_0(X8),u1_pre_topc(X8))
      | ~ m1_pre_topc(X7,X6)
      | m1_pre_topc(X8,sK3) ) ),
    inference(backward_demodulation,[],[f164,f205])).

fof(f205,plain,(
    sK3 = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) ),
    inference(subsumption_resolution,[],[f204,f104])).

fof(f104,plain,(
    l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f102,f65])).

fof(f102,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK3) ),
    inference(resolution,[],[f71,f57])).

fof(f57,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f204,plain,
    ( ~ l1_pre_topc(sK3)
    | sK3 = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) ),
    inference(resolution,[],[f132,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
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

fof(f132,plain,(
    v1_pre_topc(sK3) ),
    inference(forward_demodulation,[],[f131,f55])).

fof(f131,plain,(
    v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(subsumption_resolution,[],[f129,f65])).

fof(f129,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(resolution,[],[f73,f59])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).

fof(f164,plain,(
    ! [X6,X8,X7] :
      ( ~ l1_pre_topc(X6)
      | ~ l1_pre_topc(X8)
      | g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6))
      | g1_pre_topc(u1_struct_0(X7),u1_pre_topc(X7)) != g1_pre_topc(u1_struct_0(X8),u1_pre_topc(X8))
      | ~ m1_pre_topc(X7,X6)
      | m1_pre_topc(X8,sK3) ) ),
    inference(subsumption_resolution,[],[f161,f71])).

fof(f161,plain,(
    ! [X6,X8,X7] :
      ( ~ l1_pre_topc(X6)
      | ~ l1_pre_topc(X7)
      | ~ l1_pre_topc(X8)
      | g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6))
      | g1_pre_topc(u1_struct_0(X7),u1_pre_topc(X7)) != g1_pre_topc(u1_struct_0(X8),u1_pre_topc(X8))
      | ~ m1_pre_topc(X7,X6)
      | m1_pre_topc(X8,sK3) ) ),
    inference(resolution,[],[f70,f104])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X2)
      | ~ l1_pre_topc(X3)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
      | ~ m1_pre_topc(X2,X0)
      | m1_pre_topc(X3,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

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

fof(f191,plain,
    ( ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f190,f50])).

fof(f50,plain,(
    ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f20])).

fof(f190,plain,
    ( ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(subsumption_resolution,[],[f189,f63])).

fof(f63,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f189,plain,
    ( ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | v2_struct_0(sK0)
    | r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(subsumption_resolution,[],[f188,f93])).

fof(f93,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f47,f48])).

fof(f48,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f20])).

fof(f47,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f20])).

fof(f188,plain,
    ( ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(subsumption_resolution,[],[f187,f51])).

fof(f51,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f20])).

fof(f187,plain,
    ( ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(subsumption_resolution,[],[f186,f54])).

fof(f54,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f20])).

fof(f186,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(subsumption_resolution,[],[f185,f53])).

fof(f53,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f185,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(subsumption_resolution,[],[f184,f52])).

fof(f52,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f20])).

fof(f184,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(subsumption_resolution,[],[f183,f57])).

fof(f183,plain,
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
    inference(subsumption_resolution,[],[f182,f56])).

fof(f56,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f182,plain,
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
    inference(subsumption_resolution,[],[f181,f59])).

fof(f181,plain,
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
    inference(subsumption_resolution,[],[f180,f58])).

fof(f58,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f180,plain,
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
    inference(subsumption_resolution,[],[f179,f62])).

fof(f62,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f179,plain,
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
    inference(subsumption_resolution,[],[f178,f61])).

fof(f61,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f178,plain,
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
    inference(subsumption_resolution,[],[f177,f60])).

fof(f60,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f177,plain,
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
    inference(subsumption_resolution,[],[f176,f65])).

fof(f176,plain,
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
    inference(subsumption_resolution,[],[f175,f64])).

fof(f64,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f175,plain,
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
    inference(resolution,[],[f89,f92])).

fof(f92,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(backward_demodulation,[],[f49,f48])).

fof(f49,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f20])).

fof(f89,plain,(
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
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
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
    inference(cnf_transformation,[],[f32])).

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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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

fof(f971,plain,(
    v1_tsep_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f970,f56])).

fof(f970,plain,
    ( v2_struct_0(sK3)
    | v1_tsep_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f968,f320])).

fof(f320,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(forward_demodulation,[],[f319,f55])).

fof(f319,plain,(
    m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK2) ),
    inference(subsumption_resolution,[],[f309,f105])).

fof(f309,plain,
    ( ~ l1_pre_topc(sK2)
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK2) ),
    inference(resolution,[],[f194,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f968,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | v2_struct_0(sK3)
    | v1_tsep_1(sK2,sK3) ),
    inference(resolution,[],[f449,f678])).

fof(f678,plain,(
    r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(resolution,[],[f651,f147])).

fof(f147,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK3)) ) ),
    inference(subsumption_resolution,[],[f146,f64])).

fof(f146,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(X0,sK3)
      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK3)) ) ),
    inference(subsumption_resolution,[],[f144,f65])).

fof(f144,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(X0,sK3)
      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK3)) ) ),
    inference(resolution,[],[f94,f57])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X2)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) ),
    inference(subsumption_resolution,[],[f84,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X2,X1)
      | m1_pre_topc(X2,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f449,plain,(
    ! [X1] :
      ( ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X1))
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | v1_tsep_1(sK2,X1) ) ),
    inference(subsumption_resolution,[],[f448,f194])).

fof(f448,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(sK2,sK2)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,sK2)
      | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X1))
      | v1_tsep_1(sK2,X1) ) ),
    inference(subsumption_resolution,[],[f447,f58])).

fof(f447,plain,(
    ! [X1] :
      ( v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,sK2)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,sK2)
      | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X1))
      | v1_tsep_1(sK2,X1) ) ),
    inference(subsumption_resolution,[],[f446,f105])).

fof(f446,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(sK2)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,sK2)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,sK2)
      | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X1))
      | v1_tsep_1(sK2,X1) ) ),
    inference(subsumption_resolution,[],[f444,f116])).

fof(f116,plain,(
    v2_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f115,f64])).

fof(f115,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f112,f65])).

fof(f112,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK2) ),
    inference(resolution,[],[f82,f59])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
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

fof(f444,plain,(
    ! [X1] :
      ( ~ v2_pre_topc(sK2)
      | ~ l1_pre_topc(sK2)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,sK2)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,sK2)
      | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X1))
      | v1_tsep_1(sK2,X1) ) ),
    inference(resolution,[],[f372,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_tsep_1(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | v1_tsep_1(X1,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X2)
                & v1_tsep_1(X1,X2) )
              | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_tsep_1(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X2)
                & v1_tsep_1(X1,X2) )
              | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_tsep_1(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & v1_tsep_1(X1,X0) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
               => ( m1_pre_topc(X1,X2)
                  & v1_tsep_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_tsep_1)).

fof(f372,plain,(
    v1_tsep_1(sK2,sK2) ),
    inference(subsumption_resolution,[],[f371,f116])).

fof(f371,plain,
    ( ~ v2_pre_topc(sK2)
    | v1_tsep_1(sK2,sK2) ),
    inference(subsumption_resolution,[],[f370,f194])).

fof(f370,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | ~ v2_pre_topc(sK2)
    | v1_tsep_1(sK2,sK2) ),
    inference(subsumption_resolution,[],[f369,f105])).

fof(f369,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | ~ v2_pre_topc(sK2)
    | v1_tsep_1(sK2,sK2) ),
    inference(resolution,[],[f260,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(u1_struct_0(X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f90,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | ~ v3_pre_topc(X2,X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f45,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f260,plain,(
    v3_pre_topc(u1_struct_0(sK2),sK2) ),
    inference(backward_demodulation,[],[f203,f259])).

fof(f259,plain,(
    u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(resolution,[],[f195,f66])).

fof(f66,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f195,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f105,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f203,plain,(
    v3_pre_topc(k2_struct_0(sK2),sK2) ),
    inference(subsumption_resolution,[],[f202,f105])).

fof(f202,plain,
    ( ~ l1_pre_topc(sK2)
    | v3_pre_topc(k2_struct_0(sK2),sK2) ),
    inference(resolution,[],[f116,f81])).

fof(f81,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v3_pre_topc(k2_struct_0(X0),X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:04:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (26639)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.47  % (26633)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.49  % (26624)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.49  % (26625)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (26632)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (26640)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (26623)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (26634)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.51  % (26620)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (26640)Refutation not found, incomplete strategy% (26640)------------------------------
% 0.21/0.52  % (26640)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (26626)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.52  % (26640)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (26640)Memory used [KB]: 10618
% 0.21/0.52  % (26640)Time elapsed: 0.091 s
% 0.21/0.52  % (26640)------------------------------
% 0.21/0.52  % (26640)------------------------------
% 0.21/0.53  % (26631)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.53  % (26630)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.53  % (26621)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (26627)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.54  % (26638)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.54  % (26622)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.55  % (26637)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.56  % (26629)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.56  % (26636)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 1.69/0.57  % (26628)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 1.84/0.59  % (26631)Refutation not found, incomplete strategy% (26631)------------------------------
% 1.84/0.59  % (26631)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.84/0.59  % (26631)Termination reason: Refutation not found, incomplete strategy
% 1.84/0.59  
% 1.84/0.59  % (26631)Memory used [KB]: 11129
% 1.84/0.59  % (26631)Time elapsed: 0.125 s
% 1.84/0.59  % (26631)------------------------------
% 1.84/0.59  % (26631)------------------------------
% 1.84/0.60  % (26635)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 1.84/0.63  % (26637)Refutation found. Thanks to Tanya!
% 1.84/0.63  % SZS status Theorem for theBenchmark
% 1.84/0.63  % SZS output start Proof for theBenchmark
% 1.84/0.63  fof(f972,plain,(
% 1.84/0.63    $false),
% 1.84/0.63    inference(subsumption_resolution,[],[f971,f652])).
% 1.84/0.63  fof(f652,plain,(
% 1.84/0.63    ~v1_tsep_1(sK2,sK3)),
% 1.84/0.63    inference(subsumption_resolution,[],[f191,f651])).
% 1.84/0.63  fof(f651,plain,(
% 1.84/0.63    m1_pre_topc(sK2,sK3)),
% 1.84/0.63    inference(subsumption_resolution,[],[f650,f55])).
% 1.84/0.63  fof(f55,plain,(
% 1.84/0.63    sK3 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 1.84/0.63    inference(cnf_transformation,[],[f20])).
% 1.84/0.63  fof(f20,plain,(
% 1.84/0.63    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.84/0.63    inference(flattening,[],[f19])).
% 1.84/0.63  fof(f19,plain,(
% 1.84/0.63    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.84/0.63    inference(ennf_transformation,[],[f18])).
% 1.84/0.63  fof(f18,negated_conjecture,(
% 1.84/0.63    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 1.84/0.63    inference(negated_conjecture,[],[f17])).
% 1.84/0.63  fof(f17,conjecture,(
% 1.84/0.63    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 1.84/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tmap_1)).
% 1.84/0.63  fof(f650,plain,(
% 1.84/0.63    sK3 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) | m1_pre_topc(sK2,sK3)),
% 1.84/0.63    inference(subsumption_resolution,[],[f643,f105])).
% 1.84/0.63  fof(f105,plain,(
% 1.84/0.63    l1_pre_topc(sK2)),
% 1.84/0.63    inference(subsumption_resolution,[],[f103,f65])).
% 1.84/0.63  fof(f65,plain,(
% 1.84/0.63    l1_pre_topc(sK0)),
% 1.84/0.63    inference(cnf_transformation,[],[f20])).
% 1.84/0.63  fof(f103,plain,(
% 1.84/0.63    ~l1_pre_topc(sK0) | l1_pre_topc(sK2)),
% 1.84/0.63    inference(resolution,[],[f71,f59])).
% 1.84/0.63  fof(f59,plain,(
% 1.84/0.63    m1_pre_topc(sK2,sK0)),
% 1.84/0.63    inference(cnf_transformation,[],[f20])).
% 1.84/0.63  fof(f71,plain,(
% 1.84/0.63    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 1.84/0.63    inference(cnf_transformation,[],[f28])).
% 1.84/0.63  fof(f28,plain,(
% 1.84/0.63    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.84/0.63    inference(ennf_transformation,[],[f5])).
% 1.84/0.63  fof(f5,axiom,(
% 1.84/0.63    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.84/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.84/0.63  fof(f643,plain,(
% 1.84/0.63    ~l1_pre_topc(sK2) | sK3 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) | m1_pre_topc(sK2,sK3)),
% 1.84/0.63    inference(duplicate_literal_removal,[],[f639])).
% 1.84/0.63  fof(f639,plain,(
% 1.84/0.63    ~l1_pre_topc(sK2) | sK3 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) | sK3 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) | m1_pre_topc(sK2,sK3)),
% 1.84/0.63    inference(resolution,[],[f512,f194])).
% 1.84/0.63  fof(f194,plain,(
% 1.84/0.63    m1_pre_topc(sK2,sK2)),
% 1.84/0.63    inference(resolution,[],[f105,f68])).
% 1.84/0.63  fof(f68,plain,(
% 1.84/0.63    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,X0)) )),
% 1.84/0.63    inference(cnf_transformation,[],[f23])).
% 1.84/0.63  fof(f23,plain,(
% 1.84/0.63    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 1.84/0.63    inference(ennf_transformation,[],[f13])).
% 1.84/0.63  fof(f13,axiom,(
% 1.84/0.63    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 1.84/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 1.84/0.63  fof(f512,plain,(
% 1.84/0.63    ( ! [X4,X5] : (~m1_pre_topc(X5,X4) | ~l1_pre_topc(X4) | sK3 != g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4)) | sK3 != g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5)) | m1_pre_topc(sK2,sK3)) )),
% 1.84/0.63    inference(forward_demodulation,[],[f510,f55])).
% 1.84/0.63  fof(f510,plain,(
% 1.84/0.63    ( ! [X4,X5] : (~l1_pre_topc(X4) | sK3 != g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4)) | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5)) | ~m1_pre_topc(X5,X4) | m1_pre_topc(sK2,sK3)) )),
% 1.84/0.63    inference(resolution,[],[f206,f105])).
% 1.84/0.63  fof(f206,plain,(
% 1.84/0.63    ( ! [X6,X8,X7] : (~l1_pre_topc(X8) | ~l1_pre_topc(X6) | sK3 != g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6)) | g1_pre_topc(u1_struct_0(X7),u1_pre_topc(X7)) != g1_pre_topc(u1_struct_0(X8),u1_pre_topc(X8)) | ~m1_pre_topc(X7,X6) | m1_pre_topc(X8,sK3)) )),
% 1.84/0.63    inference(backward_demodulation,[],[f164,f205])).
% 1.84/0.63  fof(f205,plain,(
% 1.84/0.63    sK3 = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),
% 1.84/0.63    inference(subsumption_resolution,[],[f204,f104])).
% 1.84/0.63  fof(f104,plain,(
% 1.84/0.63    l1_pre_topc(sK3)),
% 1.84/0.63    inference(subsumption_resolution,[],[f102,f65])).
% 1.84/0.63  fof(f102,plain,(
% 1.84/0.63    ~l1_pre_topc(sK0) | l1_pre_topc(sK3)),
% 1.84/0.63    inference(resolution,[],[f71,f57])).
% 1.84/0.63  fof(f57,plain,(
% 1.84/0.63    m1_pre_topc(sK3,sK0)),
% 1.84/0.63    inference(cnf_transformation,[],[f20])).
% 1.84/0.63  fof(f204,plain,(
% 1.84/0.63    ~l1_pre_topc(sK3) | sK3 = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),
% 1.84/0.63    inference(resolution,[],[f132,f69])).
% 1.84/0.63  fof(f69,plain,(
% 1.84/0.63    ( ! [X0] : (~v1_pre_topc(X0) | ~l1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0) )),
% 1.84/0.63    inference(cnf_transformation,[],[f25])).
% 1.84/0.63  fof(f25,plain,(
% 1.84/0.63    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 1.84/0.63    inference(flattening,[],[f24])).
% 1.84/0.63  fof(f24,plain,(
% 1.84/0.63    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 1.84/0.63    inference(ennf_transformation,[],[f1])).
% 1.84/0.63  fof(f1,axiom,(
% 1.84/0.63    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 1.84/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).
% 1.84/0.63  fof(f132,plain,(
% 1.84/0.63    v1_pre_topc(sK3)),
% 1.84/0.63    inference(forward_demodulation,[],[f131,f55])).
% 1.84/0.63  fof(f131,plain,(
% 1.84/0.63    v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),
% 1.84/0.63    inference(subsumption_resolution,[],[f129,f65])).
% 1.84/0.63  fof(f129,plain,(
% 1.84/0.63    ~l1_pre_topc(sK0) | v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),
% 1.84/0.63    inference(resolution,[],[f73,f59])).
% 1.84/0.63  fof(f73,plain,(
% 1.84/0.63    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) )),
% 1.84/0.63    inference(cnf_transformation,[],[f30])).
% 1.84/0.63  fof(f30,plain,(
% 1.84/0.63    ! [X0] : (! [X1] : ((m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.84/0.63    inference(ennf_transformation,[],[f9])).
% 1.84/0.63  fof(f9,axiom,(
% 1.84/0.63    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 1.84/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).
% 1.84/0.63  fof(f164,plain,(
% 1.84/0.63    ( ! [X6,X8,X7] : (~l1_pre_topc(X6) | ~l1_pre_topc(X8) | g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6)) | g1_pre_topc(u1_struct_0(X7),u1_pre_topc(X7)) != g1_pre_topc(u1_struct_0(X8),u1_pre_topc(X8)) | ~m1_pre_topc(X7,X6) | m1_pre_topc(X8,sK3)) )),
% 1.84/0.63    inference(subsumption_resolution,[],[f161,f71])).
% 1.84/0.63  fof(f161,plain,(
% 1.84/0.63    ( ! [X6,X8,X7] : (~l1_pre_topc(X6) | ~l1_pre_topc(X7) | ~l1_pre_topc(X8) | g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6)) | g1_pre_topc(u1_struct_0(X7),u1_pre_topc(X7)) != g1_pre_topc(u1_struct_0(X8),u1_pre_topc(X8)) | ~m1_pre_topc(X7,X6) | m1_pre_topc(X8,sK3)) )),
% 1.84/0.63    inference(resolution,[],[f70,f104])).
% 1.84/0.63  fof(f70,plain,(
% 1.84/0.63    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~l1_pre_topc(X2) | ~l1_pre_topc(X3) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) | ~m1_pre_topc(X2,X0) | m1_pre_topc(X3,X1)) )),
% 1.84/0.63    inference(cnf_transformation,[],[f27])).
% 1.84/0.63  fof(f27,plain,(
% 1.84/0.63    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (m1_pre_topc(X3,X1) | ~m1_pre_topc(X2,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~l1_pre_topc(X3)) | ~l1_pre_topc(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.84/0.63    inference(flattening,[],[f26])).
% 1.84/0.63  fof(f26,plain,(
% 1.84/0.63    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((m1_pre_topc(X3,X1) | (~m1_pre_topc(X2,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X3)) | ~l1_pre_topc(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.84/0.63    inference(ennf_transformation,[],[f7])).
% 1.84/0.63  fof(f7,axiom,(
% 1.84/0.63    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (l1_pre_topc(X2) => ! [X3] : (l1_pre_topc(X3) => ((m1_pre_topc(X2,X0) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => m1_pre_topc(X3,X1))))))),
% 1.84/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_pre_topc)).
% 1.84/0.63  fof(f191,plain,(
% 1.84/0.63    ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3)),
% 1.84/0.63    inference(subsumption_resolution,[],[f190,f50])).
% 1.84/0.63  fof(f50,plain,(
% 1.84/0.63    ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 1.84/0.63    inference(cnf_transformation,[],[f20])).
% 1.84/0.63  fof(f190,plain,(
% 1.84/0.63    ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | r1_tmap_1(sK3,sK1,sK4,sK5)),
% 1.84/0.63    inference(subsumption_resolution,[],[f189,f63])).
% 1.84/0.63  fof(f63,plain,(
% 1.84/0.63    ~v2_struct_0(sK0)),
% 1.84/0.63    inference(cnf_transformation,[],[f20])).
% 1.84/0.63  fof(f189,plain,(
% 1.84/0.63    ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK5)),
% 1.84/0.63    inference(subsumption_resolution,[],[f188,f93])).
% 1.84/0.63  fof(f93,plain,(
% 1.84/0.63    m1_subset_1(sK5,u1_struct_0(sK2))),
% 1.84/0.63    inference(forward_demodulation,[],[f47,f48])).
% 1.84/0.63  fof(f48,plain,(
% 1.84/0.63    sK5 = sK6),
% 1.84/0.63    inference(cnf_transformation,[],[f20])).
% 1.84/0.63  fof(f47,plain,(
% 1.84/0.63    m1_subset_1(sK6,u1_struct_0(sK2))),
% 1.84/0.63    inference(cnf_transformation,[],[f20])).
% 1.84/0.63  fof(f188,plain,(
% 1.84/0.63    ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK5)),
% 1.84/0.63    inference(subsumption_resolution,[],[f187,f51])).
% 1.84/0.63  fof(f51,plain,(
% 1.84/0.63    m1_subset_1(sK5,u1_struct_0(sK3))),
% 1.84/0.63    inference(cnf_transformation,[],[f20])).
% 1.84/0.63  fof(f187,plain,(
% 1.84/0.63    ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK5)),
% 1.84/0.63    inference(subsumption_resolution,[],[f186,f54])).
% 1.84/0.63  fof(f54,plain,(
% 1.84/0.63    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 1.84/0.63    inference(cnf_transformation,[],[f20])).
% 1.84/0.63  fof(f186,plain,(
% 1.84/0.63    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK5)),
% 1.84/0.63    inference(subsumption_resolution,[],[f185,f53])).
% 1.84/0.63  fof(f53,plain,(
% 1.84/0.63    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 1.84/0.63    inference(cnf_transformation,[],[f20])).
% 1.84/0.63  fof(f185,plain,(
% 1.84/0.63    ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK5)),
% 1.84/0.63    inference(subsumption_resolution,[],[f184,f52])).
% 1.84/0.63  fof(f52,plain,(
% 1.84/0.63    v1_funct_1(sK4)),
% 1.84/0.63    inference(cnf_transformation,[],[f20])).
% 1.84/0.63  fof(f184,plain,(
% 1.84/0.63    ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK5)),
% 1.84/0.63    inference(subsumption_resolution,[],[f183,f57])).
% 1.84/0.63  fof(f183,plain,(
% 1.84/0.63    ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK5)),
% 1.84/0.63    inference(subsumption_resolution,[],[f182,f56])).
% 1.84/0.63  fof(f56,plain,(
% 1.84/0.63    ~v2_struct_0(sK3)),
% 1.84/0.63    inference(cnf_transformation,[],[f20])).
% 1.84/0.63  fof(f182,plain,(
% 1.84/0.63    v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK5)),
% 1.84/0.63    inference(subsumption_resolution,[],[f181,f59])).
% 1.84/0.63  fof(f181,plain,(
% 1.84/0.63    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK5)),
% 1.84/0.63    inference(subsumption_resolution,[],[f180,f58])).
% 1.84/0.63  fof(f58,plain,(
% 1.84/0.63    ~v2_struct_0(sK2)),
% 1.84/0.63    inference(cnf_transformation,[],[f20])).
% 1.84/0.63  fof(f180,plain,(
% 1.84/0.63    v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK5)),
% 1.84/0.63    inference(subsumption_resolution,[],[f179,f62])).
% 1.84/0.63  fof(f62,plain,(
% 1.84/0.63    l1_pre_topc(sK1)),
% 1.84/0.63    inference(cnf_transformation,[],[f20])).
% 1.84/0.63  fof(f179,plain,(
% 1.84/0.63    ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK5)),
% 1.84/0.63    inference(subsumption_resolution,[],[f178,f61])).
% 1.84/0.63  fof(f61,plain,(
% 1.84/0.63    v2_pre_topc(sK1)),
% 1.84/0.63    inference(cnf_transformation,[],[f20])).
% 1.84/0.63  fof(f178,plain,(
% 1.84/0.63    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK5)),
% 1.84/0.63    inference(subsumption_resolution,[],[f177,f60])).
% 1.84/0.63  fof(f60,plain,(
% 1.84/0.63    ~v2_struct_0(sK1)),
% 1.84/0.63    inference(cnf_transformation,[],[f20])).
% 1.84/0.63  fof(f177,plain,(
% 1.84/0.63    v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK5)),
% 1.84/0.63    inference(subsumption_resolution,[],[f176,f65])).
% 1.84/0.63  fof(f176,plain,(
% 1.84/0.63    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK5)),
% 1.84/0.63    inference(subsumption_resolution,[],[f175,f64])).
% 1.84/0.63  fof(f64,plain,(
% 1.84/0.63    v2_pre_topc(sK0)),
% 1.84/0.63    inference(cnf_transformation,[],[f20])).
% 1.84/0.63  fof(f175,plain,(
% 1.84/0.63    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK5)),
% 1.84/0.63    inference(resolution,[],[f89,f92])).
% 1.84/0.63  fof(f92,plain,(
% 1.84/0.63    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)),
% 1.84/0.63    inference(backward_demodulation,[],[f49,f48])).
% 1.84/0.63  fof(f49,plain,(
% 1.84/0.63    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 1.84/0.63    inference(cnf_transformation,[],[f20])).
% 1.84/0.63  fof(f89,plain,(
% 1.84/0.63    ( ! [X6,X4,X2,X0,X3,X1] : (~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_tsep_1(X2,X3) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | v2_struct_0(X0) | r1_tmap_1(X3,X1,X4,X6)) )),
% 1.84/0.63    inference(equality_resolution,[],[f75])).
% 1.84/0.63  fof(f75,plain,(
% 1.84/0.63    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_tsep_1(X2,X3) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | X5 != X6 | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) )),
% 1.84/0.63    inference(cnf_transformation,[],[f32])).
% 1.84/0.63  fof(f32,plain,(
% 1.84/0.63    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.84/0.63    inference(flattening,[],[f31])).
% 1.84/0.63  fof(f31,plain,(
% 1.84/0.63    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | (~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.84/0.63    inference(ennf_transformation,[],[f16])).
% 1.84/0.63  fof(f16,axiom,(
% 1.84/0.63    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 1.84/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tmap_1)).
% 1.84/0.63  fof(f971,plain,(
% 1.84/0.63    v1_tsep_1(sK2,sK3)),
% 1.84/0.63    inference(subsumption_resolution,[],[f970,f56])).
% 1.84/0.63  fof(f970,plain,(
% 1.84/0.63    v2_struct_0(sK3) | v1_tsep_1(sK2,sK3)),
% 1.84/0.63    inference(subsumption_resolution,[],[f968,f320])).
% 1.84/0.63  fof(f320,plain,(
% 1.84/0.63    m1_pre_topc(sK3,sK2)),
% 1.84/0.63    inference(forward_demodulation,[],[f319,f55])).
% 1.84/0.63  fof(f319,plain,(
% 1.84/0.63    m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK2)),
% 1.84/0.63    inference(subsumption_resolution,[],[f309,f105])).
% 1.84/0.63  fof(f309,plain,(
% 1.84/0.63    ~l1_pre_topc(sK2) | m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK2)),
% 1.84/0.63    inference(resolution,[],[f194,f74])).
% 1.84/0.63  fof(f74,plain,(
% 1.84/0.63    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)) )),
% 1.84/0.63    inference(cnf_transformation,[],[f30])).
% 1.84/0.63  fof(f968,plain,(
% 1.84/0.63    ~m1_pre_topc(sK3,sK2) | v2_struct_0(sK3) | v1_tsep_1(sK2,sK3)),
% 1.84/0.63    inference(resolution,[],[f449,f678])).
% 1.84/0.63  fof(f678,plain,(
% 1.84/0.63    r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))),
% 1.84/0.63    inference(resolution,[],[f651,f147])).
% 1.84/0.63  fof(f147,plain,(
% 1.84/0.63    ( ! [X0] : (~m1_pre_topc(X0,sK3) | r1_tarski(u1_struct_0(X0),u1_struct_0(sK3))) )),
% 1.84/0.63    inference(subsumption_resolution,[],[f146,f64])).
% 1.84/0.63  fof(f146,plain,(
% 1.84/0.63    ( ! [X0] : (~v2_pre_topc(sK0) | ~m1_pre_topc(X0,sK3) | r1_tarski(u1_struct_0(X0),u1_struct_0(sK3))) )),
% 1.84/0.63    inference(subsumption_resolution,[],[f144,f65])).
% 1.84/0.63  fof(f144,plain,(
% 1.84/0.63    ( ! [X0] : (~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_pre_topc(X0,sK3) | r1_tarski(u1_struct_0(X0),u1_struct_0(sK3))) )),
% 1.84/0.63    inference(resolution,[],[f94,f57])).
% 1.84/0.63  fof(f94,plain,(
% 1.84/0.63    ( ! [X2,X0,X1] : (~m1_pre_topc(X2,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X1,X2) | r1_tarski(u1_struct_0(X1),u1_struct_0(X2))) )),
% 1.84/0.63    inference(subsumption_resolution,[],[f84,f83])).
% 1.84/0.63  fof(f83,plain,(
% 1.84/0.63    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X2,X1) | m1_pre_topc(X2,X0)) )),
% 1.84/0.63    inference(cnf_transformation,[],[f42])).
% 1.84/0.63  fof(f42,plain,(
% 1.84/0.63    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.84/0.63    inference(flattening,[],[f41])).
% 1.84/0.63  fof(f41,plain,(
% 1.84/0.63    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.84/0.63    inference(ennf_transformation,[],[f15])).
% 1.84/0.63  fof(f15,axiom,(
% 1.84/0.63    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 1.84/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).
% 1.84/0.63  fof(f84,plain,(
% 1.84/0.63    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X2) | r1_tarski(u1_struct_0(X1),u1_struct_0(X2))) )),
% 1.84/0.63    inference(cnf_transformation,[],[f44])).
% 1.84/0.63  fof(f44,plain,(
% 1.84/0.63    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.84/0.63    inference(flattening,[],[f43])).
% 1.84/0.63  fof(f43,plain,(
% 1.84/0.63    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.84/0.63    inference(ennf_transformation,[],[f14])).
% 1.84/0.63  fof(f14,axiom,(
% 1.84/0.63    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 1.84/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).
% 1.84/0.63  fof(f449,plain,(
% 1.84/0.63    ( ! [X1] : (~r1_tarski(u1_struct_0(sK2),u1_struct_0(X1)) | ~m1_pre_topc(X1,sK2) | v2_struct_0(X1) | v1_tsep_1(sK2,X1)) )),
% 1.84/0.63    inference(subsumption_resolution,[],[f448,f194])).
% 1.84/0.63  fof(f448,plain,(
% 1.84/0.63    ( ! [X1] : (~m1_pre_topc(sK2,sK2) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK2) | ~r1_tarski(u1_struct_0(sK2),u1_struct_0(X1)) | v1_tsep_1(sK2,X1)) )),
% 1.84/0.63    inference(subsumption_resolution,[],[f447,f58])).
% 1.84/0.63  fof(f447,plain,(
% 1.84/0.63    ( ! [X1] : (v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK2) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK2) | ~r1_tarski(u1_struct_0(sK2),u1_struct_0(X1)) | v1_tsep_1(sK2,X1)) )),
% 1.84/0.63    inference(subsumption_resolution,[],[f446,f105])).
% 1.84/0.63  fof(f446,plain,(
% 1.84/0.63    ( ! [X1] : (~l1_pre_topc(sK2) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK2) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK2) | ~r1_tarski(u1_struct_0(sK2),u1_struct_0(X1)) | v1_tsep_1(sK2,X1)) )),
% 1.84/0.63    inference(subsumption_resolution,[],[f444,f116])).
% 1.84/0.63  fof(f116,plain,(
% 1.84/0.63    v2_pre_topc(sK2)),
% 1.84/0.63    inference(subsumption_resolution,[],[f115,f64])).
% 1.84/0.63  fof(f115,plain,(
% 1.84/0.63    ~v2_pre_topc(sK0) | v2_pre_topc(sK2)),
% 1.84/0.63    inference(subsumption_resolution,[],[f112,f65])).
% 1.84/0.63  fof(f112,plain,(
% 1.84/0.63    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_pre_topc(sK2)),
% 1.84/0.63    inference(resolution,[],[f82,f59])).
% 1.84/0.63  fof(f82,plain,(
% 1.84/0.63    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_pre_topc(X1)) )),
% 1.84/0.63    inference(cnf_transformation,[],[f40])).
% 1.84/0.63  fof(f40,plain,(
% 1.84/0.63    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.84/0.63    inference(flattening,[],[f39])).
% 1.84/0.63  fof(f39,plain,(
% 1.84/0.63    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.84/0.63    inference(ennf_transformation,[],[f2])).
% 1.84/0.63  fof(f2,axiom,(
% 1.84/0.63    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 1.84/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 1.84/0.63  fof(f444,plain,(
% 1.84/0.63    ( ! [X1] : (~v2_pre_topc(sK2) | ~l1_pre_topc(sK2) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK2) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK2) | ~r1_tarski(u1_struct_0(sK2),u1_struct_0(X1)) | v1_tsep_1(sK2,X1)) )),
% 1.84/0.63    inference(resolution,[],[f372,f77])).
% 2.23/0.63  fof(f77,plain,(
% 2.23/0.63    ( ! [X2,X0,X1] : (~v1_tsep_1(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | v1_tsep_1(X1,X2)) )),
% 2.23/0.63    inference(cnf_transformation,[],[f34])).
% 2.23/0.63  fof(f34,plain,(
% 2.23/0.63    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.23/0.63    inference(flattening,[],[f33])).
% 2.23/0.63  fof(f33,plain,(
% 2.23/0.63    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.23/0.63    inference(ennf_transformation,[],[f11])).
% 2.23/0.63  fof(f11,axiom,(
% 2.23/0.63    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) => (m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2))))))),
% 2.23/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_tsep_1)).
% 2.23/0.63  fof(f372,plain,(
% 2.23/0.63    v1_tsep_1(sK2,sK2)),
% 2.23/0.63    inference(subsumption_resolution,[],[f371,f116])).
% 2.23/0.63  fof(f371,plain,(
% 2.23/0.63    ~v2_pre_topc(sK2) | v1_tsep_1(sK2,sK2)),
% 2.23/0.63    inference(subsumption_resolution,[],[f370,f194])).
% 2.23/0.63  fof(f370,plain,(
% 2.23/0.63    ~m1_pre_topc(sK2,sK2) | ~v2_pre_topc(sK2) | v1_tsep_1(sK2,sK2)),
% 2.23/0.63    inference(subsumption_resolution,[],[f369,f105])).
% 2.23/0.63  fof(f369,plain,(
% 2.23/0.63    ~l1_pre_topc(sK2) | ~m1_pre_topc(sK2,sK2) | ~v2_pre_topc(sK2) | v1_tsep_1(sK2,sK2)),
% 2.23/0.63    inference(resolution,[],[f260,f95])).
% 2.23/0.63  fof(f95,plain,(
% 2.23/0.63    ( ! [X0,X1] : (~v3_pre_topc(u1_struct_0(X1),X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | v1_tsep_1(X1,X0)) )),
% 2.23/0.63    inference(subsumption_resolution,[],[f90,f72])).
% 2.23/0.63  fof(f72,plain,(
% 2.23/0.63    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 2.23/0.63    inference(cnf_transformation,[],[f29])).
% 2.23/0.63  fof(f29,plain,(
% 2.23/0.63    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.23/0.63    inference(ennf_transformation,[],[f12])).
% 2.23/0.63  fof(f12,axiom,(
% 2.23/0.63    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.23/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 2.23/0.63  fof(f90,plain,(
% 2.23/0.63    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(u1_struct_0(X1),X0) | v1_tsep_1(X1,X0)) )),
% 2.23/0.63    inference(equality_resolution,[],[f87])).
% 2.23/0.63  fof(f87,plain,(
% 2.23/0.63    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | ~v3_pre_topc(X2,X0) | v1_tsep_1(X1,X0)) )),
% 2.23/0.63    inference(cnf_transformation,[],[f46])).
% 2.23/0.63  fof(f46,plain,(
% 2.23/0.63    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.23/0.63    inference(flattening,[],[f45])).
% 2.23/0.63  fof(f45,plain,(
% 2.23/0.63    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.23/0.63    inference(ennf_transformation,[],[f10])).
% 2.23/0.63  fof(f10,axiom,(
% 2.23/0.63    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 2.23/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).
% 2.23/0.63  fof(f260,plain,(
% 2.23/0.63    v3_pre_topc(u1_struct_0(sK2),sK2)),
% 2.23/0.63    inference(backward_demodulation,[],[f203,f259])).
% 2.23/0.63  fof(f259,plain,(
% 2.23/0.63    u1_struct_0(sK2) = k2_struct_0(sK2)),
% 2.23/0.63    inference(resolution,[],[f195,f66])).
% 2.23/0.63  fof(f66,plain,(
% 2.23/0.63    ( ! [X0] : (~l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0)) )),
% 2.23/0.63    inference(cnf_transformation,[],[f21])).
% 2.23/0.63  fof(f21,plain,(
% 2.23/0.63    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 2.23/0.63    inference(ennf_transformation,[],[f3])).
% 2.23/0.63  fof(f3,axiom,(
% 2.23/0.63    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 2.23/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 2.23/0.63  fof(f195,plain,(
% 2.23/0.63    l1_struct_0(sK2)),
% 2.23/0.63    inference(resolution,[],[f105,f67])).
% 2.23/0.63  fof(f67,plain,(
% 2.23/0.63    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 2.23/0.63    inference(cnf_transformation,[],[f22])).
% 2.23/0.63  fof(f22,plain,(
% 2.23/0.63    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.23/0.63    inference(ennf_transformation,[],[f4])).
% 2.23/0.63  fof(f4,axiom,(
% 2.23/0.63    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.23/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 2.23/0.63  fof(f203,plain,(
% 2.23/0.63    v3_pre_topc(k2_struct_0(sK2),sK2)),
% 2.23/0.63    inference(subsumption_resolution,[],[f202,f105])).
% 2.23/0.63  fof(f202,plain,(
% 2.23/0.63    ~l1_pre_topc(sK2) | v3_pre_topc(k2_struct_0(sK2),sK2)),
% 2.23/0.63    inference(resolution,[],[f116,f81])).
% 2.23/0.63  fof(f81,plain,(
% 2.23/0.63    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v3_pre_topc(k2_struct_0(X0),X0)) )),
% 2.23/0.63    inference(cnf_transformation,[],[f38])).
% 2.23/0.63  fof(f38,plain,(
% 2.23/0.63    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.23/0.63    inference(flattening,[],[f37])).
% 2.23/0.63  fof(f37,plain,(
% 2.23/0.63    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.23/0.63    inference(ennf_transformation,[],[f8])).
% 2.23/0.63  fof(f8,axiom,(
% 2.23/0.63    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 2.23/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).
% 2.23/0.63  % SZS output end Proof for theBenchmark
% 2.23/0.63  % (26637)------------------------------
% 2.23/0.63  % (26637)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.23/0.63  % (26637)Termination reason: Refutation
% 2.23/0.63  
% 2.23/0.63  % (26637)Memory used [KB]: 2046
% 2.23/0.63  % (26637)Time elapsed: 0.182 s
% 2.23/0.63  % (26637)------------------------------
% 2.23/0.63  % (26637)------------------------------
% 2.23/0.64  % (26619)Success in time 0.282 s
%------------------------------------------------------------------------------
