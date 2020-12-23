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
% DateTime   : Thu Dec  3 13:18:49 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  160 ( 852 expanded)
%              Number of leaves         :   13 ( 151 expanded)
%              Depth                    :   39
%              Number of atoms          : 1045 (12617 expanded)
%              Number of equality atoms :   49 ( 537 expanded)
%              Maximal formula depth    :   31 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f259,plain,(
    $false ),
    inference(subsumption_resolution,[],[f258,f237])).

fof(f237,plain,(
    ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),sK6) ),
    inference(subsumption_resolution,[],[f233,f205])).

fof(f205,plain,(
    r1_tmap_1(sK3,sK1,sK4,sK6) ),
    inference(resolution,[],[f203,f156])).

fof(f156,plain,
    ( ~ sP9(sK3,sK2,sK6)
    | r1_tmap_1(sK3,sK1,sK4,sK6) ),
    inference(subsumption_resolution,[],[f155,f57])).

fof(f57,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( r1_tmap_1(X3,X1,X4,X6)
                                  <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                  & X6 = X7
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X3)
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      & m1_pre_topc(X2,X3)
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( r1_tmap_1(X3,X1,X4,X6)
                                  <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                  & X6 = X7
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X3)
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      & m1_pre_topc(X2,X3)
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
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
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
                       => ( m1_pre_topc(X2,X3)
                         => ! [X5] :
                              ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X3))
                                 => ! [X7] :
                                      ( m1_subset_1(X7,u1_struct_0(X2))
                                     => ( ( X6 = X7
                                          & r1_tarski(X5,u1_struct_0(X2))
                                          & r2_hidden(X6,X5)
                                          & v3_pre_topc(X5,X3) )
                                       => ( r1_tmap_1(X3,X1,X4,X6)
                                        <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
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
                     => ( m1_pre_topc(X2,X3)
                       => ! [X5] :
                            ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X3))
                               => ! [X7] :
                                    ( m1_subset_1(X7,u1_struct_0(X2))
                                   => ( ( X6 = X7
                                        & r1_tarski(X5,u1_struct_0(X2))
                                        & r2_hidden(X6,X5)
                                        & v3_pre_topc(X5,X3) )
                                     => ( r1_tmap_1(X3,X1,X4,X6)
                                      <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tmap_1)).

fof(f155,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK6)
    | v2_struct_0(sK0)
    | ~ sP9(sK3,sK2,sK6) ),
    inference(subsumption_resolution,[],[f154,f85])).

fof(f85,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f39,f43])).

fof(f43,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f16])).

fof(f39,plain,(
    m1_subset_1(sK7,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f154,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | ~ sP9(sK3,sK2,sK6) ),
    inference(subsumption_resolution,[],[f153,f44])).

fof(f44,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f16])).

fof(f153,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | ~ sP9(sK3,sK2,sK6) ),
    inference(subsumption_resolution,[],[f152,f49])).

fof(f49,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f152,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK6)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | ~ sP9(sK3,sK2,sK6) ),
    inference(subsumption_resolution,[],[f151,f48])).

fof(f48,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f16])).

fof(f151,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK6)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | ~ sP9(sK3,sK2,sK6) ),
    inference(subsumption_resolution,[],[f150,f47])).

fof(f47,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f150,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK6)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | ~ sP9(sK3,sK2,sK6) ),
    inference(subsumption_resolution,[],[f149,f46])).

fof(f46,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f16])).

fof(f149,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK6)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | ~ sP9(sK3,sK2,sK6) ),
    inference(subsumption_resolution,[],[f148,f51])).

fof(f51,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f148,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK6)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | ~ sP9(sK3,sK2,sK6) ),
    inference(subsumption_resolution,[],[f147,f50])).

fof(f50,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f147,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK6)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | ~ sP9(sK3,sK2,sK6) ),
    inference(subsumption_resolution,[],[f146,f53])).

fof(f53,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f146,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK6)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | ~ sP9(sK3,sK2,sK6) ),
    inference(subsumption_resolution,[],[f145,f52])).

fof(f52,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f145,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK6)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | ~ sP9(sK3,sK2,sK6) ),
    inference(subsumption_resolution,[],[f144,f56])).

fof(f56,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f144,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK6)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | ~ sP9(sK3,sK2,sK6) ),
    inference(subsumption_resolution,[],[f143,f55])).

fof(f55,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f143,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK6)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | ~ sP9(sK3,sK2,sK6) ),
    inference(subsumption_resolution,[],[f142,f54])).

fof(f54,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f142,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK6)
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
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | ~ sP9(sK3,sK2,sK6) ),
    inference(subsumption_resolution,[],[f141,f59])).

fof(f59,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f141,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK6)
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
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | ~ sP9(sK3,sK2,sK6) ),
    inference(subsumption_resolution,[],[f140,f58])).

fof(f58,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f140,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK6)
    | ~ v2_pre_topc(sK0)
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
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | ~ sP9(sK3,sK2,sK6) ),
    inference(duplicate_literal_removal,[],[f137])).

fof(f137,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK6)
    | ~ v2_pre_topc(sK0)
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
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | r1_tmap_1(sK3,sK1,sK4,sK6)
    | ~ sP9(sK3,sK2,sK6) ),
    inference(resolution,[],[f87,f84])).

fof(f84,plain,(
    ! [X4,X2,X0,X7,X3,X1] :
      ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
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
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | v2_struct_0(X0)
      | r1_tmap_1(X3,X1,X4,X7)
      | ~ sP9(X3,X2,X7) ) ),
    inference(general_splitting,[],[f77,f83_D])).

fof(f83,plain,(
    ! [X2,X7,X5,X3] :
      ( ~ m1_connsp_2(X5,X3,X7)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | sP9(X3,X2,X7) ) ),
    inference(cnf_transformation,[],[f83_D])).

fof(f83_D,plain,(
    ! [X7,X2,X3] :
      ( ! [X5] :
          ( ~ m1_connsp_2(X5,X3,X7)
          | ~ r1_tarski(X5,u1_struct_0(X2))
          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
    <=> ~ sP9(X3,X2,X7) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP9])])).

fof(f77,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
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
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ m1_connsp_2(X5,X3,X7)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | r1_tmap_1(X3,X1,X4,X7) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
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
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ m1_connsp_2(X5,X3,X6)
      | X6 != X7
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | r1_tmap_1(X3,X1,X4,X6) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tmap_1(X3,X1,X4,X6)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                  | X6 != X7
                                  | ~ m1_connsp_2(X5,X3,X6)
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      | ~ m1_pre_topc(X2,X3)
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tmap_1(X3,X1,X4,X6)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                  | X6 != X7
                                  | ~ m1_connsp_2(X5,X3,X6)
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      | ~ m1_pre_topc(X2,X3)
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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
                     => ( m1_pre_topc(X2,X3)
                       => ! [X5] :
                            ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X3))
                               => ! [X7] :
                                    ( m1_subset_1(X7,u1_struct_0(X2))
                                   => ( ( X6 = X7
                                        & m1_connsp_2(X5,X3,X6)
                                        & r1_tarski(X5,u1_struct_0(X2)) )
                                     => ( r1_tmap_1(X3,X1,X4,X6)
                                      <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_tmap_1)).

fof(f87,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)
    | r1_tmap_1(sK3,sK1,sK4,sK6) ),
    inference(forward_demodulation,[],[f37,f43])).

fof(f37,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7)
    | r1_tmap_1(sK3,sK1,sK4,sK6) ),
    inference(cnf_transformation,[],[f16])).

fof(f203,plain,(
    sP9(sK3,sK2,sK6) ),
    inference(resolution,[],[f201,f42])).

fof(f42,plain,(
    r1_tarski(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f201,plain,(
    ! [X1] :
      ( ~ r1_tarski(sK5,u1_struct_0(X1))
      | sP9(sK3,X1,sK6) ) ),
    inference(subsumption_resolution,[],[f193,f45])).

fof(f45,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f16])).

fof(f193,plain,(
    ! [X1] :
      ( ~ r1_tarski(sK5,u1_struct_0(X1))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
      | sP9(sK3,X1,sK6) ) ),
    inference(resolution,[],[f190,f83])).

fof(f190,plain,(
    m1_connsp_2(sK5,sK3,sK6) ),
    inference(subsumption_resolution,[],[f189,f44])).

fof(f189,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | m1_connsp_2(sK5,sK3,sK6) ),
    inference(resolution,[],[f188,f41])).

fof(f41,plain,(
    r2_hidden(sK6,sK5) ),
    inference(cnf_transformation,[],[f16])).

fof(f188,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK5)
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | m1_connsp_2(sK5,sK3,X0) ) ),
    inference(subsumption_resolution,[],[f187,f50])).

fof(f187,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK5)
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | v2_struct_0(sK3)
      | m1_connsp_2(sK5,sK3,X0) ) ),
    inference(subsumption_resolution,[],[f186,f45])).

fof(f186,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK5)
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
      | v2_struct_0(sK3)
      | m1_connsp_2(sK5,sK3,X0) ) ),
    inference(subsumption_resolution,[],[f185,f96])).

fof(f96,plain,(
    l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f93,f59])).

fof(f93,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK3) ),
    inference(resolution,[],[f51,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f185,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK5)
      | ~ l1_pre_topc(sK3)
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
      | v2_struct_0(sK3)
      | m1_connsp_2(sK5,sK3,X0) ) ),
    inference(subsumption_resolution,[],[f184,f98])).

fof(f98,plain,(
    v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f97,f58])).

fof(f97,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f94,f59])).

fof(f94,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK3) ),
    inference(resolution,[],[f51,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f184,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK5)
      | ~ v2_pre_topc(sK3)
      | ~ l1_pre_topc(sK3)
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
      | v2_struct_0(sK3)
      | m1_connsp_2(sK5,sK3,X0) ) ),
    inference(superposition,[],[f68,f180])).

fof(f180,plain,(
    sK5 = k1_tops_1(sK3,sK5) ),
    inference(resolution,[],[f179,f117])).

fof(f117,plain,
    ( ~ r1_tarski(sK5,k1_tops_1(sK3,sK5))
    | sK5 = k1_tops_1(sK3,sK5) ),
    inference(resolution,[],[f116,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f116,plain,(
    r1_tarski(k1_tops_1(sK3,sK5),sK5) ),
    inference(subsumption_resolution,[],[f115,f96])).

fof(f115,plain,
    ( ~ l1_pre_topc(sK3)
    | r1_tarski(k1_tops_1(sK3,sK5),sK5) ),
    inference(resolution,[],[f45,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f179,plain,(
    r1_tarski(sK5,k1_tops_1(sK3,sK5)) ),
    inference(subsumption_resolution,[],[f178,f80])).

fof(f80,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f178,plain,
    ( ~ r1_tarski(sK5,sK5)
    | r1_tarski(sK5,k1_tops_1(sK3,sK5)) ),
    inference(subsumption_resolution,[],[f177,f96])).

fof(f177,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ r1_tarski(sK5,sK5)
    | r1_tarski(sK5,k1_tops_1(sK3,sK5)) ),
    inference(resolution,[],[f89,f45])).

fof(f89,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ l1_pre_topc(sK3)
      | ~ r1_tarski(sK5,X0)
      | r1_tarski(sK5,k1_tops_1(sK3,X0)) ) ),
    inference(subsumption_resolution,[],[f88,f45])).

fof(f88,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ l1_pre_topc(sK3)
      | ~ r1_tarski(sK5,X0)
      | r1_tarski(sK5,k1_tops_1(sK3,X0)) ) ),
    inference(resolution,[],[f40,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X1,k1_tops_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).

fof(f40,plain,(
    v3_pre_topc(sK5,sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0)
      | m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
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
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).

fof(f233,plain,
    ( ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),sK6)
    | ~ r1_tmap_1(sK3,sK1,sK4,sK6) ),
    inference(backward_demodulation,[],[f86,f232])).

fof(f232,plain,(
    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_tmap_1(sK3,sK1,sK4,sK2) ),
    inference(forward_demodulation,[],[f231,f204])).

fof(f204,plain,(
    k2_tmap_1(sK3,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) ),
    inference(resolution,[],[f127,f49])).

fof(f127,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | k2_tmap_1(sK3,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f126,f48])).

fof(f126,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X0,sK3)
      | k2_tmap_1(sK3,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f125,f50])).

fof(f125,plain,(
    ! [X0] :
      ( v2_struct_0(sK3)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X0,sK3)
      | k2_tmap_1(sK3,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f124,f46])).

fof(f124,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK4)
      | v2_struct_0(sK3)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X0,sK3)
      | k2_tmap_1(sK3,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f123,f56])).

fof(f123,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK4)
      | v2_struct_0(sK3)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X0,sK3)
      | k2_tmap_1(sK3,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f122,f55])).

fof(f122,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK4)
      | v2_struct_0(sK3)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X0,sK3)
      | k2_tmap_1(sK3,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f121,f54])).

fof(f121,plain,(
    ! [X0] :
      ( v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK4)
      | v2_struct_0(sK3)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X0,sK3)
      | k2_tmap_1(sK3,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f120,f96])).

fof(f120,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK3)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK4)
      | v2_struct_0(sK3)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X0,sK3)
      | k2_tmap_1(sK3,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f118,f98])).

fof(f118,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK3)
      | ~ l1_pre_topc(sK3)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK4)
      | v2_struct_0(sK3)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X0,sK3)
      | k2_tmap_1(sK3,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) ) ),
    inference(resolution,[],[f47,f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X0)
      | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f231,plain,(
    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) ),
    inference(resolution,[],[f209,f49])).

fof(f209,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK4) ) ),
    inference(subsumption_resolution,[],[f208,f57])).

fof(f208,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ m1_pre_topc(X0,sK3)
      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK4) ) ),
    inference(subsumption_resolution,[],[f207,f58])).

fof(f207,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_pre_topc(X0,sK3)
      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK4) ) ),
    inference(subsumption_resolution,[],[f206,f59])).

fof(f206,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_pre_topc(X0,sK3)
      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK4) ) ),
    inference(resolution,[],[f133,f51])).

fof(f133,plain,(
    ! [X2,X1] :
      ( ~ m1_pre_topc(sK3,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X2,sK3)
      | k3_tmap_1(X1,sK1,sK3,X2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X2)) ) ),
    inference(subsumption_resolution,[],[f132,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X2,X1)
      | m1_pre_topc(X2,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
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
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f132,plain,(
    ! [X2,X1] :
      ( ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(sK3,X1)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X2,sK3)
      | k3_tmap_1(X1,sK1,sK3,X2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X2)) ) ),
    inference(subsumption_resolution,[],[f131,f48])).

fof(f131,plain,(
    ! [X2,X1] :
      ( ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(sK3,X1)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X2,sK3)
      | k3_tmap_1(X1,sK1,sK3,X2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X2)) ) ),
    inference(subsumption_resolution,[],[f130,f46])).

fof(f130,plain,(
    ! [X2,X1] :
      ( ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(sK3,X1)
      | ~ m1_pre_topc(X2,X1)
      | ~ v1_funct_1(sK4)
      | v2_struct_0(X1)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X2,sK3)
      | k3_tmap_1(X1,sK1,sK3,X2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X2)) ) ),
    inference(subsumption_resolution,[],[f129,f56])).

fof(f129,plain,(
    ! [X2,X1] :
      ( ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(sK1)
      | ~ m1_pre_topc(sK3,X1)
      | ~ m1_pre_topc(X2,X1)
      | ~ v1_funct_1(sK4)
      | v2_struct_0(X1)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X2,sK3)
      | k3_tmap_1(X1,sK1,sK3,X2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X2)) ) ),
    inference(subsumption_resolution,[],[f128,f55])).

fof(f128,plain,(
    ! [X2,X1] :
      ( ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ m1_pre_topc(sK3,X1)
      | ~ m1_pre_topc(X2,X1)
      | ~ v1_funct_1(sK4)
      | v2_struct_0(X1)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X2,sK3)
      | k3_tmap_1(X1,sK1,sK3,X2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X2)) ) ),
    inference(subsumption_resolution,[],[f119,f54])).

fof(f119,plain,(
    ! [X2,X1] :
      ( ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ m1_pre_topc(sK3,X1)
      | ~ m1_pre_topc(X2,X1)
      | ~ v1_funct_1(sK4)
      | v2_struct_0(X1)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X2,sK3)
      | k3_tmap_1(X1,sK1,sK3,X2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X2)) ) ),
    inference(resolution,[],[f47,f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X2)
      | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).

fof(f86,plain,
    ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)
    | ~ r1_tmap_1(sK3,sK1,sK4,sK6) ),
    inference(forward_demodulation,[],[f38,f43])).

fof(f38,plain,
    ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7)
    | ~ r1_tmap_1(sK3,sK1,sK4,sK6) ),
    inference(cnf_transformation,[],[f16])).

fof(f258,plain,(
    r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),sK6) ),
    inference(subsumption_resolution,[],[f257,f52])).

fof(f257,plain,
    ( v2_struct_0(sK2)
    | r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),sK6) ),
    inference(subsumption_resolution,[],[f254,f49])).

fof(f254,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | v2_struct_0(sK2)
    | r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),sK6) ),
    inference(resolution,[],[f221,f85])).

fof(f221,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK6,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,sK3)
      | v2_struct_0(X0)
      | r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,sK4,X0),sK6) ) ),
    inference(subsumption_resolution,[],[f220,f54])).

fof(f220,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK3)
      | ~ m1_subset_1(sK6,u1_struct_0(X0))
      | v2_struct_0(sK1)
      | r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,sK4,X0),sK6) ) ),
    inference(subsumption_resolution,[],[f219,f44])).

fof(f219,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK3)
      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
      | ~ m1_subset_1(sK6,u1_struct_0(X0))
      | v2_struct_0(sK1)
      | r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,sK4,X0),sK6) ) ),
    inference(subsumption_resolution,[],[f218,f48])).

fof(f218,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK3)
      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
      | ~ m1_subset_1(sK6,u1_struct_0(X0))
      | v2_struct_0(sK1)
      | r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,sK4,X0),sK6) ) ),
    inference(subsumption_resolution,[],[f217,f47])).

fof(f217,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK3)
      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
      | ~ m1_subset_1(sK6,u1_struct_0(X0))
      | v2_struct_0(sK1)
      | r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,sK4,X0),sK6) ) ),
    inference(subsumption_resolution,[],[f216,f46])).

fof(f216,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK4)
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK3)
      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
      | ~ m1_subset_1(sK6,u1_struct_0(X0))
      | v2_struct_0(sK1)
      | r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,sK4,X0),sK6) ) ),
    inference(subsumption_resolution,[],[f215,f96])).

fof(f215,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK3)
      | ~ v1_funct_1(sK4)
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK3)
      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
      | ~ m1_subset_1(sK6,u1_struct_0(X0))
      | v2_struct_0(sK1)
      | r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,sK4,X0),sK6) ) ),
    inference(subsumption_resolution,[],[f214,f98])).

fof(f214,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK3)
      | ~ l1_pre_topc(sK3)
      | ~ v1_funct_1(sK4)
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK3)
      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
      | ~ m1_subset_1(sK6,u1_struct_0(X0))
      | v2_struct_0(sK1)
      | r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,sK4,X0),sK6) ) ),
    inference(subsumption_resolution,[],[f213,f50])).

fof(f213,plain,(
    ! [X0] :
      ( v2_struct_0(sK3)
      | ~ v2_pre_topc(sK3)
      | ~ l1_pre_topc(sK3)
      | ~ v1_funct_1(sK4)
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK3)
      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
      | ~ m1_subset_1(sK6,u1_struct_0(X0))
      | v2_struct_0(sK1)
      | r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,sK4,X0),sK6) ) ),
    inference(subsumption_resolution,[],[f212,f56])).

fof(f212,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK1)
      | v2_struct_0(sK3)
      | ~ v2_pre_topc(sK3)
      | ~ l1_pre_topc(sK3)
      | ~ v1_funct_1(sK4)
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK3)
      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
      | ~ m1_subset_1(sK6,u1_struct_0(X0))
      | v2_struct_0(sK1)
      | r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,sK4,X0),sK6) ) ),
    inference(subsumption_resolution,[],[f210,f55])).

fof(f210,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK3)
      | ~ v2_pre_topc(sK3)
      | ~ l1_pre_topc(sK3)
      | ~ v1_funct_1(sK4)
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK3)
      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
      | ~ m1_subset_1(sK6,u1_struct_0(X0))
      | v2_struct_0(sK1)
      | r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,sK4,X0),sK6) ) ),
    inference(resolution,[],[f205,f78])).

fof(f78,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ r1_tmap_1(X1,X0,X2,X5)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | v2_struct_0(X0)
      | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | X4 != X5
      | ~ r1_tmap_1(X1,X0,X2,X4)
      | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                          | ~ r1_tmap_1(X1,X0,X2,X4)
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                          | ~ r1_tmap_1(X1,X0,X2,X4)
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X3))
                         => ( ( r1_tmap_1(X1,X0,X2,X4)
                              & X4 = X5 )
                           => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tmap_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:32:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (27990)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.50  % (27980)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.50  % (27982)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (27983)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (27989)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.50  % (27985)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.50  % (27979)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (27992)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (27996)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.51  % (27981)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (27998)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.51  % (28002)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.51  % (27984)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.51  % (28000)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.51  % (27988)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.52  % (27983)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (28001)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.52  % (27985)Refutation not found, incomplete strategy% (27985)------------------------------
% 0.21/0.52  % (27985)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (27985)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (27985)Memory used [KB]: 1791
% 0.21/0.52  % (27985)Time elapsed: 0.102 s
% 0.21/0.52  % (27985)------------------------------
% 0.21/0.52  % (27985)------------------------------
% 0.21/0.52  % (27991)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (27978)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.52  % (27997)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.52  % (27993)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f259,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(subsumption_resolution,[],[f258,f237])).
% 0.21/0.53  fof(f237,plain,(
% 0.21/0.53    ~r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),sK6)),
% 0.21/0.53    inference(subsumption_resolution,[],[f233,f205])).
% 0.21/0.53  fof(f205,plain,(
% 0.21/0.53    r1_tmap_1(sK3,sK1,sK4,sK6)),
% 0.21/0.53    inference(resolution,[],[f203,f156])).
% 0.21/0.53  fof(f156,plain,(
% 0.21/0.53    ~sP9(sK3,sK2,sK6) | r1_tmap_1(sK3,sK1,sK4,sK6)),
% 0.21/0.53    inference(subsumption_resolution,[],[f155,f57])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    ~v2_struct_0(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((r1_tmap_1(X3,X1,X4,X6) <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (? [X7] : (((r1_tmap_1(X3,X1,X4,X6) <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3))) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,negated_conjecture,(
% 0.21/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3)) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 0.21/0.53    inference(negated_conjecture,[],[f13])).
% 0.21/0.53  fof(f13,conjecture,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3)) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tmap_1)).
% 0.21/0.53  fof(f155,plain,(
% 0.21/0.53    r1_tmap_1(sK3,sK1,sK4,sK6) | v2_struct_0(sK0) | ~sP9(sK3,sK2,sK6)),
% 0.21/0.53    inference(subsumption_resolution,[],[f154,f85])).
% 0.21/0.53  fof(f85,plain,(
% 0.21/0.53    m1_subset_1(sK6,u1_struct_0(sK2))),
% 0.21/0.53    inference(forward_demodulation,[],[f39,f43])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    sK6 = sK7),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    m1_subset_1(sK7,u1_struct_0(sK2))),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f154,plain,(
% 0.21/0.53    r1_tmap_1(sK3,sK1,sK4,sK6) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | v2_struct_0(sK0) | ~sP9(sK3,sK2,sK6)),
% 0.21/0.53    inference(subsumption_resolution,[],[f153,f44])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    m1_subset_1(sK6,u1_struct_0(sK3))),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f153,plain,(
% 0.21/0.53    r1_tmap_1(sK3,sK1,sK4,sK6) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | v2_struct_0(sK0) | ~sP9(sK3,sK2,sK6)),
% 0.21/0.53    inference(subsumption_resolution,[],[f152,f49])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    m1_pre_topc(sK2,sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f152,plain,(
% 0.21/0.53    r1_tmap_1(sK3,sK1,sK4,sK6) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | v2_struct_0(sK0) | ~sP9(sK3,sK2,sK6)),
% 0.21/0.53    inference(subsumption_resolution,[],[f151,f48])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f151,plain,(
% 0.21/0.53    r1_tmap_1(sK3,sK1,sK4,sK6) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | v2_struct_0(sK0) | ~sP9(sK3,sK2,sK6)),
% 0.21/0.53    inference(subsumption_resolution,[],[f150,f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f150,plain,(
% 0.21/0.53    r1_tmap_1(sK3,sK1,sK4,sK6) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | v2_struct_0(sK0) | ~sP9(sK3,sK2,sK6)),
% 0.21/0.53    inference(subsumption_resolution,[],[f149,f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    v1_funct_1(sK4)),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f149,plain,(
% 0.21/0.53    r1_tmap_1(sK3,sK1,sK4,sK6) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | v2_struct_0(sK0) | ~sP9(sK3,sK2,sK6)),
% 0.21/0.53    inference(subsumption_resolution,[],[f148,f51])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    m1_pre_topc(sK3,sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f148,plain,(
% 0.21/0.53    r1_tmap_1(sK3,sK1,sK4,sK6) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | v2_struct_0(sK0) | ~sP9(sK3,sK2,sK6)),
% 0.21/0.53    inference(subsumption_resolution,[],[f147,f50])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ~v2_struct_0(sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f147,plain,(
% 0.21/0.53    r1_tmap_1(sK3,sK1,sK4,sK6) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | v2_struct_0(sK0) | ~sP9(sK3,sK2,sK6)),
% 0.21/0.53    inference(subsumption_resolution,[],[f146,f53])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    m1_pre_topc(sK2,sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f146,plain,(
% 0.21/0.53    r1_tmap_1(sK3,sK1,sK4,sK6) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | v2_struct_0(sK0) | ~sP9(sK3,sK2,sK6)),
% 0.21/0.53    inference(subsumption_resolution,[],[f145,f52])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ~v2_struct_0(sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f145,plain,(
% 0.21/0.53    r1_tmap_1(sK3,sK1,sK4,sK6) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | v2_struct_0(sK0) | ~sP9(sK3,sK2,sK6)),
% 0.21/0.53    inference(subsumption_resolution,[],[f144,f56])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    l1_pre_topc(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f144,plain,(
% 0.21/0.53    r1_tmap_1(sK3,sK1,sK4,sK6) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | v2_struct_0(sK0) | ~sP9(sK3,sK2,sK6)),
% 0.21/0.53    inference(subsumption_resolution,[],[f143,f55])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    v2_pre_topc(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f143,plain,(
% 0.21/0.53    r1_tmap_1(sK3,sK1,sK4,sK6) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | v2_struct_0(sK0) | ~sP9(sK3,sK2,sK6)),
% 0.21/0.53    inference(subsumption_resolution,[],[f142,f54])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ~v2_struct_0(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f142,plain,(
% 0.21/0.53    r1_tmap_1(sK3,sK1,sK4,sK6) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | v2_struct_0(sK0) | ~sP9(sK3,sK2,sK6)),
% 0.21/0.53    inference(subsumption_resolution,[],[f141,f59])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    l1_pre_topc(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f141,plain,(
% 0.21/0.53    r1_tmap_1(sK3,sK1,sK4,sK6) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | v2_struct_0(sK0) | ~sP9(sK3,sK2,sK6)),
% 0.21/0.53    inference(subsumption_resolution,[],[f140,f58])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    v2_pre_topc(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f140,plain,(
% 0.21/0.53    r1_tmap_1(sK3,sK1,sK4,sK6) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | v2_struct_0(sK0) | ~sP9(sK3,sK2,sK6)),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f137])).
% 0.21/0.53  fof(f137,plain,(
% 0.21/0.53    r1_tmap_1(sK3,sK1,sK4,sK6) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK6) | ~sP9(sK3,sK2,sK6)),
% 0.21/0.53    inference(resolution,[],[f87,f84])).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X7,X3,X1] : (~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(X2)) | v2_struct_0(X0) | r1_tmap_1(X3,X1,X4,X7) | ~sP9(X3,X2,X7)) )),
% 0.21/0.53    inference(general_splitting,[],[f77,f83_D])).
% 0.21/0.53  fof(f83,plain,(
% 0.21/0.53    ( ! [X2,X7,X5,X3] : (~m1_connsp_2(X5,X3,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | sP9(X3,X2,X7)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f83_D])).
% 0.21/0.53  fof(f83_D,plain,(
% 0.21/0.53    ( ! [X7,X2,X3] : (( ! [X5] : (~m1_connsp_2(X5,X3,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) ) <=> ~sP9(X3,X2,X7)) )),
% 0.21/0.53    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP9])])).
% 0.21/0.53  fof(f77,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X7,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_connsp_2(X5,X3,X7) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X7)) )),
% 0.21/0.53    inference(equality_resolution,[],[f60])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_connsp_2(X5,X3,X6) | X6 != X7 | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | (X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & m1_connsp_2(X5,X3,X6) & r1_tarski(X5,u1_struct_0(X2))) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_tmap_1)).
% 0.21/0.53  fof(f87,plain,(
% 0.21/0.53    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) | r1_tmap_1(sK3,sK1,sK4,sK6)),
% 0.21/0.53    inference(forward_demodulation,[],[f37,f43])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) | r1_tmap_1(sK3,sK1,sK4,sK6)),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f203,plain,(
% 0.21/0.53    sP9(sK3,sK2,sK6)),
% 0.21/0.53    inference(resolution,[],[f201,f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    r1_tarski(sK5,u1_struct_0(sK2))),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f201,plain,(
% 0.21/0.53    ( ! [X1] : (~r1_tarski(sK5,u1_struct_0(X1)) | sP9(sK3,X1,sK6)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f193,f45])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f193,plain,(
% 0.21/0.53    ( ! [X1] : (~r1_tarski(sK5,u1_struct_0(X1)) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) | sP9(sK3,X1,sK6)) )),
% 0.21/0.53    inference(resolution,[],[f190,f83])).
% 0.21/0.53  fof(f190,plain,(
% 0.21/0.53    m1_connsp_2(sK5,sK3,sK6)),
% 0.21/0.53    inference(subsumption_resolution,[],[f189,f44])).
% 0.21/0.53  fof(f189,plain,(
% 0.21/0.53    ~m1_subset_1(sK6,u1_struct_0(sK3)) | m1_connsp_2(sK5,sK3,sK6)),
% 0.21/0.53    inference(resolution,[],[f188,f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    r2_hidden(sK6,sK5)),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f188,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(X0,sK5) | ~m1_subset_1(X0,u1_struct_0(sK3)) | m1_connsp_2(sK5,sK3,X0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f187,f50])).
% 0.21/0.53  fof(f187,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(X0,sK5) | ~m1_subset_1(X0,u1_struct_0(sK3)) | v2_struct_0(sK3) | m1_connsp_2(sK5,sK3,X0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f186,f45])).
% 0.21/0.53  fof(f186,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(X0,sK5) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) | v2_struct_0(sK3) | m1_connsp_2(sK5,sK3,X0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f185,f96])).
% 0.21/0.53  fof(f96,plain,(
% 0.21/0.53    l1_pre_topc(sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f93,f59])).
% 0.21/0.53  fof(f93,plain,(
% 0.21/0.53    ~l1_pre_topc(sK0) | l1_pre_topc(sK3)),
% 0.21/0.53    inference(resolution,[],[f51,f74])).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.53  fof(f185,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(X0,sK5) | ~l1_pre_topc(sK3) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) | v2_struct_0(sK3) | m1_connsp_2(sK5,sK3,X0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f184,f98])).
% 0.21/0.53  fof(f98,plain,(
% 0.21/0.53    v2_pre_topc(sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f97,f58])).
% 0.21/0.53  fof(f97,plain,(
% 0.21/0.53    ~v2_pre_topc(sK0) | v2_pre_topc(sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f94,f59])).
% 0.21/0.53  fof(f94,plain,(
% 0.21/0.53    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_pre_topc(sK3)),
% 0.21/0.53    inference(resolution,[],[f51,f73])).
% 0.21/0.53  fof(f73,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_pre_topc(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.21/0.53  fof(f184,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(X0,sK5) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) | v2_struct_0(sK3) | m1_connsp_2(sK5,sK3,X0)) )),
% 0.21/0.53    inference(superposition,[],[f68,f180])).
% 0.21/0.53  fof(f180,plain,(
% 0.21/0.53    sK5 = k1_tops_1(sK3,sK5)),
% 0.21/0.53    inference(resolution,[],[f179,f117])).
% 0.21/0.53  fof(f117,plain,(
% 0.21/0.53    ~r1_tarski(sK5,k1_tops_1(sK3,sK5)) | sK5 = k1_tops_1(sK3,sK5)),
% 0.21/0.53    inference(resolution,[],[f116,f66])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.53  fof(f116,plain,(
% 0.21/0.53    r1_tarski(k1_tops_1(sK3,sK5),sK5)),
% 0.21/0.53    inference(subsumption_resolution,[],[f115,f96])).
% 0.21/0.53  fof(f115,plain,(
% 0.21/0.53    ~l1_pre_topc(sK3) | r1_tarski(k1_tops_1(sK3,sK5),sK5)),
% 0.21/0.53    inference(resolution,[],[f45,f67])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 0.21/0.53  fof(f179,plain,(
% 0.21/0.53    r1_tarski(sK5,k1_tops_1(sK3,sK5))),
% 0.21/0.53    inference(subsumption_resolution,[],[f178,f80])).
% 0.21/0.53  fof(f80,plain,(
% 0.21/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.53    inference(equality_resolution,[],[f64])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f178,plain,(
% 0.21/0.53    ~r1_tarski(sK5,sK5) | r1_tarski(sK5,k1_tops_1(sK3,sK5))),
% 0.21/0.53    inference(subsumption_resolution,[],[f177,f96])).
% 0.21/0.53  fof(f177,plain,(
% 0.21/0.53    ~l1_pre_topc(sK3) | ~r1_tarski(sK5,sK5) | r1_tarski(sK5,k1_tops_1(sK3,sK5))),
% 0.21/0.53    inference(resolution,[],[f89,f45])).
% 0.21/0.53  fof(f89,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~l1_pre_topc(sK3) | ~r1_tarski(sK5,X0) | r1_tarski(sK5,k1_tops_1(sK3,X0))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f88,f45])).
% 0.21/0.53  fof(f88,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~l1_pre_topc(sK3) | ~r1_tarski(sK5,X0) | r1_tarski(sK5,k1_tops_1(sK3,X0))) )),
% 0.21/0.53    inference(resolution,[],[f40,f70])).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~r1_tarski(X1,X2) | r1_tarski(X1,k1_tops_1(X0,X2))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    v3_pre_topc(sK5,sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X1,k1_tops_1(X0,X2)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0) | m1_connsp_2(X2,X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).
% 0.21/0.53  fof(f233,plain,(
% 0.21/0.53    ~r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),sK6) | ~r1_tmap_1(sK3,sK1,sK4,sK6)),
% 0.21/0.53    inference(backward_demodulation,[],[f86,f232])).
% 0.21/0.53  fof(f232,plain,(
% 0.21/0.53    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_tmap_1(sK3,sK1,sK4,sK2)),
% 0.21/0.53    inference(forward_demodulation,[],[f231,f204])).
% 0.21/0.53  fof(f204,plain,(
% 0.21/0.53    k2_tmap_1(sK3,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2))),
% 0.21/0.53    inference(resolution,[],[f127,f49])).
% 0.21/0.53  fof(f127,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f126,f48])).
% 0.21/0.53  fof(f126,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f125,f50])).
% 0.21/0.53  fof(f125,plain,(
% 0.21/0.53    ( ! [X0] : (v2_struct_0(sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f124,f46])).
% 0.21/0.53  fof(f124,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_funct_1(sK4) | v2_struct_0(sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f123,f56])).
% 0.21/0.53  fof(f123,plain,(
% 0.21/0.53    ( ! [X0] : (~l1_pre_topc(sK1) | ~v1_funct_1(sK4) | v2_struct_0(sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f122,f55])).
% 0.21/0.53  fof(f122,plain,(
% 0.21/0.53    ( ! [X0] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK4) | v2_struct_0(sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f121,f54])).
% 0.21/0.53  fof(f121,plain,(
% 0.21/0.53    ( ! [X0] : (v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK4) | v2_struct_0(sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f120,f96])).
% 0.21/0.53  fof(f120,plain,(
% 0.21/0.53    ( ! [X0] : (~l1_pre_topc(sK3) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK4) | v2_struct_0(sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f118,f98])).
% 0.21/0.53  fof(f118,plain,(
% 0.21/0.53    ( ! [X0] : (~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK4) | v2_struct_0(sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0))) )),
% 0.21/0.53    inference(resolution,[],[f47,f75])).
% 0.21/0.53  fof(f75,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | v2_struct_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).
% 0.21/0.53  fof(f231,plain,(
% 0.21/0.53    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2))),
% 0.21/0.53    inference(resolution,[],[f209,f49])).
% 0.21/0.53  fof(f209,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK4)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f208,f57])).
% 0.21/0.53  fof(f208,plain,(
% 0.21/0.53    ( ! [X0] : (v2_struct_0(sK0) | ~m1_pre_topc(X0,sK3) | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK4)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f207,f58])).
% 0.21/0.53  fof(f207,plain,(
% 0.21/0.53    ( ! [X0] : (~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_pre_topc(X0,sK3) | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK4)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f206,f59])).
% 0.21/0.53  fof(f206,plain,(
% 0.21/0.53    ( ! [X0] : (~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_pre_topc(X0,sK3) | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK4)) )),
% 0.21/0.53    inference(resolution,[],[f133,f51])).
% 0.21/0.53  fof(f133,plain,(
% 0.21/0.53    ( ! [X2,X1] : (~m1_pre_topc(sK3,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~m1_pre_topc(X2,sK3) | k3_tmap_1(X1,sK1,sK3,X2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X2))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f132,f72])).
% 0.21/0.53  fof(f72,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X2,X1) | m1_pre_topc(X2,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).
% 0.21/0.53  fof(f132,plain,(
% 0.21/0.53    ( ! [X2,X1] : (~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(sK3,X1) | ~m1_pre_topc(X2,X1) | v2_struct_0(X1) | ~m1_pre_topc(X2,sK3) | k3_tmap_1(X1,sK1,sK3,X2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X2))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f131,f48])).
% 0.21/0.53  fof(f131,plain,(
% 0.21/0.53    ( ! [X2,X1] : (~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(sK3,X1) | ~m1_pre_topc(X2,X1) | v2_struct_0(X1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(X2,sK3) | k3_tmap_1(X1,sK1,sK3,X2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X2))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f130,f46])).
% 0.21/0.53  fof(f130,plain,(
% 0.21/0.53    ( ! [X2,X1] : (~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(sK3,X1) | ~m1_pre_topc(X2,X1) | ~v1_funct_1(sK4) | v2_struct_0(X1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(X2,sK3) | k3_tmap_1(X1,sK1,sK3,X2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X2))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f129,f56])).
% 0.21/0.53  fof(f129,plain,(
% 0.21/0.53    ( ! [X2,X1] : (~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(sK1) | ~m1_pre_topc(sK3,X1) | ~m1_pre_topc(X2,X1) | ~v1_funct_1(sK4) | v2_struct_0(X1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(X2,sK3) | k3_tmap_1(X1,sK1,sK3,X2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X2))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f128,f55])).
% 0.21/0.53  fof(f128,plain,(
% 0.21/0.53    ( ! [X2,X1] : (~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_pre_topc(sK3,X1) | ~m1_pre_topc(X2,X1) | ~v1_funct_1(sK4) | v2_struct_0(X1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(X2,sK3) | k3_tmap_1(X1,sK1,sK3,X2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X2))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f119,f54])).
% 0.21/0.53  fof(f119,plain,(
% 0.21/0.53    ( ! [X2,X1] : (~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_pre_topc(sK3,X1) | ~m1_pre_topc(X2,X1) | ~v1_funct_1(sK4) | v2_struct_0(X1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(X2,sK3) | k3_tmap_1(X1,sK1,sK3,X2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X2))) )),
% 0.21/0.53    inference(resolution,[],[f47,f62])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | v2_struct_0(X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).
% 0.21/0.53  fof(f86,plain,(
% 0.21/0.53    ~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) | ~r1_tmap_1(sK3,sK1,sK4,sK6)),
% 0.21/0.53    inference(forward_demodulation,[],[f38,f43])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK1,sK4,sK6)),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f258,plain,(
% 0.21/0.53    r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),sK6)),
% 0.21/0.53    inference(subsumption_resolution,[],[f257,f52])).
% 0.21/0.53  fof(f257,plain,(
% 0.21/0.53    v2_struct_0(sK2) | r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),sK6)),
% 0.21/0.53    inference(subsumption_resolution,[],[f254,f49])).
% 0.21/0.53  fof(f254,plain,(
% 0.21/0.53    ~m1_pre_topc(sK2,sK3) | v2_struct_0(sK2) | r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),sK6)),
% 0.21/0.53    inference(resolution,[],[f221,f85])).
% 0.21/0.53  fof(f221,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(sK6,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3) | v2_struct_0(X0) | r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,sK4,X0),sK6)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f220,f54])).
% 0.21/0.53  fof(f220,plain,(
% 0.21/0.53    ( ! [X0] : (v2_struct_0(X0) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(sK6,u1_struct_0(X0)) | v2_struct_0(sK1) | r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,sK4,X0),sK6)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f219,f44])).
% 0.21/0.53  fof(f219,plain,(
% 0.21/0.53    ( ! [X0] : (v2_struct_0(X0) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(X0)) | v2_struct_0(sK1) | r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,sK4,X0),sK6)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f218,f48])).
% 0.21/0.53  fof(f218,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(X0)) | v2_struct_0(sK1) | r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,sK4,X0),sK6)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f217,f47])).
% 0.21/0.53  fof(f217,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(X0)) | v2_struct_0(sK1) | r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,sK4,X0),sK6)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f216,f46])).
% 0.21/0.53  fof(f216,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(X0)) | v2_struct_0(sK1) | r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,sK4,X0),sK6)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f215,f96])).
% 0.21/0.53  fof(f215,plain,(
% 0.21/0.53    ( ! [X0] : (~l1_pre_topc(sK3) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(X0)) | v2_struct_0(sK1) | r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,sK4,X0),sK6)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f214,f98])).
% 0.21/0.53  fof(f214,plain,(
% 0.21/0.53    ( ! [X0] : (~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(X0)) | v2_struct_0(sK1) | r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,sK4,X0),sK6)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f213,f50])).
% 0.21/0.53  fof(f213,plain,(
% 0.21/0.53    ( ! [X0] : (v2_struct_0(sK3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(X0)) | v2_struct_0(sK1) | r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,sK4,X0),sK6)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f212,f56])).
% 0.21/0.53  fof(f212,plain,(
% 0.21/0.53    ( ! [X0] : (~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(X0)) | v2_struct_0(sK1) | r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,sK4,X0),sK6)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f210,f55])).
% 0.21/0.53  fof(f210,plain,(
% 0.21/0.53    ( ! [X0] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(X0)) | v2_struct_0(sK1) | r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,sK4,X0),sK6)) )),
% 0.21/0.53    inference(resolution,[],[f205,f78])).
% 0.21/0.53  fof(f78,plain,(
% 0.21/0.53    ( ! [X2,X0,X5,X3,X1] : (~r1_tmap_1(X1,X0,X2,X5) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X3)) | v2_struct_0(X0) | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) )),
% 0.21/0.53    inference(equality_resolution,[],[f63])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X3)) | X4 != X5 | ~r1_tmap_1(X1,X0,X2,X4) | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tmap_1)).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (27983)------------------------------
% 0.21/0.53  % (27983)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (27983)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (27983)Memory used [KB]: 6268
% 0.21/0.53  % (27983)Time elapsed: 0.099 s
% 0.21/0.53  % (27983)------------------------------
% 0.21/0.53  % (27983)------------------------------
% 0.21/0.53  % (27977)Success in time 0.171 s
%------------------------------------------------------------------------------
