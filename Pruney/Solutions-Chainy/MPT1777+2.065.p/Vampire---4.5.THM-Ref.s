%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:12 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  182 (1415 expanded)
%              Number of leaves         :   15 ( 277 expanded)
%              Depth                    :   45
%              Number of atoms          :  904 (13028 expanded)
%              Number of equality atoms :   68 (1352 expanded)
%              Maximal formula depth    :   24 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f992,plain,(
    $false ),
    inference(subsumption_resolution,[],[f991,f244])).

fof(f244,plain,(
    m1_subset_1(sK5,k2_struct_0(sK2)) ),
    inference(backward_demodulation,[],[f92,f242])).

fof(f242,plain,(
    u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(resolution,[],[f176,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f176,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f113,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f113,plain,(
    l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f111,f61])).

fof(f61,plain,(
    l1_pre_topc(sK0) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tmap_1)).

fof(f111,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2) ),
    inference(resolution,[],[f67,f55])).

fof(f55,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f92,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f43,f44])).

fof(f44,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f19])).

fof(f43,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f991,plain,(
    ~ m1_subset_1(sK5,k2_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f990,f242])).

fof(f990,plain,(
    ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f989,f215])).

fof(f215,plain,(
    m1_subset_1(sK5,k2_struct_0(sK3)) ),
    inference(backward_demodulation,[],[f47,f214])).

fof(f214,plain,(
    u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(resolution,[],[f153,f62])).

fof(f153,plain,(
    l1_struct_0(sK3) ),
    inference(resolution,[],[f112,f63])).

fof(f112,plain,(
    l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f110,f61])).

fof(f110,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK3) ),
    inference(resolution,[],[f67,f53])).

fof(f53,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f47,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f19])).

fof(f989,plain,
    ( ~ m1_subset_1(sK5,k2_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f988,f214])).

% (24354)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
fof(f988,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f987,f217])).

fof(f217,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f109,f214])).

fof(f109,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f50,f107])).

fof(f107,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(resolution,[],[f62,f103])).

fof(f103,plain,(
    l1_struct_0(sK1) ),
    inference(resolution,[],[f63,f58])).

fof(f58,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f50,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f19])).

fof(f987,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1))))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f986,f214])).

fof(f986,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1))))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f985,f107])).

fof(f985,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f984,f216])).

fof(f216,plain,(
    v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f108,f214])).

fof(f108,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f49,f107])).

fof(f49,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f984,plain,
    ( ~ v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f983,f214])).

fof(f983,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK3),k2_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f982,f107])).

fof(f982,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f981,f46])).

fof(f46,plain,(
    ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f19])).

fof(f981,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(subsumption_resolution,[],[f980,f56])).

fof(f56,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f980,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK1)
    | r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(subsumption_resolution,[],[f979,f290])).

fof(f290,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(forward_demodulation,[],[f289,f243])).

fof(f243,plain,(
    sK3 = g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(backward_demodulation,[],[f51,f242])).

fof(f51,plain,(
    sK3 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f289,plain,(
    m1_pre_topc(sK2,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(forward_demodulation,[],[f288,f242])).

fof(f288,plain,(
    m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(subsumption_resolution,[],[f280,f113])).

fof(f280,plain,
    ( ~ l1_pre_topc(sK2)
    | m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(duplicate_literal_removal,[],[f275])).

fof(f275,plain,
    ( ~ l1_pre_topc(sK2)
    | m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f175,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f175,plain,(
    m1_pre_topc(sK2,sK2) ),
    inference(resolution,[],[f113,f64])).

fof(f64,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f979,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK1)
    | r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(subsumption_resolution,[],[f978,f832])).

fof(f832,plain,(
    v1_tsep_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f831,f152])).

fof(f152,plain,(
    m1_pre_topc(sK3,sK3) ),
    inference(resolution,[],[f112,f64])).

fof(f831,plain,
    ( ~ m1_pre_topc(sK3,sK3)
    | v1_tsep_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f830,f121])).

fof(f121,plain,(
    v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f120,f60])).

fof(f60,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f120,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f118,f61])).

fof(f118,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK3) ),
    inference(resolution,[],[f75,f53])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f830,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ m1_pre_topc(sK3,sK3)
    | v1_tsep_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f825,f112])).

fof(f825,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ m1_pre_topc(sK3,sK3)
    | v1_tsep_1(sK2,sK3) ),
    inference(resolution,[],[f822,f150])).

fof(f150,plain,(
    ! [X0] :
      ( ~ v1_tsep_1(sK3,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(sK3,X0)
      | v1_tsep_1(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f149,f113])).

fof(f149,plain,(
    ! [X0] :
      ( ~ v1_tsep_1(sK3,X0)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(sK3,X0)
      | v1_tsep_1(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f148,f123])).

fof(f123,plain,(
    v2_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f122,f60])).

fof(f122,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f119,f61])).

fof(f119,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK2) ),
    inference(resolution,[],[f75,f55])).

fof(f148,plain,(
    ! [X0] :
      ( ~ v1_tsep_1(sK3,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(sK2)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(sK3,X0)
      | v1_tsep_1(sK2,X0) ) ),
    inference(superposition,[],[f100,f51])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ v1_tsep_1(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f99,f75])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v1_tsep_1(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f89,f67])).

% (24349)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
fof(f89,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v1_tsep_1(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2
      | ~ v1_tsep_1(X2,X0)
      | ~ m1_pre_topc(X2,X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> ( m1_pre_topc(X2,X0)
                  & v1_tsep_1(X2,X0) ) )
              | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> ( m1_pre_topc(X2,X0)
                  & v1_tsep_1(X2,X0) ) )
              | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2) )
             => ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                <=> ( m1_pre_topc(X2,X0)
                    & v1_tsep_1(X2,X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_tmap_1)).

fof(f822,plain,(
    v1_tsep_1(sK3,sK3) ),
    inference(subsumption_resolution,[],[f821,f121])).

fof(f821,plain,
    ( ~ v2_pre_topc(sK3)
    | v1_tsep_1(sK3,sK3) ),
    inference(subsumption_resolution,[],[f820,f152])).

fof(f820,plain,
    ( ~ m1_pre_topc(sK3,sK3)
    | ~ v2_pre_topc(sK3)
    | v1_tsep_1(sK3,sK3) ),
    inference(subsumption_resolution,[],[f819,f112])).

fof(f819,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ m1_pre_topc(sK3,sK3)
    | ~ v2_pre_topc(sK3)
    | v1_tsep_1(sK3,sK3) ),
    inference(resolution,[],[f473,f154])).

fof(f154,plain,(
    v3_pre_topc(k2_struct_0(sK3),sK3) ),
    inference(subsumption_resolution,[],[f151,f121])).

fof(f151,plain,
    ( ~ v2_pre_topc(sK3)
    | v3_pre_topc(k2_struct_0(sK3),sK3) ),
    inference(resolution,[],[f112,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v3_pre_topc(k2_struct_0(X0),X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

fof(f473,plain,(
    ! [X16] :
      ( ~ v3_pre_topc(k2_struct_0(sK3),X16)
      | ~ l1_pre_topc(X16)
      | ~ m1_pre_topc(sK3,X16)
      | ~ v2_pre_topc(X16)
      | v1_tsep_1(sK3,X16) ) ),
    inference(superposition,[],[f93,f214])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(u1_struct_0(X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f85,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | ~ v3_pre_topc(X2,X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f39,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).

fof(f978,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK1)
    | r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(subsumption_resolution,[],[f977,f54])).

fof(f54,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f977,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK2)
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK1)
    | r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(subsumption_resolution,[],[f976,f48])).

fof(f48,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f19])).

fof(f976,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK2)
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK1)
    | r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(subsumption_resolution,[],[f975,f112])).

fof(f975,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK2)
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK1)
    | r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(subsumption_resolution,[],[f974,f121])).

fof(f974,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK2)
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK1)
    | r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(subsumption_resolution,[],[f973,f52])).

fof(f52,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f973,plain,
    ( v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK2)
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK1)
    | r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(subsumption_resolution,[],[f972,f58])).

fof(f972,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK2)
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK1)
    | r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(subsumption_resolution,[],[f971,f57])).

fof(f57,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f971,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK2)
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK1)
    | r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(resolution,[],[f970,f84])).

fof(f84,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | v2_struct_0(X3)
      | ~ v1_tsep_1(X3,X1)
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | v2_struct_0(X0)
      | r1_tmap_1(X1,X0,X2,X5) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
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
      | ~ v1_tsep_1(X3,X1)
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | X4 != X5
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | r1_tmap_1(X1,X0,X2,X4) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( r1_tmap_1(X1,X0,X2,X4)
                          <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | ~ v1_tsep_1(X3,X1)
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( r1_tmap_1(X1,X0,X2,X4)
                          <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | ~ v1_tsep_1(X3,X1)
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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & v1_tsep_1(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X3))
                         => ( X4 = X5
                           => ( r1_tmap_1(X1,X0,X2,X4)
                            <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_tmap_1)).

fof(f970,plain,(
    r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),sK5) ),
    inference(backward_demodulation,[],[f91,f969])).

fof(f969,plain,(
    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_tmap_1(sK3,sK1,sK4,sK2) ),
    inference(backward_demodulation,[],[f840,f968])).

fof(f968,plain,(
    k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,k2_struct_0(sK2)) = k2_tmap_1(sK3,sK1,sK4,sK2) ),
    inference(forward_demodulation,[],[f965,f242])).

fof(f965,plain,(
    k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,u1_struct_0(sK2)) = k2_tmap_1(sK3,sK1,sK4,sK2) ),
    inference(resolution,[],[f853,f290])).

fof(f853,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,u1_struct_0(X0)) = k2_tmap_1(sK3,sK1,sK4,X0) ) ),
    inference(subsumption_resolution,[],[f852,f216])).

fof(f852,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1))
      | ~ m1_pre_topc(X0,sK3)
      | k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,u1_struct_0(X0)) = k2_tmap_1(sK3,sK1,sK4,X0) ) ),
    inference(subsumption_resolution,[],[f851,f48])).

fof(f851,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK4)
      | ~ v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1))
      | ~ m1_pre_topc(X0,sK3)
      | k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,u1_struct_0(X0)) = k2_tmap_1(sK3,sK1,sK4,X0) ) ),
    inference(resolution,[],[f660,f217])).

fof(f660,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1))))
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,k2_struct_0(sK3),k2_struct_0(sK1))
      | ~ m1_pre_topc(X7,sK3)
      | k2_tmap_1(sK3,sK1,X6,X7) = k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),X6,u1_struct_0(X7)) ) ),
    inference(subsumption_resolution,[],[f659,f52])).

fof(f659,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1))))
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,k2_struct_0(sK3),k2_struct_0(sK1))
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(X7,sK3)
      | k2_tmap_1(sK3,sK1,X6,X7) = k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),X6,u1_struct_0(X7)) ) ),
    inference(subsumption_resolution,[],[f658,f112])).

fof(f658,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1))))
      | ~ l1_pre_topc(sK3)
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,k2_struct_0(sK3),k2_struct_0(sK1))
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(X7,sK3)
      | k2_tmap_1(sK3,sK1,X6,X7) = k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),X6,u1_struct_0(X7)) ) ),
    inference(subsumption_resolution,[],[f651,f121])).

fof(f651,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1))))
      | ~ v2_pre_topc(sK3)
      | ~ l1_pre_topc(sK3)
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,k2_struct_0(sK3),k2_struct_0(sK1))
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(X7,sK3)
      | k2_tmap_1(sK3,sK1,X6,X7) = k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),X6,u1_struct_0(X7)) ) ),
    inference(superposition,[],[f313,f214])).

fof(f313,plain,(
    ! [X6,X7,X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),k2_struct_0(sK1))))
      | ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(X6),k2_struct_0(sK1))
      | v2_struct_0(X6)
      | ~ m1_pre_topc(X7,X6)
      | k2_tmap_1(X6,sK1,X5,X7) = k2_partfun1(u1_struct_0(X6),k2_struct_0(sK1),X5,u1_struct_0(X7)) ) ),
    inference(subsumption_resolution,[],[f312,f58])).

fof(f312,plain,(
    ! [X6,X7,X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),k2_struct_0(sK1))))
      | ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(X6),k2_struct_0(sK1))
      | v2_struct_0(X6)
      | ~ m1_pre_topc(X7,X6)
      | k2_tmap_1(X6,sK1,X5,X7) = k2_partfun1(u1_struct_0(X6),k2_struct_0(sK1),X5,u1_struct_0(X7)) ) ),
    inference(subsumption_resolution,[],[f311,f57])).

fof(f311,plain,(
    ! [X6,X7,X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),k2_struct_0(sK1))))
      | ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(X6),k2_struct_0(sK1))
      | v2_struct_0(X6)
      | ~ m1_pre_topc(X7,X6)
      | k2_tmap_1(X6,sK1,X5,X7) = k2_partfun1(u1_struct_0(X6),k2_struct_0(sK1),X5,u1_struct_0(X7)) ) ),
    inference(subsumption_resolution,[],[f296,f56])).

fof(f296,plain,(
    ! [X6,X7,X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),k2_struct_0(sK1))))
      | ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(X6),k2_struct_0(sK1))
      | v2_struct_0(X6)
      | ~ m1_pre_topc(X7,X6)
      | k2_tmap_1(X6,sK1,X5,X7) = k2_partfun1(u1_struct_0(X6),k2_struct_0(sK1),X5,u1_struct_0(X7)) ) ),
    inference(superposition,[],[f71,f107])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X3,X0)
      | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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

fof(f840,plain,(
    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,k2_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f838,f242])).

fof(f838,plain,(
    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,u1_struct_0(sK2)) ),
    inference(resolution,[],[f629,f290])).

fof(f629,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | k3_tmap_1(sK0,sK1,sK3,X0,sK4) = k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f628,f48])).

fof(f628,plain,(
    ! [X0] :
      ( k3_tmap_1(sK0,sK1,sK3,X0,sK4) = k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,u1_struct_0(X0))
      | ~ v1_funct_1(sK4)
      | ~ m1_pre_topc(X0,sK3) ) ),
    inference(subsumption_resolution,[],[f627,f216])).

fof(f627,plain,(
    ! [X0] :
      ( k3_tmap_1(sK0,sK1,sK3,X0,sK4) = k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,u1_struct_0(X0))
      | ~ v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1))
      | ~ v1_funct_1(sK4)
      | ~ m1_pre_topc(X0,sK3) ) ),
    inference(resolution,[],[f326,f217])).

fof(f326,plain,(
    ! [X21,X22] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1))))
      | k3_tmap_1(sK0,sK1,sK3,X22,X21) = k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),X21,u1_struct_0(X22))
      | ~ v1_funct_2(X21,k2_struct_0(sK3),k2_struct_0(sK1))
      | ~ v1_funct_1(X21)
      | ~ m1_pre_topc(X22,sK3) ) ),
    inference(subsumption_resolution,[],[f325,f58])).

fof(f325,plain,(
    ! [X21,X22] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1))))
      | k3_tmap_1(sK0,sK1,sK3,X22,X21) = k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),X21,u1_struct_0(X22))
      | ~ v1_funct_2(X21,k2_struct_0(sK3),k2_struct_0(sK1))
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(X21)
      | ~ m1_pre_topc(X22,sK3) ) ),
    inference(subsumption_resolution,[],[f324,f57])).

fof(f324,plain,(
    ! [X21,X22] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1))))
      | k3_tmap_1(sK0,sK1,sK3,X22,X21) = k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),X21,u1_struct_0(X22))
      | ~ v1_funct_2(X21,k2_struct_0(sK3),k2_struct_0(sK1))
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(X21)
      | ~ m1_pre_topc(X22,sK3) ) ),
    inference(subsumption_resolution,[],[f304,f56])).

fof(f304,plain,(
    ! [X21,X22] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1))))
      | k3_tmap_1(sK0,sK1,sK3,X22,X21) = k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),X21,u1_struct_0(X22))
      | ~ v1_funct_2(X21,k2_struct_0(sK3),k2_struct_0(sK1))
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(X21)
      | ~ m1_pre_topc(X22,sK3) ) ),
    inference(superposition,[],[f221,f107])).

fof(f221,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(X0))))
      | k3_tmap_1(sK0,X0,sK3,X1,X2) = k2_partfun1(k2_struct_0(sK3),u1_struct_0(X0),X2,u1_struct_0(X1))
      | ~ v1_funct_2(X2,k2_struct_0(sK3),u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,sK3) ) ),
    inference(forward_demodulation,[],[f220,f214])).

fof(f220,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,k2_struct_0(sK3),u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,sK3)
      | k3_tmap_1(sK0,X0,sK3,X1,X2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X0),X2,u1_struct_0(X1)) ) ),
    inference(forward_demodulation,[],[f219,f214])).

fof(f219,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,k2_struct_0(sK3),u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
      | ~ m1_pre_topc(X1,sK3)
      | k3_tmap_1(sK0,X0,sK3,X1,X2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X0),X2,u1_struct_0(X1)) ) ),
    inference(backward_demodulation,[],[f169,f214])).

fof(f169,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
      | ~ m1_pre_topc(X1,sK3)
      | k3_tmap_1(sK0,X0,sK3,X1,X2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X0),X2,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f168,f136])).

fof(f136,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | m1_pre_topc(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f135,f60])).

fof(f135,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(X0,sK3)
      | m1_pre_topc(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f133,f61])).

fof(f133,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(X0,sK3)
      | m1_pre_topc(X0,sK0) ) ),
    inference(resolution,[],[f76,f53])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X2,X1)
      | m1_pre_topc(X2,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f168,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,sK0)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
      | ~ m1_pre_topc(X1,sK3)
      | k3_tmap_1(sK0,X0,sK3,X1,X2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X0),X2,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f167,f59])).

fof(f59,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f167,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(sK0)
      | ~ m1_pre_topc(X1,sK0)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
      | ~ m1_pre_topc(X1,sK3)
      | k3_tmap_1(sK0,X0,sK3,X1,X2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X0),X2,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f166,f61])).

fof(f166,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(sK0)
      | ~ m1_pre_topc(X1,sK0)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
      | ~ m1_pre_topc(X1,sK3)
      | k3_tmap_1(sK0,X0,sK3,X1,X2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X0),X2,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f164,f60])).

fof(f164,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(sK0)
      | ~ m1_pre_topc(X1,sK0)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
      | ~ m1_pre_topc(X1,sK3)
      | k3_tmap_1(sK0,X0,sK3,X1,X2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X0),X2,u1_struct_0(X1)) ) ),
    inference(resolution,[],[f70,f53])).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_pre_topc(X2,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X2)
      | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

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

fof(f91,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(backward_demodulation,[],[f45,f44])).

fof(f45,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:16:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.45  % (24351)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.46  % (24335)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.47  % (24345)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.47  % (24343)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.48  % (24352)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.48  % (24353)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.48  % (24344)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.49  % (24339)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (24334)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.50  % (24338)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.51  % (24348)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.51  % (24351)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f992,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(subsumption_resolution,[],[f991,f244])).
% 0.22/0.51  fof(f244,plain,(
% 0.22/0.51    m1_subset_1(sK5,k2_struct_0(sK2))),
% 0.22/0.51    inference(backward_demodulation,[],[f92,f242])).
% 0.22/0.51  fof(f242,plain,(
% 0.22/0.51    u1_struct_0(sK2) = k2_struct_0(sK2)),
% 0.22/0.51    inference(resolution,[],[f176,f62])).
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.51  fof(f176,plain,(
% 0.22/0.51    l1_struct_0(sK2)),
% 0.22/0.51    inference(resolution,[],[f113,f63])).
% 0.22/0.51  fof(f63,plain,(
% 0.22/0.51    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.51  fof(f113,plain,(
% 0.22/0.51    l1_pre_topc(sK2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f111,f61])).
% 0.22/0.51  fof(f61,plain,(
% 0.22/0.51    l1_pre_topc(sK0)),
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
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tmap_1)).
% 0.22/0.51  fof(f111,plain,(
% 0.22/0.51    ~l1_pre_topc(sK0) | l1_pre_topc(sK2)),
% 0.22/0.51    inference(resolution,[],[f67,f55])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    m1_pre_topc(sK2,sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f67,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.22/0.51  fof(f92,plain,(
% 0.22/0.51    m1_subset_1(sK5,u1_struct_0(sK2))),
% 0.22/0.51    inference(forward_demodulation,[],[f43,f44])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    sK5 = sK6),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    m1_subset_1(sK6,u1_struct_0(sK2))),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f991,plain,(
% 0.22/0.51    ~m1_subset_1(sK5,k2_struct_0(sK2))),
% 0.22/0.51    inference(forward_demodulation,[],[f990,f242])).
% 0.22/0.51  fof(f990,plain,(
% 0.22/0.51    ~m1_subset_1(sK5,u1_struct_0(sK2))),
% 0.22/0.51    inference(subsumption_resolution,[],[f989,f215])).
% 0.22/0.51  fof(f215,plain,(
% 0.22/0.51    m1_subset_1(sK5,k2_struct_0(sK3))),
% 0.22/0.51    inference(backward_demodulation,[],[f47,f214])).
% 0.22/0.51  fof(f214,plain,(
% 0.22/0.51    u1_struct_0(sK3) = k2_struct_0(sK3)),
% 0.22/0.51    inference(resolution,[],[f153,f62])).
% 0.22/0.51  fof(f153,plain,(
% 0.22/0.51    l1_struct_0(sK3)),
% 0.22/0.51    inference(resolution,[],[f112,f63])).
% 0.22/0.51  fof(f112,plain,(
% 0.22/0.51    l1_pre_topc(sK3)),
% 0.22/0.51    inference(subsumption_resolution,[],[f110,f61])).
% 0.22/0.51  fof(f110,plain,(
% 0.22/0.51    ~l1_pre_topc(sK0) | l1_pre_topc(sK3)),
% 0.22/0.51    inference(resolution,[],[f67,f53])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    m1_pre_topc(sK3,sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f989,plain,(
% 0.22/0.51    ~m1_subset_1(sK5,k2_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2))),
% 0.22/0.51    inference(forward_demodulation,[],[f988,f214])).
% 0.22/0.51  % (24354)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.51  fof(f988,plain,(
% 0.22/0.51    ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2))),
% 0.22/0.51    inference(subsumption_resolution,[],[f987,f217])).
% 0.22/0.51  fof(f217,plain,(
% 0.22/0.51    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1))))),
% 0.22/0.51    inference(backward_demodulation,[],[f109,f214])).
% 0.22/0.51  fof(f109,plain,(
% 0.22/0.51    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1))))),
% 0.22/0.51    inference(backward_demodulation,[],[f50,f107])).
% 0.22/0.51  fof(f107,plain,(
% 0.22/0.51    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.22/0.51    inference(resolution,[],[f62,f103])).
% 0.22/0.51  fof(f103,plain,(
% 0.22/0.51    l1_struct_0(sK1)),
% 0.22/0.51    inference(resolution,[],[f63,f58])).
% 0.22/0.51  fof(f58,plain,(
% 0.22/0.51    l1_pre_topc(sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f987,plain,(
% 0.22/0.51    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1)))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2))),
% 0.22/0.51    inference(forward_demodulation,[],[f986,f214])).
% 0.22/0.51  fof(f986,plain,(
% 0.22/0.51    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1)))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2))),
% 0.22/0.51    inference(forward_demodulation,[],[f985,f107])).
% 0.22/0.51  fof(f985,plain,(
% 0.22/0.51    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2))),
% 0.22/0.51    inference(subsumption_resolution,[],[f984,f216])).
% 0.22/0.51  fof(f216,plain,(
% 0.22/0.51    v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1))),
% 0.22/0.51    inference(backward_demodulation,[],[f108,f214])).
% 0.22/0.51  fof(f108,plain,(
% 0.22/0.51    v1_funct_2(sK4,u1_struct_0(sK3),k2_struct_0(sK1))),
% 0.22/0.51    inference(backward_demodulation,[],[f49,f107])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f984,plain,(
% 0.22/0.51    ~v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2))),
% 0.22/0.51    inference(forward_demodulation,[],[f983,f214])).
% 0.22/0.51  fof(f983,plain,(
% 0.22/0.51    ~v1_funct_2(sK4,u1_struct_0(sK3),k2_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2))),
% 0.22/0.51    inference(forward_demodulation,[],[f982,f107])).
% 0.22/0.51  fof(f982,plain,(
% 0.22/0.51    ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2))),
% 0.22/0.51    inference(subsumption_resolution,[],[f981,f46])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f981,plain,(
% 0.22/0.51    ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.22/0.51    inference(subsumption_resolution,[],[f980,f56])).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    ~v2_struct_0(sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f980,plain,(
% 0.22/0.51    ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.22/0.51    inference(subsumption_resolution,[],[f979,f290])).
% 0.22/0.51  fof(f290,plain,(
% 0.22/0.51    m1_pre_topc(sK2,sK3)),
% 0.22/0.51    inference(forward_demodulation,[],[f289,f243])).
% 0.22/0.51  fof(f243,plain,(
% 0.22/0.51    sK3 = g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))),
% 0.22/0.51    inference(backward_demodulation,[],[f51,f242])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    sK3 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f289,plain,(
% 0.22/0.51    m1_pre_topc(sK2,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)))),
% 0.22/0.51    inference(forward_demodulation,[],[f288,f242])).
% 0.22/0.51  fof(f288,plain,(
% 0.22/0.51    m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),
% 0.22/0.51    inference(subsumption_resolution,[],[f280,f113])).
% 0.22/0.51  fof(f280,plain,(
% 0.22/0.51    ~l1_pre_topc(sK2) | m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f275])).
% 0.22/0.51  fof(f275,plain,(
% 0.22/0.51    ~l1_pre_topc(sK2) | m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~l1_pre_topc(sK2)),
% 0.22/0.51    inference(resolution,[],[f175,f66])).
% 0.22/0.51  fof(f66,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).
% 0.22/0.51  fof(f175,plain,(
% 0.22/0.51    m1_pre_topc(sK2,sK2)),
% 0.22/0.51    inference(resolution,[],[f113,f64])).
% 0.22/0.51  fof(f64,plain,(
% 0.22/0.51    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.22/0.51  fof(f979,plain,(
% 0.22/0.51    ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.22/0.51    inference(subsumption_resolution,[],[f978,f832])).
% 0.22/0.51  fof(f832,plain,(
% 0.22/0.51    v1_tsep_1(sK2,sK3)),
% 0.22/0.51    inference(subsumption_resolution,[],[f831,f152])).
% 0.22/0.51  fof(f152,plain,(
% 0.22/0.51    m1_pre_topc(sK3,sK3)),
% 0.22/0.51    inference(resolution,[],[f112,f64])).
% 0.22/0.51  fof(f831,plain,(
% 0.22/0.51    ~m1_pre_topc(sK3,sK3) | v1_tsep_1(sK2,sK3)),
% 0.22/0.51    inference(subsumption_resolution,[],[f830,f121])).
% 0.22/0.51  fof(f121,plain,(
% 0.22/0.51    v2_pre_topc(sK3)),
% 0.22/0.51    inference(subsumption_resolution,[],[f120,f60])).
% 0.22/0.51  fof(f60,plain,(
% 0.22/0.51    v2_pre_topc(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f120,plain,(
% 0.22/0.51    ~v2_pre_topc(sK0) | v2_pre_topc(sK3)),
% 0.22/0.51    inference(subsumption_resolution,[],[f118,f61])).
% 0.22/0.51  fof(f118,plain,(
% 0.22/0.51    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_pre_topc(sK3)),
% 0.22/0.51    inference(resolution,[],[f75,f53])).
% 0.22/0.51  fof(f75,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_pre_topc(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f36])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.51    inference(flattening,[],[f35])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.22/0.51  fof(f830,plain,(
% 0.22/0.51    ~v2_pre_topc(sK3) | ~m1_pre_topc(sK3,sK3) | v1_tsep_1(sK2,sK3)),
% 0.22/0.51    inference(subsumption_resolution,[],[f825,f112])).
% 0.22/0.51  fof(f825,plain,(
% 0.22/0.51    ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | ~m1_pre_topc(sK3,sK3) | v1_tsep_1(sK2,sK3)),
% 0.22/0.51    inference(resolution,[],[f822,f150])).
% 0.22/0.51  fof(f150,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_tsep_1(sK3,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(sK3,X0) | v1_tsep_1(sK2,X0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f149,f113])).
% 0.22/0.51  fof(f149,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_tsep_1(sK3,X0) | ~l1_pre_topc(X0) | ~l1_pre_topc(sK2) | ~v2_pre_topc(X0) | ~m1_pre_topc(sK3,X0) | v1_tsep_1(sK2,X0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f148,f123])).
% 0.22/0.51  fof(f123,plain,(
% 0.22/0.51    v2_pre_topc(sK2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f122,f60])).
% 0.22/0.51  fof(f122,plain,(
% 0.22/0.51    ~v2_pre_topc(sK0) | v2_pre_topc(sK2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f119,f61])).
% 0.22/0.51  fof(f119,plain,(
% 0.22/0.51    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_pre_topc(sK2)),
% 0.22/0.51    inference(resolution,[],[f75,f55])).
% 0.22/0.51  fof(f148,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_tsep_1(sK3,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(X0) | ~m1_pre_topc(sK3,X0) | v1_tsep_1(sK2,X0)) )),
% 0.22/0.51    inference(superposition,[],[f100,f51])).
% 0.22/0.51  fof(f100,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v1_tsep_1(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X0) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | v1_tsep_1(X1,X0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f99,f75])).
% 0.22/0.51  fof(f99,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v1_tsep_1(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | v1_tsep_1(X1,X0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f89,f67])).
% 0.22/0.51  % (24349)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.51  fof(f89,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v1_tsep_1(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | v1_tsep_1(X1,X0)) )),
% 0.22/0.51    inference(equality_resolution,[],[f80])).
% 0.22/0.51  fof(f80,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2 | ~v1_tsep_1(X2,X0) | ~m1_pre_topc(X2,X0) | v1_tsep_1(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f42])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> (m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0))) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.51    inference(flattening,[],[f41])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> (m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0))) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> (m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_tmap_1)).
% 0.22/0.51  fof(f822,plain,(
% 0.22/0.51    v1_tsep_1(sK3,sK3)),
% 0.22/0.51    inference(subsumption_resolution,[],[f821,f121])).
% 0.22/0.51  fof(f821,plain,(
% 0.22/0.51    ~v2_pre_topc(sK3) | v1_tsep_1(sK3,sK3)),
% 0.22/0.51    inference(subsumption_resolution,[],[f820,f152])).
% 0.22/0.51  fof(f820,plain,(
% 0.22/0.51    ~m1_pre_topc(sK3,sK3) | ~v2_pre_topc(sK3) | v1_tsep_1(sK3,sK3)),
% 0.22/0.51    inference(subsumption_resolution,[],[f819,f112])).
% 0.22/0.51  fof(f819,plain,(
% 0.22/0.51    ~l1_pre_topc(sK3) | ~m1_pre_topc(sK3,sK3) | ~v2_pre_topc(sK3) | v1_tsep_1(sK3,sK3)),
% 0.22/0.51    inference(resolution,[],[f473,f154])).
% 0.22/0.51  fof(f154,plain,(
% 0.22/0.51    v3_pre_topc(k2_struct_0(sK3),sK3)),
% 0.22/0.51    inference(subsumption_resolution,[],[f151,f121])).
% 0.22/0.51  fof(f151,plain,(
% 0.22/0.51    ~v2_pre_topc(sK3) | v3_pre_topc(k2_struct_0(sK3),sK3)),
% 0.22/0.51    inference(resolution,[],[f112,f74])).
% 0.22/0.51  fof(f74,plain,(
% 0.22/0.51    ( ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v3_pre_topc(k2_struct_0(X0),X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f34])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.51    inference(flattening,[],[f33])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).
% 0.22/0.51  fof(f473,plain,(
% 0.22/0.51    ( ! [X16] : (~v3_pre_topc(k2_struct_0(sK3),X16) | ~l1_pre_topc(X16) | ~m1_pre_topc(sK3,X16) | ~v2_pre_topc(X16) | v1_tsep_1(sK3,X16)) )),
% 0.22/0.51    inference(superposition,[],[f93,f214])).
% 0.22/0.51  fof(f93,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v3_pre_topc(u1_struct_0(X1),X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | v1_tsep_1(X1,X0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f85,f68])).
% 0.22/0.51  fof(f68,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.22/0.51  fof(f85,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(u1_struct_0(X1),X0) | v1_tsep_1(X1,X0)) )),
% 0.22/0.51    inference(equality_resolution,[],[f78])).
% 0.22/0.51  fof(f78,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | ~v3_pre_topc(X2,X0) | v1_tsep_1(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f40])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.51    inference(flattening,[],[f39])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).
% 0.22/0.51  fof(f978,plain,(
% 0.22/0.51    ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.22/0.51    inference(subsumption_resolution,[],[f977,f54])).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    ~v2_struct_0(sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f977,plain,(
% 0.22/0.51    ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | v2_struct_0(sK2) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.22/0.51    inference(subsumption_resolution,[],[f976,f48])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    v1_funct_1(sK4)),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f976,plain,(
% 0.22/0.51    ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | v2_struct_0(sK2) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.22/0.51    inference(subsumption_resolution,[],[f975,f112])).
% 0.22/0.51  fof(f975,plain,(
% 0.22/0.51    ~l1_pre_topc(sK3) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | v2_struct_0(sK2) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.22/0.51    inference(subsumption_resolution,[],[f974,f121])).
% 0.22/0.51  fof(f974,plain,(
% 0.22/0.51    ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | v2_struct_0(sK2) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.22/0.51    inference(subsumption_resolution,[],[f973,f52])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    ~v2_struct_0(sK3)),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f973,plain,(
% 0.22/0.51    v2_struct_0(sK3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | v2_struct_0(sK2) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.22/0.51    inference(subsumption_resolution,[],[f972,f58])).
% 0.22/0.51  fof(f972,plain,(
% 0.22/0.51    ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | v2_struct_0(sK2) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.22/0.51    inference(subsumption_resolution,[],[f971,f57])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    v2_pre_topc(sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f971,plain,(
% 0.22/0.51    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | v2_struct_0(sK2) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.22/0.51    inference(resolution,[],[f970,f84])).
% 0.22/0.51  fof(f84,plain,(
% 0.22/0.51    ( ! [X2,X0,X5,X3,X1] : (~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~v1_tsep_1(X3,X1) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X3)) | v2_struct_0(X0) | r1_tmap_1(X1,X0,X2,X5)) )),
% 0.22/0.51    inference(equality_resolution,[],[f72])).
% 0.22/0.51  fof(f72,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~v1_tsep_1(X3,X1) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X3)) | X4 != X5 | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (((r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) | X4 != X5) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_tmap_1)).
% 0.22/0.51  fof(f970,plain,(
% 0.22/0.51    r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),sK5)),
% 0.22/0.51    inference(backward_demodulation,[],[f91,f969])).
% 0.22/0.51  fof(f969,plain,(
% 0.22/0.51    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_tmap_1(sK3,sK1,sK4,sK2)),
% 0.22/0.51    inference(backward_demodulation,[],[f840,f968])).
% 0.22/0.51  fof(f968,plain,(
% 0.22/0.51    k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,k2_struct_0(sK2)) = k2_tmap_1(sK3,sK1,sK4,sK2)),
% 0.22/0.51    inference(forward_demodulation,[],[f965,f242])).
% 0.22/0.51  fof(f965,plain,(
% 0.22/0.51    k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,u1_struct_0(sK2)) = k2_tmap_1(sK3,sK1,sK4,sK2)),
% 0.22/0.51    inference(resolution,[],[f853,f290])).
% 0.22/0.51  fof(f853,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,u1_struct_0(X0)) = k2_tmap_1(sK3,sK1,sK4,X0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f852,f216])).
% 0.22/0.51  fof(f852,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1)) | ~m1_pre_topc(X0,sK3) | k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,u1_struct_0(X0)) = k2_tmap_1(sK3,sK1,sK4,X0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f851,f48])).
% 0.22/0.51  fof(f851,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_funct_1(sK4) | ~v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1)) | ~m1_pre_topc(X0,sK3) | k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,u1_struct_0(X0)) = k2_tmap_1(sK3,sK1,sK4,X0)) )),
% 0.22/0.51    inference(resolution,[],[f660,f217])).
% 0.22/0.51  fof(f660,plain,(
% 0.22/0.51    ( ! [X6,X7] : (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1)))) | ~v1_funct_1(X6) | ~v1_funct_2(X6,k2_struct_0(sK3),k2_struct_0(sK1)) | ~m1_pre_topc(X7,sK3) | k2_tmap_1(sK3,sK1,X6,X7) = k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),X6,u1_struct_0(X7))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f659,f52])).
% 0.22/0.51  fof(f659,plain,(
% 0.22/0.51    ( ! [X6,X7] : (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1)))) | ~v1_funct_1(X6) | ~v1_funct_2(X6,k2_struct_0(sK3),k2_struct_0(sK1)) | v2_struct_0(sK3) | ~m1_pre_topc(X7,sK3) | k2_tmap_1(sK3,sK1,X6,X7) = k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),X6,u1_struct_0(X7))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f658,f112])).
% 0.22/0.51  fof(f658,plain,(
% 0.22/0.51    ( ! [X6,X7] : (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1)))) | ~l1_pre_topc(sK3) | ~v1_funct_1(X6) | ~v1_funct_2(X6,k2_struct_0(sK3),k2_struct_0(sK1)) | v2_struct_0(sK3) | ~m1_pre_topc(X7,sK3) | k2_tmap_1(sK3,sK1,X6,X7) = k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),X6,u1_struct_0(X7))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f651,f121])).
% 0.22/0.51  fof(f651,plain,(
% 0.22/0.51    ( ! [X6,X7] : (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1)))) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~v1_funct_1(X6) | ~v1_funct_2(X6,k2_struct_0(sK3),k2_struct_0(sK1)) | v2_struct_0(sK3) | ~m1_pre_topc(X7,sK3) | k2_tmap_1(sK3,sK1,X6,X7) = k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),X6,u1_struct_0(X7))) )),
% 0.22/0.51    inference(superposition,[],[f313,f214])).
% 0.22/0.51  fof(f313,plain,(
% 0.22/0.51    ( ! [X6,X7,X5] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),k2_struct_0(sK1)))) | ~v2_pre_topc(X6) | ~l1_pre_topc(X6) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X6),k2_struct_0(sK1)) | v2_struct_0(X6) | ~m1_pre_topc(X7,X6) | k2_tmap_1(X6,sK1,X5,X7) = k2_partfun1(u1_struct_0(X6),k2_struct_0(sK1),X5,u1_struct_0(X7))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f312,f58])).
% 0.22/0.51  fof(f312,plain,(
% 0.22/0.51    ( ! [X6,X7,X5] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),k2_struct_0(sK1)))) | ~v2_pre_topc(X6) | ~l1_pre_topc(X6) | ~l1_pre_topc(sK1) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X6),k2_struct_0(sK1)) | v2_struct_0(X6) | ~m1_pre_topc(X7,X6) | k2_tmap_1(X6,sK1,X5,X7) = k2_partfun1(u1_struct_0(X6),k2_struct_0(sK1),X5,u1_struct_0(X7))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f311,f57])).
% 0.22/0.51  fof(f311,plain,(
% 0.22/0.51    ( ! [X6,X7,X5] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),k2_struct_0(sK1)))) | ~v2_pre_topc(X6) | ~l1_pre_topc(X6) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X6),k2_struct_0(sK1)) | v2_struct_0(X6) | ~m1_pre_topc(X7,X6) | k2_tmap_1(X6,sK1,X5,X7) = k2_partfun1(u1_struct_0(X6),k2_struct_0(sK1),X5,u1_struct_0(X7))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f296,f56])).
% 0.22/0.51  fof(f296,plain,(
% 0.22/0.51    ( ! [X6,X7,X5] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),k2_struct_0(sK1)))) | ~v2_pre_topc(X6) | ~l1_pre_topc(X6) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X6),k2_struct_0(sK1)) | v2_struct_0(X6) | ~m1_pre_topc(X7,X6) | k2_tmap_1(X6,sK1,X5,X7) = k2_partfun1(u1_struct_0(X6),k2_struct_0(sK1),X5,u1_struct_0(X7))) )),
% 0.22/0.51    inference(superposition,[],[f71,f107])).
% 0.22/0.51  fof(f71,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | v2_struct_0(X0) | ~m1_pre_topc(X3,X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).
% 0.22/0.51  fof(f840,plain,(
% 0.22/0.51    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,k2_struct_0(sK2))),
% 0.22/0.51    inference(forward_demodulation,[],[f838,f242])).
% 0.22/0.51  fof(f838,plain,(
% 0.22/0.51    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,u1_struct_0(sK2))),
% 0.22/0.51    inference(resolution,[],[f629,f290])).
% 0.22/0.51  fof(f629,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k3_tmap_1(sK0,sK1,sK3,X0,sK4) = k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,u1_struct_0(X0))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f628,f48])).
% 0.22/0.51  fof(f628,plain,(
% 0.22/0.51    ( ! [X0] : (k3_tmap_1(sK0,sK1,sK3,X0,sK4) = k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,u1_struct_0(X0)) | ~v1_funct_1(sK4) | ~m1_pre_topc(X0,sK3)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f627,f216])).
% 0.22/0.51  fof(f627,plain,(
% 0.22/0.51    ( ! [X0] : (k3_tmap_1(sK0,sK1,sK3,X0,sK4) = k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,u1_struct_0(X0)) | ~v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(X0,sK3)) )),
% 0.22/0.51    inference(resolution,[],[f326,f217])).
% 0.22/0.51  fof(f326,plain,(
% 0.22/0.51    ( ! [X21,X22] : (~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1)))) | k3_tmap_1(sK0,sK1,sK3,X22,X21) = k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),X21,u1_struct_0(X22)) | ~v1_funct_2(X21,k2_struct_0(sK3),k2_struct_0(sK1)) | ~v1_funct_1(X21) | ~m1_pre_topc(X22,sK3)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f325,f58])).
% 0.22/0.51  fof(f325,plain,(
% 0.22/0.51    ( ! [X21,X22] : (~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1)))) | k3_tmap_1(sK0,sK1,sK3,X22,X21) = k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),X21,u1_struct_0(X22)) | ~v1_funct_2(X21,k2_struct_0(sK3),k2_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v1_funct_1(X21) | ~m1_pre_topc(X22,sK3)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f324,f57])).
% 0.22/0.51  fof(f324,plain,(
% 0.22/0.51    ( ! [X21,X22] : (~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1)))) | k3_tmap_1(sK0,sK1,sK3,X22,X21) = k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),X21,u1_struct_0(X22)) | ~v1_funct_2(X21,k2_struct_0(sK3),k2_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(X21) | ~m1_pre_topc(X22,sK3)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f304,f56])).
% 0.22/0.51  fof(f304,plain,(
% 0.22/0.51    ( ! [X21,X22] : (~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1)))) | k3_tmap_1(sK0,sK1,sK3,X22,X21) = k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),X21,u1_struct_0(X22)) | ~v1_funct_2(X21,k2_struct_0(sK3),k2_struct_0(sK1)) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(X21) | ~m1_pre_topc(X22,sK3)) )),
% 0.22/0.51    inference(superposition,[],[f221,f107])).
% 0.22/0.51  fof(f221,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(X0)))) | k3_tmap_1(sK0,X0,sK3,X1,X2) = k2_partfun1(k2_struct_0(sK3),u1_struct_0(X0),X2,u1_struct_0(X1)) | ~v1_funct_2(X2,k2_struct_0(sK3),u1_struct_0(X0)) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,sK3)) )),
% 0.22/0.51    inference(forward_demodulation,[],[f220,f214])).
% 0.22/0.51  fof(f220,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X2,k2_struct_0(sK3),u1_struct_0(X0)) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,sK3) | k3_tmap_1(sK0,X0,sK3,X1,X2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X0),X2,u1_struct_0(X1))) )),
% 0.22/0.51    inference(forward_demodulation,[],[f219,f214])).
% 0.22/0.51  fof(f219,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v1_funct_2(X2,k2_struct_0(sK3),u1_struct_0(X0)) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~m1_pre_topc(X1,sK3) | k3_tmap_1(sK0,X0,sK3,X1,X2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X0),X2,u1_struct_0(X1))) )),
% 0.22/0.51    inference(backward_demodulation,[],[f169,f214])).
% 0.22/0.51  fof(f169,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~m1_pre_topc(X1,sK3) | k3_tmap_1(sK0,X0,sK3,X1,X2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X0),X2,u1_struct_0(X1))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f168,f136])).
% 0.22/0.51  fof(f136,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_pre_topc(X0,sK3) | m1_pre_topc(X0,sK0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f135,f60])).
% 0.22/0.51  fof(f135,plain,(
% 0.22/0.51    ( ! [X0] : (~v2_pre_topc(sK0) | ~m1_pre_topc(X0,sK3) | m1_pre_topc(X0,sK0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f133,f61])).
% 0.22/0.51  fof(f133,plain,(
% 0.22/0.51    ( ! [X0] : (~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_pre_topc(X0,sK3) | m1_pre_topc(X0,sK0)) )),
% 0.22/0.51    inference(resolution,[],[f76,f53])).
% 0.22/0.51  fof(f76,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X2,X1) | m1_pre_topc(X2,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f38])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.51    inference(flattening,[],[f37])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).
% 0.22/0.51  fof(f168,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,sK0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~m1_pre_topc(X1,sK3) | k3_tmap_1(sK0,X0,sK3,X1,X2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X0),X2,u1_struct_0(X1))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f167,f59])).
% 0.22/0.51  fof(f59,plain,(
% 0.22/0.51    ~v2_struct_0(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f167,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK0) | ~m1_pre_topc(X1,sK0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~m1_pre_topc(X1,sK3) | k3_tmap_1(sK0,X0,sK3,X1,X2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X0),X2,u1_struct_0(X1))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f166,f61])).
% 0.22/0.51  fof(f166,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~l1_pre_topc(sK0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK0) | ~m1_pre_topc(X1,sK0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~m1_pre_topc(X1,sK3) | k3_tmap_1(sK0,X0,sK3,X1,X2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X0),X2,u1_struct_0(X1))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f164,f60])).
% 0.22/0.51  fof(f164,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK0) | ~m1_pre_topc(X1,sK0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~m1_pre_topc(X1,sK3) | k3_tmap_1(sK0,X0,sK3,X1,X2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X0),X2,u1_struct_0(X1))) )),
% 0.22/0.51    inference(resolution,[],[f70,f53])).
% 0.22/0.51  fof(f70,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X3,X1] : (~m1_pre_topc(X2,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).
% 0.22/0.51  fof(f91,plain,(
% 0.22/0.51    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)),
% 0.22/0.51    inference(backward_demodulation,[],[f45,f44])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (24351)------------------------------
% 0.22/0.51  % (24351)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (24351)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (24351)Memory used [KB]: 2430
% 0.22/0.51  % (24351)Time elapsed: 0.109 s
% 0.22/0.51  % (24351)------------------------------
% 0.22/0.51  % (24351)------------------------------
% 0.22/0.51  % (24333)Success in time 0.153 s
%------------------------------------------------------------------------------
