%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:06 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  214 (7926 expanded)
%              Number of leaves         :   20 (1611 expanded)
%              Depth                    :   30
%              Number of atoms          :  998 (67272 expanded)
%              Number of equality atoms :   82 (7186 expanded)
%              Maximal formula depth    :   24 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2965,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2964,f56])).

fof(f56,plain,(
    ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
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
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
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

fof(f2964,plain,(
    r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(subsumption_resolution,[],[f2963,f135])).

fof(f135,plain,(
    m1_subset_1(sK5,k2_struct_0(sK2)) ),
    inference(backward_demodulation,[],[f109,f131])).

fof(f131,plain,(
    u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(resolution,[],[f115,f120])).

fof(f120,plain,(
    l1_pre_topc(sK2) ),
    inference(resolution,[],[f117,f65])).

fof(f65,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f117,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK0)
      | l1_pre_topc(X1) ) ),
    inference(resolution,[],[f77,f71])).

fof(f71,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f115,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(resolution,[],[f72,f73])).

fof(f73,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f72,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f109,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f53,f54])).

fof(f54,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f24])).

fof(f53,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f24])).

fof(f2963,plain,
    ( ~ m1_subset_1(sK5,k2_struct_0(sK2))
    | r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(resolution,[],[f2958,f2722])).

fof(f2722,plain,(
    r1_tmap_1(sK2,sK1,k2_tmap_1(sK2,sK1,sK4,sK2),sK5) ),
    inference(backward_demodulation,[],[f108,f2721])).

fof(f2721,plain,(
    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_tmap_1(sK2,sK1,sK4,sK2) ),
    inference(forward_demodulation,[],[f2720,f2445])).

fof(f2445,plain,(
    k2_tmap_1(sK2,sK1,sK4,sK2) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,k2_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f2443,f131])).

fof(f2443,plain,(
    k2_tmap_1(sK2,sK1,sK4,sK2) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(sK2)) ),
    inference(resolution,[],[f2437,f125])).

fof(f125,plain,(
    m1_pre_topc(sK2,sK2) ),
    inference(resolution,[],[f120,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f2437,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK2)
      | k2_tmap_1(sK2,sK1,sK4,X2) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X2)) ) ),
    inference(subsumption_resolution,[],[f2436,f120])).

fof(f2436,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK2)
      | k2_tmap_1(sK2,sK1,sK4,X2) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X2))
      | ~ l1_pre_topc(sK2) ) ),
    inference(subsumption_resolution,[],[f2435,f156])).

fof(f156,plain,(
    v2_pre_topc(sK2) ),
    inference(resolution,[],[f151,f65])).

fof(f151,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f147,f70])).

fof(f70,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f147,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_pre_topc(X0) ) ),
    inference(resolution,[],[f87,f71])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f2435,plain,(
    ! [X2] :
      ( ~ v2_pre_topc(sK2)
      | ~ m1_pre_topc(X2,sK2)
      | k2_tmap_1(sK2,sK1,sK4,X2) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X2))
      | ~ l1_pre_topc(sK2) ) ),
    inference(subsumption_resolution,[],[f2434,f447])).

fof(f447,plain,(
    v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f138,f444])).

fof(f444,plain,(
    k2_struct_0(sK2) = k2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f438,f125])).

fof(f438,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | k2_struct_0(sK2) = k2_struct_0(sK3) ),
    inference(resolution,[],[f427,f282])).

fof(f282,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | k2_struct_0(sK2) = k2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f226,f281])).

fof(f281,plain,(
    r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f196,f278])).

fof(f278,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(resolution,[],[f276,f123])).

fof(f123,plain,(
    m1_pre_topc(sK3,sK3) ),
    inference(resolution,[],[f119,f74])).

fof(f119,plain,(
    l1_pre_topc(sK3) ),
    inference(resolution,[],[f117,f63])).

fof(f63,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f276,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK3)
      | m1_pre_topc(X2,sK2) ) ),
    inference(forward_demodulation,[],[f275,f136])).

fof(f136,plain,(
    sK3 = g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(backward_demodulation,[],[f61,f131])).

fof(f61,plain,(
    sK3 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f24])).

fof(f275,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)))
      | m1_pre_topc(X2,sK2) ) ),
    inference(forward_demodulation,[],[f271,f131])).

fof(f271,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
      | m1_pre_topc(X2,sK2) ) ),
    inference(resolution,[],[f80,f120])).

fof(f80,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

fof(f196,plain,
    ( r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2))
    | ~ m1_pre_topc(sK3,sK2) ),
    inference(superposition,[],[f176,f132])).

fof(f132,plain,(
    u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(resolution,[],[f115,f119])).

fof(f176,plain,(
    ! [X2] :
      ( r1_tarski(u1_struct_0(X2),k2_struct_0(sK2))
      | ~ m1_pre_topc(X2,sK2) ) ),
    inference(subsumption_resolution,[],[f172,f120])).

fof(f172,plain,(
    ! [X2] :
      ( r1_tarski(u1_struct_0(X2),k2_struct_0(sK2))
      | ~ m1_pre_topc(X2,sK2)
      | ~ l1_pre_topc(sK2) ) ),
    inference(superposition,[],[f78,f131])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).

fof(f226,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2))
    | k2_struct_0(sK2) = k2_struct_0(sK3) ),
    inference(resolution,[],[f200,f99])).

fof(f99,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f200,plain,
    ( r1_tarski(k2_struct_0(sK2),k2_struct_0(sK3))
    | ~ m1_pre_topc(sK2,sK3) ),
    inference(superposition,[],[f177,f131])).

fof(f177,plain,(
    ! [X3] :
      ( r1_tarski(u1_struct_0(X3),k2_struct_0(sK3))
      | ~ m1_pre_topc(X3,sK3) ) ),
    inference(subsumption_resolution,[],[f173,f119])).

fof(f173,plain,(
    ! [X3] :
      ( r1_tarski(u1_struct_0(X3),k2_struct_0(sK3))
      | ~ m1_pre_topc(X3,sK3)
      | ~ l1_pre_topc(sK3) ) ),
    inference(superposition,[],[f78,f132])).

fof(f427,plain,(
    ! [X2] :
      ( m1_pre_topc(X2,sK3)
      | ~ m1_pre_topc(X2,sK2) ) ),
    inference(forward_demodulation,[],[f426,f136])).

fof(f426,plain,(
    ! [X2] :
      ( m1_pre_topc(X2,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)))
      | ~ m1_pre_topc(X2,sK2) ) ),
    inference(forward_demodulation,[],[f425,f131])).

fof(f425,plain,(
    ! [X2] :
      ( m1_pre_topc(X2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
      | ~ m1_pre_topc(X2,sK2) ) ),
    inference(subsumption_resolution,[],[f419,f124])).

fof(f124,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | l1_pre_topc(X0) ) ),
    inference(resolution,[],[f120,f77])).

fof(f419,plain,(
    ! [X2] :
      ( ~ l1_pre_topc(X2)
      | m1_pre_topc(X2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
      | ~ m1_pre_topc(X2,sK2) ) ),
    inference(resolution,[],[f76,f120])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f138,plain,(
    v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f133,f132])).

fof(f133,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f59,f130])).

fof(f130,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(resolution,[],[f115,f68])).

fof(f68,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f59,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f2434,plain,(
    ! [X2] :
      ( ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1))
      | ~ v2_pre_topc(sK2)
      | ~ m1_pre_topc(X2,sK2)
      | k2_tmap_1(sK2,sK1,sK4,X2) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X2))
      | ~ l1_pre_topc(sK2) ) ),
    inference(subsumption_resolution,[],[f2433,f64])).

fof(f64,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f2433,plain,(
    ! [X2] :
      ( v2_struct_0(sK2)
      | ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1))
      | ~ v2_pre_topc(sK2)
      | ~ m1_pre_topc(X2,sK2)
      | k2_tmap_1(sK2,sK1,sK4,X2) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X2))
      | ~ l1_pre_topc(sK2) ) ),
    inference(subsumption_resolution,[],[f2431,f449])).

fof(f449,plain,(
    r1_tarski(sK4,k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1))) ),
    inference(backward_demodulation,[],[f140,f444])).

fof(f140,plain,(
    r1_tarski(sK4,k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1))) ),
    inference(resolution,[],[f137,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f137,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f134,f132])).

fof(f134,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f60,f130])).

fof(f60,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f24])).

fof(f2431,plain,(
    ! [X2] :
      ( ~ r1_tarski(sK4,k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1)))
      | v2_struct_0(sK2)
      | ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1))
      | ~ v2_pre_topc(sK2)
      | ~ m1_pre_topc(X2,sK2)
      | k2_tmap_1(sK2,sK1,sK4,X2) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X2))
      | ~ l1_pre_topc(sK2) ) ),
    inference(superposition,[],[f2349,f131])).

fof(f2349,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(sK4,k2_zfmisc_1(u1_struct_0(X2),k2_struct_0(sK1)))
      | v2_struct_0(X2)
      | ~ v1_funct_2(sK4,u1_struct_0(X2),k2_struct_0(sK1))
      | ~ v2_pre_topc(X2)
      | ~ m1_pre_topc(X3,X2)
      | k2_tmap_1(X2,sK1,sK4,X3) = k2_partfun1(u1_struct_0(X2),k2_struct_0(sK1),sK4,u1_struct_0(X3))
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f2348,f68])).

fof(f2348,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(sK4,k2_zfmisc_1(u1_struct_0(X2),k2_struct_0(sK1)))
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(X2)
      | ~ v1_funct_2(sK4,u1_struct_0(X2),k2_struct_0(sK1))
      | ~ v2_pre_topc(X2)
      | ~ m1_pre_topc(X3,X2)
      | k2_tmap_1(X2,sK1,sK4,X3) = k2_partfun1(u1_struct_0(X2),k2_struct_0(sK1),sK4,u1_struct_0(X3))
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f2347,f67])).

fof(f67,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f2347,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(sK4,k2_zfmisc_1(u1_struct_0(X2),k2_struct_0(sK1)))
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(X2)
      | ~ v1_funct_2(sK4,u1_struct_0(X2),k2_struct_0(sK1))
      | ~ v2_pre_topc(X2)
      | ~ m1_pre_topc(X3,X2)
      | k2_tmap_1(X2,sK1,sK4,X3) = k2_partfun1(u1_struct_0(X2),k2_struct_0(sK1),sK4,u1_struct_0(X3))
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f2329,f66])).

fof(f66,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f2329,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(sK4,k2_zfmisc_1(u1_struct_0(X2),k2_struct_0(sK1)))
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(X2)
      | ~ v1_funct_2(sK4,u1_struct_0(X2),k2_struct_0(sK1))
      | ~ v2_pre_topc(X2)
      | ~ m1_pre_topc(X3,X2)
      | k2_tmap_1(X2,sK1,sK4,X3) = k2_partfun1(u1_struct_0(X2),k2_struct_0(sK1),sK4,u1_struct_0(X3))
      | ~ l1_pre_topc(X2) ) ),
    inference(superposition,[],[f1965,f130])).

fof(f1965,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(sK4,k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X0)
      | ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X2,X0)
      | k2_tmap_1(X0,X1,sK4,X2) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f1772,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f1772,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X0)
      | ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X2,X0)
      | k2_tmap_1(X0,X1,sK4,X2) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) ) ),
    inference(resolution,[],[f82,f58])).

fof(f58,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f24])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X0)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f2720,plain,(
    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,k2_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f2717,f131])).

fof(f2717,plain,(
    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(sK2)) ),
    inference(resolution,[],[f2708,f1151])).

fof(f1151,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f1150,f70])).

fof(f1150,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f1149,f71])).

fof(f1149,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_pre_topc(sK2,sK3)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f1144,f65])).

fof(f1144,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | m1_pre_topc(sK2,sK3)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f1140,f63])).

fof(f1140,plain,(
    ! [X3] :
      ( ~ m1_pre_topc(sK3,X3)
      | ~ m1_pre_topc(sK2,X3)
      | ~ l1_pre_topc(X3)
      | m1_pre_topc(sK2,sK3)
      | ~ v2_pre_topc(X3) ) ),
    inference(subsumption_resolution,[],[f1137,f106])).

fof(f106,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1137,plain,(
    ! [X3] :
      ( ~ r1_tarski(k2_struct_0(sK2),k2_struct_0(sK2))
      | ~ l1_pre_topc(X3)
      | ~ m1_pre_topc(sK2,X3)
      | ~ m1_pre_topc(sK3,X3)
      | m1_pre_topc(sK2,sK3)
      | ~ v2_pre_topc(X3) ) ),
    inference(superposition,[],[f1036,f445])).

fof(f445,plain,(
    u1_struct_0(sK3) = k2_struct_0(sK2) ),
    inference(backward_demodulation,[],[f132,f444])).

fof(f1036,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(k2_struct_0(sK2),u1_struct_0(X4))
      | ~ l1_pre_topc(X5)
      | ~ m1_pre_topc(sK2,X5)
      | ~ m1_pre_topc(X4,X5)
      | m1_pre_topc(sK2,X4)
      | ~ v2_pre_topc(X5) ) ),
    inference(superposition,[],[f90,f131])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | m1_pre_topc(X1,X2)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

fof(f2708,plain,(
    ! [X3] :
      ( ~ m1_pre_topc(X3,sK3)
      | k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3)) = k3_tmap_1(sK0,sK1,sK3,X3,sK4) ) ),
    inference(subsumption_resolution,[],[f2707,f71])).

fof(f2707,plain,(
    ! [X3] :
      ( ~ m1_pre_topc(X3,sK3)
      | k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3)) = k3_tmap_1(sK0,sK1,sK3,X3,sK4)
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f2706,f70])).

fof(f2706,plain,(
    ! [X3] :
      ( ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(X3,sK3)
      | k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3)) = k3_tmap_1(sK0,sK1,sK3,X3,sK4)
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f2700,f69])).

fof(f69,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f2700,plain,(
    ! [X3] :
      ( v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(X3,sK3)
      | k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3)) = k3_tmap_1(sK0,sK1,sK3,X3,sK4)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f2660,f63])).

fof(f2660,plain,(
    ! [X6,X7] :
      ( ~ m1_pre_topc(sK3,X6)
      | v2_struct_0(X6)
      | ~ v2_pre_topc(X6)
      | ~ m1_pre_topc(X7,sK3)
      | k3_tmap_1(X6,sK1,sK3,X7,sK4) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X7))
      | ~ l1_pre_topc(X6) ) ),
    inference(subsumption_resolution,[],[f2659,f447])).

fof(f2659,plain,(
    ! [X6,X7] :
      ( ~ m1_pre_topc(sK3,X6)
      | v2_struct_0(X6)
      | ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1))
      | ~ v2_pre_topc(X6)
      | ~ m1_pre_topc(X7,sK3)
      | k3_tmap_1(X6,sK1,sK3,X7,sK4) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X7))
      | ~ l1_pre_topc(X6) ) ),
    inference(subsumption_resolution,[],[f2656,f449])).

fof(f2656,plain,(
    ! [X6,X7] :
      ( ~ r1_tarski(sK4,k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1)))
      | ~ m1_pre_topc(sK3,X6)
      | v2_struct_0(X6)
      | ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1))
      | ~ v2_pre_topc(X6)
      | ~ m1_pre_topc(X7,sK3)
      | k3_tmap_1(X6,sK1,sK3,X7,sK4) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X7))
      | ~ l1_pre_topc(X6) ) ),
    inference(superposition,[],[f2396,f445])).

fof(f2396,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(sK4,k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK1)))
      | ~ m1_pre_topc(X3,X4)
      | v2_struct_0(X4)
      | ~ v1_funct_2(sK4,u1_struct_0(X3),k2_struct_0(sK1))
      | ~ v2_pre_topc(X4)
      | ~ m1_pre_topc(X5,X3)
      | k3_tmap_1(X4,sK1,X3,X5,sK4) = k2_partfun1(u1_struct_0(X3),k2_struct_0(sK1),sK4,u1_struct_0(X5))
      | ~ l1_pre_topc(X4) ) ),
    inference(subsumption_resolution,[],[f2395,f68])).

fof(f2395,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(sK4,k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK1)))
      | ~ l1_pre_topc(sK1)
      | ~ m1_pre_topc(X3,X4)
      | v2_struct_0(X4)
      | ~ v1_funct_2(sK4,u1_struct_0(X3),k2_struct_0(sK1))
      | ~ v2_pre_topc(X4)
      | ~ m1_pre_topc(X5,X3)
      | k3_tmap_1(X4,sK1,X3,X5,sK4) = k2_partfun1(u1_struct_0(X3),k2_struct_0(sK1),sK4,u1_struct_0(X5))
      | ~ l1_pre_topc(X4) ) ),
    inference(subsumption_resolution,[],[f2394,f67])).

fof(f2394,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(sK4,k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK1)))
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ m1_pre_topc(X3,X4)
      | v2_struct_0(X4)
      | ~ v1_funct_2(sK4,u1_struct_0(X3),k2_struct_0(sK1))
      | ~ v2_pre_topc(X4)
      | ~ m1_pre_topc(X5,X3)
      | k3_tmap_1(X4,sK1,X3,X5,sK4) = k2_partfun1(u1_struct_0(X3),k2_struct_0(sK1),sK4,u1_struct_0(X5))
      | ~ l1_pre_topc(X4) ) ),
    inference(subsumption_resolution,[],[f2388,f66])).

fof(f2388,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(sK4,k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK1)))
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ m1_pre_topc(X3,X4)
      | v2_struct_0(X4)
      | ~ v1_funct_2(sK4,u1_struct_0(X3),k2_struct_0(sK1))
      | ~ v2_pre_topc(X4)
      | ~ m1_pre_topc(X5,X3)
      | k3_tmap_1(X4,sK1,X3,X5,sK4) = k2_partfun1(u1_struct_0(X3),k2_struct_0(sK1),sK4,u1_struct_0(X5))
      | ~ l1_pre_topc(X4) ) ),
    inference(superposition,[],[f2027,f130])).

fof(f2027,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(sK4,k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0)
      | ~ v1_funct_2(sK4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X3,X2)
      | k3_tmap_1(X0,X1,X2,X3,sK4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),sK4,u1_struct_0(X3))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f1888,f100])).

fof(f1888,plain,(
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
    inference(subsumption_resolution,[],[f1887,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X1)
      | m1_pre_topc(X2,X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f1887,plain,(
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
    inference(resolution,[],[f81,f58])).

fof(f81,plain,(
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
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f108,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(backward_demodulation,[],[f55,f54])).

fof(f55,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f24])).

fof(f2958,plain,(
    ! [X2] :
      ( ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK2,sK1,sK4,sK2),X2)
      | ~ m1_subset_1(X2,k2_struct_0(sK2))
      | r1_tmap_1(sK3,sK1,sK4,X2) ) ),
    inference(forward_demodulation,[],[f2957,f2454])).

fof(f2454,plain,(
    k2_tmap_1(sK2,sK1,sK4,sK2) = k2_tmap_1(sK3,sK1,sK4,sK2) ),
    inference(forward_demodulation,[],[f2453,f2445])).

fof(f2453,plain,(
    k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,k2_struct_0(sK2)) = k2_tmap_1(sK3,sK1,sK4,sK2) ),
    inference(forward_demodulation,[],[f2450,f131])).

fof(f2450,plain,(
    k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(sK2)) = k2_tmap_1(sK3,sK1,sK4,sK2) ),
    inference(resolution,[],[f2442,f1151])).

fof(f2442,plain,(
    ! [X3] :
      ( ~ m1_pre_topc(X3,sK3)
      | k2_tmap_1(sK3,sK1,sK4,X3) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3)) ) ),
    inference(subsumption_resolution,[],[f2441,f119])).

fof(f2441,plain,(
    ! [X3] :
      ( ~ m1_pre_topc(X3,sK3)
      | k2_tmap_1(sK3,sK1,sK4,X3) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3))
      | ~ l1_pre_topc(sK3) ) ),
    inference(subsumption_resolution,[],[f2440,f155])).

fof(f155,plain,(
    v2_pre_topc(sK3) ),
    inference(resolution,[],[f151,f63])).

fof(f2440,plain,(
    ! [X3] :
      ( ~ v2_pre_topc(sK3)
      | ~ m1_pre_topc(X3,sK3)
      | k2_tmap_1(sK3,sK1,sK4,X3) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3))
      | ~ l1_pre_topc(sK3) ) ),
    inference(subsumption_resolution,[],[f2439,f447])).

fof(f2439,plain,(
    ! [X3] :
      ( ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1))
      | ~ v2_pre_topc(sK3)
      | ~ m1_pre_topc(X3,sK3)
      | k2_tmap_1(sK3,sK1,sK4,X3) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3))
      | ~ l1_pre_topc(sK3) ) ),
    inference(subsumption_resolution,[],[f2438,f62])).

fof(f62,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f2438,plain,(
    ! [X3] :
      ( v2_struct_0(sK3)
      | ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1))
      | ~ v2_pre_topc(sK3)
      | ~ m1_pre_topc(X3,sK3)
      | k2_tmap_1(sK3,sK1,sK4,X3) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3))
      | ~ l1_pre_topc(sK3) ) ),
    inference(subsumption_resolution,[],[f2432,f449])).

fof(f2432,plain,(
    ! [X3] :
      ( ~ r1_tarski(sK4,k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1)))
      | v2_struct_0(sK3)
      | ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1))
      | ~ v2_pre_topc(sK3)
      | ~ m1_pre_topc(X3,sK3)
      | k2_tmap_1(sK3,sK1,sK4,X3) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3))
      | ~ l1_pre_topc(sK3) ) ),
    inference(superposition,[],[f2349,f445])).

fof(f2957,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k2_struct_0(sK2))
      | ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),X2)
      | r1_tmap_1(sK3,sK1,sK4,X2) ) ),
    inference(forward_demodulation,[],[f2956,f131])).

fof(f2956,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK2))
      | ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),X2)
      | r1_tmap_1(sK3,sK1,sK4,X2) ) ),
    inference(subsumption_resolution,[],[f2955,f1151])).

fof(f2955,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(sK2,sK3)
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),X2)
      | r1_tmap_1(sK3,sK1,sK4,X2) ) ),
    inference(subsumption_resolution,[],[f2952,f64])).

fof(f2952,plain,(
    ! [X2] :
      ( v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,sK3)
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),X2)
      | r1_tmap_1(sK3,sK1,sK4,X2) ) ),
    inference(resolution,[],[f2908,f1152])).

fof(f1152,plain,(
    v1_tsep_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f610,f1151])).

fof(f610,plain,
    ( v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f608,f451])).

fof(f451,plain,(
    v3_pre_topc(k2_struct_0(sK2),sK3) ),
    inference(backward_demodulation,[],[f159,f444])).

fof(f159,plain,(
    v3_pre_topc(k2_struct_0(sK3),sK3) ),
    inference(subsumption_resolution,[],[f144,f155])).

fof(f144,plain,
    ( v3_pre_topc(k2_struct_0(sK3),sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(resolution,[],[f86,f119])).

fof(f86,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v3_pre_topc(k2_struct_0(X0),X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

fof(f608,plain,
    ( ~ v3_pre_topc(k2_struct_0(sK2),sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | v1_tsep_1(sK2,sK3) ),
    inference(superposition,[],[f583,f131])).

fof(f583,plain,(
    ! [X3] :
      ( ~ v3_pre_topc(u1_struct_0(X3),sK3)
      | ~ m1_pre_topc(X3,sK3)
      | v1_tsep_1(X3,sK3) ) ),
    inference(subsumption_resolution,[],[f579,f155])).

fof(f579,plain,(
    ! [X3] :
      ( ~ v2_pre_topc(sK3)
      | ~ m1_pre_topc(X3,sK3)
      | ~ v3_pre_topc(u1_struct_0(X3),sK3)
      | v1_tsep_1(X3,sK3) ) ),
    inference(resolution,[],[f111,f119])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f104,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | ~ v3_pre_topc(X2,X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
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
    inference(flattening,[],[f49])).

fof(f49,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f2908,plain,(
    ! [X6,X7] :
      ( ~ v1_tsep_1(X6,sK3)
      | v2_struct_0(X6)
      | ~ m1_pre_topc(X6,sK3)
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ r1_tmap_1(X6,sK1,k2_tmap_1(sK3,sK1,sK4,X6),X7)
      | r1_tmap_1(sK3,sK1,sK4,X7) ) ),
    inference(subsumption_resolution,[],[f2907,f447])).

fof(f2907,plain,(
    ! [X6,X7] :
      ( ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1))
      | v2_struct_0(X6)
      | ~ v1_tsep_1(X6,sK3)
      | ~ m1_pre_topc(X6,sK3)
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ r1_tmap_1(X6,sK1,k2_tmap_1(sK3,sK1,sK4,X6),X7)
      | r1_tmap_1(sK3,sK1,sK4,X7) ) ),
    inference(subsumption_resolution,[],[f2906,f119])).

fof(f2906,plain,(
    ! [X6,X7] :
      ( ~ l1_pre_topc(sK3)
      | ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1))
      | v2_struct_0(X6)
      | ~ v1_tsep_1(X6,sK3)
      | ~ m1_pre_topc(X6,sK3)
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ r1_tmap_1(X6,sK1,k2_tmap_1(sK3,sK1,sK4,X6),X7)
      | r1_tmap_1(sK3,sK1,sK4,X7) ) ),
    inference(subsumption_resolution,[],[f2905,f155])).

fof(f2905,plain,(
    ! [X6,X7] :
      ( ~ v2_pre_topc(sK3)
      | ~ l1_pre_topc(sK3)
      | ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1))
      | v2_struct_0(X6)
      | ~ v1_tsep_1(X6,sK3)
      | ~ m1_pre_topc(X6,sK3)
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ r1_tmap_1(X6,sK1,k2_tmap_1(sK3,sK1,sK4,X6),X7)
      | r1_tmap_1(sK3,sK1,sK4,X7) ) ),
    inference(subsumption_resolution,[],[f2904,f62])).

fof(f2904,plain,(
    ! [X6,X7] :
      ( v2_struct_0(sK3)
      | ~ v2_pre_topc(sK3)
      | ~ l1_pre_topc(sK3)
      | ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1))
      | v2_struct_0(X6)
      | ~ v1_tsep_1(X6,sK3)
      | ~ m1_pre_topc(X6,sK3)
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ r1_tmap_1(X6,sK1,k2_tmap_1(sK3,sK1,sK4,X6),X7)
      | r1_tmap_1(sK3,sK1,sK4,X7) ) ),
    inference(subsumption_resolution,[],[f2898,f449])).

fof(f2898,plain,(
    ! [X6,X7] :
      ( ~ r1_tarski(sK4,k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1)))
      | v2_struct_0(sK3)
      | ~ v2_pre_topc(sK3)
      | ~ l1_pre_topc(sK3)
      | ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1))
      | v2_struct_0(X6)
      | ~ v1_tsep_1(X6,sK3)
      | ~ m1_pre_topc(X6,sK3)
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ r1_tmap_1(X6,sK1,k2_tmap_1(sK3,sK1,sK4,X6),X7)
      | r1_tmap_1(sK3,sK1,sK4,X7) ) ),
    inference(superposition,[],[f2642,f445])).

fof(f2642,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(sK4,k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK1)))
      | v2_struct_0(X3)
      | ~ v2_pre_topc(X3)
      | ~ l1_pre_topc(X3)
      | ~ v1_funct_2(sK4,u1_struct_0(X3),k2_struct_0(sK1))
      | v2_struct_0(X4)
      | ~ v1_tsep_1(X4,X3)
      | ~ m1_pre_topc(X4,X3)
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ r1_tmap_1(X4,sK1,k2_tmap_1(X3,sK1,sK4,X4),X5)
      | r1_tmap_1(X3,sK1,sK4,X5) ) ),
    inference(subsumption_resolution,[],[f2641,f68])).

fof(f2641,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(sK4,k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK1)))
      | v2_struct_0(X3)
      | ~ v2_pre_topc(X3)
      | ~ l1_pre_topc(X3)
      | ~ v1_funct_2(sK4,u1_struct_0(X3),k2_struct_0(sK1))
      | v2_struct_0(X4)
      | ~ v1_tsep_1(X4,X3)
      | ~ m1_pre_topc(X4,X3)
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ r1_tmap_1(X4,sK1,k2_tmap_1(X3,sK1,sK4,X4),X5)
      | r1_tmap_1(X3,sK1,sK4,X5)
      | ~ l1_pre_topc(sK1) ) ),
    inference(subsumption_resolution,[],[f2640,f67])).

fof(f2640,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(sK4,k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK1)))
      | v2_struct_0(X3)
      | ~ v2_pre_topc(X3)
      | ~ l1_pre_topc(X3)
      | ~ v1_funct_2(sK4,u1_struct_0(X3),k2_struct_0(sK1))
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(X4)
      | ~ v1_tsep_1(X4,X3)
      | ~ m1_pre_topc(X4,X3)
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ r1_tmap_1(X4,sK1,k2_tmap_1(X3,sK1,sK4,X4),X5)
      | r1_tmap_1(X3,sK1,sK4,X5)
      | ~ l1_pre_topc(sK1) ) ),
    inference(subsumption_resolution,[],[f2622,f66])).

fof(f2622,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(sK4,k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK1)))
      | v2_struct_0(X3)
      | ~ v2_pre_topc(X3)
      | ~ l1_pre_topc(X3)
      | v2_struct_0(sK1)
      | ~ v1_funct_2(sK4,u1_struct_0(X3),k2_struct_0(sK1))
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(X4)
      | ~ v1_tsep_1(X4,X3)
      | ~ m1_pre_topc(X4,X3)
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ r1_tmap_1(X4,sK1,k2_tmap_1(X3,sK1,sK4,X4),X5)
      | r1_tmap_1(X3,sK1,sK4,X5)
      | ~ l1_pre_topc(sK1) ) ),
    inference(superposition,[],[f2228,f130])).

fof(f2228,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(sK4,k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X0)
      | ~ v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X2)
      | ~ v1_tsep_1(X2,X1)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ r1_tmap_1(X2,X0,k2_tmap_1(X1,X0,sK4,X2),X3)
      | r1_tmap_1(X1,X0,sK4,X3)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f1928,f100])).

fof(f1928,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X0)
      | ~ v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X2)
      | ~ v1_tsep_1(X2,X1)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ r1_tmap_1(X2,X0,k2_tmap_1(X1,X0,sK4,X2),X3)
      | r1_tmap_1(X1,X0,sK4,X3) ) ),
    inference(subsumption_resolution,[],[f1927,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).

fof(f1927,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X0)
      | ~ v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | v2_struct_0(X2)
      | ~ v1_tsep_1(X2,X1)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ r1_tmap_1(X2,X0,k2_tmap_1(X1,X0,sK4,X2),X3)
      | r1_tmap_1(X1,X0,sK4,X3) ) ),
    inference(resolution,[],[f103,f58])).

fof(f103,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X0)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | v2_struct_0(X3)
      | ~ v1_tsep_1(X3,X1)
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | r1_tmap_1(X1,X0,X2,X5) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
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
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:40:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.45  % (25794)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.46  % (25808)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.47  % (25804)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.47  % (25796)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.49  % (25795)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.49  % (25789)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.49  % (25794)Refutation not found, incomplete strategy% (25794)------------------------------
% 0.22/0.49  % (25794)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (25794)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (25794)Memory used [KB]: 6652
% 0.22/0.49  % (25794)Time elapsed: 0.072 s
% 0.22/0.49  % (25794)------------------------------
% 0.22/0.49  % (25794)------------------------------
% 0.22/0.49  % (25796)Refutation not found, incomplete strategy% (25796)------------------------------
% 0.22/0.49  % (25796)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (25796)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (25796)Memory used [KB]: 1918
% 0.22/0.49  % (25796)Time elapsed: 0.064 s
% 0.22/0.49  % (25796)------------------------------
% 0.22/0.49  % (25796)------------------------------
% 0.22/0.50  % (25792)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.50  % (25790)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (25813)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.52  % (25791)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.52  % (25789)Refutation not found, incomplete strategy% (25789)------------------------------
% 0.22/0.52  % (25789)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (25789)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (25789)Memory used [KB]: 10874
% 0.22/0.52  % (25789)Time elapsed: 0.105 s
% 0.22/0.52  % (25789)------------------------------
% 0.22/0.52  % (25789)------------------------------
% 0.22/0.52  % (25799)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.52  % (25812)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.52  % (25802)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.53  % (25793)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.53  % (25806)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.53  % (25803)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.54  % (25809)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.54  % (25811)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.54  % (25800)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.54  % (25797)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.54  % (25814)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.54  % (25798)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.55  % (25810)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.55  % (25801)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.55  % (25807)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.56  % (25805)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.57  % (25808)Refutation found. Thanks to Tanya!
% 0.22/0.57  % SZS status Theorem for theBenchmark
% 0.22/0.57  % SZS output start Proof for theBenchmark
% 0.22/0.57  fof(f2965,plain,(
% 0.22/0.57    $false),
% 0.22/0.57    inference(subsumption_resolution,[],[f2964,f56])).
% 0.22/0.57  fof(f56,plain,(
% 0.22/0.57    ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.22/0.57    inference(cnf_transformation,[],[f24])).
% 0.22/0.57  fof(f24,plain,(
% 0.22/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.57    inference(flattening,[],[f23])).
% 0.22/0.57  fof(f23,plain,(
% 0.22/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f22])).
% 0.22/0.57  fof(f22,negated_conjecture,(
% 0.22/0.57    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 0.22/0.57    inference(negated_conjecture,[],[f21])).
% 0.22/0.57  fof(f21,conjecture,(
% 0.22/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tmap_1)).
% 0.22/0.57  fof(f2964,plain,(
% 0.22/0.57    r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.22/0.57    inference(subsumption_resolution,[],[f2963,f135])).
% 0.22/0.57  fof(f135,plain,(
% 0.22/0.57    m1_subset_1(sK5,k2_struct_0(sK2))),
% 0.22/0.57    inference(backward_demodulation,[],[f109,f131])).
% 0.22/0.57  fof(f131,plain,(
% 0.22/0.57    u1_struct_0(sK2) = k2_struct_0(sK2)),
% 0.22/0.57    inference(resolution,[],[f115,f120])).
% 0.22/0.57  fof(f120,plain,(
% 0.22/0.57    l1_pre_topc(sK2)),
% 0.22/0.57    inference(resolution,[],[f117,f65])).
% 0.22/0.57  fof(f65,plain,(
% 0.22/0.57    m1_pre_topc(sK2,sK0)),
% 0.22/0.57    inference(cnf_transformation,[],[f24])).
% 0.22/0.57  fof(f117,plain,(
% 0.22/0.57    ( ! [X1] : (~m1_pre_topc(X1,sK0) | l1_pre_topc(X1)) )),
% 0.22/0.57    inference(resolution,[],[f77,f71])).
% 0.22/0.57  fof(f71,plain,(
% 0.22/0.57    l1_pre_topc(sK0)),
% 0.22/0.57    inference(cnf_transformation,[],[f24])).
% 0.22/0.57  fof(f77,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f29])).
% 0.22/0.57  fof(f29,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.57    inference(ennf_transformation,[],[f6])).
% 0.22/0.57  fof(f6,axiom,(
% 0.22/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.22/0.57  fof(f115,plain,(
% 0.22/0.57    ( ! [X0] : (~l1_pre_topc(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.57    inference(resolution,[],[f72,f73])).
% 0.22/0.57  fof(f73,plain,(
% 0.22/0.57    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f26])).
% 0.22/0.57  fof(f26,plain,(
% 0.22/0.57    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.57    inference(ennf_transformation,[],[f5])).
% 0.22/0.57  fof(f5,axiom,(
% 0.22/0.57    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.57  fof(f72,plain,(
% 0.22/0.57    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f25])).
% 0.22/0.57  fof(f25,plain,(
% 0.22/0.57    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.57    inference(ennf_transformation,[],[f4])).
% 0.22/0.57  fof(f4,axiom,(
% 0.22/0.57    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.57  fof(f109,plain,(
% 0.22/0.57    m1_subset_1(sK5,u1_struct_0(sK2))),
% 0.22/0.57    inference(forward_demodulation,[],[f53,f54])).
% 0.22/0.57  fof(f54,plain,(
% 0.22/0.57    sK5 = sK6),
% 0.22/0.57    inference(cnf_transformation,[],[f24])).
% 0.22/0.57  fof(f53,plain,(
% 0.22/0.57    m1_subset_1(sK6,u1_struct_0(sK2))),
% 0.22/0.57    inference(cnf_transformation,[],[f24])).
% 0.22/0.57  fof(f2963,plain,(
% 0.22/0.57    ~m1_subset_1(sK5,k2_struct_0(sK2)) | r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.22/0.57    inference(resolution,[],[f2958,f2722])).
% 0.22/0.57  fof(f2722,plain,(
% 0.22/0.57    r1_tmap_1(sK2,sK1,k2_tmap_1(sK2,sK1,sK4,sK2),sK5)),
% 0.22/0.57    inference(backward_demodulation,[],[f108,f2721])).
% 0.22/0.57  fof(f2721,plain,(
% 0.22/0.57    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_tmap_1(sK2,sK1,sK4,sK2)),
% 0.22/0.57    inference(forward_demodulation,[],[f2720,f2445])).
% 0.22/0.57  fof(f2445,plain,(
% 0.22/0.57    k2_tmap_1(sK2,sK1,sK4,sK2) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,k2_struct_0(sK2))),
% 0.22/0.57    inference(forward_demodulation,[],[f2443,f131])).
% 0.22/0.57  fof(f2443,plain,(
% 0.22/0.57    k2_tmap_1(sK2,sK1,sK4,sK2) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(sK2))),
% 0.22/0.57    inference(resolution,[],[f2437,f125])).
% 0.22/0.57  fof(f125,plain,(
% 0.22/0.57    m1_pre_topc(sK2,sK2)),
% 0.22/0.57    inference(resolution,[],[f120,f74])).
% 0.22/0.57  fof(f74,plain,(
% 0.22/0.57    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f27])).
% 0.22/0.57  fof(f27,plain,(
% 0.22/0.57    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.22/0.57    inference(ennf_transformation,[],[f16])).
% 0.22/0.57  fof(f16,axiom,(
% 0.22/0.57    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.22/0.57  fof(f2437,plain,(
% 0.22/0.57    ( ! [X2] : (~m1_pre_topc(X2,sK2) | k2_tmap_1(sK2,sK1,sK4,X2) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X2))) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f2436,f120])).
% 0.22/0.57  fof(f2436,plain,(
% 0.22/0.57    ( ! [X2] : (~m1_pre_topc(X2,sK2) | k2_tmap_1(sK2,sK1,sK4,X2) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X2)) | ~l1_pre_topc(sK2)) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f2435,f156])).
% 0.22/0.57  fof(f156,plain,(
% 0.22/0.57    v2_pre_topc(sK2)),
% 0.22/0.57    inference(resolution,[],[f151,f65])).
% 0.22/0.57  fof(f151,plain,(
% 0.22/0.57    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v2_pre_topc(X0)) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f147,f70])).
% 0.22/0.57  fof(f70,plain,(
% 0.22/0.57    v2_pre_topc(sK0)),
% 0.22/0.57    inference(cnf_transformation,[],[f24])).
% 0.22/0.57  fof(f147,plain,(
% 0.22/0.57    ( ! [X0] : (~v2_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | v2_pre_topc(X0)) )),
% 0.22/0.57    inference(resolution,[],[f87,f71])).
% 0.22/0.57  fof(f87,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_pre_topc(X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f44])).
% 0.22/0.57  fof(f44,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.57    inference(flattening,[],[f43])).
% 0.22/0.57  fof(f43,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f3])).
% 0.22/0.57  fof(f3,axiom,(
% 0.22/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.22/0.57  fof(f2435,plain,(
% 0.22/0.57    ( ! [X2] : (~v2_pre_topc(sK2) | ~m1_pre_topc(X2,sK2) | k2_tmap_1(sK2,sK1,sK4,X2) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X2)) | ~l1_pre_topc(sK2)) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f2434,f447])).
% 0.22/0.57  fof(f447,plain,(
% 0.22/0.57    v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1))),
% 0.22/0.57    inference(backward_demodulation,[],[f138,f444])).
% 0.22/0.57  fof(f444,plain,(
% 0.22/0.57    k2_struct_0(sK2) = k2_struct_0(sK3)),
% 0.22/0.57    inference(subsumption_resolution,[],[f438,f125])).
% 0.22/0.57  fof(f438,plain,(
% 0.22/0.57    ~m1_pre_topc(sK2,sK2) | k2_struct_0(sK2) = k2_struct_0(sK3)),
% 0.22/0.57    inference(resolution,[],[f427,f282])).
% 0.22/0.57  fof(f282,plain,(
% 0.22/0.57    ~m1_pre_topc(sK2,sK3) | k2_struct_0(sK2) = k2_struct_0(sK3)),
% 0.22/0.57    inference(subsumption_resolution,[],[f226,f281])).
% 0.22/0.57  fof(f281,plain,(
% 0.22/0.57    r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2))),
% 0.22/0.57    inference(subsumption_resolution,[],[f196,f278])).
% 0.22/0.57  fof(f278,plain,(
% 0.22/0.57    m1_pre_topc(sK3,sK2)),
% 0.22/0.57    inference(resolution,[],[f276,f123])).
% 0.22/0.57  fof(f123,plain,(
% 0.22/0.57    m1_pre_topc(sK3,sK3)),
% 0.22/0.57    inference(resolution,[],[f119,f74])).
% 0.22/0.57  fof(f119,plain,(
% 0.22/0.57    l1_pre_topc(sK3)),
% 0.22/0.57    inference(resolution,[],[f117,f63])).
% 0.22/0.57  fof(f63,plain,(
% 0.22/0.57    m1_pre_topc(sK3,sK0)),
% 0.22/0.57    inference(cnf_transformation,[],[f24])).
% 0.22/0.57  fof(f276,plain,(
% 0.22/0.57    ( ! [X2] : (~m1_pre_topc(X2,sK3) | m1_pre_topc(X2,sK2)) )),
% 0.22/0.57    inference(forward_demodulation,[],[f275,f136])).
% 0.22/0.57  fof(f136,plain,(
% 0.22/0.57    sK3 = g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))),
% 0.22/0.57    inference(backward_demodulation,[],[f61,f131])).
% 0.22/0.57  fof(f61,plain,(
% 0.22/0.57    sK3 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 0.22/0.57    inference(cnf_transformation,[],[f24])).
% 0.22/0.57  fof(f275,plain,(
% 0.22/0.57    ( ! [X2] : (~m1_pre_topc(X2,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))) | m1_pre_topc(X2,sK2)) )),
% 0.22/0.57    inference(forward_demodulation,[],[f271,f131])).
% 0.22/0.57  fof(f271,plain,(
% 0.22/0.57    ( ! [X2] : (~m1_pre_topc(X2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | m1_pre_topc(X2,sK2)) )),
% 0.22/0.57    inference(resolution,[],[f80,f120])).
% 0.22/0.57  fof(f80,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | m1_pre_topc(X1,X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f32])).
% 0.22/0.57  fof(f32,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.57    inference(ennf_transformation,[],[f8])).
% 0.22/0.57  fof(f8,axiom,(
% 0.22/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).
% 0.22/0.57  fof(f196,plain,(
% 0.22/0.57    r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) | ~m1_pre_topc(sK3,sK2)),
% 0.22/0.57    inference(superposition,[],[f176,f132])).
% 0.22/0.57  fof(f132,plain,(
% 0.22/0.57    u1_struct_0(sK3) = k2_struct_0(sK3)),
% 0.22/0.57    inference(resolution,[],[f115,f119])).
% 0.22/0.57  fof(f176,plain,(
% 0.22/0.57    ( ! [X2] : (r1_tarski(u1_struct_0(X2),k2_struct_0(sK2)) | ~m1_pre_topc(X2,sK2)) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f172,f120])).
% 0.22/0.57  fof(f172,plain,(
% 0.22/0.57    ( ! [X2] : (r1_tarski(u1_struct_0(X2),k2_struct_0(sK2)) | ~m1_pre_topc(X2,sK2) | ~l1_pre_topc(sK2)) )),
% 0.22/0.57    inference(superposition,[],[f78,f131])).
% 0.22/0.57  fof(f78,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f30])).
% 0.22/0.57  fof(f30,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.57    inference(ennf_transformation,[],[f17])).
% 0.22/0.57  fof(f17,axiom,(
% 0.22/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).
% 0.22/0.57  fof(f226,plain,(
% 0.22/0.57    ~m1_pre_topc(sK2,sK3) | ~r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) | k2_struct_0(sK2) = k2_struct_0(sK3)),
% 0.22/0.57    inference(resolution,[],[f200,f99])).
% 0.22/0.57  fof(f99,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.22/0.57    inference(cnf_transformation,[],[f1])).
% 0.22/0.57  fof(f1,axiom,(
% 0.22/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.57  fof(f200,plain,(
% 0.22/0.57    r1_tarski(k2_struct_0(sK2),k2_struct_0(sK3)) | ~m1_pre_topc(sK2,sK3)),
% 0.22/0.57    inference(superposition,[],[f177,f131])).
% 0.22/0.57  fof(f177,plain,(
% 0.22/0.57    ( ! [X3] : (r1_tarski(u1_struct_0(X3),k2_struct_0(sK3)) | ~m1_pre_topc(X3,sK3)) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f173,f119])).
% 0.22/0.57  fof(f173,plain,(
% 0.22/0.57    ( ! [X3] : (r1_tarski(u1_struct_0(X3),k2_struct_0(sK3)) | ~m1_pre_topc(X3,sK3) | ~l1_pre_topc(sK3)) )),
% 0.22/0.57    inference(superposition,[],[f78,f132])).
% 0.22/0.57  fof(f427,plain,(
% 0.22/0.57    ( ! [X2] : (m1_pre_topc(X2,sK3) | ~m1_pre_topc(X2,sK2)) )),
% 0.22/0.57    inference(forward_demodulation,[],[f426,f136])).
% 0.22/0.57  fof(f426,plain,(
% 0.22/0.57    ( ! [X2] : (m1_pre_topc(X2,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))) | ~m1_pre_topc(X2,sK2)) )),
% 0.22/0.57    inference(forward_demodulation,[],[f425,f131])).
% 0.22/0.57  fof(f425,plain,(
% 0.22/0.57    ( ! [X2] : (m1_pre_topc(X2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~m1_pre_topc(X2,sK2)) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f419,f124])).
% 0.22/0.57  fof(f124,plain,(
% 0.22/0.57    ( ! [X0] : (~m1_pre_topc(X0,sK2) | l1_pre_topc(X0)) )),
% 0.22/0.57    inference(resolution,[],[f120,f77])).
% 0.22/0.57  fof(f419,plain,(
% 0.22/0.57    ( ! [X2] : (~l1_pre_topc(X2) | m1_pre_topc(X2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~m1_pre_topc(X2,sK2)) )),
% 0.22/0.57    inference(resolution,[],[f76,f120])).
% 0.22/0.57  fof(f76,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~l1_pre_topc(X1) | ~l1_pre_topc(X0) | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f28])).
% 0.22/0.57  fof(f28,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.57    inference(ennf_transformation,[],[f10])).
% 0.22/0.57  fof(f10,axiom,(
% 0.22/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).
% 0.22/0.57  fof(f138,plain,(
% 0.22/0.57    v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1))),
% 0.22/0.57    inference(backward_demodulation,[],[f133,f132])).
% 0.22/0.57  fof(f133,plain,(
% 0.22/0.57    v1_funct_2(sK4,u1_struct_0(sK3),k2_struct_0(sK1))),
% 0.22/0.57    inference(backward_demodulation,[],[f59,f130])).
% 0.22/0.57  fof(f130,plain,(
% 0.22/0.57    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.22/0.57    inference(resolution,[],[f115,f68])).
% 0.22/0.57  fof(f68,plain,(
% 0.22/0.57    l1_pre_topc(sK1)),
% 0.22/0.57    inference(cnf_transformation,[],[f24])).
% 0.22/0.57  fof(f59,plain,(
% 0.22/0.57    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.22/0.57    inference(cnf_transformation,[],[f24])).
% 0.22/0.57  fof(f2434,plain,(
% 0.22/0.57    ( ! [X2] : (~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1)) | ~v2_pre_topc(sK2) | ~m1_pre_topc(X2,sK2) | k2_tmap_1(sK2,sK1,sK4,X2) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X2)) | ~l1_pre_topc(sK2)) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f2433,f64])).
% 0.22/0.57  fof(f64,plain,(
% 0.22/0.57    ~v2_struct_0(sK2)),
% 0.22/0.57    inference(cnf_transformation,[],[f24])).
% 0.22/0.57  fof(f2433,plain,(
% 0.22/0.57    ( ! [X2] : (v2_struct_0(sK2) | ~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1)) | ~v2_pre_topc(sK2) | ~m1_pre_topc(X2,sK2) | k2_tmap_1(sK2,sK1,sK4,X2) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X2)) | ~l1_pre_topc(sK2)) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f2431,f449])).
% 0.22/0.57  fof(f449,plain,(
% 0.22/0.57    r1_tarski(sK4,k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1)))),
% 0.22/0.57    inference(backward_demodulation,[],[f140,f444])).
% 0.22/0.57  fof(f140,plain,(
% 0.22/0.57    r1_tarski(sK4,k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1)))),
% 0.22/0.57    inference(resolution,[],[f137,f101])).
% 0.22/0.57  fof(f101,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f2])).
% 0.22/0.57  fof(f2,axiom,(
% 0.22/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.57  fof(f137,plain,(
% 0.22/0.57    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1))))),
% 0.22/0.57    inference(backward_demodulation,[],[f134,f132])).
% 0.22/0.57  fof(f134,plain,(
% 0.22/0.57    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1))))),
% 0.22/0.57    inference(backward_demodulation,[],[f60,f130])).
% 0.22/0.57  fof(f60,plain,(
% 0.22/0.57    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.22/0.57    inference(cnf_transformation,[],[f24])).
% 0.22/0.57  fof(f2431,plain,(
% 0.22/0.57    ( ! [X2] : (~r1_tarski(sK4,k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1))) | v2_struct_0(sK2) | ~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1)) | ~v2_pre_topc(sK2) | ~m1_pre_topc(X2,sK2) | k2_tmap_1(sK2,sK1,sK4,X2) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X2)) | ~l1_pre_topc(sK2)) )),
% 0.22/0.57    inference(superposition,[],[f2349,f131])).
% 0.22/0.57  fof(f2349,plain,(
% 0.22/0.57    ( ! [X2,X3] : (~r1_tarski(sK4,k2_zfmisc_1(u1_struct_0(X2),k2_struct_0(sK1))) | v2_struct_0(X2) | ~v1_funct_2(sK4,u1_struct_0(X2),k2_struct_0(sK1)) | ~v2_pre_topc(X2) | ~m1_pre_topc(X3,X2) | k2_tmap_1(X2,sK1,sK4,X3) = k2_partfun1(u1_struct_0(X2),k2_struct_0(sK1),sK4,u1_struct_0(X3)) | ~l1_pre_topc(X2)) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f2348,f68])).
% 0.22/0.57  fof(f2348,plain,(
% 0.22/0.57    ( ! [X2,X3] : (~r1_tarski(sK4,k2_zfmisc_1(u1_struct_0(X2),k2_struct_0(sK1))) | ~l1_pre_topc(sK1) | v2_struct_0(X2) | ~v1_funct_2(sK4,u1_struct_0(X2),k2_struct_0(sK1)) | ~v2_pre_topc(X2) | ~m1_pre_topc(X3,X2) | k2_tmap_1(X2,sK1,sK4,X3) = k2_partfun1(u1_struct_0(X2),k2_struct_0(sK1),sK4,u1_struct_0(X3)) | ~l1_pre_topc(X2)) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f2347,f67])).
% 0.22/0.57  fof(f67,plain,(
% 0.22/0.57    v2_pre_topc(sK1)),
% 0.22/0.57    inference(cnf_transformation,[],[f24])).
% 0.22/0.57  fof(f2347,plain,(
% 0.22/0.57    ( ! [X2,X3] : (~r1_tarski(sK4,k2_zfmisc_1(u1_struct_0(X2),k2_struct_0(sK1))) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X2) | ~v1_funct_2(sK4,u1_struct_0(X2),k2_struct_0(sK1)) | ~v2_pre_topc(X2) | ~m1_pre_topc(X3,X2) | k2_tmap_1(X2,sK1,sK4,X3) = k2_partfun1(u1_struct_0(X2),k2_struct_0(sK1),sK4,u1_struct_0(X3)) | ~l1_pre_topc(X2)) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f2329,f66])).
% 0.22/0.57  fof(f66,plain,(
% 0.22/0.57    ~v2_struct_0(sK1)),
% 0.22/0.57    inference(cnf_transformation,[],[f24])).
% 0.22/0.57  fof(f2329,plain,(
% 0.22/0.57    ( ! [X2,X3] : (~r1_tarski(sK4,k2_zfmisc_1(u1_struct_0(X2),k2_struct_0(sK1))) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X2) | ~v1_funct_2(sK4,u1_struct_0(X2),k2_struct_0(sK1)) | ~v2_pre_topc(X2) | ~m1_pre_topc(X3,X2) | k2_tmap_1(X2,sK1,sK4,X3) = k2_partfun1(u1_struct_0(X2),k2_struct_0(sK1),sK4,u1_struct_0(X3)) | ~l1_pre_topc(X2)) )),
% 0.22/0.57    inference(superposition,[],[f1965,f130])).
% 0.22/0.57  fof(f1965,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~r1_tarski(sK4,k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) | ~v2_pre_topc(X0) | ~m1_pre_topc(X2,X0) | k2_tmap_1(X0,X1,sK4,X2) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) | ~l1_pre_topc(X0)) )),
% 0.22/0.57    inference(resolution,[],[f1772,f100])).
% 0.22/0.57  fof(f100,plain,(
% 0.22/0.57    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f2])).
% 0.22/0.57  fof(f1772,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) | ~v2_pre_topc(X0) | ~m1_pre_topc(X2,X0) | k2_tmap_1(X0,X1,sK4,X2) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2))) )),
% 0.22/0.57    inference(resolution,[],[f82,f58])).
% 0.22/0.57  fof(f58,plain,(
% 0.22/0.57    v1_funct_1(sK4)),
% 0.22/0.57    inference(cnf_transformation,[],[f24])).
% 0.22/0.57  fof(f82,plain,(
% 0.22/0.57    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f36])).
% 0.22/0.57  fof(f36,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.57    inference(flattening,[],[f35])).
% 0.22/0.57  fof(f35,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f12])).
% 0.22/0.57  fof(f12,axiom,(
% 0.22/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).
% 0.22/0.57  fof(f2720,plain,(
% 0.22/0.57    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,k2_struct_0(sK2))),
% 0.22/0.57    inference(forward_demodulation,[],[f2717,f131])).
% 0.22/0.57  fof(f2717,plain,(
% 0.22/0.57    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(sK2))),
% 0.22/0.57    inference(resolution,[],[f2708,f1151])).
% 0.22/0.57  fof(f1151,plain,(
% 0.22/0.57    m1_pre_topc(sK2,sK3)),
% 0.22/0.57    inference(subsumption_resolution,[],[f1150,f70])).
% 0.22/0.57  fof(f1150,plain,(
% 0.22/0.57    m1_pre_topc(sK2,sK3) | ~v2_pre_topc(sK0)),
% 0.22/0.57    inference(subsumption_resolution,[],[f1149,f71])).
% 0.22/0.57  fof(f1149,plain,(
% 0.22/0.57    ~l1_pre_topc(sK0) | m1_pre_topc(sK2,sK3) | ~v2_pre_topc(sK0)),
% 0.22/0.57    inference(subsumption_resolution,[],[f1144,f65])).
% 0.22/0.57  fof(f1144,plain,(
% 0.22/0.57    ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK0) | m1_pre_topc(sK2,sK3) | ~v2_pre_topc(sK0)),
% 0.22/0.57    inference(resolution,[],[f1140,f63])).
% 0.22/0.57  fof(f1140,plain,(
% 0.22/0.57    ( ! [X3] : (~m1_pre_topc(sK3,X3) | ~m1_pre_topc(sK2,X3) | ~l1_pre_topc(X3) | m1_pre_topc(sK2,sK3) | ~v2_pre_topc(X3)) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f1137,f106])).
% 0.22/0.57  fof(f106,plain,(
% 0.22/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.57    inference(equality_resolution,[],[f98])).
% 0.22/0.57  fof(f98,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.57    inference(cnf_transformation,[],[f1])).
% 0.22/0.57  fof(f1137,plain,(
% 0.22/0.57    ( ! [X3] : (~r1_tarski(k2_struct_0(sK2),k2_struct_0(sK2)) | ~l1_pre_topc(X3) | ~m1_pre_topc(sK2,X3) | ~m1_pre_topc(sK3,X3) | m1_pre_topc(sK2,sK3) | ~v2_pre_topc(X3)) )),
% 0.22/0.57    inference(superposition,[],[f1036,f445])).
% 0.22/0.57  fof(f445,plain,(
% 0.22/0.57    u1_struct_0(sK3) = k2_struct_0(sK2)),
% 0.22/0.57    inference(backward_demodulation,[],[f132,f444])).
% 0.22/0.57  fof(f1036,plain,(
% 0.22/0.57    ( ! [X4,X5] : (~r1_tarski(k2_struct_0(sK2),u1_struct_0(X4)) | ~l1_pre_topc(X5) | ~m1_pre_topc(sK2,X5) | ~m1_pre_topc(X4,X5) | m1_pre_topc(sK2,X4) | ~v2_pre_topc(X5)) )),
% 0.22/0.57    inference(superposition,[],[f90,f131])).
% 0.22/0.57  fof(f90,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | m1_pre_topc(X1,X2) | ~v2_pre_topc(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f48])).
% 0.22/0.57  fof(f48,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.57    inference(flattening,[],[f47])).
% 0.22/0.57  fof(f47,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f18])).
% 0.22/0.57  fof(f18,axiom,(
% 0.22/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).
% 0.22/0.57  fof(f2708,plain,(
% 0.22/0.57    ( ! [X3] : (~m1_pre_topc(X3,sK3) | k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3)) = k3_tmap_1(sK0,sK1,sK3,X3,sK4)) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f2707,f71])).
% 0.22/0.57  fof(f2707,plain,(
% 0.22/0.57    ( ! [X3] : (~m1_pre_topc(X3,sK3) | k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3)) = k3_tmap_1(sK0,sK1,sK3,X3,sK4) | ~l1_pre_topc(sK0)) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f2706,f70])).
% 0.22/0.57  fof(f2706,plain,(
% 0.22/0.57    ( ! [X3] : (~v2_pre_topc(sK0) | ~m1_pre_topc(X3,sK3) | k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3)) = k3_tmap_1(sK0,sK1,sK3,X3,sK4) | ~l1_pre_topc(sK0)) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f2700,f69])).
% 0.22/0.57  fof(f69,plain,(
% 0.22/0.57    ~v2_struct_0(sK0)),
% 0.22/0.57    inference(cnf_transformation,[],[f24])).
% 0.22/0.57  fof(f2700,plain,(
% 0.22/0.57    ( ! [X3] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_pre_topc(X3,sK3) | k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3)) = k3_tmap_1(sK0,sK1,sK3,X3,sK4) | ~l1_pre_topc(sK0)) )),
% 0.22/0.57    inference(resolution,[],[f2660,f63])).
% 0.22/0.57  fof(f2660,plain,(
% 0.22/0.57    ( ! [X6,X7] : (~m1_pre_topc(sK3,X6) | v2_struct_0(X6) | ~v2_pre_topc(X6) | ~m1_pre_topc(X7,sK3) | k3_tmap_1(X6,sK1,sK3,X7,sK4) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X7)) | ~l1_pre_topc(X6)) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f2659,f447])).
% 0.22/0.57  fof(f2659,plain,(
% 0.22/0.57    ( ! [X6,X7] : (~m1_pre_topc(sK3,X6) | v2_struct_0(X6) | ~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1)) | ~v2_pre_topc(X6) | ~m1_pre_topc(X7,sK3) | k3_tmap_1(X6,sK1,sK3,X7,sK4) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X7)) | ~l1_pre_topc(X6)) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f2656,f449])).
% 0.22/0.57  fof(f2656,plain,(
% 0.22/0.57    ( ! [X6,X7] : (~r1_tarski(sK4,k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1))) | ~m1_pre_topc(sK3,X6) | v2_struct_0(X6) | ~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1)) | ~v2_pre_topc(X6) | ~m1_pre_topc(X7,sK3) | k3_tmap_1(X6,sK1,sK3,X7,sK4) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X7)) | ~l1_pre_topc(X6)) )),
% 0.22/0.57    inference(superposition,[],[f2396,f445])).
% 0.22/0.57  fof(f2396,plain,(
% 0.22/0.57    ( ! [X4,X5,X3] : (~r1_tarski(sK4,k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK1))) | ~m1_pre_topc(X3,X4) | v2_struct_0(X4) | ~v1_funct_2(sK4,u1_struct_0(X3),k2_struct_0(sK1)) | ~v2_pre_topc(X4) | ~m1_pre_topc(X5,X3) | k3_tmap_1(X4,sK1,X3,X5,sK4) = k2_partfun1(u1_struct_0(X3),k2_struct_0(sK1),sK4,u1_struct_0(X5)) | ~l1_pre_topc(X4)) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f2395,f68])).
% 0.22/0.57  fof(f2395,plain,(
% 0.22/0.57    ( ! [X4,X5,X3] : (~r1_tarski(sK4,k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK1))) | ~l1_pre_topc(sK1) | ~m1_pre_topc(X3,X4) | v2_struct_0(X4) | ~v1_funct_2(sK4,u1_struct_0(X3),k2_struct_0(sK1)) | ~v2_pre_topc(X4) | ~m1_pre_topc(X5,X3) | k3_tmap_1(X4,sK1,X3,X5,sK4) = k2_partfun1(u1_struct_0(X3),k2_struct_0(sK1),sK4,u1_struct_0(X5)) | ~l1_pre_topc(X4)) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f2394,f67])).
% 0.22/0.57  fof(f2394,plain,(
% 0.22/0.57    ( ! [X4,X5,X3] : (~r1_tarski(sK4,k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK1))) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_pre_topc(X3,X4) | v2_struct_0(X4) | ~v1_funct_2(sK4,u1_struct_0(X3),k2_struct_0(sK1)) | ~v2_pre_topc(X4) | ~m1_pre_topc(X5,X3) | k3_tmap_1(X4,sK1,X3,X5,sK4) = k2_partfun1(u1_struct_0(X3),k2_struct_0(sK1),sK4,u1_struct_0(X5)) | ~l1_pre_topc(X4)) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f2388,f66])).
% 0.22/0.57  fof(f2388,plain,(
% 0.22/0.57    ( ! [X4,X5,X3] : (~r1_tarski(sK4,k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK1))) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_pre_topc(X3,X4) | v2_struct_0(X4) | ~v1_funct_2(sK4,u1_struct_0(X3),k2_struct_0(sK1)) | ~v2_pre_topc(X4) | ~m1_pre_topc(X5,X3) | k3_tmap_1(X4,sK1,X3,X5,sK4) = k2_partfun1(u1_struct_0(X3),k2_struct_0(sK1),sK4,u1_struct_0(X5)) | ~l1_pre_topc(X4)) )),
% 0.22/0.57    inference(superposition,[],[f2027,f130])).
% 0.22/0.57  fof(f2027,plain,(
% 0.22/0.57    ( ! [X2,X0,X3,X1] : (~r1_tarski(sK4,k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(X2),u1_struct_0(X1)) | ~v2_pre_topc(X0) | ~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,sK4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),sK4,u1_struct_0(X3)) | ~l1_pre_topc(X0)) )),
% 0.22/0.57    inference(resolution,[],[f1888,f100])).
% 0.22/0.57  fof(f1888,plain,(
% 0.22/0.57    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(X2),u1_struct_0(X1)) | ~v2_pre_topc(X0) | ~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,sK4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),sK4,u1_struct_0(X3))) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f1887,f88])).
% 0.22/0.57  fof(f88,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X1) | m1_pre_topc(X2,X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f46])).
% 0.22/0.57  fof(f46,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.57    inference(flattening,[],[f45])).
% 0.22/0.57  fof(f45,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f20])).
% 0.22/0.57  fof(f20,axiom,(
% 0.22/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).
% 0.22/0.57  fof(f1887,plain,(
% 0.22/0.57    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X3,X0) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,sK4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),sK4,u1_struct_0(X3))) )),
% 0.22/0.57    inference(resolution,[],[f81,f58])).
% 0.22/0.57  fof(f81,plain,(
% 0.22/0.57    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X4) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X3,X0) | v2_struct_0(X0) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f34])).
% 0.22/0.57  fof(f34,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.57    inference(flattening,[],[f33])).
% 0.22/0.57  fof(f33,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f13])).
% 0.22/0.57  fof(f13,axiom,(
% 0.22/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).
% 0.22/0.58  fof(f108,plain,(
% 0.22/0.58    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)),
% 0.22/0.58    inference(backward_demodulation,[],[f55,f54])).
% 0.22/0.58  fof(f55,plain,(
% 0.22/0.58    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 0.22/0.58    inference(cnf_transformation,[],[f24])).
% 0.22/0.58  fof(f2958,plain,(
% 0.22/0.58    ( ! [X2] : (~r1_tmap_1(sK2,sK1,k2_tmap_1(sK2,sK1,sK4,sK2),X2) | ~m1_subset_1(X2,k2_struct_0(sK2)) | r1_tmap_1(sK3,sK1,sK4,X2)) )),
% 0.22/0.58    inference(forward_demodulation,[],[f2957,f2454])).
% 0.22/0.58  fof(f2454,plain,(
% 0.22/0.58    k2_tmap_1(sK2,sK1,sK4,sK2) = k2_tmap_1(sK3,sK1,sK4,sK2)),
% 0.22/0.58    inference(forward_demodulation,[],[f2453,f2445])).
% 0.22/0.58  fof(f2453,plain,(
% 0.22/0.58    k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,k2_struct_0(sK2)) = k2_tmap_1(sK3,sK1,sK4,sK2)),
% 0.22/0.58    inference(forward_demodulation,[],[f2450,f131])).
% 0.22/0.58  fof(f2450,plain,(
% 0.22/0.58    k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(sK2)) = k2_tmap_1(sK3,sK1,sK4,sK2)),
% 0.22/0.58    inference(resolution,[],[f2442,f1151])).
% 0.22/0.58  fof(f2442,plain,(
% 0.22/0.58    ( ! [X3] : (~m1_pre_topc(X3,sK3) | k2_tmap_1(sK3,sK1,sK4,X3) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3))) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f2441,f119])).
% 0.22/0.58  fof(f2441,plain,(
% 0.22/0.58    ( ! [X3] : (~m1_pre_topc(X3,sK3) | k2_tmap_1(sK3,sK1,sK4,X3) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3)) | ~l1_pre_topc(sK3)) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f2440,f155])).
% 0.22/0.58  fof(f155,plain,(
% 0.22/0.58    v2_pre_topc(sK3)),
% 0.22/0.58    inference(resolution,[],[f151,f63])).
% 0.22/0.58  fof(f2440,plain,(
% 0.22/0.58    ( ! [X3] : (~v2_pre_topc(sK3) | ~m1_pre_topc(X3,sK3) | k2_tmap_1(sK3,sK1,sK4,X3) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3)) | ~l1_pre_topc(sK3)) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f2439,f447])).
% 0.22/0.58  fof(f2439,plain,(
% 0.22/0.58    ( ! [X3] : (~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1)) | ~v2_pre_topc(sK3) | ~m1_pre_topc(X3,sK3) | k2_tmap_1(sK3,sK1,sK4,X3) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3)) | ~l1_pre_topc(sK3)) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f2438,f62])).
% 0.22/0.58  fof(f62,plain,(
% 0.22/0.58    ~v2_struct_0(sK3)),
% 0.22/0.58    inference(cnf_transformation,[],[f24])).
% 0.22/0.58  fof(f2438,plain,(
% 0.22/0.58    ( ! [X3] : (v2_struct_0(sK3) | ~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1)) | ~v2_pre_topc(sK3) | ~m1_pre_topc(X3,sK3) | k2_tmap_1(sK3,sK1,sK4,X3) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3)) | ~l1_pre_topc(sK3)) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f2432,f449])).
% 0.22/0.58  fof(f2432,plain,(
% 0.22/0.58    ( ! [X3] : (~r1_tarski(sK4,k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1))) | v2_struct_0(sK3) | ~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1)) | ~v2_pre_topc(sK3) | ~m1_pre_topc(X3,sK3) | k2_tmap_1(sK3,sK1,sK4,X3) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3)) | ~l1_pre_topc(sK3)) )),
% 0.22/0.58    inference(superposition,[],[f2349,f445])).
% 0.22/0.58  fof(f2957,plain,(
% 0.22/0.58    ( ! [X2] : (~m1_subset_1(X2,k2_struct_0(sK2)) | ~r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),X2) | r1_tmap_1(sK3,sK1,sK4,X2)) )),
% 0.22/0.58    inference(forward_demodulation,[],[f2956,f131])).
% 0.22/0.58  fof(f2956,plain,(
% 0.22/0.58    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK2)) | ~r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),X2) | r1_tmap_1(sK3,sK1,sK4,X2)) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f2955,f1151])).
% 0.22/0.58  fof(f2955,plain,(
% 0.22/0.58    ( ! [X2] : (~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X2,u1_struct_0(sK2)) | ~r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),X2) | r1_tmap_1(sK3,sK1,sK4,X2)) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f2952,f64])).
% 0.22/0.58  fof(f2952,plain,(
% 0.22/0.58    ( ! [X2] : (v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X2,u1_struct_0(sK2)) | ~r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),X2) | r1_tmap_1(sK3,sK1,sK4,X2)) )),
% 0.22/0.58    inference(resolution,[],[f2908,f1152])).
% 0.22/0.58  fof(f1152,plain,(
% 0.22/0.58    v1_tsep_1(sK2,sK3)),
% 0.22/0.58    inference(subsumption_resolution,[],[f610,f1151])).
% 0.22/0.58  fof(f610,plain,(
% 0.22/0.58    v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3)),
% 0.22/0.58    inference(subsumption_resolution,[],[f608,f451])).
% 0.22/0.58  fof(f451,plain,(
% 0.22/0.58    v3_pre_topc(k2_struct_0(sK2),sK3)),
% 0.22/0.58    inference(backward_demodulation,[],[f159,f444])).
% 0.22/0.58  fof(f159,plain,(
% 0.22/0.58    v3_pre_topc(k2_struct_0(sK3),sK3)),
% 0.22/0.58    inference(subsumption_resolution,[],[f144,f155])).
% 0.22/0.58  fof(f144,plain,(
% 0.22/0.58    v3_pre_topc(k2_struct_0(sK3),sK3) | ~v2_pre_topc(sK3)),
% 0.22/0.58    inference(resolution,[],[f86,f119])).
% 0.22/0.58  fof(f86,plain,(
% 0.22/0.58    ( ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v3_pre_topc(k2_struct_0(X0),X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f42])).
% 0.22/0.58  fof(f42,plain,(
% 0.22/0.58    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.58    inference(flattening,[],[f41])).
% 0.22/0.58  fof(f41,plain,(
% 0.22/0.58    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.58    inference(ennf_transformation,[],[f11])).
% 0.22/0.58  fof(f11,axiom,(
% 0.22/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).
% 0.22/0.58  fof(f608,plain,(
% 0.22/0.58    ~v3_pre_topc(k2_struct_0(sK2),sK3) | ~m1_pre_topc(sK2,sK3) | v1_tsep_1(sK2,sK3)),
% 0.22/0.58    inference(superposition,[],[f583,f131])).
% 0.22/0.58  fof(f583,plain,(
% 0.22/0.58    ( ! [X3] : (~v3_pre_topc(u1_struct_0(X3),sK3) | ~m1_pre_topc(X3,sK3) | v1_tsep_1(X3,sK3)) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f579,f155])).
% 0.22/0.58  fof(f579,plain,(
% 0.22/0.58    ( ! [X3] : (~v2_pre_topc(sK3) | ~m1_pre_topc(X3,sK3) | ~v3_pre_topc(u1_struct_0(X3),sK3) | v1_tsep_1(X3,sK3)) )),
% 0.22/0.58    inference(resolution,[],[f111,f119])).
% 0.22/0.58  fof(f111,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v3_pre_topc(u1_struct_0(X1),X0) | v1_tsep_1(X1,X0)) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f104,f79])).
% 0.22/0.58  fof(f79,plain,(
% 0.22/0.58    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f31])).
% 0.22/0.58  fof(f31,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.58    inference(ennf_transformation,[],[f15])).
% 0.22/0.58  fof(f15,axiom,(
% 0.22/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.22/0.58  fof(f104,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(u1_struct_0(X1),X0) | v1_tsep_1(X1,X0)) )),
% 0.22/0.58    inference(equality_resolution,[],[f92])).
% 0.22/0.58  fof(f92,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | ~v3_pre_topc(X2,X0) | v1_tsep_1(X1,X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f50])).
% 0.22/0.58  fof(f50,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.58    inference(flattening,[],[f49])).
% 0.22/0.58  fof(f49,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.58    inference(ennf_transformation,[],[f14])).
% 0.22/0.58  fof(f14,axiom,(
% 0.22/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).
% 0.22/0.58  fof(f2908,plain,(
% 0.22/0.58    ( ! [X6,X7] : (~v1_tsep_1(X6,sK3) | v2_struct_0(X6) | ~m1_pre_topc(X6,sK3) | ~m1_subset_1(X7,u1_struct_0(X6)) | ~r1_tmap_1(X6,sK1,k2_tmap_1(sK3,sK1,sK4,X6),X7) | r1_tmap_1(sK3,sK1,sK4,X7)) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f2907,f447])).
% 0.22/0.58  fof(f2907,plain,(
% 0.22/0.58    ( ! [X6,X7] : (~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1)) | v2_struct_0(X6) | ~v1_tsep_1(X6,sK3) | ~m1_pre_topc(X6,sK3) | ~m1_subset_1(X7,u1_struct_0(X6)) | ~r1_tmap_1(X6,sK1,k2_tmap_1(sK3,sK1,sK4,X6),X7) | r1_tmap_1(sK3,sK1,sK4,X7)) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f2906,f119])).
% 0.22/0.58  fof(f2906,plain,(
% 0.22/0.58    ( ! [X6,X7] : (~l1_pre_topc(sK3) | ~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1)) | v2_struct_0(X6) | ~v1_tsep_1(X6,sK3) | ~m1_pre_topc(X6,sK3) | ~m1_subset_1(X7,u1_struct_0(X6)) | ~r1_tmap_1(X6,sK1,k2_tmap_1(sK3,sK1,sK4,X6),X7) | r1_tmap_1(sK3,sK1,sK4,X7)) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f2905,f155])).
% 0.22/0.58  fof(f2905,plain,(
% 0.22/0.58    ( ! [X6,X7] : (~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1)) | v2_struct_0(X6) | ~v1_tsep_1(X6,sK3) | ~m1_pre_topc(X6,sK3) | ~m1_subset_1(X7,u1_struct_0(X6)) | ~r1_tmap_1(X6,sK1,k2_tmap_1(sK3,sK1,sK4,X6),X7) | r1_tmap_1(sK3,sK1,sK4,X7)) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f2904,f62])).
% 0.22/0.58  fof(f2904,plain,(
% 0.22/0.58    ( ! [X6,X7] : (v2_struct_0(sK3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1)) | v2_struct_0(X6) | ~v1_tsep_1(X6,sK3) | ~m1_pre_topc(X6,sK3) | ~m1_subset_1(X7,u1_struct_0(X6)) | ~r1_tmap_1(X6,sK1,k2_tmap_1(sK3,sK1,sK4,X6),X7) | r1_tmap_1(sK3,sK1,sK4,X7)) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f2898,f449])).
% 0.22/0.58  fof(f2898,plain,(
% 0.22/0.58    ( ! [X6,X7] : (~r1_tarski(sK4,k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1))) | v2_struct_0(sK3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1)) | v2_struct_0(X6) | ~v1_tsep_1(X6,sK3) | ~m1_pre_topc(X6,sK3) | ~m1_subset_1(X7,u1_struct_0(X6)) | ~r1_tmap_1(X6,sK1,k2_tmap_1(sK3,sK1,sK4,X6),X7) | r1_tmap_1(sK3,sK1,sK4,X7)) )),
% 0.22/0.58    inference(superposition,[],[f2642,f445])).
% 0.22/0.58  fof(f2642,plain,(
% 0.22/0.58    ( ! [X4,X5,X3] : (~r1_tarski(sK4,k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK1))) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | ~v1_funct_2(sK4,u1_struct_0(X3),k2_struct_0(sK1)) | v2_struct_0(X4) | ~v1_tsep_1(X4,X3) | ~m1_pre_topc(X4,X3) | ~m1_subset_1(X5,u1_struct_0(X4)) | ~r1_tmap_1(X4,sK1,k2_tmap_1(X3,sK1,sK4,X4),X5) | r1_tmap_1(X3,sK1,sK4,X5)) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f2641,f68])).
% 0.22/0.58  fof(f2641,plain,(
% 0.22/0.58    ( ! [X4,X5,X3] : (~r1_tarski(sK4,k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK1))) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | ~v1_funct_2(sK4,u1_struct_0(X3),k2_struct_0(sK1)) | v2_struct_0(X4) | ~v1_tsep_1(X4,X3) | ~m1_pre_topc(X4,X3) | ~m1_subset_1(X5,u1_struct_0(X4)) | ~r1_tmap_1(X4,sK1,k2_tmap_1(X3,sK1,sK4,X4),X5) | r1_tmap_1(X3,sK1,sK4,X5) | ~l1_pre_topc(sK1)) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f2640,f67])).
% 0.22/0.58  fof(f2640,plain,(
% 0.22/0.58    ( ! [X4,X5,X3] : (~r1_tarski(sK4,k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK1))) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | ~v1_funct_2(sK4,u1_struct_0(X3),k2_struct_0(sK1)) | ~v2_pre_topc(sK1) | v2_struct_0(X4) | ~v1_tsep_1(X4,X3) | ~m1_pre_topc(X4,X3) | ~m1_subset_1(X5,u1_struct_0(X4)) | ~r1_tmap_1(X4,sK1,k2_tmap_1(X3,sK1,sK4,X4),X5) | r1_tmap_1(X3,sK1,sK4,X5) | ~l1_pre_topc(sK1)) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f2622,f66])).
% 0.22/0.58  fof(f2622,plain,(
% 0.22/0.58    ( ! [X4,X5,X3] : (~r1_tarski(sK4,k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK1))) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | v2_struct_0(sK1) | ~v1_funct_2(sK4,u1_struct_0(X3),k2_struct_0(sK1)) | ~v2_pre_topc(sK1) | v2_struct_0(X4) | ~v1_tsep_1(X4,X3) | ~m1_pre_topc(X4,X3) | ~m1_subset_1(X5,u1_struct_0(X4)) | ~r1_tmap_1(X4,sK1,k2_tmap_1(X3,sK1,sK4,X4),X5) | r1_tmap_1(X3,sK1,sK4,X5) | ~l1_pre_topc(sK1)) )),
% 0.22/0.58    inference(superposition,[],[f2228,f130])).
% 0.22/0.58  fof(f2228,plain,(
% 0.22/0.58    ( ! [X2,X0,X3,X1] : (~r1_tarski(sK4,k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X0)) | ~v2_pre_topc(X0) | v2_struct_0(X2) | ~v1_tsep_1(X2,X1) | ~m1_pre_topc(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~r1_tmap_1(X2,X0,k2_tmap_1(X1,X0,sK4,X2),X3) | r1_tmap_1(X1,X0,sK4,X3) | ~l1_pre_topc(X0)) )),
% 0.22/0.58    inference(resolution,[],[f1928,f100])).
% 0.22/0.58  fof(f1928,plain,(
% 0.22/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X0)) | ~v2_pre_topc(X0) | v2_struct_0(X2) | ~v1_tsep_1(X2,X1) | ~m1_pre_topc(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~r1_tmap_1(X2,X0,k2_tmap_1(X1,X0,sK4,X2),X3) | r1_tmap_1(X1,X0,sK4,X3)) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f1927,f85])).
% 0.22/0.58  fof(f85,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | m1_subset_1(X2,u1_struct_0(X0))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f40])).
% 0.22/0.58  fof(f40,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.58    inference(flattening,[],[f39])).
% 0.22/0.58  fof(f39,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.58    inference(ennf_transformation,[],[f7])).
% 0.22/0.58  fof(f7,axiom,(
% 0.22/0.58    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).
% 0.22/0.58  fof(f1927,plain,(
% 0.22/0.58    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X2) | ~v1_tsep_1(X2,X1) | ~m1_pre_topc(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~r1_tmap_1(X2,X0,k2_tmap_1(X1,X0,sK4,X2),X3) | r1_tmap_1(X1,X0,sK4,X3)) )),
% 0.22/0.58    inference(resolution,[],[f103,f58])).
% 0.22/0.58  fof(f103,plain,(
% 0.22/0.58    ( ! [X2,X0,X5,X3,X1] : (~v1_funct_1(X2) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~v1_tsep_1(X3,X1) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X5)) )),
% 0.22/0.58    inference(equality_resolution,[],[f83])).
% 0.22/0.58  fof(f83,plain,(
% 0.22/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~v1_tsep_1(X3,X1) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X3)) | X4 != X5 | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f38])).
% 0.22/0.58  fof(f38,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.58    inference(flattening,[],[f37])).
% 0.22/0.58  fof(f37,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (((r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) | X4 != X5) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.58    inference(ennf_transformation,[],[f19])).
% 0.22/0.58  fof(f19,axiom,(
% 0.22/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_tmap_1)).
% 0.22/0.58  % SZS output end Proof for theBenchmark
% 0.22/0.58  % (25808)------------------------------
% 0.22/0.58  % (25808)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (25808)Termination reason: Refutation
% 0.22/0.58  
% 0.22/0.58  % (25808)Memory used [KB]: 3326
% 0.22/0.58  % (25808)Time elapsed: 0.160 s
% 0.22/0.58  % (25808)------------------------------
% 0.22/0.58  % (25808)------------------------------
% 0.22/0.58  % (25788)Success in time 0.219 s
%------------------------------------------------------------------------------
