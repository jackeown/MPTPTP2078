%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:06 EST 2020

% Result     : Theorem 1.39s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :  145 (1656 expanded)
%              Number of leaves         :   14 ( 314 expanded)
%              Depth                    :   31
%              Number of atoms          :  740 (16519 expanded)
%              Number of equality atoms :   27 (1511 expanded)
%              Maximal formula depth    :   28 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f966,plain,(
    $false ),
    inference(subsumption_resolution,[],[f965,f47])).

fof(f47,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f18])).

% (2406)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
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
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
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

fof(f965,plain,(
    ~ m1_pre_topc(sK3,sK0) ),
    inference(subsumption_resolution,[],[f964,f55])).

fof(f55,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f964,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK3,sK0) ),
    inference(subsumption_resolution,[],[f963,f54])).

fof(f54,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f963,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK3,sK0) ),
    inference(subsumption_resolution,[],[f962,f53])).

fof(f53,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f962,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK3,sK0) ),
    inference(resolution,[],[f957,f99])).

fof(f99,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(backward_demodulation,[],[f39,f38])).

fof(f38,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f18])).

fof(f39,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f18])).

fof(f957,plain,(
    ! [X0] :
      ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK3,X0) ) ),
    inference(subsumption_resolution,[],[f956,f48])).

fof(f48,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f956,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK3,X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(sK2)
      | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5) ) ),
    inference(subsumption_resolution,[],[f955,f629])).

fof(f629,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f628,f54])).

fof(f628,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f624,f55])).

fof(f624,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_pre_topc(sK2,sK3)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f620,f49])).

fof(f49,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f620,plain,(
    ! [X5] :
      ( ~ m1_pre_topc(sK2,X5)
      | ~ l1_pre_topc(X5)
      | m1_pre_topc(sK2,sK3)
      | ~ v2_pre_topc(X5) ) ),
    inference(subsumption_resolution,[],[f615,f138])).

fof(f138,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(resolution,[],[f137,f113])).

fof(f113,plain,(
    m1_pre_topc(sK3,sK3) ),
    inference(resolution,[],[f109,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f109,plain,(
    l1_pre_topc(sK3) ),
    inference(resolution,[],[f107,f47])).

fof(f107,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK0)
      | l1_pre_topc(X1) ) ),
    inference(resolution,[],[f77,f55])).

fof(f77,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f137,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK3)
      | m1_pre_topc(X2,sK2) ) ),
    inference(forward_demodulation,[],[f135,f45])).

fof(f45,plain,(
    sK3 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f135,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
      | m1_pre_topc(X2,sK2) ) ),
    inference(resolution,[],[f81,f110])).

fof(f110,plain,(
    l1_pre_topc(sK2) ),
    inference(resolution,[],[f107,f49])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | m1_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

fof(f615,plain,(
    ! [X5] :
      ( ~ m1_pre_topc(sK3,sK2)
      | ~ l1_pre_topc(X5)
      | ~ m1_pre_topc(sK2,X5)
      | m1_pre_topc(sK2,sK3)
      | ~ v2_pre_topc(X5) ) ),
    inference(resolution,[],[f450,f113])).

fof(f450,plain,(
    ! [X2,X1] :
      ( ~ m1_pre_topc(sK3,X1)
      | ~ m1_pre_topc(X1,sK2)
      | ~ l1_pre_topc(X2)
      | ~ m1_pre_topc(sK2,X2)
      | m1_pre_topc(sK2,X1)
      | ~ v2_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f446,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X1)
      | m1_pre_topc(X2,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f446,plain,(
    ! [X2,X1] :
      ( ~ m1_pre_topc(sK3,X1)
      | ~ m1_pre_topc(X1,sK2)
      | ~ l1_pre_topc(X2)
      | ~ m1_pre_topc(sK2,X2)
      | ~ m1_pre_topc(X1,X2)
      | m1_pre_topc(sK2,X1)
      | ~ v2_pre_topc(X2) ) ),
    inference(resolution,[],[f359,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | m1_pre_topc(X1,X2)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
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
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

fof(f359,plain,(
    ! [X10] :
      ( r1_tarski(u1_struct_0(sK2),u1_struct_0(X10))
      | ~ m1_pre_topc(sK3,X10)
      | ~ m1_pre_topc(X10,sK2) ) ),
    inference(superposition,[],[f269,f317])).

fof(f317,plain,(
    u1_struct_0(sK2) = u1_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f316,f115])).

fof(f115,plain,(
    m1_pre_topc(sK2,sK2) ),
    inference(resolution,[],[f110,f56])).

fof(f316,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK2) ),
    inference(resolution,[],[f310,f171])).

fof(f171,plain,(
    ! [X2] :
      ( m1_pre_topc(X2,sK3)
      | ~ m1_pre_topc(X2,sK2) ) ),
    inference(forward_demodulation,[],[f170,f45])).

fof(f170,plain,(
    ! [X2] :
      ( m1_pre_topc(X2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
      | ~ m1_pre_topc(X2,sK2) ) ),
    inference(subsumption_resolution,[],[f166,f114])).

fof(f114,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | l1_pre_topc(X0) ) ),
    inference(resolution,[],[f110,f77])).

fof(f166,plain,(
    ! [X2] :
      ( ~ l1_pre_topc(X2)
      | m1_pre_topc(X2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
      | ~ m1_pre_topc(X2,sK2) ) ),
    inference(resolution,[],[f76,f110])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f310,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | u1_struct_0(sK2) = u1_struct_0(sK3) ),
    inference(resolution,[],[f303,f138])).

fof(f303,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK3,X0)
      | ~ m1_pre_topc(X0,sK3)
      | u1_struct_0(X0) = u1_struct_0(sK3) ) ),
    inference(resolution,[],[f302,f47])).

fof(f302,plain,(
    ! [X6,X7] :
      ( ~ m1_pre_topc(X7,sK0)
      | u1_struct_0(X7) = u1_struct_0(X6)
      | ~ m1_pre_topc(X6,X7)
      | ~ m1_pre_topc(X7,X6) ) ),
    inference(subsumption_resolution,[],[f300,f145])).

fof(f145,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK0)
      | ~ m1_pre_topc(X1,X0)
      | m1_pre_topc(X1,sK0) ) ),
    inference(subsumption_resolution,[],[f141,f54])).

fof(f141,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | ~ m1_pre_topc(X1,X0)
      | m1_pre_topc(X1,sK0) ) ),
    inference(resolution,[],[f85,f55])).

fof(f300,plain,(
    ! [X6,X7] :
      ( ~ m1_pre_topc(X6,sK0)
      | ~ m1_pre_topc(X7,X6)
      | u1_struct_0(X7) = u1_struct_0(X6)
      | ~ m1_pre_topc(X6,X7)
      | ~ m1_pre_topc(X7,sK0) ) ),
    inference(resolution,[],[f271,f267])).

fof(f267,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f263,f54])).

fof(f263,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | ~ m1_pre_topc(X1,X0)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ),
    inference(resolution,[],[f101,f55])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X2)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) ),
    inference(subsumption_resolution,[],[f86,f85])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X2)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f271,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,sK0)
      | ~ m1_pre_topc(X0,X1)
      | u1_struct_0(X0) = u1_struct_0(X1) ) ),
    inference(resolution,[],[f267,f92])).

fof(f92,plain,(
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

fof(f269,plain,(
    ! [X4,X5] :
      ( r1_tarski(u1_struct_0(X5),u1_struct_0(X4))
      | ~ m1_pre_topc(X5,X4)
      | ~ m1_pre_topc(X4,sK2) ) ),
    inference(subsumption_resolution,[],[f265,f125])).

fof(f125,plain,(
    v2_pre_topc(sK2) ),
    inference(resolution,[],[f122,f49])).

fof(f122,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f118,f54])).

fof(f118,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_pre_topc(X0) ) ),
    inference(resolution,[],[f84,f55])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
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

fof(f265,plain,(
    ! [X4,X5] :
      ( ~ v2_pre_topc(sK2)
      | ~ m1_pre_topc(X4,sK2)
      | ~ m1_pre_topc(X5,X4)
      | r1_tarski(u1_struct_0(X5),u1_struct_0(X4)) ) ),
    inference(resolution,[],[f101,f110])).

fof(f955,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK3,X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(sK2,sK3)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(sK2)
      | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5) ) ),
    inference(subsumption_resolution,[],[f953,f631])).

fof(f631,plain,(
    v1_tsep_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f333,f629])).

fof(f333,plain,
    ( v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3) ),
    inference(resolution,[],[f324,f222])).

fof(f222,plain,(
    ! [X3] :
      ( ~ v3_pre_topc(u1_struct_0(X3),sK3)
      | ~ m1_pre_topc(X3,sK3)
      | v1_tsep_1(X3,sK3) ) ),
    inference(subsumption_resolution,[],[f218,f124])).

fof(f124,plain,(
    v2_pre_topc(sK3) ),
    inference(resolution,[],[f122,f47])).

fof(f218,plain,(
    ! [X3] :
      ( ~ v2_pre_topc(sK3)
      | ~ m1_pre_topc(X3,sK3)
      | ~ v3_pre_topc(u1_struct_0(X3),sK3)
      | v1_tsep_1(X3,sK3) ) ),
    inference(resolution,[],[f102,f109])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f95,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | ~ v3_pre_topc(X2,X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f36])).

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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f324,plain,(
    v3_pre_topc(u1_struct_0(sK2),sK3) ),
    inference(backward_demodulation,[],[f210,f317])).

fof(f210,plain,(
    v3_pre_topc(u1_struct_0(sK3),sK3) ),
    inference(subsumption_resolution,[],[f209,f124])).

fof(f209,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f208,f109])).

fof(f208,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f207,f113])).

fof(f207,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK3)
    | ~ m1_pre_topc(sK3,sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(resolution,[],[f202,f74])).

fof(f74,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X3,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X1,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_pre_topc)).

fof(f202,plain,(
    ! [X0] :
      ( ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(sK3))
      | v3_pre_topc(u1_struct_0(X0),sK3)
      | ~ m1_pre_topc(X0,sK3) ) ),
    inference(subsumption_resolution,[],[f201,f109])).

fof(f201,plain,(
    ! [X0] :
      ( ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(sK3))
      | v3_pre_topc(u1_struct_0(X0),sK3)
      | ~ m1_pre_topc(X0,sK3)
      | ~ l1_pre_topc(sK3) ) ),
    inference(resolution,[],[f186,f78])).

fof(f186,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ r2_hidden(X3,u1_pre_topc(sK3))
      | v3_pre_topc(X3,sK3) ) ),
    inference(resolution,[],[f79,f109])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f953,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK3,X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ v1_tsep_1(sK2,sK3)
      | ~ m1_pre_topc(sK2,sK3)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(sK2)
      | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5) ) ),
    inference(resolution,[],[f952,f100])).

fof(f100,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f37,f38])).

fof(f37,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f952,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK5,u1_struct_0(X0))
      | ~ m1_pre_topc(sK3,X1)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ v1_tsep_1(X0,sK3)
      | ~ m1_pre_topc(X0,sK3)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X0)
      | ~ r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5) ) ),
    inference(subsumption_resolution,[],[f951,f40])).

fof(f40,plain,(
    ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f18])).

fof(f951,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_pre_topc(sK3,X1)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ v1_tsep_1(X0,sK3)
      | ~ m1_pre_topc(X0,sK3)
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(sK5,u1_struct_0(X0))
      | ~ r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5)
      | r1_tmap_1(sK3,sK1,sK4,sK5) ) ),
    inference(resolution,[],[f950,f100])).

fof(f950,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK2))
      | v2_struct_0(X1)
      | ~ m1_pre_topc(sK3,X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ v1_tsep_1(X1,sK3)
      | ~ m1_pre_topc(X1,sK3)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),X2)
      | r1_tmap_1(sK3,sK1,sK4,X2) ) ),
    inference(subsumption_resolution,[],[f949,f319])).

fof(f319,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f43,f317])).

fof(f43,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f949,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(sK3,X0)
      | v2_struct_0(X0)
      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ v2_pre_topc(X0)
      | ~ v1_tsep_1(X1,sK3)
      | ~ m1_pre_topc(X1,sK3)
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),X2)
      | r1_tmap_1(sK3,sK1,sK4,X2) ) ),
    inference(subsumption_resolution,[],[f948,f52])).

fof(f52,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f948,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(sK3,X0)
      | v2_struct_0(X0)
      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ v2_pre_topc(X0)
      | ~ v1_tsep_1(X1,sK3)
      | ~ m1_pre_topc(X1,sK3)
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),X2)
      | r1_tmap_1(sK3,sK1,sK4,X2) ) ),
    inference(subsumption_resolution,[],[f947,f51])).

fof(f51,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f947,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(sK3,X0)
      | v2_struct_0(X0)
      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ v2_pre_topc(X0)
      | ~ v1_tsep_1(X1,sK3)
      | ~ m1_pre_topc(X1,sK3)
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),X2)
      | r1_tmap_1(sK3,sK1,sK4,X2) ) ),
    inference(subsumption_resolution,[],[f945,f50])).

fof(f50,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f945,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(sK3,X0)
      | v2_struct_0(X0)
      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ v2_pre_topc(X0)
      | ~ v1_tsep_1(X1,sK3)
      | ~ m1_pre_topc(X1,sK3)
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),X2)
      | r1_tmap_1(sK3,sK1,sK4,X2) ) ),
    inference(resolution,[],[f929,f320])).

fof(f320,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f44,f317])).

fof(f44,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f18])).

fof(f929,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(sK3,X1)
      | v2_struct_0(X1)
      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(X0))
      | ~ v2_pre_topc(X1)
      | ~ v1_tsep_1(X2,sK3)
      | ~ m1_pre_topc(X2,sK3)
      | ~ m1_subset_1(X3,u1_struct_0(sK2))
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK3,X2,sK4),X3)
      | r1_tmap_1(sK3,X0,sK4,X3) ) ),
    inference(subsumption_resolution,[],[f922,f46])).

fof(f46,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f922,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X2)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,X1)
      | v2_struct_0(X1)
      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(X0))
      | ~ v2_pre_topc(X1)
      | ~ v1_tsep_1(X2,sK3)
      | ~ m1_pre_topc(X2,sK3)
      | ~ m1_subset_1(X3,u1_struct_0(sK2))
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK3,X2,sK4),X3)
      | r1_tmap_1(sK3,X0,sK4,X3) ) ),
    inference(superposition,[],[f920,f317])).

fof(f920,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X0)
      | ~ v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v2_pre_topc(X0)
      | ~ v1_tsep_1(X2,X3)
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X2))
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X4)
      | r1_tmap_1(X3,X1,sK4,X4) ) ),
    inference(subsumption_resolution,[],[f919,f85])).

fof(f919,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X0)
      | ~ v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_tsep_1(X2,X3)
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X2))
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X4)
      | r1_tmap_1(X3,X1,sK4,X4) ) ),
    inference(resolution,[],[f94,f42])).

fof(f42,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f18])).

fof(f94,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X0)
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_tsep_1(X2,X3)
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
      | r1_tmap_1(X3,X1,X4,X6) ) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
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
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tmap_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n022.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 14:09:41 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.23/0.50  % (2407)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.23/0.50  % (2398)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.23/0.52  % (2400)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.23/0.52  % (2415)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.23/0.52  % (2399)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.23/0.52  % (2394)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.17/0.53  % (2392)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.17/0.53  % (2396)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.17/0.53  % (2399)Refutation not found, incomplete strategy% (2399)------------------------------
% 1.17/0.53  % (2399)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.17/0.53  % (2399)Termination reason: Refutation not found, incomplete strategy
% 1.17/0.53  
% 1.17/0.53  % (2399)Memory used [KB]: 1791
% 1.17/0.53  % (2399)Time elapsed: 0.103 s
% 1.17/0.53  % (2399)------------------------------
% 1.17/0.53  % (2399)------------------------------
% 1.17/0.53  % (2393)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.17/0.53  % (2401)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.17/0.53  % (2417)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.17/0.53  % (2392)Refutation not found, incomplete strategy% (2392)------------------------------
% 1.17/0.53  % (2392)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.17/0.53  % (2392)Termination reason: Refutation not found, incomplete strategy
% 1.17/0.53  
% 1.17/0.53  % (2392)Memory used [KB]: 10746
% 1.17/0.53  % (2392)Time elapsed: 0.105 s
% 1.17/0.53  % (2392)------------------------------
% 1.17/0.53  % (2392)------------------------------
% 1.17/0.54  % (2412)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.17/0.54  % (2410)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.17/0.54  % (2414)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.17/0.54  % (2408)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.17/0.54  % (2403)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.39/0.55  % (2402)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.39/0.55  % (2409)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.39/0.55  % (2405)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.39/0.55  % (2413)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.39/0.55  % (2397)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.39/0.55  % (2395)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.39/0.55  % (2418)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.39/0.55  % (2411)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.39/0.56  % (2412)Refutation found. Thanks to Tanya!
% 1.39/0.56  % SZS status Theorem for theBenchmark
% 1.39/0.56  % SZS output start Proof for theBenchmark
% 1.39/0.56  fof(f966,plain,(
% 1.39/0.56    $false),
% 1.39/0.56    inference(subsumption_resolution,[],[f965,f47])).
% 1.39/0.56  fof(f47,plain,(
% 1.39/0.56    m1_pre_topc(sK3,sK0)),
% 1.39/0.56    inference(cnf_transformation,[],[f18])).
% 1.39/0.56  % (2406)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.39/0.56  fof(f18,plain,(
% 1.39/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.39/0.56    inference(flattening,[],[f17])).
% 1.39/0.56  fof(f17,plain,(
% 1.39/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.39/0.56    inference(ennf_transformation,[],[f15])).
% 1.39/0.56  fof(f15,negated_conjecture,(
% 1.39/0.56    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 1.39/0.56    inference(negated_conjecture,[],[f14])).
% 1.39/0.56  fof(f14,conjecture,(
% 1.39/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tmap_1)).
% 1.39/0.56  fof(f965,plain,(
% 1.39/0.56    ~m1_pre_topc(sK3,sK0)),
% 1.39/0.56    inference(subsumption_resolution,[],[f964,f55])).
% 1.39/0.56  fof(f55,plain,(
% 1.39/0.56    l1_pre_topc(sK0)),
% 1.39/0.56    inference(cnf_transformation,[],[f18])).
% 1.39/0.56  fof(f964,plain,(
% 1.39/0.56    ~l1_pre_topc(sK0) | ~m1_pre_topc(sK3,sK0)),
% 1.39/0.56    inference(subsumption_resolution,[],[f963,f54])).
% 1.39/0.56  fof(f54,plain,(
% 1.39/0.56    v2_pre_topc(sK0)),
% 1.39/0.56    inference(cnf_transformation,[],[f18])).
% 1.39/0.56  fof(f963,plain,(
% 1.39/0.56    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK3,sK0)),
% 1.39/0.56    inference(subsumption_resolution,[],[f962,f53])).
% 1.39/0.56  fof(f53,plain,(
% 1.39/0.56    ~v2_struct_0(sK0)),
% 1.39/0.56    inference(cnf_transformation,[],[f18])).
% 1.39/0.56  fof(f962,plain,(
% 1.39/0.56    v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK3,sK0)),
% 1.39/0.56    inference(resolution,[],[f957,f99])).
% 1.39/0.56  fof(f99,plain,(
% 1.39/0.56    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)),
% 1.39/0.56    inference(backward_demodulation,[],[f39,f38])).
% 1.39/0.56  fof(f38,plain,(
% 1.39/0.56    sK5 = sK6),
% 1.39/0.56    inference(cnf_transformation,[],[f18])).
% 1.39/0.56  fof(f39,plain,(
% 1.39/0.56    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 1.39/0.56    inference(cnf_transformation,[],[f18])).
% 1.39/0.56  fof(f957,plain,(
% 1.39/0.56    ( ! [X0] : (~r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK3,X0)) )),
% 1.39/0.56    inference(subsumption_resolution,[],[f956,f48])).
% 1.39/0.56  fof(f48,plain,(
% 1.39/0.56    ~v2_struct_0(sK2)),
% 1.39/0.56    inference(cnf_transformation,[],[f18])).
% 1.39/0.56  fof(f956,plain,(
% 1.39/0.56    ( ! [X0] : (~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK2) | ~r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5)) )),
% 1.39/0.56    inference(subsumption_resolution,[],[f955,f629])).
% 1.39/0.56  fof(f629,plain,(
% 1.39/0.56    m1_pre_topc(sK2,sK3)),
% 1.39/0.56    inference(subsumption_resolution,[],[f628,f54])).
% 1.39/0.56  fof(f628,plain,(
% 1.39/0.56    m1_pre_topc(sK2,sK3) | ~v2_pre_topc(sK0)),
% 1.39/0.56    inference(subsumption_resolution,[],[f624,f55])).
% 1.39/0.56  fof(f624,plain,(
% 1.39/0.56    ~l1_pre_topc(sK0) | m1_pre_topc(sK2,sK3) | ~v2_pre_topc(sK0)),
% 1.39/0.56    inference(resolution,[],[f620,f49])).
% 1.39/0.56  fof(f49,plain,(
% 1.39/0.56    m1_pre_topc(sK2,sK0)),
% 1.39/0.56    inference(cnf_transformation,[],[f18])).
% 1.39/0.56  fof(f620,plain,(
% 1.39/0.56    ( ! [X5] : (~m1_pre_topc(sK2,X5) | ~l1_pre_topc(X5) | m1_pre_topc(sK2,sK3) | ~v2_pre_topc(X5)) )),
% 1.39/0.56    inference(subsumption_resolution,[],[f615,f138])).
% 1.39/0.56  fof(f138,plain,(
% 1.39/0.56    m1_pre_topc(sK3,sK2)),
% 1.39/0.56    inference(resolution,[],[f137,f113])).
% 1.39/0.56  fof(f113,plain,(
% 1.39/0.56    m1_pre_topc(sK3,sK3)),
% 1.39/0.56    inference(resolution,[],[f109,f56])).
% 1.39/0.56  fof(f56,plain,(
% 1.39/0.56    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,X0)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f19])).
% 1.39/0.56  fof(f19,plain,(
% 1.39/0.56    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 1.39/0.56    inference(ennf_transformation,[],[f10])).
% 1.39/0.56  fof(f10,axiom,(
% 1.39/0.56    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).
% 1.39/0.56  fof(f109,plain,(
% 1.39/0.56    l1_pre_topc(sK3)),
% 1.39/0.56    inference(resolution,[],[f107,f47])).
% 1.39/0.56  fof(f107,plain,(
% 1.39/0.56    ( ! [X1] : (~m1_pre_topc(X1,sK0) | l1_pre_topc(X1)) )),
% 1.39/0.56    inference(resolution,[],[f77,f55])).
% 1.39/0.56  fof(f77,plain,(
% 1.39/0.56    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f23])).
% 1.39/0.56  fof(f23,plain,(
% 1.39/0.56    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.39/0.56    inference(ennf_transformation,[],[f5])).
% 1.39/0.56  fof(f5,axiom,(
% 1.39/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.39/0.56  fof(f137,plain,(
% 1.39/0.56    ( ! [X2] : (~m1_pre_topc(X2,sK3) | m1_pre_topc(X2,sK2)) )),
% 1.39/0.56    inference(forward_demodulation,[],[f135,f45])).
% 1.39/0.56  fof(f45,plain,(
% 1.39/0.56    sK3 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 1.39/0.56    inference(cnf_transformation,[],[f18])).
% 1.39/0.56  fof(f135,plain,(
% 1.39/0.56    ( ! [X2] : (~m1_pre_topc(X2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | m1_pre_topc(X2,sK2)) )),
% 1.39/0.56    inference(resolution,[],[f81,f110])).
% 1.39/0.56  fof(f110,plain,(
% 1.39/0.56    l1_pre_topc(sK2)),
% 1.39/0.56    inference(resolution,[],[f107,f49])).
% 1.39/0.56  fof(f81,plain,(
% 1.39/0.56    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | m1_pre_topc(X1,X0)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f26])).
% 1.39/0.56  fof(f26,plain,(
% 1.39/0.56    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 1.39/0.56    inference(ennf_transformation,[],[f6])).
% 1.39/0.56  fof(f6,axiom,(
% 1.39/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).
% 1.39/0.56  fof(f615,plain,(
% 1.39/0.56    ( ! [X5] : (~m1_pre_topc(sK3,sK2) | ~l1_pre_topc(X5) | ~m1_pre_topc(sK2,X5) | m1_pre_topc(sK2,sK3) | ~v2_pre_topc(X5)) )),
% 1.39/0.56    inference(resolution,[],[f450,f113])).
% 1.39/0.56  fof(f450,plain,(
% 1.39/0.56    ( ! [X2,X1] : (~m1_pre_topc(sK3,X1) | ~m1_pre_topc(X1,sK2) | ~l1_pre_topc(X2) | ~m1_pre_topc(sK2,X2) | m1_pre_topc(sK2,X1) | ~v2_pre_topc(X2)) )),
% 1.39/0.56    inference(subsumption_resolution,[],[f446,f85])).
% 1.39/0.56  fof(f85,plain,(
% 1.39/0.56    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X1) | m1_pre_topc(X2,X0)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f32])).
% 1.39/0.56  fof(f32,plain,(
% 1.39/0.56    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.39/0.56    inference(flattening,[],[f31])).
% 1.39/0.56  fof(f31,plain,(
% 1.39/0.56    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.39/0.56    inference(ennf_transformation,[],[f12])).
% 1.39/0.56  fof(f12,axiom,(
% 1.39/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).
% 1.39/0.56  fof(f446,plain,(
% 1.39/0.56    ( ! [X2,X1] : (~m1_pre_topc(sK3,X1) | ~m1_pre_topc(X1,sK2) | ~l1_pre_topc(X2) | ~m1_pre_topc(sK2,X2) | ~m1_pre_topc(X1,X2) | m1_pre_topc(sK2,X1) | ~v2_pre_topc(X2)) )),
% 1.39/0.56    inference(resolution,[],[f359,f87])).
% 1.39/0.56  fof(f87,plain,(
% 1.39/0.56    ( ! [X2,X0,X1] : (~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | m1_pre_topc(X1,X2) | ~v2_pre_topc(X0)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f34])).
% 1.39/0.56  fof(f34,plain,(
% 1.39/0.56    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.39/0.56    inference(flattening,[],[f33])).
% 1.39/0.56  fof(f33,plain,(
% 1.39/0.56    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.39/0.56    inference(ennf_transformation,[],[f11])).
% 1.39/0.56  fof(f11,axiom,(
% 1.39/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).
% 1.39/0.56  fof(f359,plain,(
% 1.39/0.56    ( ! [X10] : (r1_tarski(u1_struct_0(sK2),u1_struct_0(X10)) | ~m1_pre_topc(sK3,X10) | ~m1_pre_topc(X10,sK2)) )),
% 1.39/0.56    inference(superposition,[],[f269,f317])).
% 1.39/0.56  fof(f317,plain,(
% 1.39/0.56    u1_struct_0(sK2) = u1_struct_0(sK3)),
% 1.39/0.56    inference(subsumption_resolution,[],[f316,f115])).
% 1.39/0.56  fof(f115,plain,(
% 1.39/0.56    m1_pre_topc(sK2,sK2)),
% 1.39/0.56    inference(resolution,[],[f110,f56])).
% 1.39/0.56  fof(f316,plain,(
% 1.39/0.56    u1_struct_0(sK2) = u1_struct_0(sK3) | ~m1_pre_topc(sK2,sK2)),
% 1.39/0.56    inference(resolution,[],[f310,f171])).
% 1.39/0.56  fof(f171,plain,(
% 1.39/0.56    ( ! [X2] : (m1_pre_topc(X2,sK3) | ~m1_pre_topc(X2,sK2)) )),
% 1.39/0.56    inference(forward_demodulation,[],[f170,f45])).
% 1.39/0.56  fof(f170,plain,(
% 1.39/0.56    ( ! [X2] : (m1_pre_topc(X2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~m1_pre_topc(X2,sK2)) )),
% 1.39/0.56    inference(subsumption_resolution,[],[f166,f114])).
% 1.39/0.56  fof(f114,plain,(
% 1.39/0.56    ( ! [X0] : (~m1_pre_topc(X0,sK2) | l1_pre_topc(X0)) )),
% 1.39/0.56    inference(resolution,[],[f110,f77])).
% 1.39/0.56  fof(f166,plain,(
% 1.39/0.56    ( ! [X2] : (~l1_pre_topc(X2) | m1_pre_topc(X2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~m1_pre_topc(X2,sK2)) )),
% 1.39/0.56    inference(resolution,[],[f76,f110])).
% 1.39/0.56  fof(f76,plain,(
% 1.39/0.56    ( ! [X0,X1] : (~l1_pre_topc(X1) | ~l1_pre_topc(X0) | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f22])).
% 1.39/0.56  fof(f22,plain,(
% 1.39/0.56    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.39/0.56    inference(ennf_transformation,[],[f7])).
% 1.39/0.56  fof(f7,axiom,(
% 1.39/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).
% 1.39/0.56  fof(f310,plain,(
% 1.39/0.56    ~m1_pre_topc(sK2,sK3) | u1_struct_0(sK2) = u1_struct_0(sK3)),
% 1.39/0.56    inference(resolution,[],[f303,f138])).
% 1.39/0.56  fof(f303,plain,(
% 1.39/0.56    ( ! [X0] : (~m1_pre_topc(sK3,X0) | ~m1_pre_topc(X0,sK3) | u1_struct_0(X0) = u1_struct_0(sK3)) )),
% 1.39/0.56    inference(resolution,[],[f302,f47])).
% 1.39/0.56  fof(f302,plain,(
% 1.39/0.56    ( ! [X6,X7] : (~m1_pre_topc(X7,sK0) | u1_struct_0(X7) = u1_struct_0(X6) | ~m1_pre_topc(X6,X7) | ~m1_pre_topc(X7,X6)) )),
% 1.39/0.56    inference(subsumption_resolution,[],[f300,f145])).
% 1.39/0.56  fof(f145,plain,(
% 1.39/0.56    ( ! [X0,X1] : (~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X1,X0) | m1_pre_topc(X1,sK0)) )),
% 1.39/0.56    inference(subsumption_resolution,[],[f141,f54])).
% 1.39/0.56  fof(f141,plain,(
% 1.39/0.56    ( ! [X0,X1] : (~v2_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X1,X0) | m1_pre_topc(X1,sK0)) )),
% 1.39/0.56    inference(resolution,[],[f85,f55])).
% 1.39/0.56  fof(f300,plain,(
% 1.39/0.56    ( ! [X6,X7] : (~m1_pre_topc(X6,sK0) | ~m1_pre_topc(X7,X6) | u1_struct_0(X7) = u1_struct_0(X6) | ~m1_pre_topc(X6,X7) | ~m1_pre_topc(X7,sK0)) )),
% 1.39/0.56    inference(resolution,[],[f271,f267])).
% 1.39/0.56  fof(f267,plain,(
% 1.39/0.56    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X0,sK0)) )),
% 1.39/0.56    inference(subsumption_resolution,[],[f263,f54])).
% 1.39/0.56  fof(f263,plain,(
% 1.39/0.56    ( ! [X0,X1] : (~v2_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X1,X0) | r1_tarski(u1_struct_0(X1),u1_struct_0(X0))) )),
% 1.39/0.56    inference(resolution,[],[f101,f55])).
% 1.39/0.56  fof(f101,plain,(
% 1.39/0.56    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X2) | r1_tarski(u1_struct_0(X1),u1_struct_0(X2))) )),
% 1.39/0.56    inference(subsumption_resolution,[],[f86,f85])).
% 1.39/0.56  fof(f86,plain,(
% 1.39/0.56    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X2) | r1_tarski(u1_struct_0(X1),u1_struct_0(X2))) )),
% 1.39/0.56    inference(cnf_transformation,[],[f34])).
% 1.39/0.56  fof(f271,plain,(
% 1.39/0.56    ( ! [X0,X1] : (~r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X0,X1) | u1_struct_0(X0) = u1_struct_0(X1)) )),
% 1.39/0.56    inference(resolution,[],[f267,f92])).
% 1.39/0.56  fof(f92,plain,(
% 1.39/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.39/0.56    inference(cnf_transformation,[],[f1])).
% 1.39/0.56  fof(f1,axiom,(
% 1.39/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.39/0.56  fof(f269,plain,(
% 1.39/0.56    ( ! [X4,X5] : (r1_tarski(u1_struct_0(X5),u1_struct_0(X4)) | ~m1_pre_topc(X5,X4) | ~m1_pre_topc(X4,sK2)) )),
% 1.39/0.56    inference(subsumption_resolution,[],[f265,f125])).
% 1.39/0.56  fof(f125,plain,(
% 1.39/0.56    v2_pre_topc(sK2)),
% 1.39/0.56    inference(resolution,[],[f122,f49])).
% 1.39/0.56  fof(f122,plain,(
% 1.39/0.56    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v2_pre_topc(X0)) )),
% 1.39/0.56    inference(subsumption_resolution,[],[f118,f54])).
% 1.39/0.56  fof(f118,plain,(
% 1.39/0.56    ( ! [X0] : (~v2_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | v2_pre_topc(X0)) )),
% 1.39/0.56    inference(resolution,[],[f84,f55])).
% 1.39/0.56  fof(f84,plain,(
% 1.39/0.56    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_pre_topc(X1)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f30])).
% 1.39/0.56  fof(f30,plain,(
% 1.39/0.56    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.39/0.56    inference(flattening,[],[f29])).
% 1.39/0.56  fof(f29,plain,(
% 1.39/0.56    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.39/0.56    inference(ennf_transformation,[],[f2])).
% 1.39/0.56  fof(f2,axiom,(
% 1.39/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).
% 1.39/0.56  fof(f265,plain,(
% 1.39/0.56    ( ! [X4,X5] : (~v2_pre_topc(sK2) | ~m1_pre_topc(X4,sK2) | ~m1_pre_topc(X5,X4) | r1_tarski(u1_struct_0(X5),u1_struct_0(X4))) )),
% 1.39/0.56    inference(resolution,[],[f101,f110])).
% 1.39/0.56  fof(f955,plain,(
% 1.39/0.56    ( ! [X0] : (~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(sK2,sK3) | ~l1_pre_topc(X0) | v2_struct_0(sK2) | ~r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5)) )),
% 1.39/0.56    inference(subsumption_resolution,[],[f953,f631])).
% 1.39/0.56  fof(f631,plain,(
% 1.39/0.56    v1_tsep_1(sK2,sK3)),
% 1.39/0.56    inference(subsumption_resolution,[],[f333,f629])).
% 1.39/0.56  fof(f333,plain,(
% 1.39/0.56    v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3)),
% 1.39/0.56    inference(resolution,[],[f324,f222])).
% 1.39/0.56  fof(f222,plain,(
% 1.39/0.56    ( ! [X3] : (~v3_pre_topc(u1_struct_0(X3),sK3) | ~m1_pre_topc(X3,sK3) | v1_tsep_1(X3,sK3)) )),
% 1.39/0.56    inference(subsumption_resolution,[],[f218,f124])).
% 1.39/0.56  fof(f124,plain,(
% 1.39/0.56    v2_pre_topc(sK3)),
% 1.39/0.56    inference(resolution,[],[f122,f47])).
% 1.39/0.56  fof(f218,plain,(
% 1.39/0.56    ( ! [X3] : (~v2_pre_topc(sK3) | ~m1_pre_topc(X3,sK3) | ~v3_pre_topc(u1_struct_0(X3),sK3) | v1_tsep_1(X3,sK3)) )),
% 1.39/0.56    inference(resolution,[],[f102,f109])).
% 1.39/0.56  fof(f102,plain,(
% 1.39/0.56    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v3_pre_topc(u1_struct_0(X1),X0) | v1_tsep_1(X1,X0)) )),
% 1.39/0.56    inference(subsumption_resolution,[],[f95,f78])).
% 1.39/0.56  fof(f78,plain,(
% 1.39/0.56    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f24])).
% 1.39/0.56  fof(f24,plain,(
% 1.39/0.56    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.39/0.56    inference(ennf_transformation,[],[f9])).
% 1.39/0.56  fof(f9,axiom,(
% 1.39/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 1.39/0.56  fof(f95,plain,(
% 1.39/0.56    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(u1_struct_0(X1),X0) | v1_tsep_1(X1,X0)) )),
% 1.39/0.56    inference(equality_resolution,[],[f89])).
% 1.39/0.56  fof(f89,plain,(
% 1.39/0.56    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | ~v3_pre_topc(X2,X0) | v1_tsep_1(X1,X0)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f36])).
% 1.39/0.56  fof(f36,plain,(
% 1.39/0.56    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.39/0.56    inference(flattening,[],[f35])).
% 1.39/0.56  fof(f35,plain,(
% 1.39/0.56    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.39/0.56    inference(ennf_transformation,[],[f8])).
% 1.39/0.56  fof(f8,axiom,(
% 1.39/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).
% 1.39/0.56  fof(f324,plain,(
% 1.39/0.56    v3_pre_topc(u1_struct_0(sK2),sK3)),
% 1.39/0.56    inference(backward_demodulation,[],[f210,f317])).
% 1.39/0.56  fof(f210,plain,(
% 1.39/0.56    v3_pre_topc(u1_struct_0(sK3),sK3)),
% 1.39/0.56    inference(subsumption_resolution,[],[f209,f124])).
% 1.39/0.56  fof(f209,plain,(
% 1.39/0.56    v3_pre_topc(u1_struct_0(sK3),sK3) | ~v2_pre_topc(sK3)),
% 1.39/0.56    inference(subsumption_resolution,[],[f208,f109])).
% 1.39/0.56  fof(f208,plain,(
% 1.39/0.56    v3_pre_topc(u1_struct_0(sK3),sK3) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3)),
% 1.39/0.56    inference(subsumption_resolution,[],[f207,f113])).
% 1.39/0.56  fof(f207,plain,(
% 1.39/0.56    v3_pre_topc(u1_struct_0(sK3),sK3) | ~m1_pre_topc(sK3,sK3) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3)),
% 1.39/0.56    inference(resolution,[],[f202,f74])).
% 1.39/0.56  fof(f74,plain,(
% 1.39/0.56    ( ! [X0] : (r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f21])).
% 1.39/0.56  fof(f21,plain,(
% 1.39/0.56    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 1.39/0.56    inference(flattening,[],[f20])).
% 1.39/0.56  fof(f20,plain,(
% 1.39/0.56    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : ((r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | (~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : ((r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 1.39/0.56    inference(ennf_transformation,[],[f16])).
% 1.39/0.56  fof(f16,plain,(
% 1.39/0.56    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X3,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 1.39/0.56    inference(rectify,[],[f3])).
% 1.39/0.56  fof(f3,axiom,(
% 1.39/0.56    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_pre_topc)).
% 1.39/0.56  fof(f202,plain,(
% 1.39/0.56    ( ! [X0] : (~r2_hidden(u1_struct_0(X0),u1_pre_topc(sK3)) | v3_pre_topc(u1_struct_0(X0),sK3) | ~m1_pre_topc(X0,sK3)) )),
% 1.39/0.56    inference(subsumption_resolution,[],[f201,f109])).
% 1.39/0.56  fof(f201,plain,(
% 1.39/0.56    ( ! [X0] : (~r2_hidden(u1_struct_0(X0),u1_pre_topc(sK3)) | v3_pre_topc(u1_struct_0(X0),sK3) | ~m1_pre_topc(X0,sK3) | ~l1_pre_topc(sK3)) )),
% 1.39/0.56    inference(resolution,[],[f186,f78])).
% 1.39/0.56  fof(f186,plain,(
% 1.39/0.56    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3))) | ~r2_hidden(X3,u1_pre_topc(sK3)) | v3_pre_topc(X3,sK3)) )),
% 1.39/0.56    inference(resolution,[],[f79,f109])).
% 1.39/0.56  fof(f79,plain,(
% 1.39/0.56    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,u1_pre_topc(X0)) | v3_pre_topc(X1,X0)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f25])).
% 1.39/0.56  fof(f25,plain,(
% 1.39/0.56    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.39/0.56    inference(ennf_transformation,[],[f4])).
% 1.39/0.56  fof(f4,axiom,(
% 1.39/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).
% 1.39/0.56  fof(f953,plain,(
% 1.39/0.56    ( ! [X0] : (~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~l1_pre_topc(X0) | v2_struct_0(sK2) | ~r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5)) )),
% 1.39/0.56    inference(resolution,[],[f952,f100])).
% 1.39/0.56  fof(f100,plain,(
% 1.39/0.56    m1_subset_1(sK5,u1_struct_0(sK2))),
% 1.39/0.56    inference(forward_demodulation,[],[f37,f38])).
% 1.39/0.56  fof(f37,plain,(
% 1.39/0.56    m1_subset_1(sK6,u1_struct_0(sK2))),
% 1.39/0.56    inference(cnf_transformation,[],[f18])).
% 1.39/0.56  fof(f952,plain,(
% 1.39/0.56    ( ! [X0,X1] : (~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_pre_topc(sK3,X1) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~v1_tsep_1(X0,sK3) | ~m1_pre_topc(X0,sK3) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5)) )),
% 1.39/0.56    inference(subsumption_resolution,[],[f951,f40])).
% 1.39/0.56  fof(f40,plain,(
% 1.39/0.56    ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 1.39/0.56    inference(cnf_transformation,[],[f18])).
% 1.39/0.56  fof(f951,plain,(
% 1.39/0.56    ( ! [X0,X1] : (v2_struct_0(X0) | ~m1_pre_topc(sK3,X1) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~v1_tsep_1(X0,sK3) | ~m1_pre_topc(X0,sK3) | ~l1_pre_topc(X1) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5) | r1_tmap_1(sK3,sK1,sK4,sK5)) )),
% 1.39/0.56    inference(resolution,[],[f950,f100])).
% 1.39/0.56  fof(f950,plain,(
% 1.39/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(sK2)) | v2_struct_0(X1) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v1_tsep_1(X1,sK3) | ~m1_pre_topc(X1,sK3) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),X2) | r1_tmap_1(sK3,sK1,sK4,X2)) )),
% 1.39/0.56    inference(subsumption_resolution,[],[f949,f319])).
% 1.39/0.56  fof(f319,plain,(
% 1.39/0.56    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))),
% 1.39/0.56    inference(backward_demodulation,[],[f43,f317])).
% 1.39/0.56  fof(f43,plain,(
% 1.39/0.56    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 1.39/0.56    inference(cnf_transformation,[],[f18])).
% 1.39/0.56  fof(f949,plain,(
% 1.39/0.56    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v2_pre_topc(X0) | ~v1_tsep_1(X1,sK3) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,u1_struct_0(sK2)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),X2) | r1_tmap_1(sK3,sK1,sK4,X2)) )),
% 1.39/0.56    inference(subsumption_resolution,[],[f948,f52])).
% 1.39/0.56  fof(f52,plain,(
% 1.39/0.56    l1_pre_topc(sK1)),
% 1.39/0.56    inference(cnf_transformation,[],[f18])).
% 1.39/0.56  fof(f948,plain,(
% 1.39/0.56    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~l1_pre_topc(sK1) | v2_struct_0(X1) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v2_pre_topc(X0) | ~v1_tsep_1(X1,sK3) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,u1_struct_0(sK2)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),X2) | r1_tmap_1(sK3,sK1,sK4,X2)) )),
% 1.39/0.56    inference(subsumption_resolution,[],[f947,f51])).
% 1.39/0.56  fof(f51,plain,(
% 1.39/0.56    v2_pre_topc(sK1)),
% 1.39/0.56    inference(cnf_transformation,[],[f18])).
% 1.39/0.56  fof(f947,plain,(
% 1.39/0.56    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X1) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v2_pre_topc(X0) | ~v1_tsep_1(X1,sK3) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,u1_struct_0(sK2)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),X2) | r1_tmap_1(sK3,sK1,sK4,X2)) )),
% 1.39/0.56    inference(subsumption_resolution,[],[f945,f50])).
% 1.39/0.56  fof(f50,plain,(
% 1.39/0.56    ~v2_struct_0(sK1)),
% 1.39/0.56    inference(cnf_transformation,[],[f18])).
% 1.39/0.56  fof(f945,plain,(
% 1.39/0.56    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X1) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v2_pre_topc(X0) | ~v1_tsep_1(X1,sK3) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,u1_struct_0(sK2)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),X2) | r1_tmap_1(sK3,sK1,sK4,X2)) )),
% 1.39/0.56    inference(resolution,[],[f929,f320])).
% 1.39/0.56  fof(f320,plain,(
% 1.39/0.56    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 1.39/0.56    inference(backward_demodulation,[],[f44,f317])).
% 1.39/0.56  fof(f44,plain,(
% 1.39/0.56    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 1.39/0.56    inference(cnf_transformation,[],[f18])).
% 1.39/0.56  fof(f929,plain,(
% 1.39/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X2) | ~m1_pre_topc(sK3,X1) | v2_struct_0(X1) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(X0)) | ~v2_pre_topc(X1) | ~v1_tsep_1(X2,sK3) | ~m1_pre_topc(X2,sK3) | ~m1_subset_1(X3,u1_struct_0(sK2)) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK3,X2,sK4),X3) | r1_tmap_1(sK3,X0,sK4,X3)) )),
% 1.39/0.56    inference(subsumption_resolution,[],[f922,f46])).
% 1.39/0.56  fof(f46,plain,(
% 1.39/0.56    ~v2_struct_0(sK3)),
% 1.39/0.56    inference(cnf_transformation,[],[f18])).
% 1.39/0.56  fof(f922,plain,(
% 1.39/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X2) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,X1) | v2_struct_0(X1) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(X0)) | ~v2_pre_topc(X1) | ~v1_tsep_1(X2,sK3) | ~m1_pre_topc(X2,sK3) | ~m1_subset_1(X3,u1_struct_0(sK2)) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK3,X2,sK4),X3) | r1_tmap_1(sK3,X0,sK4,X3)) )),
% 1.39/0.56    inference(superposition,[],[f920,f317])).
% 1.39/0.56  fof(f920,plain,(
% 1.39/0.56    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) | ~v2_pre_topc(X0) | ~v1_tsep_1(X2,X3) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X2)) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X4) | r1_tmap_1(X3,X1,sK4,X4)) )),
% 1.39/0.56    inference(subsumption_resolution,[],[f919,f85])).
% 1.39/0.56  fof(f919,plain,(
% 1.39/0.56    ( ! [X4,X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_tsep_1(X2,X3) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X2)) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X4) | r1_tmap_1(X3,X1,sK4,X4)) )),
% 1.39/0.56    inference(resolution,[],[f94,f42])).
% 1.39/0.56  fof(f42,plain,(
% 1.39/0.56    v1_funct_1(sK4)),
% 1.39/0.56    inference(cnf_transformation,[],[f18])).
% 1.39/0.56  fof(f94,plain,(
% 1.39/0.56    ( ! [X6,X4,X2,X0,X3,X1] : (~v1_funct_1(X4) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X0) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_tsep_1(X2,X3) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X6)) )),
% 1.39/0.56    inference(equality_resolution,[],[f82])).
% 1.39/0.56  fof(f82,plain,(
% 1.39/0.56    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_tsep_1(X2,X3) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | X5 != X6 | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f28])).
% 1.39/0.56  fof(f28,plain,(
% 1.39/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.39/0.56    inference(flattening,[],[f27])).
% 1.39/0.56  fof(f27,plain,(
% 1.39/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | (~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.39/0.56    inference(ennf_transformation,[],[f13])).
% 1.39/0.56  fof(f13,axiom,(
% 1.39/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tmap_1)).
% 1.39/0.56  % SZS output end Proof for theBenchmark
% 1.39/0.56  % (2412)------------------------------
% 1.39/0.56  % (2412)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.56  % (2412)Termination reason: Refutation
% 1.39/0.56  
% 1.39/0.56  % (2412)Memory used [KB]: 2174
% 1.39/0.56  % (2412)Time elapsed: 0.141 s
% 1.39/0.56  % (2412)------------------------------
% 1.39/0.56  % (2412)------------------------------
% 1.39/0.56  % (2389)Success in time 0.188 s
%------------------------------------------------------------------------------
