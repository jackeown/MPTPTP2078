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
% DateTime   : Thu Dec  3 13:19:12 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  197 (1677 expanded)
%              Number of leaves         :   16 ( 330 expanded)
%              Depth                    :   58
%              Number of atoms          : 1093 (15356 expanded)
%              Number of equality atoms :   68 (1592 expanded)
%              Maximal formula depth    :   27 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f984,plain,(
    $false ),
    inference(subsumption_resolution,[],[f983,f193])).

fof(f193,plain,(
    m1_subset_1(sK5,k2_struct_0(sK3)) ),
    inference(backward_demodulation,[],[f47,f192])).

fof(f192,plain,(
    u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(resolution,[],[f136,f62])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f136,plain,(
    l1_struct_0(sK3) ),
    inference(resolution,[],[f98,f63])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f98,plain,(
    l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f96,f61])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tmap_1)).

fof(f96,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK3) ),
    inference(resolution,[],[f67,f53])).

fof(f53,plain,(
    m1_pre_topc(sK3,sK0) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f47,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f19])).

fof(f983,plain,(
    ~ m1_subset_1(sK5,k2_struct_0(sK3)) ),
    inference(forward_demodulation,[],[f982,f192])).

fof(f982,plain,(
    ~ m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f981,f195])).

fof(f195,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f95,f192])).

fof(f95,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f50,f93])).

fof(f93,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(resolution,[],[f62,f89])).

fof(f89,plain,(
    l1_struct_0(sK1) ),
    inference(resolution,[],[f63,f58])).

fof(f58,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f50,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f19])).

fof(f981,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1))))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(forward_demodulation,[],[f980,f192])).

fof(f980,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1))))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(forward_demodulation,[],[f979,f93])).

fof(f979,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f978,f194])).

fof(f194,plain,(
    v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f94,f192])).

fof(f94,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f49,f93])).

fof(f49,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f978,plain,
    ( ~ v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(forward_demodulation,[],[f977,f192])).

fof(f977,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK3),k2_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(forward_demodulation,[],[f976,f93])).

fof(f976,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f975,f46])).

fof(f46,plain,(
    ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f19])).

fof(f975,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(subsumption_resolution,[],[f974,f56])).

fof(f56,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f974,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | v2_struct_0(sK1)
    | r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(subsumption_resolution,[],[f973,f135])).

fof(f135,plain,(
    m1_pre_topc(sK3,sK3) ),
    inference(resolution,[],[f98,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f973,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK3,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | v2_struct_0(sK1)
    | r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(subsumption_resolution,[],[f972,f832])).

fof(f832,plain,(
    v1_tsep_1(sK3,sK3) ),
    inference(subsumption_resolution,[],[f831,f107])).

fof(f107,plain,(
    v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f106,f60])).

fof(f60,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f106,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f104,f61])).

fof(f104,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK3) ),
    inference(resolution,[],[f76,f53])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f831,plain,
    ( ~ v2_pre_topc(sK3)
    | v1_tsep_1(sK3,sK3) ),
    inference(subsumption_resolution,[],[f830,f135])).

fof(f830,plain,
    ( ~ m1_pre_topc(sK3,sK3)
    | ~ v2_pre_topc(sK3)
    | v1_tsep_1(sK3,sK3) ),
    inference(subsumption_resolution,[],[f829,f98])).

fof(f829,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ m1_pre_topc(sK3,sK3)
    | ~ v2_pre_topc(sK3)
    | v1_tsep_1(sK3,sK3) ),
    inference(resolution,[],[f499,f137])).

fof(f137,plain,(
    v3_pre_topc(k2_struct_0(sK3),sK3) ),
    inference(subsumption_resolution,[],[f134,f107])).

fof(f134,plain,
    ( ~ v2_pre_topc(sK3)
    | v3_pre_topc(k2_struct_0(sK3),sK3) ),
    inference(resolution,[],[f98,f75])).

fof(f75,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v3_pre_topc(k2_struct_0(X0),X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
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

fof(f499,plain,(
    ! [X16] :
      ( ~ v3_pre_topc(k2_struct_0(sK3),X16)
      | ~ l1_pre_topc(X16)
      | ~ m1_pre_topc(sK3,X16)
      | ~ v2_pre_topc(X16)
      | v1_tsep_1(sK3,X16) ) ),
    inference(superposition,[],[f87,f192])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(u1_struct_0(X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f83,f68])).

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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | ~ v3_pre_topc(X2,X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f42])).

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
    inference(flattening,[],[f41])).

fof(f41,plain,(
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

fof(f972,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_tsep_1(sK3,sK3)
    | ~ m1_pre_topc(sK3,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | v2_struct_0(sK1)
    | r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(subsumption_resolution,[],[f971,f48])).

fof(f48,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f19])).

fof(f971,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_tsep_1(sK3,sK3)
    | ~ m1_pre_topc(sK3,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | v2_struct_0(sK1)
    | r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(subsumption_resolution,[],[f970,f98])).

fof(f970,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_tsep_1(sK3,sK3)
    | ~ m1_pre_topc(sK3,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | v2_struct_0(sK1)
    | r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(subsumption_resolution,[],[f969,f107])).

fof(f969,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_tsep_1(sK3,sK3)
    | ~ m1_pre_topc(sK3,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | v2_struct_0(sK1)
    | r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(subsumption_resolution,[],[f968,f52])).

fof(f52,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f968,plain,
    ( v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_tsep_1(sK3,sK3)
    | ~ m1_pre_topc(sK3,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | v2_struct_0(sK1)
    | r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(subsumption_resolution,[],[f967,f58])).

fof(f967,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_tsep_1(sK3,sK3)
    | ~ m1_pre_topc(sK3,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | v2_struct_0(sK1)
    | r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(subsumption_resolution,[],[f966,f57])).

fof(f57,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f966,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_tsep_1(sK3,sK3)
    | ~ m1_pre_topc(sK3,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | v2_struct_0(sK1)
    | r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(duplicate_literal_removal,[],[f963])).

fof(f963,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK3)
    | ~ v1_tsep_1(sK3,sK3)
    | ~ m1_pre_topc(sK3,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | v2_struct_0(sK1)
    | r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(resolution,[],[f962,f82])).

fof(f82,plain,(
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
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
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
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_tmap_1)).

fof(f962,plain,(
    r1_tmap_1(sK3,sK1,k2_tmap_1(sK3,sK1,sK4,sK3),sK5) ),
    inference(subsumption_resolution,[],[f961,f229])).

fof(f229,plain,(
    m1_subset_1(sK5,k2_struct_0(sK2)) ),
    inference(backward_demodulation,[],[f86,f227])).

fof(f227,plain,(
    u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(resolution,[],[f164,f62])).

fof(f164,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f99,f63])).

fof(f99,plain,(
    l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f97,f61])).

fof(f97,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2) ),
    inference(resolution,[],[f67,f55])).

fof(f55,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f86,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f43,f44])).

fof(f44,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f19])).

fof(f43,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f961,plain,
    ( ~ m1_subset_1(sK5,k2_struct_0(sK2))
    | r1_tmap_1(sK3,sK1,k2_tmap_1(sK3,sK1,sK4,sK3),sK5) ),
    inference(forward_demodulation,[],[f960,f227])).

fof(f960,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | r1_tmap_1(sK3,sK1,k2_tmap_1(sK3,sK1,sK4,sK3),sK5) ),
    inference(subsumption_resolution,[],[f959,f194])).

fof(f959,plain,
    ( ~ v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | r1_tmap_1(sK3,sK1,k2_tmap_1(sK3,sK1,sK4,sK3),sK5) ),
    inference(forward_demodulation,[],[f958,f93])).

fof(f958,plain,
    ( ~ v1_funct_2(sK4,k2_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | r1_tmap_1(sK3,sK1,k2_tmap_1(sK3,sK1,sK4,sK3),sK5) ),
    inference(subsumption_resolution,[],[f957,f195])).

fof(f957,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1))))
    | ~ v1_funct_2(sK4,k2_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | r1_tmap_1(sK3,sK1,k2_tmap_1(sK3,sK1,sK4,sK3),sK5) ),
    inference(forward_demodulation,[],[f956,f93])).

fof(f956,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,k2_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | r1_tmap_1(sK3,sK1,k2_tmap_1(sK3,sK1,sK4,sK3),sK5) ),
    inference(subsumption_resolution,[],[f955,f193])).

fof(f955,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,k2_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,k2_struct_0(sK3))
    | r1_tmap_1(sK3,sK1,k2_tmap_1(sK3,sK1,sK4,sK3),sK5) ),
    inference(subsumption_resolution,[],[f954,f266])).

fof(f266,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(resolution,[],[f135,f118])).

fof(f118,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | m1_pre_topc(X0,sK2) ) ),
    inference(subsumption_resolution,[],[f117,f99])).

fof(f117,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | ~ l1_pre_topc(sK2)
      | m1_pre_topc(X0,sK2) ) ),
    inference(superposition,[],[f69,f51])).

fof(f51,plain,(
    sK3 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | m1_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

fof(f954,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,k2_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK3,sK2)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,k2_struct_0(sK3))
    | r1_tmap_1(sK3,sK1,k2_tmap_1(sK3,sK1,sK4,sK3),sK5) ),
    inference(subsumption_resolution,[],[f953,f48])).

fof(f953,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,k2_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,k2_struct_0(sK3))
    | r1_tmap_1(sK3,sK1,k2_tmap_1(sK3,sK1,sK4,sK3),sK5) ),
    inference(subsumption_resolution,[],[f952,f306])).

fof(f306,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(forward_demodulation,[],[f305,f228])).

fof(f228,plain,(
    sK3 = g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(backward_demodulation,[],[f51,f227])).

fof(f305,plain,(
    m1_pre_topc(sK2,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(forward_demodulation,[],[f304,f227])).

fof(f304,plain,(
    m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(subsumption_resolution,[],[f303,f99])).

fof(f303,plain,
    ( ~ l1_pre_topc(sK2)
    | m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(duplicate_literal_removal,[],[f294])).

fof(f294,plain,
    ( ~ l1_pre_topc(sK2)
    | m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f163,f66])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f163,plain,(
    m1_pre_topc(sK2,sK2) ),
    inference(resolution,[],[f99,f64])).

fof(f952,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,k2_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,k2_struct_0(sK3))
    | r1_tmap_1(sK3,sK1,k2_tmap_1(sK3,sK1,sK4,sK3),sK5) ),
    inference(subsumption_resolution,[],[f951,f54])).

fof(f54,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f951,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,k2_struct_0(sK3),u1_struct_0(sK1))
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,k2_struct_0(sK3))
    | r1_tmap_1(sK3,sK1,k2_tmap_1(sK3,sK1,sK4,sK3),sK5) ),
    inference(subsumption_resolution,[],[f950,f58])).

fof(f950,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,k2_struct_0(sK3),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,k2_struct_0(sK3))
    | r1_tmap_1(sK3,sK1,k2_tmap_1(sK3,sK1,sK4,sK3),sK5) ),
    inference(subsumption_resolution,[],[f949,f57])).

fof(f949,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,k2_struct_0(sK3),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,k2_struct_0(sK3))
    | r1_tmap_1(sK3,sK1,k2_tmap_1(sK3,sK1,sK4,sK3),sK5) ),
    inference(subsumption_resolution,[],[f928,f56])).

fof(f928,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,k2_struct_0(sK3),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,k2_struct_0(sK3))
    | r1_tmap_1(sK3,sK1,k2_tmap_1(sK3,sK1,sK4,sK3),sK5) ),
    inference(resolution,[],[f926,f292])).

fof(f292,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_tmap_1(X5,X4,k2_tmap_1(sK3,X4,X6,X5),X7)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(X4))))
      | ~ v1_funct_2(X6,k2_struct_0(sK3),u1_struct_0(X4))
      | v2_struct_0(X4)
      | ~ v2_pre_topc(X4)
      | ~ l1_pre_topc(X4)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X5,sK3)
      | ~ v1_funct_1(X6)
      | ~ m1_pre_topc(sK3,X5)
      | ~ m1_subset_1(X7,u1_struct_0(X5))
      | ~ m1_subset_1(X7,k2_struct_0(sK3))
      | r1_tmap_1(sK3,X4,k2_tmap_1(sK3,X4,X6,sK3),X7) ) ),
    inference(forward_demodulation,[],[f291,f192])).

fof(f291,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(X4))))
      | ~ v1_funct_2(X6,k2_struct_0(sK3),u1_struct_0(X4))
      | v2_struct_0(X4)
      | ~ v2_pre_topc(X4)
      | ~ l1_pre_topc(X4)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X5,sK3)
      | ~ v1_funct_1(X6)
      | ~ m1_pre_topc(sK3,X5)
      | ~ m1_subset_1(X7,u1_struct_0(X5))
      | ~ m1_subset_1(X7,u1_struct_0(sK3))
      | ~ r1_tmap_1(X5,X4,k2_tmap_1(sK3,X4,X6,X5),X7)
      | r1_tmap_1(sK3,X4,k2_tmap_1(sK3,X4,X6,sK3),X7) ) ),
    inference(forward_demodulation,[],[f290,f192])).

fof(f290,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ v1_funct_2(X6,k2_struct_0(sK3),u1_struct_0(X4))
      | v2_struct_0(X4)
      | ~ v2_pre_topc(X4)
      | ~ l1_pre_topc(X4)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X5,sK3)
      | ~ v1_funct_1(X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4))))
      | ~ m1_pre_topc(sK3,X5)
      | ~ m1_subset_1(X7,u1_struct_0(X5))
      | ~ m1_subset_1(X7,u1_struct_0(sK3))
      | ~ r1_tmap_1(X5,X4,k2_tmap_1(sK3,X4,X6,X5),X7)
      | r1_tmap_1(sK3,X4,k2_tmap_1(sK3,X4,X6,sK3),X7) ) ),
    inference(forward_demodulation,[],[f289,f192])).

fof(f289,plain,(
    ! [X6,X4,X7,X5] :
      ( v2_struct_0(X4)
      | ~ v2_pre_topc(X4)
      | ~ l1_pre_topc(X4)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X5,sK3)
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,u1_struct_0(sK3),u1_struct_0(X4))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4))))
      | ~ m1_pre_topc(sK3,X5)
      | ~ m1_subset_1(X7,u1_struct_0(X5))
      | ~ m1_subset_1(X7,u1_struct_0(sK3))
      | ~ r1_tmap_1(X5,X4,k2_tmap_1(sK3,X4,X6,X5),X7)
      | r1_tmap_1(sK3,X4,k2_tmap_1(sK3,X4,X6,sK3),X7) ) ),
    inference(subsumption_resolution,[],[f288,f52])).

fof(f288,plain,(
    ! [X6,X4,X7,X5] :
      ( v2_struct_0(X4)
      | ~ v2_pre_topc(X4)
      | ~ l1_pre_topc(X4)
      | v2_struct_0(sK3)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X5,sK3)
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,u1_struct_0(sK3),u1_struct_0(X4))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4))))
      | ~ m1_pre_topc(sK3,X5)
      | ~ m1_subset_1(X7,u1_struct_0(X5))
      | ~ m1_subset_1(X7,u1_struct_0(sK3))
      | ~ r1_tmap_1(X5,X4,k2_tmap_1(sK3,X4,X6,X5),X7)
      | r1_tmap_1(sK3,X4,k2_tmap_1(sK3,X4,X6,sK3),X7) ) ),
    inference(subsumption_resolution,[],[f287,f98])).

fof(f287,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ l1_pre_topc(sK3)
      | v2_struct_0(X4)
      | ~ v2_pre_topc(X4)
      | ~ l1_pre_topc(X4)
      | v2_struct_0(sK3)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X5,sK3)
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,u1_struct_0(sK3),u1_struct_0(X4))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4))))
      | ~ m1_pre_topc(sK3,X5)
      | ~ m1_subset_1(X7,u1_struct_0(X5))
      | ~ m1_subset_1(X7,u1_struct_0(sK3))
      | ~ r1_tmap_1(X5,X4,k2_tmap_1(sK3,X4,X6,X5),X7)
      | r1_tmap_1(sK3,X4,k2_tmap_1(sK3,X4,X6,sK3),X7) ) ),
    inference(subsumption_resolution,[],[f274,f107])).

% (30195)Termination reason: Refutation not found, incomplete strategy
fof(f274,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ v2_pre_topc(sK3)
      | ~ l1_pre_topc(sK3)
      | v2_struct_0(X4)
      | ~ v2_pre_topc(X4)
      | ~ l1_pre_topc(X4)
      | v2_struct_0(sK3)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X5,sK3)
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,u1_struct_0(sK3),u1_struct_0(X4))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4))))
      | ~ m1_pre_topc(sK3,X5)
      | ~ m1_subset_1(X7,u1_struct_0(X5))
      | ~ m1_subset_1(X7,u1_struct_0(sK3))
      | ~ r1_tmap_1(X5,X4,k2_tmap_1(sK3,X4,X6,X5),X7)
      | r1_tmap_1(sK3,X4,k2_tmap_1(sK3,X4,X6,sK3),X7) ) ),
    inference(duplicate_literal_removal,[],[f273])).

% (30195)Memory used [KB]: 6780
% (30195)Time elapsed: 0.134 s
% (30195)------------------------------
% (30195)------------------------------
fof(f273,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ v2_pre_topc(sK3)
      | ~ l1_pre_topc(sK3)
      | v2_struct_0(X4)
      | ~ v2_pre_topc(X4)
      | ~ l1_pre_topc(X4)
      | v2_struct_0(sK3)
      | v2_struct_0(sK3)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X5,sK3)
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,u1_struct_0(sK3),u1_struct_0(X4))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4))))
      | ~ m1_pre_topc(sK3,X5)
      | ~ m1_subset_1(X7,u1_struct_0(X5))
      | ~ m1_subset_1(X7,u1_struct_0(sK3))
      | ~ r1_tmap_1(X5,X4,k2_tmap_1(sK3,X4,X6,X5),X7)
      | r1_tmap_1(sK3,X4,k2_tmap_1(sK3,X4,X6,sK3),X7) ) ),
    inference(resolution,[],[f135,f80])).

fof(f80,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( ~ m1_pre_topc(X2,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | v2_struct_0(X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X6)
      | r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
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
      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | X5 != X6
      | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5)
      | r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6)
                              | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5)
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6)
                              | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5)
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X2,X3)
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( ( r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5)
                                    & X5 = X6 )
                                 => r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_tmap_1)).

fof(f926,plain,(
    r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),sK5) ),
    inference(backward_demodulation,[],[f85,f925])).

fof(f925,plain,(
    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_tmap_1(sK3,sK1,sK4,sK2) ),
    inference(backward_demodulation,[],[f840,f924])).

fof(f924,plain,(
    k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,k2_struct_0(sK2)) = k2_tmap_1(sK3,sK1,sK4,sK2) ),
    inference(forward_demodulation,[],[f921,f227])).

fof(f921,plain,(
    k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,u1_struct_0(sK2)) = k2_tmap_1(sK3,sK1,sK4,sK2) ),
    inference(resolution,[],[f848,f306])).

fof(f848,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,u1_struct_0(X0)) = k2_tmap_1(sK3,sK1,sK4,X0) ) ),
    inference(subsumption_resolution,[],[f847,f194])).

fof(f847,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1))
      | ~ m1_pre_topc(X0,sK3)
      | k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,u1_struct_0(X0)) = k2_tmap_1(sK3,sK1,sK4,X0) ) ),
    inference(subsumption_resolution,[],[f846,f48])).

fof(f846,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK4)
      | ~ v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1))
      | ~ m1_pre_topc(X0,sK3)
      | k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,u1_struct_0(X0)) = k2_tmap_1(sK3,sK1,sK4,X0) ) ),
    inference(resolution,[],[f665,f195])).

fof(f665,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1))))
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,k2_struct_0(sK3),k2_struct_0(sK1))
      | ~ m1_pre_topc(X7,sK3)
      | k2_tmap_1(sK3,sK1,X6,X7) = k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),X6,u1_struct_0(X7)) ) ),
    inference(subsumption_resolution,[],[f664,f52])).

fof(f664,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1))))
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,k2_struct_0(sK3),k2_struct_0(sK1))
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(X7,sK3)
      | k2_tmap_1(sK3,sK1,X6,X7) = k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),X6,u1_struct_0(X7)) ) ),
    inference(subsumption_resolution,[],[f663,f98])).

fof(f663,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1))))
      | ~ l1_pre_topc(sK3)
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,k2_struct_0(sK3),k2_struct_0(sK1))
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(X7,sK3)
      | k2_tmap_1(sK3,sK1,X6,X7) = k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),X6,u1_struct_0(X7)) ) ),
    inference(subsumption_resolution,[],[f656,f107])).

fof(f656,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1))))
      | ~ v2_pre_topc(sK3)
      | ~ l1_pre_topc(sK3)
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,k2_struct_0(sK3),k2_struct_0(sK1))
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(X7,sK3)
      | k2_tmap_1(sK3,sK1,X6,X7) = k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),X6,u1_struct_0(X7)) ) ),
    inference(superposition,[],[f337,f192])).

fof(f337,plain,(
    ! [X6,X7,X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),k2_struct_0(sK1))))
      | ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(X6),k2_struct_0(sK1))
      | v2_struct_0(X6)
      | ~ m1_pre_topc(X7,X6)
      | k2_tmap_1(X6,sK1,X5,X7) = k2_partfun1(u1_struct_0(X6),k2_struct_0(sK1),X5,u1_struct_0(X7)) ) ),
    inference(subsumption_resolution,[],[f336,f58])).

fof(f336,plain,(
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
    inference(subsumption_resolution,[],[f335,f57])).

fof(f335,plain,(
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
    inference(subsumption_resolution,[],[f324,f56])).

fof(f324,plain,(
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
    inference(superposition,[],[f72,f93])).

fof(f72,plain,(
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
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f840,plain,(
    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,k2_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f838,f227])).

fof(f838,plain,(
    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,u1_struct_0(sK2)) ),
    inference(resolution,[],[f631,f306])).

fof(f631,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | k3_tmap_1(sK0,sK1,sK3,X0,sK4) = k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f630,f48])).

fof(f630,plain,(
    ! [X0] :
      ( k3_tmap_1(sK0,sK1,sK3,X0,sK4) = k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,u1_struct_0(X0))
      | ~ v1_funct_1(sK4)
      | ~ m1_pre_topc(X0,sK3) ) ),
    inference(subsumption_resolution,[],[f629,f194])).

fof(f629,plain,(
    ! [X0] :
      ( k3_tmap_1(sK0,sK1,sK3,X0,sK4) = k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,u1_struct_0(X0))
      | ~ v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1))
      | ~ v1_funct_1(sK4)
      | ~ m1_pre_topc(X0,sK3) ) ),
    inference(resolution,[],[f346,f195])).

fof(f346,plain,(
    ! [X17,X18] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1))))
      | k3_tmap_1(sK0,sK1,sK3,X18,X17) = k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),X17,u1_struct_0(X18))
      | ~ v1_funct_2(X17,k2_struct_0(sK3),k2_struct_0(sK1))
      | ~ v1_funct_1(X17)
      | ~ m1_pre_topc(X18,sK3) ) ),
    inference(subsumption_resolution,[],[f345,f58])).

fof(f345,plain,(
    ! [X17,X18] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1))))
      | k3_tmap_1(sK0,sK1,sK3,X18,X17) = k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),X17,u1_struct_0(X18))
      | ~ v1_funct_2(X17,k2_struct_0(sK3),k2_struct_0(sK1))
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(X17)
      | ~ m1_pre_topc(X18,sK3) ) ),
    inference(subsumption_resolution,[],[f344,f57])).

fof(f344,plain,(
    ! [X17,X18] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1))))
      | k3_tmap_1(sK0,sK1,sK3,X18,X17) = k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),X17,u1_struct_0(X18))
      | ~ v1_funct_2(X17,k2_struct_0(sK3),k2_struct_0(sK1))
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(X17)
      | ~ m1_pre_topc(X18,sK3) ) ),
    inference(subsumption_resolution,[],[f328,f56])).

fof(f328,plain,(
    ! [X17,X18] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1))))
      | k3_tmap_1(sK0,sK1,sK3,X18,X17) = k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),X17,u1_struct_0(X18))
      | ~ v1_funct_2(X17,k2_struct_0(sK3),k2_struct_0(sK1))
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(X17)
      | ~ m1_pre_topc(X18,sK3) ) ),
    inference(superposition,[],[f200,f93])).

fof(f200,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(X0))))
      | k3_tmap_1(sK0,X0,sK3,X1,X2) = k2_partfun1(k2_struct_0(sK3),u1_struct_0(X0),X2,u1_struct_0(X1))
      | ~ v1_funct_2(X2,k2_struct_0(sK3),u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,sK3) ) ),
    inference(forward_demodulation,[],[f199,f192])).

fof(f199,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,k2_struct_0(sK3),u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,sK3)
      | k3_tmap_1(sK0,X0,sK3,X1,X2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X0),X2,u1_struct_0(X1)) ) ),
    inference(forward_demodulation,[],[f197,f192])).

fof(f197,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,k2_struct_0(sK3),u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
      | ~ m1_pre_topc(X1,sK3)
      | k3_tmap_1(sK0,X0,sK3,X1,X2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X0),X2,u1_struct_0(X1)) ) ),
    inference(backward_demodulation,[],[f143,f192])).

fof(f143,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
      | ~ m1_pre_topc(X1,sK3)
      | k3_tmap_1(sK0,X0,sK3,X1,X2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X0),X2,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f142,f122])).

fof(f122,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | m1_pre_topc(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f121,f60])).

fof(f121,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(X0,sK3)
      | m1_pre_topc(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f119,f61])).

fof(f119,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(X0,sK3)
      | m1_pre_topc(X0,sK0) ) ),
    inference(resolution,[],[f77,f53])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X2,X1)
      | m1_pre_topc(X2,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
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
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f142,plain,(
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
    inference(subsumption_resolution,[],[f141,f59])).

fof(f59,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f141,plain,(
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
    inference(subsumption_resolution,[],[f140,f61])).

fof(f140,plain,(
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
    inference(subsumption_resolution,[],[f138,f60])).

fof(f138,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).

fof(f85,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(backward_demodulation,[],[f45,f44])).

fof(f45,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f19])).
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
% 0.14/0.35  % DateTime   : Tue Dec  1 19:27:06 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.50  % (30210)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.50  % (30214)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.50  % (30200)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (30199)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.51  % (30201)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.51  % (30208)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.51  % (30204)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.51  % (30215)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.51  % (30203)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.51  % (30198)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.51  % (30197)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.52  % (30207)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (30209)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.52  % (30213)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.52  % (30212)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.52  % (30205)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.52  % (30211)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.52  % (30195)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.53  % (30206)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.53  % (30202)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.53  % (30196)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.57  % (30195)Refutation not found, incomplete strategy% (30195)------------------------------
% 0.22/0.57  % (30195)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (30212)Refutation found. Thanks to Tanya!
% 0.22/0.57  % SZS status Theorem for theBenchmark
% 0.22/0.57  % SZS output start Proof for theBenchmark
% 0.22/0.57  fof(f984,plain,(
% 0.22/0.57    $false),
% 0.22/0.57    inference(subsumption_resolution,[],[f983,f193])).
% 0.22/0.57  fof(f193,plain,(
% 0.22/0.57    m1_subset_1(sK5,k2_struct_0(sK3))),
% 0.22/0.57    inference(backward_demodulation,[],[f47,f192])).
% 0.22/0.57  fof(f192,plain,(
% 0.22/0.57    u1_struct_0(sK3) = k2_struct_0(sK3)),
% 0.22/0.57    inference(resolution,[],[f136,f62])).
% 0.22/0.57  fof(f62,plain,(
% 0.22/0.57    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f20])).
% 0.22/0.57  fof(f20,plain,(
% 0.22/0.57    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.57    inference(ennf_transformation,[],[f2])).
% 0.22/0.57  fof(f2,axiom,(
% 0.22/0.57    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.57  fof(f136,plain,(
% 0.22/0.57    l1_struct_0(sK3)),
% 0.22/0.57    inference(resolution,[],[f98,f63])).
% 0.22/0.57  fof(f63,plain,(
% 0.22/0.57    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f21])).
% 0.22/0.57  fof(f21,plain,(
% 0.22/0.57    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.57    inference(ennf_transformation,[],[f3])).
% 0.22/0.57  fof(f3,axiom,(
% 0.22/0.57    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.57  fof(f98,plain,(
% 0.22/0.57    l1_pre_topc(sK3)),
% 0.22/0.57    inference(subsumption_resolution,[],[f96,f61])).
% 0.22/0.57  fof(f61,plain,(
% 0.22/0.57    l1_pre_topc(sK0)),
% 0.22/0.57    inference(cnf_transformation,[],[f19])).
% 0.22/0.57  fof(f19,plain,(
% 0.22/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.57    inference(flattening,[],[f18])).
% 0.22/0.57  fof(f18,plain,(
% 0.22/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f17])).
% 0.22/0.57  fof(f17,negated_conjecture,(
% 0.22/0.57    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 0.22/0.57    inference(negated_conjecture,[],[f16])).
% 0.22/0.57  fof(f16,conjecture,(
% 0.22/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tmap_1)).
% 0.22/0.57  fof(f96,plain,(
% 0.22/0.57    ~l1_pre_topc(sK0) | l1_pre_topc(sK3)),
% 0.22/0.57    inference(resolution,[],[f67,f53])).
% 0.22/0.57  fof(f53,plain,(
% 0.22/0.57    m1_pre_topc(sK3,sK0)),
% 0.22/0.57    inference(cnf_transformation,[],[f19])).
% 0.22/0.57  fof(f67,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f24])).
% 0.22/0.57  fof(f24,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.57    inference(ennf_transformation,[],[f4])).
% 0.22/0.57  fof(f4,axiom,(
% 0.22/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.22/0.57  fof(f47,plain,(
% 0.22/0.57    m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.22/0.57    inference(cnf_transformation,[],[f19])).
% 0.22/0.57  fof(f983,plain,(
% 0.22/0.57    ~m1_subset_1(sK5,k2_struct_0(sK3))),
% 0.22/0.57    inference(forward_demodulation,[],[f982,f192])).
% 0.22/0.57  fof(f982,plain,(
% 0.22/0.57    ~m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.22/0.57    inference(subsumption_resolution,[],[f981,f195])).
% 0.22/0.57  fof(f195,plain,(
% 0.22/0.57    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1))))),
% 0.22/0.57    inference(backward_demodulation,[],[f95,f192])).
% 0.22/0.57  fof(f95,plain,(
% 0.22/0.57    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1))))),
% 0.22/0.57    inference(backward_demodulation,[],[f50,f93])).
% 0.22/0.57  fof(f93,plain,(
% 0.22/0.57    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.22/0.57    inference(resolution,[],[f62,f89])).
% 0.22/0.57  fof(f89,plain,(
% 0.22/0.57    l1_struct_0(sK1)),
% 0.22/0.57    inference(resolution,[],[f63,f58])).
% 0.22/0.57  fof(f58,plain,(
% 0.22/0.57    l1_pre_topc(sK1)),
% 0.22/0.57    inference(cnf_transformation,[],[f19])).
% 0.22/0.57  fof(f50,plain,(
% 0.22/0.57    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.22/0.57    inference(cnf_transformation,[],[f19])).
% 0.22/0.57  fof(f981,plain,(
% 0.22/0.57    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1)))) | ~m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.22/0.57    inference(forward_demodulation,[],[f980,f192])).
% 0.22/0.57  fof(f980,plain,(
% 0.22/0.57    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1)))) | ~m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.22/0.57    inference(forward_demodulation,[],[f979,f93])).
% 0.22/0.57  fof(f979,plain,(
% 0.22/0.57    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.22/0.57    inference(subsumption_resolution,[],[f978,f194])).
% 0.22/0.57  fof(f194,plain,(
% 0.22/0.57    v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1))),
% 0.22/0.57    inference(backward_demodulation,[],[f94,f192])).
% 0.22/0.57  fof(f94,plain,(
% 0.22/0.57    v1_funct_2(sK4,u1_struct_0(sK3),k2_struct_0(sK1))),
% 0.22/0.57    inference(backward_demodulation,[],[f49,f93])).
% 0.22/0.57  fof(f49,plain,(
% 0.22/0.57    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.22/0.57    inference(cnf_transformation,[],[f19])).
% 0.22/0.57  fof(f978,plain,(
% 0.22/0.57    ~v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.22/0.57    inference(forward_demodulation,[],[f977,f192])).
% 0.22/0.57  fof(f977,plain,(
% 0.22/0.57    ~v1_funct_2(sK4,u1_struct_0(sK3),k2_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.22/0.57    inference(forward_demodulation,[],[f976,f93])).
% 0.22/0.57  fof(f976,plain,(
% 0.22/0.57    ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.22/0.57    inference(subsumption_resolution,[],[f975,f46])).
% 0.22/0.57  fof(f46,plain,(
% 0.22/0.57    ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.22/0.57    inference(cnf_transformation,[],[f19])).
% 0.22/0.57  fof(f975,plain,(
% 0.22/0.57    ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.22/0.57    inference(subsumption_resolution,[],[f974,f56])).
% 0.22/0.57  fof(f56,plain,(
% 0.22/0.57    ~v2_struct_0(sK1)),
% 0.22/0.57    inference(cnf_transformation,[],[f19])).
% 0.22/0.57  fof(f974,plain,(
% 0.22/0.57    ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.22/0.57    inference(subsumption_resolution,[],[f973,f135])).
% 0.22/0.57  fof(f135,plain,(
% 0.22/0.57    m1_pre_topc(sK3,sK3)),
% 0.22/0.57    inference(resolution,[],[f98,f64])).
% 0.22/0.57  fof(f64,plain,(
% 0.22/0.57    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f22])).
% 0.22/0.57  fof(f22,plain,(
% 0.22/0.57    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.22/0.57    inference(ennf_transformation,[],[f12])).
% 0.22/0.57  fof(f12,axiom,(
% 0.22/0.57    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.22/0.57  fof(f973,plain,(
% 0.22/0.57    ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK3,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.22/0.57    inference(subsumption_resolution,[],[f972,f832])).
% 0.22/0.57  fof(f832,plain,(
% 0.22/0.57    v1_tsep_1(sK3,sK3)),
% 0.22/0.57    inference(subsumption_resolution,[],[f831,f107])).
% 0.22/0.57  fof(f107,plain,(
% 0.22/0.57    v2_pre_topc(sK3)),
% 0.22/0.57    inference(subsumption_resolution,[],[f106,f60])).
% 0.22/0.57  fof(f60,plain,(
% 0.22/0.57    v2_pre_topc(sK0)),
% 0.22/0.57    inference(cnf_transformation,[],[f19])).
% 0.22/0.57  fof(f106,plain,(
% 0.22/0.57    ~v2_pre_topc(sK0) | v2_pre_topc(sK3)),
% 0.22/0.57    inference(subsumption_resolution,[],[f104,f61])).
% 0.22/0.57  fof(f104,plain,(
% 0.22/0.57    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_pre_topc(sK3)),
% 0.22/0.57    inference(resolution,[],[f76,f53])).
% 0.22/0.57  fof(f76,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_pre_topc(X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f38])).
% 0.22/0.57  fof(f38,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.57    inference(flattening,[],[f37])).
% 0.22/0.57  fof(f37,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f1])).
% 0.22/0.57  fof(f1,axiom,(
% 0.22/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.22/0.57  fof(f831,plain,(
% 0.22/0.57    ~v2_pre_topc(sK3) | v1_tsep_1(sK3,sK3)),
% 0.22/0.57    inference(subsumption_resolution,[],[f830,f135])).
% 0.22/0.57  fof(f830,plain,(
% 0.22/0.57    ~m1_pre_topc(sK3,sK3) | ~v2_pre_topc(sK3) | v1_tsep_1(sK3,sK3)),
% 0.22/0.57    inference(subsumption_resolution,[],[f829,f98])).
% 0.22/0.57  fof(f829,plain,(
% 0.22/0.57    ~l1_pre_topc(sK3) | ~m1_pre_topc(sK3,sK3) | ~v2_pre_topc(sK3) | v1_tsep_1(sK3,sK3)),
% 0.22/0.57    inference(resolution,[],[f499,f137])).
% 0.22/0.57  fof(f137,plain,(
% 0.22/0.57    v3_pre_topc(k2_struct_0(sK3),sK3)),
% 0.22/0.57    inference(subsumption_resolution,[],[f134,f107])).
% 0.22/0.57  fof(f134,plain,(
% 0.22/0.57    ~v2_pre_topc(sK3) | v3_pre_topc(k2_struct_0(sK3),sK3)),
% 0.22/0.57    inference(resolution,[],[f98,f75])).
% 0.22/0.57  fof(f75,plain,(
% 0.22/0.57    ( ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v3_pre_topc(k2_struct_0(X0),X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f36])).
% 0.22/0.57  fof(f36,plain,(
% 0.22/0.57    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.57    inference(flattening,[],[f35])).
% 0.22/0.57  fof(f35,plain,(
% 0.22/0.57    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f7])).
% 0.22/0.57  fof(f7,axiom,(
% 0.22/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).
% 0.22/0.57  fof(f499,plain,(
% 0.22/0.57    ( ! [X16] : (~v3_pre_topc(k2_struct_0(sK3),X16) | ~l1_pre_topc(X16) | ~m1_pre_topc(sK3,X16) | ~v2_pre_topc(X16) | v1_tsep_1(sK3,X16)) )),
% 0.22/0.57    inference(superposition,[],[f87,f192])).
% 0.22/0.57  fof(f87,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~v3_pre_topc(u1_struct_0(X1),X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | v1_tsep_1(X1,X0)) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f83,f68])).
% 0.22/0.57  fof(f68,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f25])).
% 0.22/0.57  fof(f25,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.57    inference(ennf_transformation,[],[f11])).
% 0.22/0.57  fof(f11,axiom,(
% 0.22/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.22/0.57  fof(f83,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(u1_struct_0(X1),X0) | v1_tsep_1(X1,X0)) )),
% 0.22/0.57    inference(equality_resolution,[],[f79])).
% 0.22/0.57  fof(f79,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | ~v3_pre_topc(X2,X0) | v1_tsep_1(X1,X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f42])).
% 0.22/0.57  fof(f42,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.57    inference(flattening,[],[f41])).
% 0.22/0.57  fof(f41,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f10])).
% 0.22/0.57  fof(f10,axiom,(
% 0.22/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).
% 0.22/0.57  fof(f972,plain,(
% 0.22/0.57    ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_tsep_1(sK3,sK3) | ~m1_pre_topc(sK3,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.22/0.57    inference(subsumption_resolution,[],[f971,f48])).
% 0.22/0.57  fof(f48,plain,(
% 0.22/0.57    v1_funct_1(sK4)),
% 0.22/0.57    inference(cnf_transformation,[],[f19])).
% 0.22/0.57  fof(f971,plain,(
% 0.22/0.57    ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_tsep_1(sK3,sK3) | ~m1_pre_topc(sK3,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.22/0.57    inference(subsumption_resolution,[],[f970,f98])).
% 0.22/0.57  fof(f970,plain,(
% 0.22/0.57    ~l1_pre_topc(sK3) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_tsep_1(sK3,sK3) | ~m1_pre_topc(sK3,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.22/0.57    inference(subsumption_resolution,[],[f969,f107])).
% 0.22/0.57  fof(f969,plain,(
% 0.22/0.57    ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_tsep_1(sK3,sK3) | ~m1_pre_topc(sK3,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.22/0.57    inference(subsumption_resolution,[],[f968,f52])).
% 0.22/0.57  fof(f52,plain,(
% 0.22/0.57    ~v2_struct_0(sK3)),
% 0.22/0.57    inference(cnf_transformation,[],[f19])).
% 0.22/0.57  fof(f968,plain,(
% 0.22/0.57    v2_struct_0(sK3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_tsep_1(sK3,sK3) | ~m1_pre_topc(sK3,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.22/0.57    inference(subsumption_resolution,[],[f967,f58])).
% 0.22/0.57  fof(f967,plain,(
% 0.22/0.57    ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_tsep_1(sK3,sK3) | ~m1_pre_topc(sK3,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.22/0.57    inference(subsumption_resolution,[],[f966,f57])).
% 0.22/0.57  fof(f57,plain,(
% 0.22/0.57    v2_pre_topc(sK1)),
% 0.22/0.57    inference(cnf_transformation,[],[f19])).
% 0.22/0.57  fof(f966,plain,(
% 0.22/0.57    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_tsep_1(sK3,sK3) | ~m1_pre_topc(sK3,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.22/0.57    inference(duplicate_literal_removal,[],[f963])).
% 0.22/0.57  fof(f963,plain,(
% 0.22/0.57    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | v2_struct_0(sK3) | ~v1_tsep_1(sK3,sK3) | ~m1_pre_topc(sK3,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.22/0.57    inference(resolution,[],[f962,f82])).
% 0.22/0.57  fof(f82,plain,(
% 0.22/0.57    ( ! [X2,X0,X5,X3,X1] : (~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~v1_tsep_1(X3,X1) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X3)) | v2_struct_0(X0) | r1_tmap_1(X1,X0,X2,X5)) )),
% 0.22/0.57    inference(equality_resolution,[],[f73])).
% 0.22/0.57  fof(f73,plain,(
% 0.22/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~v1_tsep_1(X3,X1) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X3)) | X4 != X5 | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f34])).
% 0.22/0.57  fof(f34,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.57    inference(flattening,[],[f33])).
% 0.22/0.57  fof(f33,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (((r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) | X4 != X5) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f13])).
% 0.22/0.57  fof(f13,axiom,(
% 0.22/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_tmap_1)).
% 0.22/0.57  fof(f962,plain,(
% 0.22/0.57    r1_tmap_1(sK3,sK1,k2_tmap_1(sK3,sK1,sK4,sK3),sK5)),
% 0.22/0.57    inference(subsumption_resolution,[],[f961,f229])).
% 0.22/0.57  fof(f229,plain,(
% 0.22/0.57    m1_subset_1(sK5,k2_struct_0(sK2))),
% 0.22/0.57    inference(backward_demodulation,[],[f86,f227])).
% 0.22/0.57  fof(f227,plain,(
% 0.22/0.57    u1_struct_0(sK2) = k2_struct_0(sK2)),
% 0.22/0.57    inference(resolution,[],[f164,f62])).
% 0.22/0.57  fof(f164,plain,(
% 0.22/0.57    l1_struct_0(sK2)),
% 0.22/0.57    inference(resolution,[],[f99,f63])).
% 0.22/0.57  fof(f99,plain,(
% 0.22/0.57    l1_pre_topc(sK2)),
% 0.22/0.57    inference(subsumption_resolution,[],[f97,f61])).
% 0.22/0.57  fof(f97,plain,(
% 0.22/0.57    ~l1_pre_topc(sK0) | l1_pre_topc(sK2)),
% 0.22/0.57    inference(resolution,[],[f67,f55])).
% 0.22/0.57  fof(f55,plain,(
% 0.22/0.57    m1_pre_topc(sK2,sK0)),
% 0.22/0.57    inference(cnf_transformation,[],[f19])).
% 0.22/0.57  fof(f86,plain,(
% 0.22/0.57    m1_subset_1(sK5,u1_struct_0(sK2))),
% 0.22/0.57    inference(forward_demodulation,[],[f43,f44])).
% 0.22/0.57  fof(f44,plain,(
% 0.22/0.57    sK5 = sK6),
% 0.22/0.57    inference(cnf_transformation,[],[f19])).
% 0.22/0.57  fof(f43,plain,(
% 0.22/0.57    m1_subset_1(sK6,u1_struct_0(sK2))),
% 0.22/0.57    inference(cnf_transformation,[],[f19])).
% 0.22/0.57  fof(f961,plain,(
% 0.22/0.57    ~m1_subset_1(sK5,k2_struct_0(sK2)) | r1_tmap_1(sK3,sK1,k2_tmap_1(sK3,sK1,sK4,sK3),sK5)),
% 0.22/0.57    inference(forward_demodulation,[],[f960,f227])).
% 0.22/0.57  fof(f960,plain,(
% 0.22/0.57    ~m1_subset_1(sK5,u1_struct_0(sK2)) | r1_tmap_1(sK3,sK1,k2_tmap_1(sK3,sK1,sK4,sK3),sK5)),
% 0.22/0.57    inference(subsumption_resolution,[],[f959,f194])).
% 0.22/0.57  fof(f959,plain,(
% 0.22/0.57    ~v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | r1_tmap_1(sK3,sK1,k2_tmap_1(sK3,sK1,sK4,sK3),sK5)),
% 0.22/0.57    inference(forward_demodulation,[],[f958,f93])).
% 0.22/0.57  fof(f958,plain,(
% 0.22/0.57    ~v1_funct_2(sK4,k2_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | r1_tmap_1(sK3,sK1,k2_tmap_1(sK3,sK1,sK4,sK3),sK5)),
% 0.22/0.57    inference(subsumption_resolution,[],[f957,f195])).
% 0.22/0.57  fof(f957,plain,(
% 0.22/0.57    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1)))) | ~v1_funct_2(sK4,k2_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | r1_tmap_1(sK3,sK1,k2_tmap_1(sK3,sK1,sK4,sK3),sK5)),
% 0.22/0.57    inference(forward_demodulation,[],[f956,f93])).
% 0.22/0.57  fof(f956,plain,(
% 0.22/0.57    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,k2_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | r1_tmap_1(sK3,sK1,k2_tmap_1(sK3,sK1,sK4,sK3),sK5)),
% 0.22/0.57    inference(subsumption_resolution,[],[f955,f193])).
% 0.22/0.57  fof(f955,plain,(
% 0.22/0.57    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,k2_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_subset_1(sK5,k2_struct_0(sK3)) | r1_tmap_1(sK3,sK1,k2_tmap_1(sK3,sK1,sK4,sK3),sK5)),
% 0.22/0.57    inference(subsumption_resolution,[],[f954,f266])).
% 0.22/0.57  fof(f266,plain,(
% 0.22/0.57    m1_pre_topc(sK3,sK2)),
% 0.22/0.57    inference(resolution,[],[f135,f118])).
% 0.22/0.57  fof(f118,plain,(
% 0.22/0.57    ( ! [X0] : (~m1_pre_topc(X0,sK3) | m1_pre_topc(X0,sK2)) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f117,f99])).
% 0.22/0.57  fof(f117,plain,(
% 0.22/0.57    ( ! [X0] : (~m1_pre_topc(X0,sK3) | ~l1_pre_topc(sK2) | m1_pre_topc(X0,sK2)) )),
% 0.22/0.57    inference(superposition,[],[f69,f51])).
% 0.22/0.57  fof(f51,plain,(
% 0.22/0.57    sK3 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 0.22/0.57    inference(cnf_transformation,[],[f19])).
% 0.22/0.57  fof(f69,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | m1_pre_topc(X1,X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f26])).
% 0.22/0.57  fof(f26,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.57    inference(ennf_transformation,[],[f5])).
% 0.22/0.57  fof(f5,axiom,(
% 0.22/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).
% 0.22/0.57  fof(f954,plain,(
% 0.22/0.57    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,k2_struct_0(sK3),u1_struct_0(sK1)) | ~m1_pre_topc(sK3,sK2) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_subset_1(sK5,k2_struct_0(sK3)) | r1_tmap_1(sK3,sK1,k2_tmap_1(sK3,sK1,sK4,sK3),sK5)),
% 0.22/0.57    inference(subsumption_resolution,[],[f953,f48])).
% 0.22/0.57  fof(f953,plain,(
% 0.22/0.57    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,k2_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK2) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_subset_1(sK5,k2_struct_0(sK3)) | r1_tmap_1(sK3,sK1,k2_tmap_1(sK3,sK1,sK4,sK3),sK5)),
% 0.22/0.57    inference(subsumption_resolution,[],[f952,f306])).
% 0.22/0.57  fof(f306,plain,(
% 0.22/0.57    m1_pre_topc(sK2,sK3)),
% 0.22/0.57    inference(forward_demodulation,[],[f305,f228])).
% 0.22/0.57  fof(f228,plain,(
% 0.22/0.57    sK3 = g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))),
% 0.22/0.57    inference(backward_demodulation,[],[f51,f227])).
% 0.22/0.57  fof(f305,plain,(
% 0.22/0.57    m1_pre_topc(sK2,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)))),
% 0.22/0.57    inference(forward_demodulation,[],[f304,f227])).
% 0.22/0.57  fof(f304,plain,(
% 0.22/0.57    m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),
% 0.22/0.57    inference(subsumption_resolution,[],[f303,f99])).
% 0.22/0.57  fof(f303,plain,(
% 0.22/0.57    ~l1_pre_topc(sK2) | m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),
% 0.22/0.57    inference(duplicate_literal_removal,[],[f294])).
% 0.22/0.57  fof(f294,plain,(
% 0.22/0.57    ~l1_pre_topc(sK2) | m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~l1_pre_topc(sK2)),
% 0.22/0.57    inference(resolution,[],[f163,f66])).
% 0.22/0.57  fof(f66,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f23])).
% 0.22/0.57  fof(f23,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.57    inference(ennf_transformation,[],[f6])).
% 0.22/0.57  fof(f6,axiom,(
% 0.22/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).
% 0.22/0.57  fof(f163,plain,(
% 0.22/0.57    m1_pre_topc(sK2,sK2)),
% 0.22/0.57    inference(resolution,[],[f99,f64])).
% 0.22/0.57  fof(f952,plain,(
% 0.22/0.57    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,k2_struct_0(sK3),u1_struct_0(sK1)) | ~m1_pre_topc(sK2,sK3) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK2) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_subset_1(sK5,k2_struct_0(sK3)) | r1_tmap_1(sK3,sK1,k2_tmap_1(sK3,sK1,sK4,sK3),sK5)),
% 0.22/0.57    inference(subsumption_resolution,[],[f951,f54])).
% 0.22/0.57  fof(f54,plain,(
% 0.22/0.57    ~v2_struct_0(sK2)),
% 0.22/0.57    inference(cnf_transformation,[],[f19])).
% 0.22/0.57  fof(f951,plain,(
% 0.22/0.57    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,k2_struct_0(sK3),u1_struct_0(sK1)) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK3) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK2) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_subset_1(sK5,k2_struct_0(sK3)) | r1_tmap_1(sK3,sK1,k2_tmap_1(sK3,sK1,sK4,sK3),sK5)),
% 0.22/0.57    inference(subsumption_resolution,[],[f950,f58])).
% 0.22/0.57  fof(f950,plain,(
% 0.22/0.57    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,k2_struct_0(sK3),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK3) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK2) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_subset_1(sK5,k2_struct_0(sK3)) | r1_tmap_1(sK3,sK1,k2_tmap_1(sK3,sK1,sK4,sK3),sK5)),
% 0.22/0.57    inference(subsumption_resolution,[],[f949,f57])).
% 0.22/0.57  fof(f949,plain,(
% 0.22/0.57    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,k2_struct_0(sK3),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK3) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK2) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_subset_1(sK5,k2_struct_0(sK3)) | r1_tmap_1(sK3,sK1,k2_tmap_1(sK3,sK1,sK4,sK3),sK5)),
% 0.22/0.57    inference(subsumption_resolution,[],[f928,f56])).
% 0.22/0.57  fof(f928,plain,(
% 0.22/0.57    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,k2_struct_0(sK3),u1_struct_0(sK1)) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK3) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK2) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_subset_1(sK5,k2_struct_0(sK3)) | r1_tmap_1(sK3,sK1,k2_tmap_1(sK3,sK1,sK4,sK3),sK5)),
% 0.22/0.57    inference(resolution,[],[f926,f292])).
% 0.22/0.58  fof(f292,plain,(
% 0.22/0.58    ( ! [X6,X4,X7,X5] : (~r1_tmap_1(X5,X4,k2_tmap_1(sK3,X4,X6,X5),X7) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(X4)))) | ~v1_funct_2(X6,k2_struct_0(sK3),u1_struct_0(X4)) | v2_struct_0(X4) | ~v2_pre_topc(X4) | ~l1_pre_topc(X4) | v2_struct_0(X5) | ~m1_pre_topc(X5,sK3) | ~v1_funct_1(X6) | ~m1_pre_topc(sK3,X5) | ~m1_subset_1(X7,u1_struct_0(X5)) | ~m1_subset_1(X7,k2_struct_0(sK3)) | r1_tmap_1(sK3,X4,k2_tmap_1(sK3,X4,X6,sK3),X7)) )),
% 0.22/0.58    inference(forward_demodulation,[],[f291,f192])).
% 0.22/0.58  fof(f291,plain,(
% 0.22/0.58    ( ! [X6,X4,X7,X5] : (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(X4)))) | ~v1_funct_2(X6,k2_struct_0(sK3),u1_struct_0(X4)) | v2_struct_0(X4) | ~v2_pre_topc(X4) | ~l1_pre_topc(X4) | v2_struct_0(X5) | ~m1_pre_topc(X5,sK3) | ~v1_funct_1(X6) | ~m1_pre_topc(sK3,X5) | ~m1_subset_1(X7,u1_struct_0(X5)) | ~m1_subset_1(X7,u1_struct_0(sK3)) | ~r1_tmap_1(X5,X4,k2_tmap_1(sK3,X4,X6,X5),X7) | r1_tmap_1(sK3,X4,k2_tmap_1(sK3,X4,X6,sK3),X7)) )),
% 0.22/0.58    inference(forward_demodulation,[],[f290,f192])).
% 0.22/0.58  fof(f290,plain,(
% 0.22/0.58    ( ! [X6,X4,X7,X5] : (~v1_funct_2(X6,k2_struct_0(sK3),u1_struct_0(X4)) | v2_struct_0(X4) | ~v2_pre_topc(X4) | ~l1_pre_topc(X4) | v2_struct_0(X5) | ~m1_pre_topc(X5,sK3) | ~v1_funct_1(X6) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4)))) | ~m1_pre_topc(sK3,X5) | ~m1_subset_1(X7,u1_struct_0(X5)) | ~m1_subset_1(X7,u1_struct_0(sK3)) | ~r1_tmap_1(X5,X4,k2_tmap_1(sK3,X4,X6,X5),X7) | r1_tmap_1(sK3,X4,k2_tmap_1(sK3,X4,X6,sK3),X7)) )),
% 0.22/0.58    inference(forward_demodulation,[],[f289,f192])).
% 0.22/0.58  fof(f289,plain,(
% 0.22/0.58    ( ! [X6,X4,X7,X5] : (v2_struct_0(X4) | ~v2_pre_topc(X4) | ~l1_pre_topc(X4) | v2_struct_0(X5) | ~m1_pre_topc(X5,sK3) | ~v1_funct_1(X6) | ~v1_funct_2(X6,u1_struct_0(sK3),u1_struct_0(X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4)))) | ~m1_pre_topc(sK3,X5) | ~m1_subset_1(X7,u1_struct_0(X5)) | ~m1_subset_1(X7,u1_struct_0(sK3)) | ~r1_tmap_1(X5,X4,k2_tmap_1(sK3,X4,X6,X5),X7) | r1_tmap_1(sK3,X4,k2_tmap_1(sK3,X4,X6,sK3),X7)) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f288,f52])).
% 0.22/0.58  fof(f288,plain,(
% 0.22/0.58    ( ! [X6,X4,X7,X5] : (v2_struct_0(X4) | ~v2_pre_topc(X4) | ~l1_pre_topc(X4) | v2_struct_0(sK3) | v2_struct_0(X5) | ~m1_pre_topc(X5,sK3) | ~v1_funct_1(X6) | ~v1_funct_2(X6,u1_struct_0(sK3),u1_struct_0(X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4)))) | ~m1_pre_topc(sK3,X5) | ~m1_subset_1(X7,u1_struct_0(X5)) | ~m1_subset_1(X7,u1_struct_0(sK3)) | ~r1_tmap_1(X5,X4,k2_tmap_1(sK3,X4,X6,X5),X7) | r1_tmap_1(sK3,X4,k2_tmap_1(sK3,X4,X6,sK3),X7)) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f287,f98])).
% 0.22/0.58  fof(f287,plain,(
% 0.22/0.58    ( ! [X6,X4,X7,X5] : (~l1_pre_topc(sK3) | v2_struct_0(X4) | ~v2_pre_topc(X4) | ~l1_pre_topc(X4) | v2_struct_0(sK3) | v2_struct_0(X5) | ~m1_pre_topc(X5,sK3) | ~v1_funct_1(X6) | ~v1_funct_2(X6,u1_struct_0(sK3),u1_struct_0(X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4)))) | ~m1_pre_topc(sK3,X5) | ~m1_subset_1(X7,u1_struct_0(X5)) | ~m1_subset_1(X7,u1_struct_0(sK3)) | ~r1_tmap_1(X5,X4,k2_tmap_1(sK3,X4,X6,X5),X7) | r1_tmap_1(sK3,X4,k2_tmap_1(sK3,X4,X6,sK3),X7)) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f274,f107])).
% 0.22/0.58  % (30195)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  fof(f274,plain,(
% 0.22/0.58    ( ! [X6,X4,X7,X5] : (~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | v2_struct_0(X4) | ~v2_pre_topc(X4) | ~l1_pre_topc(X4) | v2_struct_0(sK3) | v2_struct_0(X5) | ~m1_pre_topc(X5,sK3) | ~v1_funct_1(X6) | ~v1_funct_2(X6,u1_struct_0(sK3),u1_struct_0(X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4)))) | ~m1_pre_topc(sK3,X5) | ~m1_subset_1(X7,u1_struct_0(X5)) | ~m1_subset_1(X7,u1_struct_0(sK3)) | ~r1_tmap_1(X5,X4,k2_tmap_1(sK3,X4,X6,X5),X7) | r1_tmap_1(sK3,X4,k2_tmap_1(sK3,X4,X6,sK3),X7)) )),
% 0.22/0.58    inference(duplicate_literal_removal,[],[f273])).
% 0.22/0.58  
% 0.22/0.58  % (30195)Memory used [KB]: 6780
% 0.22/0.58  % (30195)Time elapsed: 0.134 s
% 0.22/0.58  % (30195)------------------------------
% 0.22/0.58  % (30195)------------------------------
% 0.22/0.58  fof(f273,plain,(
% 0.22/0.58    ( ! [X6,X4,X7,X5] : (~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | v2_struct_0(X4) | ~v2_pre_topc(X4) | ~l1_pre_topc(X4) | v2_struct_0(sK3) | v2_struct_0(sK3) | v2_struct_0(X5) | ~m1_pre_topc(X5,sK3) | ~v1_funct_1(X6) | ~v1_funct_2(X6,u1_struct_0(sK3),u1_struct_0(X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4)))) | ~m1_pre_topc(sK3,X5) | ~m1_subset_1(X7,u1_struct_0(X5)) | ~m1_subset_1(X7,u1_struct_0(sK3)) | ~r1_tmap_1(X5,X4,k2_tmap_1(sK3,X4,X6,X5),X7) | r1_tmap_1(sK3,X4,k2_tmap_1(sK3,X4,X6,sK3),X7)) )),
% 0.22/0.58    inference(resolution,[],[f135,f80])).
% 0.22/0.58  fof(f80,plain,(
% 0.22/0.58    ( ! [X6,X4,X2,X0,X3,X1] : (~m1_pre_topc(X2,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | v2_struct_0(X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X6) | r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6)) )),
% 0.22/0.58    inference(equality_resolution,[],[f71])).
% 0.22/0.58  fof(f71,plain,(
% 0.22/0.58    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | X5 != X6 | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) | r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f30])).
% 0.22/0.58  fof(f30,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.58    inference(flattening,[],[f29])).
% 0.22/0.58  fof(f29,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : ((r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) | (~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) | X5 != X6)) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.58    inference(ennf_transformation,[],[f15])).
% 0.22/0.58  fof(f15,axiom,(
% 0.22/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6) => r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6))))))))))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_tmap_1)).
% 0.22/0.58  fof(f926,plain,(
% 0.22/0.58    r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),sK5)),
% 0.22/0.58    inference(backward_demodulation,[],[f85,f925])).
% 0.22/0.58  fof(f925,plain,(
% 0.22/0.58    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_tmap_1(sK3,sK1,sK4,sK2)),
% 0.22/0.58    inference(backward_demodulation,[],[f840,f924])).
% 0.22/0.58  fof(f924,plain,(
% 0.22/0.58    k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,k2_struct_0(sK2)) = k2_tmap_1(sK3,sK1,sK4,sK2)),
% 0.22/0.58    inference(forward_demodulation,[],[f921,f227])).
% 0.22/0.58  fof(f921,plain,(
% 0.22/0.58    k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,u1_struct_0(sK2)) = k2_tmap_1(sK3,sK1,sK4,sK2)),
% 0.22/0.58    inference(resolution,[],[f848,f306])).
% 0.22/0.58  fof(f848,plain,(
% 0.22/0.58    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,u1_struct_0(X0)) = k2_tmap_1(sK3,sK1,sK4,X0)) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f847,f194])).
% 0.22/0.58  fof(f847,plain,(
% 0.22/0.58    ( ! [X0] : (~v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1)) | ~m1_pre_topc(X0,sK3) | k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,u1_struct_0(X0)) = k2_tmap_1(sK3,sK1,sK4,X0)) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f846,f48])).
% 0.22/0.58  fof(f846,plain,(
% 0.22/0.58    ( ! [X0] : (~v1_funct_1(sK4) | ~v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1)) | ~m1_pre_topc(X0,sK3) | k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,u1_struct_0(X0)) = k2_tmap_1(sK3,sK1,sK4,X0)) )),
% 0.22/0.58    inference(resolution,[],[f665,f195])).
% 0.22/0.58  fof(f665,plain,(
% 0.22/0.58    ( ! [X6,X7] : (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1)))) | ~v1_funct_1(X6) | ~v1_funct_2(X6,k2_struct_0(sK3),k2_struct_0(sK1)) | ~m1_pre_topc(X7,sK3) | k2_tmap_1(sK3,sK1,X6,X7) = k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),X6,u1_struct_0(X7))) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f664,f52])).
% 0.22/0.58  fof(f664,plain,(
% 0.22/0.58    ( ! [X6,X7] : (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1)))) | ~v1_funct_1(X6) | ~v1_funct_2(X6,k2_struct_0(sK3),k2_struct_0(sK1)) | v2_struct_0(sK3) | ~m1_pre_topc(X7,sK3) | k2_tmap_1(sK3,sK1,X6,X7) = k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),X6,u1_struct_0(X7))) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f663,f98])).
% 0.22/0.58  fof(f663,plain,(
% 0.22/0.58    ( ! [X6,X7] : (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1)))) | ~l1_pre_topc(sK3) | ~v1_funct_1(X6) | ~v1_funct_2(X6,k2_struct_0(sK3),k2_struct_0(sK1)) | v2_struct_0(sK3) | ~m1_pre_topc(X7,sK3) | k2_tmap_1(sK3,sK1,X6,X7) = k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),X6,u1_struct_0(X7))) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f656,f107])).
% 0.22/0.58  fof(f656,plain,(
% 0.22/0.58    ( ! [X6,X7] : (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1)))) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~v1_funct_1(X6) | ~v1_funct_2(X6,k2_struct_0(sK3),k2_struct_0(sK1)) | v2_struct_0(sK3) | ~m1_pre_topc(X7,sK3) | k2_tmap_1(sK3,sK1,X6,X7) = k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),X6,u1_struct_0(X7))) )),
% 0.22/0.58    inference(superposition,[],[f337,f192])).
% 0.22/0.58  fof(f337,plain,(
% 0.22/0.58    ( ! [X6,X7,X5] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),k2_struct_0(sK1)))) | ~v2_pre_topc(X6) | ~l1_pre_topc(X6) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X6),k2_struct_0(sK1)) | v2_struct_0(X6) | ~m1_pre_topc(X7,X6) | k2_tmap_1(X6,sK1,X5,X7) = k2_partfun1(u1_struct_0(X6),k2_struct_0(sK1),X5,u1_struct_0(X7))) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f336,f58])).
% 0.22/0.58  fof(f336,plain,(
% 0.22/0.58    ( ! [X6,X7,X5] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),k2_struct_0(sK1)))) | ~v2_pre_topc(X6) | ~l1_pre_topc(X6) | ~l1_pre_topc(sK1) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X6),k2_struct_0(sK1)) | v2_struct_0(X6) | ~m1_pre_topc(X7,X6) | k2_tmap_1(X6,sK1,X5,X7) = k2_partfun1(u1_struct_0(X6),k2_struct_0(sK1),X5,u1_struct_0(X7))) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f335,f57])).
% 0.22/0.58  fof(f335,plain,(
% 0.22/0.58    ( ! [X6,X7,X5] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),k2_struct_0(sK1)))) | ~v2_pre_topc(X6) | ~l1_pre_topc(X6) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X6),k2_struct_0(sK1)) | v2_struct_0(X6) | ~m1_pre_topc(X7,X6) | k2_tmap_1(X6,sK1,X5,X7) = k2_partfun1(u1_struct_0(X6),k2_struct_0(sK1),X5,u1_struct_0(X7))) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f324,f56])).
% 0.22/0.58  fof(f324,plain,(
% 0.22/0.58    ( ! [X6,X7,X5] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),k2_struct_0(sK1)))) | ~v2_pre_topc(X6) | ~l1_pre_topc(X6) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X6),k2_struct_0(sK1)) | v2_struct_0(X6) | ~m1_pre_topc(X7,X6) | k2_tmap_1(X6,sK1,X5,X7) = k2_partfun1(u1_struct_0(X6),k2_struct_0(sK1),X5,u1_struct_0(X7))) )),
% 0.22/0.58    inference(superposition,[],[f72,f93])).
% 0.22/0.58  fof(f72,plain,(
% 0.22/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | v2_struct_0(X0) | ~m1_pre_topc(X3,X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f32])).
% 0.22/0.58  fof(f32,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.58    inference(flattening,[],[f31])).
% 0.22/0.58  fof(f31,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.58    inference(ennf_transformation,[],[f8])).
% 0.22/0.58  fof(f8,axiom,(
% 0.22/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).
% 0.22/0.58  fof(f840,plain,(
% 0.22/0.58    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,k2_struct_0(sK2))),
% 0.22/0.58    inference(forward_demodulation,[],[f838,f227])).
% 0.22/0.58  fof(f838,plain,(
% 0.22/0.58    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,u1_struct_0(sK2))),
% 0.22/0.58    inference(resolution,[],[f631,f306])).
% 0.22/0.58  fof(f631,plain,(
% 0.22/0.58    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k3_tmap_1(sK0,sK1,sK3,X0,sK4) = k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,u1_struct_0(X0))) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f630,f48])).
% 0.22/0.58  fof(f630,plain,(
% 0.22/0.58    ( ! [X0] : (k3_tmap_1(sK0,sK1,sK3,X0,sK4) = k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,u1_struct_0(X0)) | ~v1_funct_1(sK4) | ~m1_pre_topc(X0,sK3)) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f629,f194])).
% 0.22/0.58  fof(f629,plain,(
% 0.22/0.58    ( ! [X0] : (k3_tmap_1(sK0,sK1,sK3,X0,sK4) = k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,u1_struct_0(X0)) | ~v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(X0,sK3)) )),
% 0.22/0.58    inference(resolution,[],[f346,f195])).
% 0.22/0.58  fof(f346,plain,(
% 0.22/0.58    ( ! [X17,X18] : (~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1)))) | k3_tmap_1(sK0,sK1,sK3,X18,X17) = k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),X17,u1_struct_0(X18)) | ~v1_funct_2(X17,k2_struct_0(sK3),k2_struct_0(sK1)) | ~v1_funct_1(X17) | ~m1_pre_topc(X18,sK3)) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f345,f58])).
% 0.22/0.58  fof(f345,plain,(
% 0.22/0.58    ( ! [X17,X18] : (~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1)))) | k3_tmap_1(sK0,sK1,sK3,X18,X17) = k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),X17,u1_struct_0(X18)) | ~v1_funct_2(X17,k2_struct_0(sK3),k2_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v1_funct_1(X17) | ~m1_pre_topc(X18,sK3)) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f344,f57])).
% 0.22/0.58  fof(f344,plain,(
% 0.22/0.58    ( ! [X17,X18] : (~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1)))) | k3_tmap_1(sK0,sK1,sK3,X18,X17) = k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),X17,u1_struct_0(X18)) | ~v1_funct_2(X17,k2_struct_0(sK3),k2_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(X17) | ~m1_pre_topc(X18,sK3)) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f328,f56])).
% 0.22/0.58  fof(f328,plain,(
% 0.22/0.58    ( ! [X17,X18] : (~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1)))) | k3_tmap_1(sK0,sK1,sK3,X18,X17) = k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),X17,u1_struct_0(X18)) | ~v1_funct_2(X17,k2_struct_0(sK3),k2_struct_0(sK1)) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(X17) | ~m1_pre_topc(X18,sK3)) )),
% 0.22/0.58    inference(superposition,[],[f200,f93])).
% 0.22/0.58  fof(f200,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(X0)))) | k3_tmap_1(sK0,X0,sK3,X1,X2) = k2_partfun1(k2_struct_0(sK3),u1_struct_0(X0),X2,u1_struct_0(X1)) | ~v1_funct_2(X2,k2_struct_0(sK3),u1_struct_0(X0)) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,sK3)) )),
% 0.22/0.58    inference(forward_demodulation,[],[f199,f192])).
% 0.22/0.58  fof(f199,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X2,k2_struct_0(sK3),u1_struct_0(X0)) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,sK3) | k3_tmap_1(sK0,X0,sK3,X1,X2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X0),X2,u1_struct_0(X1))) )),
% 0.22/0.58    inference(forward_demodulation,[],[f197,f192])).
% 0.22/0.58  fof(f197,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (~v1_funct_2(X2,k2_struct_0(sK3),u1_struct_0(X0)) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~m1_pre_topc(X1,sK3) | k3_tmap_1(sK0,X0,sK3,X1,X2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X0),X2,u1_struct_0(X1))) )),
% 0.22/0.58    inference(backward_demodulation,[],[f143,f192])).
% 0.22/0.58  fof(f143,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~m1_pre_topc(X1,sK3) | k3_tmap_1(sK0,X0,sK3,X1,X2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X0),X2,u1_struct_0(X1))) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f142,f122])).
% 0.22/0.58  fof(f122,plain,(
% 0.22/0.58    ( ! [X0] : (~m1_pre_topc(X0,sK3) | m1_pre_topc(X0,sK0)) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f121,f60])).
% 0.22/0.58  fof(f121,plain,(
% 0.22/0.58    ( ! [X0] : (~v2_pre_topc(sK0) | ~m1_pre_topc(X0,sK3) | m1_pre_topc(X0,sK0)) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f119,f61])).
% 0.22/0.58  fof(f119,plain,(
% 0.22/0.58    ( ! [X0] : (~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_pre_topc(X0,sK3) | m1_pre_topc(X0,sK0)) )),
% 0.22/0.58    inference(resolution,[],[f77,f53])).
% 0.22/0.58  fof(f77,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X2,X1) | m1_pre_topc(X2,X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f40])).
% 0.22/0.58  fof(f40,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.58    inference(flattening,[],[f39])).
% 0.22/0.58  fof(f39,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.58    inference(ennf_transformation,[],[f14])).
% 0.22/0.58  fof(f14,axiom,(
% 0.22/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).
% 0.22/0.58  fof(f142,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,sK0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~m1_pre_topc(X1,sK3) | k3_tmap_1(sK0,X0,sK3,X1,X2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X0),X2,u1_struct_0(X1))) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f141,f59])).
% 0.22/0.58  fof(f59,plain,(
% 0.22/0.58    ~v2_struct_0(sK0)),
% 0.22/0.58    inference(cnf_transformation,[],[f19])).
% 0.22/0.58  fof(f141,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK0) | ~m1_pre_topc(X1,sK0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~m1_pre_topc(X1,sK3) | k3_tmap_1(sK0,X0,sK3,X1,X2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X0),X2,u1_struct_0(X1))) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f140,f61])).
% 0.22/0.58  fof(f140,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (~l1_pre_topc(sK0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK0) | ~m1_pre_topc(X1,sK0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~m1_pre_topc(X1,sK3) | k3_tmap_1(sK0,X0,sK3,X1,X2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X0),X2,u1_struct_0(X1))) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f138,f60])).
% 0.22/0.58  fof(f138,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK0) | ~m1_pre_topc(X1,sK0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~m1_pre_topc(X1,sK3) | k3_tmap_1(sK0,X0,sK3,X1,X2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X0),X2,u1_struct_0(X1))) )),
% 0.22/0.58    inference(resolution,[],[f70,f53])).
% 0.22/0.58  fof(f70,plain,(
% 0.22/0.58    ( ! [X4,X2,X0,X3,X1] : (~m1_pre_topc(X2,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f28])).
% 0.22/0.58  fof(f28,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.58    inference(flattening,[],[f27])).
% 0.22/0.58  fof(f27,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.58    inference(ennf_transformation,[],[f9])).
% 0.22/0.58  fof(f9,axiom,(
% 0.22/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).
% 0.22/0.58  fof(f85,plain,(
% 0.22/0.58    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)),
% 0.22/0.58    inference(backward_demodulation,[],[f45,f44])).
% 0.22/0.58  fof(f45,plain,(
% 0.22/0.58    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 0.22/0.58    inference(cnf_transformation,[],[f19])).
% 0.22/0.58  % SZS output end Proof for theBenchmark
% 0.22/0.58  % (30212)------------------------------
% 0.22/0.58  % (30212)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (30212)Termination reason: Refutation
% 0.22/0.58  
% 0.22/0.58  % (30212)Memory used [KB]: 2430
% 0.22/0.58  % (30212)Time elapsed: 0.147 s
% 0.22/0.58  % (30212)------------------------------
% 0.22/0.58  % (30212)------------------------------
% 0.22/0.58  % (30194)Success in time 0.205 s
%------------------------------------------------------------------------------
