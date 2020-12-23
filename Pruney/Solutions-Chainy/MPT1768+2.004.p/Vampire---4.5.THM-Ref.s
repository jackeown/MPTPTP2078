%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:43 EST 2020

% Result     : Theorem 1.72s
% Output     : Refutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :  225 (5137 expanded)
%              Number of leaves         :   10 ( 888 expanded)
%              Depth                    :   66
%              Number of atoms          : 1400 (62649 expanded)
%              Number of equality atoms :   75 ( 654 expanded)
%              Maximal formula depth    :   26 (   8 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f930,plain,(
    $false ),
    inference(subsumption_resolution,[],[f929,f66])).

fof(f66,plain,(
    l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f60,f47])).

fof(f47,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_pre_topc(X4,X3)
                      & m1_pre_topc(X3,X2)
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_pre_topc(X4,X3)
                      & m1_pre_topc(X3,X2)
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
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
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
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
                        ( ( m1_pre_topc(X4,X0)
                          & ~ v2_struct_0(X4) )
                       => ( ( m1_pre_topc(X4,X3)
                            & m1_pre_topc(X3,X2) )
                         => ! [X5] :
                              ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                                & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                                & v1_funct_1(X5) )
                             => r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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
                      ( ( m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ( ( m1_pre_topc(X4,X3)
                          & m1_pre_topc(X3,X2) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                              & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                              & v1_funct_1(X5) )
                           => r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_tmap_1)).

fof(f60,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2) ),
    inference(resolution,[],[f49,f41])).

fof(f41,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f929,plain,(
    ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f928,f48])).

fof(f48,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f928,plain,(
    ~ m1_pre_topc(sK2,sK2) ),
    inference(subsumption_resolution,[],[f927,f37])).

fof(f37,plain,(
    m1_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f13])).

fof(f927,plain,
    ( ~ m1_pre_topc(sK4,sK3)
    | ~ m1_pre_topc(sK2,sK2) ),
    inference(subsumption_resolution,[],[f926,f102])).

fof(f102,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(subsumption_resolution,[],[f101,f77])).

fof(f77,plain,(
    v2_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f76,f46])).

fof(f46,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f76,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f70,f47])).

fof(f70,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK2) ),
    inference(resolution,[],[f54,f41])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
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

fof(f101,plain,
    ( ~ v2_pre_topc(sK2)
    | m1_pre_topc(sK4,sK2) ),
    inference(subsumption_resolution,[],[f97,f66])).

fof(f97,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | m1_pre_topc(sK4,sK2) ),
    inference(resolution,[],[f87,f36])).

fof(f36,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f87,plain,(
    ! [X6] :
      ( ~ m1_pre_topc(sK3,X6)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | m1_pre_topc(sK4,X6) ) ),
    inference(resolution,[],[f55,f37])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X2,X1)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | m1_pre_topc(X2,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
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
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f926,plain,
    ( ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(sK4,sK3)
    | ~ m1_pre_topc(sK2,sK2) ),
    inference(subsumption_resolution,[],[f925,f34])).

fof(f34,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f13])).

fof(f925,plain,
    ( v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(sK4,sK3)
    | ~ m1_pre_topc(sK2,sK2) ),
    inference(subsumption_resolution,[],[f912,f719])).

fof(f719,plain,(
    ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4),k2_tmap_1(sK2,sK1,sK5,sK4)) ),
    inference(backward_demodulation,[],[f167,f718])).

fof(f718,plain,(
    k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4) ),
    inference(forward_demodulation,[],[f715,f362])).

fof(f362,plain,(
    k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK4)) ),
    inference(resolution,[],[f308,f37])).

fof(f308,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK3)
      | k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),X2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X2)) ) ),
    inference(subsumption_resolution,[],[f307,f38])).

fof(f38,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f13])).

fof(f307,plain,(
    ! [X2] :
      ( v2_struct_0(sK3)
      | ~ m1_pre_topc(X2,sK3)
      | k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),X2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X2)) ) ),
    inference(subsumption_resolution,[],[f306,f239])).

fof(f239,plain,(
    v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f238,f45])).

fof(f45,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f238,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f237,f32])).

fof(f32,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f13])).

fof(f237,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f236,f31])).

fof(f31,plain,(
    v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f236,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f235,f30])).

fof(f30,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f13])).

fof(f235,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f234,f39])).

fof(f39,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f234,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f233,f41])).

fof(f233,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f232,f44])).

fof(f44,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f232,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f231,f43])).

fof(f43,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f231,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f230,f42])).

fof(f42,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f230,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f229,f47])).

fof(f229,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f212,f46])).

fof(f212,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f57,f164])).

fof(f164,plain,(
    k3_tmap_1(sK0,sK1,sK2,sK3,sK5) = k2_tmap_1(sK2,sK1,sK5,sK3) ),
    inference(forward_demodulation,[],[f160,f125])).

fof(f125,plain,(
    k2_tmap_1(sK2,sK1,sK5,sK3) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK3)) ),
    inference(resolution,[],[f123,f36])).

fof(f123,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | k2_tmap_1(sK2,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f122,f40])).

fof(f40,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f122,plain,(
    ! [X0] :
      ( v2_struct_0(sK2)
      | ~ m1_pre_topc(X0,sK2)
      | k2_tmap_1(sK2,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f121,f31])).

fof(f121,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(X0,sK2)
      | k2_tmap_1(sK2,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f120,f30])).

fof(f120,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK5)
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(X0,sK2)
      | k2_tmap_1(sK2,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f119,f44])).

fof(f119,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK5)
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(X0,sK2)
      | k2_tmap_1(sK2,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f118,f43])).

fof(f118,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK5)
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(X0,sK2)
      | k2_tmap_1(sK2,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f117,f42])).

fof(f117,plain,(
    ! [X0] :
      ( v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK5)
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(X0,sK2)
      | k2_tmap_1(sK2,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f116,f66])).

fof(f116,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK2)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK5)
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(X0,sK2)
      | k2_tmap_1(sK2,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f115,f77])).

fof(f115,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK2)
      | ~ l1_pre_topc(sK2)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK5)
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(X0,sK2)
      | k2_tmap_1(sK2,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0)) ) ),
    inference(resolution,[],[f53,f32])).

fof(f53,plain,(
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
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f160,plain,(
    k3_tmap_1(sK0,sK1,sK2,sK3,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK3)) ),
    inference(resolution,[],[f155,f36])).

fof(f155,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK2,X0,sK5) ) ),
    inference(subsumption_resolution,[],[f154,f45])).

fof(f154,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ m1_pre_topc(X0,sK2)
      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK2,X0,sK5) ) ),
    inference(subsumption_resolution,[],[f153,f46])).

fof(f153,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_pre_topc(X0,sK2)
      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK2,X0,sK5) ) ),
    inference(subsumption_resolution,[],[f150,f47])).

fof(f150,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_pre_topc(X0,sK2)
      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK2,X0,sK5) ) ),
    inference(resolution,[],[f146,f41])).

fof(f146,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(sK2,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK2)
      | k3_tmap_1(X0,sK1,sK2,X1,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f145,f55])).

fof(f145,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK2,X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK2)
      | k3_tmap_1(X0,sK1,sK2,X1,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f144,f31])).

fof(f144,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK2)
      | k3_tmap_1(X0,sK1,sK2,X1,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f143,f30])).

fof(f143,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(sK5)
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK2)
      | k3_tmap_1(X0,sK1,sK2,X1,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f142,f44])).

fof(f142,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(sK1)
      | ~ m1_pre_topc(sK2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(sK5)
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK2)
      | k3_tmap_1(X0,sK1,sK2,X1,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f141,f43])).

fof(f141,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ m1_pre_topc(sK2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(sK5)
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK2)
      | k3_tmap_1(X0,sK1,sK2,X1,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f138,f42])).

fof(f138,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ m1_pre_topc(sK2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(sK5)
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK2)
      | k3_tmap_1(X0,sK1,sK2,X1,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X1)) ) ),
    inference(resolution,[],[f50,f32])).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X3,X2)
      | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(X4)
        & m1_pre_topc(X3,X0)
        & m1_pre_topc(X2,X0)
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_tmap_1)).

fof(f306,plain,(
    ! [X2] :
      ( ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(X2,sK3)
      | k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),X2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X2)) ) ),
    inference(subsumption_resolution,[],[f305,f217])).

fof(f217,plain,(
    v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) ),
    inference(subsumption_resolution,[],[f216,f46])).

fof(f216,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3))
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f215,f45])).

fof(f215,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3))
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f214,f39])).

fof(f214,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3))
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f213,f41])).

fof(f213,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f210,f47])).

fof(f210,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3))
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(superposition,[],[f114,f164])).

fof(f114,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k3_tmap_1(X0,sK1,sK2,X1,sK5))
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK2,X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f113,f31])).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | v2_struct_0(X0)
      | v1_funct_1(k3_tmap_1(X0,sK1,sK2,X1,sK5)) ) ),
    inference(subsumption_resolution,[],[f112,f30])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(sK5)
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | v2_struct_0(X0)
      | v1_funct_1(k3_tmap_1(X0,sK1,sK2,X1,sK5)) ) ),
    inference(subsumption_resolution,[],[f111,f44])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(sK1)
      | ~ m1_pre_topc(sK2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(sK5)
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | v2_struct_0(X0)
      | v1_funct_1(k3_tmap_1(X0,sK1,sK2,X1,sK5)) ) ),
    inference(subsumption_resolution,[],[f110,f43])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ m1_pre_topc(sK2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(sK5)
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | v2_struct_0(X0)
      | v1_funct_1(k3_tmap_1(X0,sK1,sK2,X1,sK5)) ) ),
    inference(subsumption_resolution,[],[f109,f42])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ m1_pre_topc(sK2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(sK5)
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | v2_struct_0(X0)
      | v1_funct_1(k3_tmap_1(X0,sK1,sK2,X1,sK5)) ) ),
    inference(resolution,[],[f56,f32])).

fof(f56,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | v2_struct_0(X0)
      | v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f305,plain,(
    ! [X2] :
      ( ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3))
      | ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(X2,sK3)
      | k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),X2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X2)) ) ),
    inference(subsumption_resolution,[],[f304,f44])).

fof(f304,plain,(
    ! [X2] :
      ( ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3))
      | ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(X2,sK3)
      | k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),X2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X2)) ) ),
    inference(subsumption_resolution,[],[f303,f43])).

fof(f303,plain,(
    ! [X2] :
      ( ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3))
      | ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(X2,sK3)
      | k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),X2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X2)) ) ),
    inference(subsumption_resolution,[],[f302,f42])).

fof(f302,plain,(
    ! [X2] :
      ( v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3))
      | ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(X2,sK3)
      | k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),X2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X2)) ) ),
    inference(subsumption_resolution,[],[f301,f67])).

fof(f67,plain,(
    l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f61,f66])).

fof(f61,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_pre_topc(sK3) ),
    inference(resolution,[],[f49,f36])).

fof(f301,plain,(
    ! [X2] :
      ( ~ l1_pre_topc(sK3)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3))
      | ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(X2,sK3)
      | k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),X2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X2)) ) ),
    inference(subsumption_resolution,[],[f293,f79])).

fof(f79,plain,(
    v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f78,f77])).

fof(f78,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f71,f66])).

fof(f71,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_pre_topc(sK3) ),
    inference(resolution,[],[f54,f36])).

fof(f293,plain,(
    ! [X2] :
      ( ~ v2_pre_topc(sK3)
      | ~ l1_pre_topc(sK3)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3))
      | ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(X2,sK3)
      | k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),X2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X2)) ) ),
    inference(resolution,[],[f228,f53])).

fof(f228,plain,(
    m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f227,f45])).

fof(f227,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f226,f32])).

fof(f226,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f225,f31])).

fof(f225,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f224,f30])).

fof(f224,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f223,f39])).

fof(f223,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f222,f41])).

fof(f222,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f221,f44])).

fof(f221,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f220,f43])).

fof(f220,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f219,f42])).

fof(f219,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f218,f47])).

fof(f218,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f211,f46])).

fof(f211,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f58,f164])).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f715,plain,(
    k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK4)) ),
    inference(resolution,[],[f589,f37])).

fof(f589,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK3)
      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X1)) = k3_tmap_1(sK0,sK1,sK3,X1,k2_tmap_1(sK2,sK1,sK5,sK3)) ) ),
    inference(subsumption_resolution,[],[f588,f45])).

fof(f588,plain,(
    ! [X1] :
      ( v2_struct_0(sK0)
      | ~ m1_pre_topc(X1,sK3)
      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X1)) = k3_tmap_1(sK0,sK1,sK3,X1,k2_tmap_1(sK2,sK1,sK5,sK3)) ) ),
    inference(subsumption_resolution,[],[f587,f46])).

fof(f587,plain,(
    ! [X1] :
      ( ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_pre_topc(X1,sK3)
      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X1)) = k3_tmap_1(sK0,sK1,sK3,X1,k2_tmap_1(sK2,sK1,sK5,sK3)) ) ),
    inference(subsumption_resolution,[],[f581,f47])).

fof(f581,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_pre_topc(X1,sK3)
      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X1)) = k3_tmap_1(sK0,sK1,sK3,X1,k2_tmap_1(sK2,sK1,sK5,sK3)) ) ),
    inference(resolution,[],[f300,f39])).

fof(f300,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(sK3,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK3)
      | k3_tmap_1(X0,sK1,sK3,X1,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f299,f55])).

fof(f299,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK3,X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK3)
      | k3_tmap_1(X0,sK1,sK3,X1,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f298,f239])).

fof(f298,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK3,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK3)
      | k3_tmap_1(X0,sK1,sK3,X1,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f297,f217])).

fof(f297,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK3,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3))
      | ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK3)
      | k3_tmap_1(X0,sK1,sK3,X1,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f296,f44])).

fof(f296,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(sK1)
      | ~ m1_pre_topc(sK3,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3))
      | ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK3)
      | k3_tmap_1(X0,sK1,sK3,X1,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f295,f43])).

fof(f295,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ m1_pre_topc(sK3,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3))
      | ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK3)
      | k3_tmap_1(X0,sK1,sK3,X1,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f292,f42])).

fof(f292,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ m1_pre_topc(sK3,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3))
      | ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK3)
      | k3_tmap_1(X0,sK1,sK3,X1,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X1)) ) ),
    inference(resolution,[],[f228,f50])).

fof(f167,plain,(
    ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)),k2_tmap_1(sK2,sK1,sK5,sK4)) ),
    inference(backward_demodulation,[],[f165,f166])).

fof(f166,plain,(
    k3_tmap_1(sK0,sK1,sK2,sK4,sK5) = k2_tmap_1(sK2,sK1,sK5,sK4) ),
    inference(forward_demodulation,[],[f161,f126])).

fof(f126,plain,(
    k2_tmap_1(sK2,sK1,sK5,sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK4)) ),
    inference(resolution,[],[f123,f102])).

fof(f161,plain,(
    k3_tmap_1(sK0,sK1,sK2,sK4,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK4)) ),
    inference(resolution,[],[f155,f102])).

fof(f165,plain,(
    ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)),k3_tmap_1(sK0,sK1,sK2,sK4,sK5)) ),
    inference(backward_demodulation,[],[f33,f164])).

fof(f33,plain,(
    ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)),k3_tmap_1(sK0,sK1,sK2,sK4,sK5)) ),
    inference(cnf_transformation,[],[f13])).

fof(f912,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4),k2_tmap_1(sK2,sK1,sK5,sK4))
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(sK4,sK3)
    | ~ m1_pre_topc(sK2,sK2) ),
    inference(superposition,[],[f830,f597])).

fof(f597,plain,(
    k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4) = k3_tmap_1(sK2,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) ),
    inference(forward_demodulation,[],[f594,f362])).

fof(f594,plain,(
    k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK4)) = k3_tmap_1(sK2,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) ),
    inference(resolution,[],[f586,f37])).

fof(f586,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X0)) = k3_tmap_1(sK2,sK1,sK3,X0,k2_tmap_1(sK2,sK1,sK5,sK3)) ) ),
    inference(subsumption_resolution,[],[f585,f40])).

fof(f585,plain,(
    ! [X0] :
      ( v2_struct_0(sK2)
      | ~ m1_pre_topc(X0,sK3)
      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X0)) = k3_tmap_1(sK2,sK1,sK3,X0,k2_tmap_1(sK2,sK1,sK5,sK3)) ) ),
    inference(subsumption_resolution,[],[f584,f77])).

fof(f584,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(X0,sK3)
      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X0)) = k3_tmap_1(sK2,sK1,sK3,X0,k2_tmap_1(sK2,sK1,sK5,sK3)) ) ),
    inference(subsumption_resolution,[],[f580,f66])).

fof(f580,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(X0,sK3)
      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X0)) = k3_tmap_1(sK2,sK1,sK3,X0,k2_tmap_1(sK2,sK1,sK5,sK3)) ) ),
    inference(resolution,[],[f300,f36])).

fof(f830,plain,(
    ! [X0] :
      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK3,X0,k2_tmap_1(sK2,sK1,sK5,sK3)),k2_tmap_1(sK2,sK1,sK5,X0))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK2)
      | ~ m1_pre_topc(X0,sK3)
      | ~ m1_pre_topc(sK2,sK2) ) ),
    inference(subsumption_resolution,[],[f829,f40])).

fof(f829,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK2,sK2)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(X0,sK3)
      | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK3,X0,k2_tmap_1(sK2,sK1,sK5,sK3)),k2_tmap_1(sK2,sK1,sK5,X0)) ) ),
    inference(subsumption_resolution,[],[f828,f228])).

fof(f828,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK2,sK2)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK2)
      | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(X0,sK3)
      | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK3,X0,k2_tmap_1(sK2,sK1,sK5,sK3)),k2_tmap_1(sK2,sK1,sK5,X0)) ) ),
    inference(subsumption_resolution,[],[f827,f239])).

fof(f827,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK2,sK2)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK2)
      | ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(X0,sK3)
      | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK3,X0,k2_tmap_1(sK2,sK1,sK5,sK3)),k2_tmap_1(sK2,sK1,sK5,X0)) ) ),
    inference(subsumption_resolution,[],[f826,f217])).

fof(f826,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK2,sK2)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK2)
      | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3))
      | ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(X0,sK3)
      | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK3,X0,k2_tmap_1(sK2,sK1,sK5,sK3)),k2_tmap_1(sK2,sK1,sK5,X0)) ) ),
    inference(subsumption_resolution,[],[f825,f32])).

fof(f825,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK2,sK2)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK2)
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3))
      | ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(X0,sK3)
      | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK3,X0,k2_tmap_1(sK2,sK1,sK5,sK3)),k2_tmap_1(sK2,sK1,sK5,X0)) ) ),
    inference(subsumption_resolution,[],[f824,f31])).

fof(f824,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK2,sK2)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK2)
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3))
      | ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(X0,sK3)
      | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK3,X0,k2_tmap_1(sK2,sK1,sK5,sK3)),k2_tmap_1(sK2,sK1,sK5,X0)) ) ),
    inference(subsumption_resolution,[],[f823,f30])).

fof(f823,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK2,sK2)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK2)
      | ~ v1_funct_1(sK5)
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3))
      | ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(X0,sK3)
      | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK3,X0,k2_tmap_1(sK2,sK1,sK5,sK3)),k2_tmap_1(sK2,sK1,sK5,X0)) ) ),
    inference(subsumption_resolution,[],[f822,f36])).

fof(f822,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK2,sK2)
      | ~ m1_pre_topc(sK3,sK2)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK2)
      | ~ v1_funct_1(sK5)
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3))
      | ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(X0,sK3)
      | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK3,X0,k2_tmap_1(sK2,sK1,sK5,sK3)),k2_tmap_1(sK2,sK1,sK5,X0)) ) ),
    inference(subsumption_resolution,[],[f821,f38])).

fof(f821,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK2,sK2)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK2)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK2)
      | ~ v1_funct_1(sK5)
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3))
      | ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(X0,sK3)
      | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK3,X0,k2_tmap_1(sK2,sK1,sK5,sK3)),k2_tmap_1(sK2,sK1,sK5,X0)) ) ),
    inference(subsumption_resolution,[],[f820,f44])).

fof(f820,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK2,sK2)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK2)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK2)
      | ~ v1_funct_1(sK5)
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3))
      | ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(X0,sK3)
      | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK3,X0,k2_tmap_1(sK2,sK1,sK5,sK3)),k2_tmap_1(sK2,sK1,sK5,X0)) ) ),
    inference(subsumption_resolution,[],[f819,f43])).

fof(f819,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK2,sK2)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK2)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK2)
      | ~ v1_funct_1(sK5)
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3))
      | ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(X0,sK3)
      | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK3,X0,k2_tmap_1(sK2,sK1,sK5,sK3)),k2_tmap_1(sK2,sK1,sK5,X0)) ) ),
    inference(subsumption_resolution,[],[f818,f42])).

fof(f818,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK2,sK2)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK2)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK2)
      | ~ v1_funct_1(sK5)
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3))
      | ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(X0,sK3)
      | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK3,X0,k2_tmap_1(sK2,sK1,sK5,sK3)),k2_tmap_1(sK2,sK1,sK5,X0)) ) ),
    inference(subsumption_resolution,[],[f817,f66])).

fof(f817,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK2,sK2)
      | ~ l1_pre_topc(sK2)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK2)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK2)
      | ~ v1_funct_1(sK5)
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3))
      | ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(X0,sK3)
      | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK3,X0,k2_tmap_1(sK2,sK1,sK5,sK3)),k2_tmap_1(sK2,sK1,sK5,X0)) ) ),
    inference(subsumption_resolution,[],[f816,f77])).

fof(f816,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK2,sK2)
      | ~ v2_pre_topc(sK2)
      | ~ l1_pre_topc(sK2)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK2)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK2)
      | ~ v1_funct_1(sK5)
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3))
      | ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(X0,sK3)
      | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK3,X0,k2_tmap_1(sK2,sK1,sK5,sK3)),k2_tmap_1(sK2,sK1,sK5,X0)) ) ),
    inference(resolution,[],[f799,f51])).

fof(f51,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2))
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
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X3,X2)
      | r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3))
                          | ~ m1_pre_topc(X3,X2)
                          | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3))
                          | ~ m1_pre_topc(X3,X2)
                          | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
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
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                         => ( ( m1_pre_topc(X3,X2)
                              & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2)) )
                           => r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tmap_1)).

fof(f799,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),k2_tmap_1(sK2,sK1,sK5,sK3))
    | ~ m1_pre_topc(sK2,sK2) ),
    inference(subsumption_resolution,[],[f798,f36])).

fof(f798,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),k2_tmap_1(sK2,sK1,sK5,sK3))
    | ~ m1_pre_topc(sK3,sK2)
    | ~ m1_pre_topc(sK2,sK2) ),
    inference(subsumption_resolution,[],[f784,f38])).

fof(f784,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),k2_tmap_1(sK2,sK1,sK5,sK3))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ m1_pre_topc(sK2,sK2) ),
    inference(superposition,[],[f763,f341])).

fof(f341,plain,(
    k2_tmap_1(sK2,sK1,sK5,sK3) = k3_tmap_1(sK2,sK1,sK2,sK3,sK5) ),
    inference(forward_demodulation,[],[f337,f125])).

fof(f337,plain,(
    k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK3)) = k3_tmap_1(sK2,sK1,sK2,sK3,sK5) ),
    inference(resolution,[],[f158,f36])).

fof(f158,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK2)
      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X1)) = k3_tmap_1(sK2,sK1,sK2,X1,sK5) ) ),
    inference(subsumption_resolution,[],[f157,f40])).

fof(f157,plain,(
    ! [X1] :
      ( v2_struct_0(sK2)
      | ~ m1_pre_topc(X1,sK2)
      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X1)) = k3_tmap_1(sK2,sK1,sK2,X1,sK5) ) ),
    inference(subsumption_resolution,[],[f156,f77])).

fof(f156,plain,(
    ! [X1] :
      ( ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(X1,sK2)
      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X1)) = k3_tmap_1(sK2,sK1,sK2,X1,sK5) ) ),
    inference(subsumption_resolution,[],[f152,f66])).

fof(f152,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(X1,sK2)
      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X1)) = k3_tmap_1(sK2,sK1,sK2,X1,sK5) ) ),
    inference(duplicate_literal_removal,[],[f151])).

fof(f151,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(X1,sK2)
      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X1)) = k3_tmap_1(sK2,sK1,sK2,X1,sK5)
      | ~ l1_pre_topc(sK2) ) ),
    inference(resolution,[],[f146,f48])).

fof(f763,plain,(
    ! [X0] :
      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK2,X0,sK5),k2_tmap_1(sK2,sK1,sK5,X0))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK2)
      | ~ m1_pre_topc(sK2,sK2) ) ),
    inference(subsumption_resolution,[],[f762,f32])).

fof(f762,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK2,sK2)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK2)
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK2,X0,sK5),k2_tmap_1(sK2,sK1,sK5,X0)) ) ),
    inference(subsumption_resolution,[],[f761,f31])).

fof(f761,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK2,sK2)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK2)
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK2,X0,sK5),k2_tmap_1(sK2,sK1,sK5,X0)) ) ),
    inference(subsumption_resolution,[],[f760,f30])).

fof(f760,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK2,sK2)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK2)
      | ~ v1_funct_1(sK5)
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK2,X0,sK5),k2_tmap_1(sK2,sK1,sK5,X0)) ) ),
    inference(subsumption_resolution,[],[f759,f40])).

fof(f759,plain,(
    ! [X0] :
      ( v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,sK2)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK2)
      | ~ v1_funct_1(sK5)
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK2,X0,sK5),k2_tmap_1(sK2,sK1,sK5,X0)) ) ),
    inference(subsumption_resolution,[],[f758,f44])).

fof(f758,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK1)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,sK2)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK2)
      | ~ v1_funct_1(sK5)
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK2,X0,sK5),k2_tmap_1(sK2,sK1,sK5,X0)) ) ),
    inference(subsumption_resolution,[],[f757,f43])).

fof(f757,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,sK2)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK2)
      | ~ v1_funct_1(sK5)
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK2,X0,sK5),k2_tmap_1(sK2,sK1,sK5,X0)) ) ),
    inference(subsumption_resolution,[],[f756,f42])).

fof(f756,plain,(
    ! [X0] :
      ( v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,sK2)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK2)
      | ~ v1_funct_1(sK5)
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK2,X0,sK5),k2_tmap_1(sK2,sK1,sK5,X0)) ) ),
    inference(subsumption_resolution,[],[f755,f66])).

fof(f755,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK2)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,sK2)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK2)
      | ~ v1_funct_1(sK5)
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK2,X0,sK5),k2_tmap_1(sK2,sK1,sK5,X0)) ) ),
    inference(subsumption_resolution,[],[f754,f77])).

fof(f754,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK2)
      | ~ l1_pre_topc(sK2)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,sK2)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK2)
      | ~ v1_funct_1(sK5)
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK2,X0,sK5),k2_tmap_1(sK2,sK1,sK5,X0)) ) ),
    inference(duplicate_literal_removal,[],[f749])).

fof(f749,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK2)
      | ~ l1_pre_topc(sK2)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,sK2)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK2)
      | ~ v1_funct_1(sK5)
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      | ~ v1_funct_1(sK5)
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(X0,sK2)
      | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK2,X0,sK5),k2_tmap_1(sK2,sK1,sK5,X0)) ) ),
    inference(resolution,[],[f51,f189])).

fof(f189,plain,(
    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,k2_tmap_1(sK2,sK1,sK5,sK2)) ),
    inference(subsumption_resolution,[],[f188,f45])).

fof(f188,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,k2_tmap_1(sK2,sK1,sK5,sK2))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f187,f32])).

fof(f187,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,k2_tmap_1(sK2,sK1,sK5,sK2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f186,f31])).

fof(f186,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,k2_tmap_1(sK2,sK1,sK5,sK2))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f185,f30])).

fof(f185,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,k2_tmap_1(sK2,sK1,sK5,sK2))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f184,f41])).

fof(f184,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,k2_tmap_1(sK2,sK1,sK5,sK2))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f183,f40])).

fof(f183,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,k2_tmap_1(sK2,sK1,sK5,sK2))
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f182,f44])).

fof(f182,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,k2_tmap_1(sK2,sK1,sK5,sK2))
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f181,f43])).

fof(f181,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,k2_tmap_1(sK2,sK1,sK5,sK2))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f180,f42])).

fof(f180,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,k2_tmap_1(sK2,sK1,sK5,sK2))
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f179,f47])).

fof(f179,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,k2_tmap_1(sK2,sK1,sK5,sK2))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f169,f46])).

fof(f169,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,k2_tmap_1(sK2,sK1,sK5,sK2))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f52,f163])).

fof(f163,plain,(
    k2_tmap_1(sK2,sK1,sK5,sK2) = k3_tmap_1(sK0,sK1,sK2,sK2,sK5) ),
    inference(forward_demodulation,[],[f162,f127])).

fof(f127,plain,(
    k2_tmap_1(sK2,sK1,sK5,sK2) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f124,f66])).

fof(f124,plain,
    ( k2_tmap_1(sK2,sK1,sK5,sK2) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f123,f48])).

fof(f162,plain,(
    k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK2)) = k3_tmap_1(sK0,sK1,sK2,sK2,sK5) ),
    inference(subsumption_resolution,[],[f159,f66])).

fof(f159,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK2)) = k3_tmap_1(sK0,sK1,sK2,sK2,sK5)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f155,f48])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
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
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                 => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tmap_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:35:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.51  % (6362)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.20/0.51  % (6355)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.20/0.51  % (6357)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.51  % (6355)Refutation not found, incomplete strategy% (6355)------------------------------
% 0.20/0.51  % (6355)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (6355)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (6355)Memory used [KB]: 10618
% 0.20/0.51  % (6355)Time elapsed: 0.076 s
% 0.20/0.51  % (6355)------------------------------
% 0.20/0.51  % (6355)------------------------------
% 0.20/0.51  % (6347)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.52  % (6368)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.20/0.52  % (6349)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.52  % (6352)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.52  % (6354)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.20/0.52  % (6365)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.20/0.53  % (6360)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.20/0.53  % (6366)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.20/0.53  % (6350)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.53  % (6345)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.20/0.53  % (6356)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.20/0.54  % (6368)Refutation not found, incomplete strategy% (6368)------------------------------
% 0.20/0.54  % (6368)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (6368)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (6368)Memory used [KB]: 10618
% 0.20/0.54  % (6368)Time elapsed: 0.130 s
% 0.20/0.54  % (6368)------------------------------
% 0.20/0.54  % (6368)------------------------------
% 0.20/0.54  % (6346)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.20/0.54  % (6361)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.20/0.55  % (6348)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.55  % (6348)Refutation not found, incomplete strategy% (6348)------------------------------
% 0.20/0.55  % (6348)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (6348)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (6348)Memory used [KB]: 10618
% 0.20/0.55  % (6348)Time elapsed: 0.135 s
% 0.20/0.55  % (6348)------------------------------
% 0.20/0.55  % (6348)------------------------------
% 0.20/0.55  % (6358)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.20/0.55  % (6353)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 1.60/0.56  % (6367)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 1.60/0.56  % (6363)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 1.60/0.56  % (6359)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 1.72/0.57  % (6364)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 1.72/0.58  % (6351)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 1.72/0.60  % (6358)Refutation found. Thanks to Tanya!
% 1.72/0.60  % SZS status Theorem for theBenchmark
% 1.72/0.60  % SZS output start Proof for theBenchmark
% 1.72/0.60  fof(f930,plain,(
% 1.72/0.60    $false),
% 1.72/0.60    inference(subsumption_resolution,[],[f929,f66])).
% 1.72/0.60  fof(f66,plain,(
% 1.72/0.60    l1_pre_topc(sK2)),
% 1.72/0.60    inference(subsumption_resolution,[],[f60,f47])).
% 1.72/0.60  fof(f47,plain,(
% 1.72/0.60    l1_pre_topc(sK0)),
% 1.72/0.60    inference(cnf_transformation,[],[f13])).
% 1.72/0.60  fof(f13,plain,(
% 1.72/0.60    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.72/0.60    inference(flattening,[],[f12])).
% 1.72/0.60  fof(f12,plain,(
% 1.72/0.60    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5))) & (m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2))) & (m1_pre_topc(X4,X0) & ~v2_struct_0(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.72/0.60    inference(ennf_transformation,[],[f11])).
% 1.72/0.60  fof(f11,negated_conjecture,(
% 1.72/0.60    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)))))))))),
% 1.72/0.60    inference(negated_conjecture,[],[f10])).
% 1.72/0.60  fof(f10,conjecture,(
% 1.72/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)))))))))),
% 1.72/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_tmap_1)).
% 1.72/0.60  fof(f60,plain,(
% 1.72/0.60    ~l1_pre_topc(sK0) | l1_pre_topc(sK2)),
% 1.72/0.60    inference(resolution,[],[f49,f41])).
% 1.72/0.60  fof(f41,plain,(
% 1.72/0.60    m1_pre_topc(sK2,sK0)),
% 1.72/0.60    inference(cnf_transformation,[],[f13])).
% 1.72/0.60  fof(f49,plain,(
% 1.72/0.60    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 1.72/0.60    inference(cnf_transformation,[],[f15])).
% 1.72/0.60  fof(f15,plain,(
% 1.72/0.60    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.72/0.60    inference(ennf_transformation,[],[f2])).
% 1.72/0.60  fof(f2,axiom,(
% 1.72/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.72/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.72/0.60  fof(f929,plain,(
% 1.72/0.60    ~l1_pre_topc(sK2)),
% 1.72/0.60    inference(resolution,[],[f928,f48])).
% 1.72/0.60  fof(f48,plain,(
% 1.72/0.60    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 1.72/0.60    inference(cnf_transformation,[],[f14])).
% 1.72/0.60  fof(f14,plain,(
% 1.72/0.60    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 1.72/0.60    inference(ennf_transformation,[],[f6])).
% 1.72/0.60  fof(f6,axiom,(
% 1.72/0.60    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 1.72/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 1.72/0.60  fof(f928,plain,(
% 1.72/0.60    ~m1_pre_topc(sK2,sK2)),
% 1.72/0.60    inference(subsumption_resolution,[],[f927,f37])).
% 1.72/0.60  fof(f37,plain,(
% 1.72/0.60    m1_pre_topc(sK4,sK3)),
% 1.72/0.60    inference(cnf_transformation,[],[f13])).
% 1.72/0.60  fof(f927,plain,(
% 1.72/0.60    ~m1_pre_topc(sK4,sK3) | ~m1_pre_topc(sK2,sK2)),
% 1.72/0.60    inference(subsumption_resolution,[],[f926,f102])).
% 1.72/0.60  fof(f102,plain,(
% 1.72/0.60    m1_pre_topc(sK4,sK2)),
% 1.72/0.60    inference(subsumption_resolution,[],[f101,f77])).
% 1.72/0.60  fof(f77,plain,(
% 1.72/0.60    v2_pre_topc(sK2)),
% 1.72/0.60    inference(subsumption_resolution,[],[f76,f46])).
% 1.72/0.60  fof(f46,plain,(
% 1.72/0.60    v2_pre_topc(sK0)),
% 1.72/0.60    inference(cnf_transformation,[],[f13])).
% 1.72/0.60  fof(f76,plain,(
% 1.72/0.60    ~v2_pre_topc(sK0) | v2_pre_topc(sK2)),
% 1.72/0.60    inference(subsumption_resolution,[],[f70,f47])).
% 1.72/0.60  fof(f70,plain,(
% 1.72/0.60    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_pre_topc(sK2)),
% 1.72/0.60    inference(resolution,[],[f54,f41])).
% 1.72/0.60  fof(f54,plain,(
% 1.72/0.60    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_pre_topc(X1)) )),
% 1.72/0.60    inference(cnf_transformation,[],[f25])).
% 1.72/0.60  fof(f25,plain,(
% 1.72/0.60    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.72/0.60    inference(flattening,[],[f24])).
% 1.72/0.60  fof(f24,plain,(
% 1.72/0.60    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.72/0.60    inference(ennf_transformation,[],[f1])).
% 1.72/0.60  fof(f1,axiom,(
% 1.72/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 1.72/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 1.72/0.60  fof(f101,plain,(
% 1.72/0.60    ~v2_pre_topc(sK2) | m1_pre_topc(sK4,sK2)),
% 1.72/0.60    inference(subsumption_resolution,[],[f97,f66])).
% 1.72/0.60  fof(f97,plain,(
% 1.72/0.60    ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | m1_pre_topc(sK4,sK2)),
% 1.72/0.60    inference(resolution,[],[f87,f36])).
% 1.72/0.60  fof(f36,plain,(
% 1.72/0.60    m1_pre_topc(sK3,sK2)),
% 1.72/0.60    inference(cnf_transformation,[],[f13])).
% 1.72/0.60  fof(f87,plain,(
% 1.72/0.60    ( ! [X6] : (~m1_pre_topc(sK3,X6) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | m1_pre_topc(sK4,X6)) )),
% 1.72/0.60    inference(resolution,[],[f55,f37])).
% 1.72/0.60  fof(f55,plain,(
% 1.72/0.60    ( ! [X2,X0,X1] : (~m1_pre_topc(X2,X1) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | m1_pre_topc(X2,X0)) )),
% 1.72/0.60    inference(cnf_transformation,[],[f27])).
% 1.72/0.60  fof(f27,plain,(
% 1.72/0.60    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.72/0.60    inference(flattening,[],[f26])).
% 1.72/0.60  fof(f26,plain,(
% 1.72/0.60    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.72/0.60    inference(ennf_transformation,[],[f9])).
% 1.72/0.60  fof(f9,axiom,(
% 1.72/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 1.72/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).
% 1.72/0.60  fof(f926,plain,(
% 1.72/0.60    ~m1_pre_topc(sK4,sK2) | ~m1_pre_topc(sK4,sK3) | ~m1_pre_topc(sK2,sK2)),
% 1.72/0.60    inference(subsumption_resolution,[],[f925,f34])).
% 1.72/0.60  fof(f34,plain,(
% 1.72/0.60    ~v2_struct_0(sK4)),
% 1.72/0.60    inference(cnf_transformation,[],[f13])).
% 1.72/0.60  fof(f925,plain,(
% 1.72/0.60    v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK2) | ~m1_pre_topc(sK4,sK3) | ~m1_pre_topc(sK2,sK2)),
% 1.72/0.60    inference(subsumption_resolution,[],[f912,f719])).
% 1.72/0.60  fof(f719,plain,(
% 1.72/0.60    ~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4),k2_tmap_1(sK2,sK1,sK5,sK4))),
% 1.72/0.60    inference(backward_demodulation,[],[f167,f718])).
% 1.72/0.60  fof(f718,plain,(
% 1.72/0.60    k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4)),
% 1.72/0.60    inference(forward_demodulation,[],[f715,f362])).
% 1.72/0.60  fof(f362,plain,(
% 1.72/0.60    k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK4))),
% 1.72/0.60    inference(resolution,[],[f308,f37])).
% 1.72/0.60  fof(f308,plain,(
% 1.72/0.60    ( ! [X2] : (~m1_pre_topc(X2,sK3) | k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),X2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X2))) )),
% 1.72/0.60    inference(subsumption_resolution,[],[f307,f38])).
% 1.72/0.60  fof(f38,plain,(
% 1.72/0.60    ~v2_struct_0(sK3)),
% 1.72/0.60    inference(cnf_transformation,[],[f13])).
% 1.72/0.60  fof(f307,plain,(
% 1.72/0.60    ( ! [X2] : (v2_struct_0(sK3) | ~m1_pre_topc(X2,sK3) | k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),X2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X2))) )),
% 1.72/0.60    inference(subsumption_resolution,[],[f306,f239])).
% 1.72/0.60  fof(f239,plain,(
% 1.72/0.60    v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))),
% 1.72/0.60    inference(subsumption_resolution,[],[f238,f45])).
% 1.72/0.60  fof(f45,plain,(
% 1.72/0.60    ~v2_struct_0(sK0)),
% 1.72/0.60    inference(cnf_transformation,[],[f13])).
% 1.72/0.60  fof(f238,plain,(
% 1.72/0.60    v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | v2_struct_0(sK0)),
% 1.72/0.60    inference(subsumption_resolution,[],[f237,f32])).
% 1.72/0.60  fof(f32,plain,(
% 1.72/0.60    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 1.72/0.60    inference(cnf_transformation,[],[f13])).
% 1.72/0.60  fof(f237,plain,(
% 1.72/0.60    v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | v2_struct_0(sK0)),
% 1.72/0.60    inference(subsumption_resolution,[],[f236,f31])).
% 1.72/0.60  fof(f31,plain,(
% 1.72/0.60    v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))),
% 1.72/0.60    inference(cnf_transformation,[],[f13])).
% 1.72/0.60  fof(f236,plain,(
% 1.72/0.60    v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | v2_struct_0(sK0)),
% 1.72/0.60    inference(subsumption_resolution,[],[f235,f30])).
% 1.72/0.60  fof(f30,plain,(
% 1.72/0.60    v1_funct_1(sK5)),
% 1.72/0.60    inference(cnf_transformation,[],[f13])).
% 1.72/0.60  fof(f235,plain,(
% 1.72/0.60    v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | v2_struct_0(sK0)),
% 1.72/0.60    inference(subsumption_resolution,[],[f234,f39])).
% 1.72/0.60  fof(f39,plain,(
% 1.72/0.60    m1_pre_topc(sK3,sK0)),
% 1.72/0.60    inference(cnf_transformation,[],[f13])).
% 1.72/0.60  fof(f234,plain,(
% 1.72/0.60    v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | v2_struct_0(sK0)),
% 1.72/0.60    inference(subsumption_resolution,[],[f233,f41])).
% 1.72/0.60  fof(f233,plain,(
% 1.72/0.60    v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | v2_struct_0(sK0)),
% 1.72/0.60    inference(subsumption_resolution,[],[f232,f44])).
% 1.72/0.60  fof(f44,plain,(
% 1.72/0.60    l1_pre_topc(sK1)),
% 1.72/0.60    inference(cnf_transformation,[],[f13])).
% 1.72/0.60  fof(f232,plain,(
% 1.72/0.60    v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | v2_struct_0(sK0)),
% 1.72/0.60    inference(subsumption_resolution,[],[f231,f43])).
% 1.72/0.60  fof(f43,plain,(
% 1.72/0.60    v2_pre_topc(sK1)),
% 1.72/0.60    inference(cnf_transformation,[],[f13])).
% 1.72/0.60  fof(f231,plain,(
% 1.72/0.60    v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | v2_struct_0(sK0)),
% 1.72/0.60    inference(subsumption_resolution,[],[f230,f42])).
% 1.72/0.60  fof(f42,plain,(
% 1.72/0.60    ~v2_struct_0(sK1)),
% 1.72/0.60    inference(cnf_transformation,[],[f13])).
% 1.72/0.60  fof(f230,plain,(
% 1.72/0.60    v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | v2_struct_0(sK0)),
% 1.72/0.60    inference(subsumption_resolution,[],[f229,f47])).
% 1.72/0.60  fof(f229,plain,(
% 1.72/0.60    v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | v2_struct_0(sK0)),
% 1.72/0.60    inference(subsumption_resolution,[],[f212,f46])).
% 1.72/0.60  fof(f212,plain,(
% 1.72/0.60    v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | v2_struct_0(sK0)),
% 1.72/0.60    inference(superposition,[],[f57,f164])).
% 1.72/0.60  fof(f164,plain,(
% 1.72/0.60    k3_tmap_1(sK0,sK1,sK2,sK3,sK5) = k2_tmap_1(sK2,sK1,sK5,sK3)),
% 1.72/0.60    inference(forward_demodulation,[],[f160,f125])).
% 1.72/0.60  fof(f125,plain,(
% 1.72/0.60    k2_tmap_1(sK2,sK1,sK5,sK3) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK3))),
% 1.72/0.60    inference(resolution,[],[f123,f36])).
% 1.72/0.60  fof(f123,plain,(
% 1.72/0.60    ( ! [X0] : (~m1_pre_topc(X0,sK2) | k2_tmap_1(sK2,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0))) )),
% 1.72/0.60    inference(subsumption_resolution,[],[f122,f40])).
% 1.72/0.60  fof(f40,plain,(
% 1.72/0.60    ~v2_struct_0(sK2)),
% 1.72/0.60    inference(cnf_transformation,[],[f13])).
% 1.72/0.60  fof(f122,plain,(
% 1.72/0.60    ( ! [X0] : (v2_struct_0(sK2) | ~m1_pre_topc(X0,sK2) | k2_tmap_1(sK2,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0))) )),
% 1.72/0.60    inference(subsumption_resolution,[],[f121,f31])).
% 1.72/0.60  fof(f121,plain,(
% 1.72/0.60    ( ! [X0] : (~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | v2_struct_0(sK2) | ~m1_pre_topc(X0,sK2) | k2_tmap_1(sK2,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0))) )),
% 1.72/0.60    inference(subsumption_resolution,[],[f120,f30])).
% 1.72/0.60  fof(f120,plain,(
% 1.72/0.60    ( ! [X0] : (~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | v2_struct_0(sK2) | ~m1_pre_topc(X0,sK2) | k2_tmap_1(sK2,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0))) )),
% 1.72/0.60    inference(subsumption_resolution,[],[f119,f44])).
% 1.72/0.60  fof(f119,plain,(
% 1.72/0.60    ( ! [X0] : (~l1_pre_topc(sK1) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | v2_struct_0(sK2) | ~m1_pre_topc(X0,sK2) | k2_tmap_1(sK2,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0))) )),
% 1.72/0.60    inference(subsumption_resolution,[],[f118,f43])).
% 1.72/0.60  fof(f118,plain,(
% 1.72/0.60    ( ! [X0] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | v2_struct_0(sK2) | ~m1_pre_topc(X0,sK2) | k2_tmap_1(sK2,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0))) )),
% 1.72/0.60    inference(subsumption_resolution,[],[f117,f42])).
% 1.72/0.60  fof(f117,plain,(
% 1.72/0.60    ( ! [X0] : (v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | v2_struct_0(sK2) | ~m1_pre_topc(X0,sK2) | k2_tmap_1(sK2,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0))) )),
% 1.72/0.60    inference(subsumption_resolution,[],[f116,f66])).
% 1.72/0.60  fof(f116,plain,(
% 1.72/0.60    ( ! [X0] : (~l1_pre_topc(sK2) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | v2_struct_0(sK2) | ~m1_pre_topc(X0,sK2) | k2_tmap_1(sK2,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0))) )),
% 1.72/0.60    inference(subsumption_resolution,[],[f115,f77])).
% 1.72/0.60  fof(f115,plain,(
% 1.72/0.60    ( ! [X0] : (~v2_pre_topc(sK2) | ~l1_pre_topc(sK2) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | v2_struct_0(sK2) | ~m1_pre_topc(X0,sK2) | k2_tmap_1(sK2,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0))) )),
% 1.72/0.60    inference(resolution,[],[f53,f32])).
% 1.72/0.60  fof(f53,plain,(
% 1.72/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | v2_struct_0(X0) | ~m1_pre_topc(X3,X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))) )),
% 1.72/0.60    inference(cnf_transformation,[],[f23])).
% 1.72/0.60  fof(f23,plain,(
% 1.72/0.60    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.72/0.60    inference(flattening,[],[f22])).
% 1.72/0.60  fof(f22,plain,(
% 1.72/0.60    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.72/0.60    inference(ennf_transformation,[],[f3])).
% 1.72/0.60  fof(f3,axiom,(
% 1.72/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 1.72/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).
% 1.72/0.60  fof(f160,plain,(
% 1.72/0.60    k3_tmap_1(sK0,sK1,sK2,sK3,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK3))),
% 1.72/0.60    inference(resolution,[],[f155,f36])).
% 1.72/0.60  fof(f155,plain,(
% 1.72/0.60    ( ! [X0] : (~m1_pre_topc(X0,sK2) | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK2,X0,sK5)) )),
% 1.72/0.60    inference(subsumption_resolution,[],[f154,f45])).
% 1.72/0.60  fof(f154,plain,(
% 1.72/0.60    ( ! [X0] : (v2_struct_0(sK0) | ~m1_pre_topc(X0,sK2) | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK2,X0,sK5)) )),
% 1.72/0.60    inference(subsumption_resolution,[],[f153,f46])).
% 1.72/0.60  fof(f153,plain,(
% 1.72/0.60    ( ! [X0] : (~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_pre_topc(X0,sK2) | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK2,X0,sK5)) )),
% 1.72/0.60    inference(subsumption_resolution,[],[f150,f47])).
% 1.72/0.60  fof(f150,plain,(
% 1.72/0.60    ( ! [X0] : (~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_pre_topc(X0,sK2) | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK2,X0,sK5)) )),
% 1.72/0.60    inference(resolution,[],[f146,f41])).
% 1.72/0.60  fof(f146,plain,(
% 1.72/0.60    ( ! [X0,X1] : (~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X1,sK2) | k3_tmap_1(X0,sK1,sK2,X1,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X1))) )),
% 1.72/0.60    inference(subsumption_resolution,[],[f145,f55])).
% 1.72/0.60  fof(f145,plain,(
% 1.72/0.60    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK2,X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0) | ~m1_pre_topc(X1,sK2) | k3_tmap_1(X0,sK1,sK2,X1,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X1))) )),
% 1.72/0.60    inference(subsumption_resolution,[],[f144,f31])).
% 1.72/0.60  fof(f144,plain,(
% 1.72/0.60    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK2,X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | v2_struct_0(X0) | ~m1_pre_topc(X1,sK2) | k3_tmap_1(X0,sK1,sK2,X1,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X1))) )),
% 1.72/0.60    inference(subsumption_resolution,[],[f143,f30])).
% 1.72/0.60  fof(f143,plain,(
% 1.72/0.60    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK2,X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | v2_struct_0(X0) | ~m1_pre_topc(X1,sK2) | k3_tmap_1(X0,sK1,sK2,X1,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X1))) )),
% 1.72/0.60    inference(subsumption_resolution,[],[f142,f44])).
% 1.72/0.60  fof(f142,plain,(
% 1.72/0.60    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~l1_pre_topc(sK1) | ~m1_pre_topc(sK2,X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | v2_struct_0(X0) | ~m1_pre_topc(X1,sK2) | k3_tmap_1(X0,sK1,sK2,X1,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X1))) )),
% 1.72/0.60    inference(subsumption_resolution,[],[f141,f43])).
% 1.72/0.60  fof(f141,plain,(
% 1.72/0.60    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_pre_topc(sK2,X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | v2_struct_0(X0) | ~m1_pre_topc(X1,sK2) | k3_tmap_1(X0,sK1,sK2,X1,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X1))) )),
% 1.72/0.60    inference(subsumption_resolution,[],[f138,f42])).
% 1.72/0.60  fof(f138,plain,(
% 1.72/0.60    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_pre_topc(sK2,X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | v2_struct_0(X0) | ~m1_pre_topc(X1,sK2) | k3_tmap_1(X0,sK1,sK2,X1,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X1))) )),
% 1.72/0.60    inference(resolution,[],[f50,f32])).
% 1.72/0.60  fof(f50,plain,(
% 1.72/0.60    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | v2_struct_0(X0) | ~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))) )),
% 1.72/0.60    inference(cnf_transformation,[],[f17])).
% 1.72/0.60  fof(f17,plain,(
% 1.72/0.60    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.72/0.60    inference(flattening,[],[f16])).
% 1.72/0.60  fof(f16,plain,(
% 1.72/0.60    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.72/0.60    inference(ennf_transformation,[],[f4])).
% 1.72/0.60  fof(f4,axiom,(
% 1.72/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 1.72/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).
% 1.72/0.60  fof(f57,plain,(
% 1.72/0.60    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | v2_struct_0(X0)) )),
% 1.72/0.60    inference(cnf_transformation,[],[f29])).
% 1.72/0.60  fof(f29,plain,(
% 1.72/0.60    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.72/0.60    inference(flattening,[],[f28])).
% 1.72/0.60  fof(f28,plain,(
% 1.72/0.60    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.72/0.60    inference(ennf_transformation,[],[f5])).
% 1.72/0.60  fof(f5,axiom,(
% 1.72/0.60    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 1.72/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_tmap_1)).
% 1.72/0.60  fof(f306,plain,(
% 1.72/0.60    ( ! [X2] : (~v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | v2_struct_0(sK3) | ~m1_pre_topc(X2,sK3) | k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),X2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X2))) )),
% 1.72/0.60    inference(subsumption_resolution,[],[f305,f217])).
% 1.72/0.60  fof(f217,plain,(
% 1.72/0.60    v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3))),
% 1.72/0.60    inference(subsumption_resolution,[],[f216,f46])).
% 1.72/0.60  fof(f216,plain,(
% 1.72/0.60    v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) | ~v2_pre_topc(sK0)),
% 1.72/0.60    inference(subsumption_resolution,[],[f215,f45])).
% 1.72/0.60  fof(f215,plain,(
% 1.72/0.60    v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) | v2_struct_0(sK0) | ~v2_pre_topc(sK0)),
% 1.72/0.60    inference(subsumption_resolution,[],[f214,f39])).
% 1.72/0.60  fof(f214,plain,(
% 1.72/0.60    v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK0) | ~v2_pre_topc(sK0)),
% 1.72/0.60    inference(subsumption_resolution,[],[f213,f41])).
% 1.72/0.60  fof(f213,plain,(
% 1.72/0.60    v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) | ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK0) | ~v2_pre_topc(sK0)),
% 1.72/0.60    inference(subsumption_resolution,[],[f210,f47])).
% 1.72/0.60  fof(f210,plain,(
% 1.72/0.60    v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK0) | ~v2_pre_topc(sK0)),
% 1.72/0.60    inference(superposition,[],[f114,f164])).
% 1.72/0.60  fof(f114,plain,(
% 1.72/0.60    ( ! [X0,X1] : (v1_funct_1(k3_tmap_1(X0,sK1,sK2,X1,sK5)) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK2,X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0)) )),
% 1.72/0.60    inference(subsumption_resolution,[],[f113,f31])).
% 1.72/0.60  fof(f113,plain,(
% 1.72/0.60    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK2,X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | v2_struct_0(X0) | v1_funct_1(k3_tmap_1(X0,sK1,sK2,X1,sK5))) )),
% 1.72/0.60    inference(subsumption_resolution,[],[f112,f30])).
% 1.72/0.60  fof(f112,plain,(
% 1.72/0.60    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK2,X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | v2_struct_0(X0) | v1_funct_1(k3_tmap_1(X0,sK1,sK2,X1,sK5))) )),
% 1.72/0.60    inference(subsumption_resolution,[],[f111,f44])).
% 1.72/0.61  fof(f111,plain,(
% 1.72/0.61    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~l1_pre_topc(sK1) | ~m1_pre_topc(sK2,X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | v2_struct_0(X0) | v1_funct_1(k3_tmap_1(X0,sK1,sK2,X1,sK5))) )),
% 1.72/0.61    inference(subsumption_resolution,[],[f110,f43])).
% 1.72/0.61  fof(f110,plain,(
% 1.72/0.61    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_pre_topc(sK2,X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | v2_struct_0(X0) | v1_funct_1(k3_tmap_1(X0,sK1,sK2,X1,sK5))) )),
% 1.72/0.61    inference(subsumption_resolution,[],[f109,f42])).
% 1.72/0.61  fof(f109,plain,(
% 1.72/0.61    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_pre_topc(sK2,X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | v2_struct_0(X0) | v1_funct_1(k3_tmap_1(X0,sK1,sK2,X1,sK5))) )),
% 1.72/0.61    inference(resolution,[],[f56,f32])).
% 1.72/0.61  fof(f56,plain,(
% 1.72/0.61    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | v2_struct_0(X0) | v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) )),
% 1.72/0.61    inference(cnf_transformation,[],[f29])).
% 1.72/0.61  fof(f305,plain,(
% 1.72/0.61    ( ! [X2] : (~v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) | ~v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | v2_struct_0(sK3) | ~m1_pre_topc(X2,sK3) | k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),X2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X2))) )),
% 1.72/0.61    inference(subsumption_resolution,[],[f304,f44])).
% 1.72/0.61  fof(f304,plain,(
% 1.72/0.61    ( ! [X2] : (~l1_pre_topc(sK1) | ~v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) | ~v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | v2_struct_0(sK3) | ~m1_pre_topc(X2,sK3) | k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),X2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X2))) )),
% 1.72/0.61    inference(subsumption_resolution,[],[f303,f43])).
% 1.72/0.61  fof(f303,plain,(
% 1.72/0.61    ( ! [X2] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) | ~v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | v2_struct_0(sK3) | ~m1_pre_topc(X2,sK3) | k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),X2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X2))) )),
% 1.72/0.61    inference(subsumption_resolution,[],[f302,f42])).
% 1.72/0.61  fof(f302,plain,(
% 1.72/0.61    ( ! [X2] : (v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) | ~v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | v2_struct_0(sK3) | ~m1_pre_topc(X2,sK3) | k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),X2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X2))) )),
% 1.72/0.61    inference(subsumption_resolution,[],[f301,f67])).
% 1.72/0.61  fof(f67,plain,(
% 1.72/0.61    l1_pre_topc(sK3)),
% 1.72/0.61    inference(subsumption_resolution,[],[f61,f66])).
% 1.72/0.61  fof(f61,plain,(
% 1.72/0.61    ~l1_pre_topc(sK2) | l1_pre_topc(sK3)),
% 1.72/0.61    inference(resolution,[],[f49,f36])).
% 1.72/0.61  fof(f301,plain,(
% 1.72/0.61    ( ! [X2] : (~l1_pre_topc(sK3) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) | ~v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | v2_struct_0(sK3) | ~m1_pre_topc(X2,sK3) | k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),X2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X2))) )),
% 1.72/0.61    inference(subsumption_resolution,[],[f293,f79])).
% 1.72/0.61  fof(f79,plain,(
% 1.72/0.61    v2_pre_topc(sK3)),
% 1.72/0.61    inference(subsumption_resolution,[],[f78,f77])).
% 1.72/0.61  fof(f78,plain,(
% 1.72/0.61    ~v2_pre_topc(sK2) | v2_pre_topc(sK3)),
% 1.72/0.61    inference(subsumption_resolution,[],[f71,f66])).
% 1.72/0.61  fof(f71,plain,(
% 1.72/0.61    ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_pre_topc(sK3)),
% 1.72/0.61    inference(resolution,[],[f54,f36])).
% 1.72/0.61  fof(f293,plain,(
% 1.72/0.61    ( ! [X2] : (~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) | ~v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | v2_struct_0(sK3) | ~m1_pre_topc(X2,sK3) | k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),X2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X2))) )),
% 1.72/0.61    inference(resolution,[],[f228,f53])).
% 1.72/0.61  fof(f228,plain,(
% 1.72/0.61    m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 1.72/0.61    inference(subsumption_resolution,[],[f227,f45])).
% 1.72/0.61  fof(f227,plain,(
% 1.72/0.61    m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | v2_struct_0(sK0)),
% 1.72/0.61    inference(subsumption_resolution,[],[f226,f32])).
% 1.72/0.61  fof(f226,plain,(
% 1.72/0.61    m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | v2_struct_0(sK0)),
% 1.72/0.61    inference(subsumption_resolution,[],[f225,f31])).
% 1.72/0.61  fof(f225,plain,(
% 1.72/0.61    m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | v2_struct_0(sK0)),
% 1.72/0.61    inference(subsumption_resolution,[],[f224,f30])).
% 1.72/0.61  fof(f224,plain,(
% 1.72/0.61    m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | v2_struct_0(sK0)),
% 1.72/0.61    inference(subsumption_resolution,[],[f223,f39])).
% 1.72/0.61  fof(f223,plain,(
% 1.72/0.61    m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | v2_struct_0(sK0)),
% 1.72/0.61    inference(subsumption_resolution,[],[f222,f41])).
% 1.72/0.61  fof(f222,plain,(
% 1.72/0.61    m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | v2_struct_0(sK0)),
% 1.72/0.61    inference(subsumption_resolution,[],[f221,f44])).
% 1.72/0.61  fof(f221,plain,(
% 1.72/0.61    m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~l1_pre_topc(sK1) | ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | v2_struct_0(sK0)),
% 1.72/0.61    inference(subsumption_resolution,[],[f220,f43])).
% 1.72/0.61  fof(f220,plain,(
% 1.72/0.61    m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | v2_struct_0(sK0)),
% 1.72/0.61    inference(subsumption_resolution,[],[f219,f42])).
% 1.72/0.61  fof(f219,plain,(
% 1.72/0.61    m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | v2_struct_0(sK0)),
% 1.72/0.61    inference(subsumption_resolution,[],[f218,f47])).
% 1.72/0.61  fof(f218,plain,(
% 1.72/0.61    m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | v2_struct_0(sK0)),
% 1.72/0.61    inference(subsumption_resolution,[],[f211,f46])).
% 1.72/0.61  fof(f211,plain,(
% 1.72/0.61    m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | v2_struct_0(sK0)),
% 1.72/0.61    inference(superposition,[],[f58,f164])).
% 1.72/0.61  fof(f58,plain,(
% 1.72/0.61    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | v2_struct_0(X0)) )),
% 1.72/0.61    inference(cnf_transformation,[],[f29])).
% 1.72/0.61  fof(f715,plain,(
% 1.72/0.61    k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK4))),
% 1.72/0.61    inference(resolution,[],[f589,f37])).
% 1.72/0.61  fof(f589,plain,(
% 1.72/0.61    ( ! [X1] : (~m1_pre_topc(X1,sK3) | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X1)) = k3_tmap_1(sK0,sK1,sK3,X1,k2_tmap_1(sK2,sK1,sK5,sK3))) )),
% 1.72/0.61    inference(subsumption_resolution,[],[f588,f45])).
% 1.72/0.61  fof(f588,plain,(
% 1.72/0.61    ( ! [X1] : (v2_struct_0(sK0) | ~m1_pre_topc(X1,sK3) | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X1)) = k3_tmap_1(sK0,sK1,sK3,X1,k2_tmap_1(sK2,sK1,sK5,sK3))) )),
% 1.72/0.61    inference(subsumption_resolution,[],[f587,f46])).
% 1.72/0.61  fof(f587,plain,(
% 1.72/0.61    ( ! [X1] : (~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_pre_topc(X1,sK3) | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X1)) = k3_tmap_1(sK0,sK1,sK3,X1,k2_tmap_1(sK2,sK1,sK5,sK3))) )),
% 1.72/0.61    inference(subsumption_resolution,[],[f581,f47])).
% 1.72/0.61  fof(f581,plain,(
% 1.72/0.61    ( ! [X1] : (~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_pre_topc(X1,sK3) | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X1)) = k3_tmap_1(sK0,sK1,sK3,X1,k2_tmap_1(sK2,sK1,sK5,sK3))) )),
% 1.72/0.61    inference(resolution,[],[f300,f39])).
% 1.72/0.61  fof(f300,plain,(
% 1.72/0.61    ( ! [X0,X1] : (~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X1,sK3) | k3_tmap_1(X0,sK1,sK3,X1,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X1))) )),
% 1.72/0.61    inference(subsumption_resolution,[],[f299,f55])).
% 1.72/0.61  fof(f299,plain,(
% 1.72/0.61    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK3,X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0) | ~m1_pre_topc(X1,sK3) | k3_tmap_1(X0,sK1,sK3,X1,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X1))) )),
% 1.72/0.61    inference(subsumption_resolution,[],[f298,f239])).
% 1.72/0.61  fof(f298,plain,(
% 1.72/0.61    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK3,X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | v2_struct_0(X0) | ~m1_pre_topc(X1,sK3) | k3_tmap_1(X0,sK1,sK3,X1,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X1))) )),
% 1.72/0.61    inference(subsumption_resolution,[],[f297,f217])).
% 1.72/0.61  fof(f297,plain,(
% 1.72/0.61    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK3,X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) | ~v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | v2_struct_0(X0) | ~m1_pre_topc(X1,sK3) | k3_tmap_1(X0,sK1,sK3,X1,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X1))) )),
% 1.72/0.61    inference(subsumption_resolution,[],[f296,f44])).
% 1.72/0.61  fof(f296,plain,(
% 1.72/0.61    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~l1_pre_topc(sK1) | ~m1_pre_topc(sK3,X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) | ~v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | v2_struct_0(X0) | ~m1_pre_topc(X1,sK3) | k3_tmap_1(X0,sK1,sK3,X1,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X1))) )),
% 1.72/0.61    inference(subsumption_resolution,[],[f295,f43])).
% 1.72/0.61  fof(f295,plain,(
% 1.72/0.61    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_pre_topc(sK3,X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) | ~v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | v2_struct_0(X0) | ~m1_pre_topc(X1,sK3) | k3_tmap_1(X0,sK1,sK3,X1,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X1))) )),
% 1.72/0.61    inference(subsumption_resolution,[],[f292,f42])).
% 1.72/0.61  fof(f292,plain,(
% 1.72/0.61    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_pre_topc(sK3,X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) | ~v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | v2_struct_0(X0) | ~m1_pre_topc(X1,sK3) | k3_tmap_1(X0,sK1,sK3,X1,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X1))) )),
% 1.72/0.61    inference(resolution,[],[f228,f50])).
% 1.72/0.61  fof(f167,plain,(
% 1.72/0.61    ~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)),k2_tmap_1(sK2,sK1,sK5,sK4))),
% 1.72/0.61    inference(backward_demodulation,[],[f165,f166])).
% 1.72/0.61  fof(f166,plain,(
% 1.72/0.61    k3_tmap_1(sK0,sK1,sK2,sK4,sK5) = k2_tmap_1(sK2,sK1,sK5,sK4)),
% 1.72/0.61    inference(forward_demodulation,[],[f161,f126])).
% 1.72/0.61  fof(f126,plain,(
% 1.72/0.61    k2_tmap_1(sK2,sK1,sK5,sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK4))),
% 1.72/0.61    inference(resolution,[],[f123,f102])).
% 1.72/0.61  fof(f161,plain,(
% 1.72/0.61    k3_tmap_1(sK0,sK1,sK2,sK4,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK4))),
% 1.72/0.61    inference(resolution,[],[f155,f102])).
% 1.72/0.61  fof(f165,plain,(
% 1.72/0.61    ~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)),k3_tmap_1(sK0,sK1,sK2,sK4,sK5))),
% 1.72/0.61    inference(backward_demodulation,[],[f33,f164])).
% 1.72/0.61  fof(f33,plain,(
% 1.72/0.61    ~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)),k3_tmap_1(sK0,sK1,sK2,sK4,sK5))),
% 1.72/0.61    inference(cnf_transformation,[],[f13])).
% 1.72/0.61  fof(f912,plain,(
% 1.72/0.61    r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4),k2_tmap_1(sK2,sK1,sK5,sK4)) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK2) | ~m1_pre_topc(sK4,sK3) | ~m1_pre_topc(sK2,sK2)),
% 1.72/0.61    inference(superposition,[],[f830,f597])).
% 1.72/0.61  fof(f597,plain,(
% 1.72/0.61    k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4) = k3_tmap_1(sK2,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3))),
% 1.72/0.61    inference(forward_demodulation,[],[f594,f362])).
% 1.72/0.61  fof(f594,plain,(
% 1.72/0.61    k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK4)) = k3_tmap_1(sK2,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3))),
% 1.72/0.61    inference(resolution,[],[f586,f37])).
% 1.72/0.61  fof(f586,plain,(
% 1.72/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X0)) = k3_tmap_1(sK2,sK1,sK3,X0,k2_tmap_1(sK2,sK1,sK5,sK3))) )),
% 1.72/0.61    inference(subsumption_resolution,[],[f585,f40])).
% 1.72/0.61  fof(f585,plain,(
% 1.72/0.61    ( ! [X0] : (v2_struct_0(sK2) | ~m1_pre_topc(X0,sK3) | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X0)) = k3_tmap_1(sK2,sK1,sK3,X0,k2_tmap_1(sK2,sK1,sK5,sK3))) )),
% 1.72/0.61    inference(subsumption_resolution,[],[f584,f77])).
% 1.72/0.61  fof(f584,plain,(
% 1.72/0.61    ( ! [X0] : (~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~m1_pre_topc(X0,sK3) | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X0)) = k3_tmap_1(sK2,sK1,sK3,X0,k2_tmap_1(sK2,sK1,sK5,sK3))) )),
% 1.72/0.61    inference(subsumption_resolution,[],[f580,f66])).
% 1.72/0.61  fof(f580,plain,(
% 1.72/0.61    ( ! [X0] : (~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~m1_pre_topc(X0,sK3) | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X0)) = k3_tmap_1(sK2,sK1,sK3,X0,k2_tmap_1(sK2,sK1,sK5,sK3))) )),
% 1.72/0.61    inference(resolution,[],[f300,f36])).
% 1.72/0.61  fof(f830,plain,(
% 1.72/0.61    ( ! [X0] : (r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK3,X0,k2_tmap_1(sK2,sK1,sK5,sK3)),k2_tmap_1(sK2,sK1,sK5,X0)) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK2) | ~m1_pre_topc(X0,sK3) | ~m1_pre_topc(sK2,sK2)) )),
% 1.72/0.61    inference(subsumption_resolution,[],[f829,f40])).
% 1.72/0.61  fof(f829,plain,(
% 1.72/0.61    ( ! [X0] : (~m1_pre_topc(sK2,sK2) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK2) | v2_struct_0(sK2) | ~m1_pre_topc(X0,sK3) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK3,X0,k2_tmap_1(sK2,sK1,sK5,sK3)),k2_tmap_1(sK2,sK1,sK5,X0))) )),
% 1.72/0.61    inference(subsumption_resolution,[],[f828,f228])).
% 1.72/0.61  fof(f828,plain,(
% 1.72/0.61    ( ! [X0] : (~m1_pre_topc(sK2,sK2) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK2) | ~m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | v2_struct_0(sK2) | ~m1_pre_topc(X0,sK3) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK3,X0,k2_tmap_1(sK2,sK1,sK5,sK3)),k2_tmap_1(sK2,sK1,sK5,X0))) )),
% 1.72/0.61    inference(subsumption_resolution,[],[f827,f239])).
% 1.72/0.61  fof(f827,plain,(
% 1.72/0.61    ( ! [X0] : (~m1_pre_topc(sK2,sK2) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK2) | ~v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | v2_struct_0(sK2) | ~m1_pre_topc(X0,sK3) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK3,X0,k2_tmap_1(sK2,sK1,sK5,sK3)),k2_tmap_1(sK2,sK1,sK5,X0))) )),
% 1.72/0.61    inference(subsumption_resolution,[],[f826,f217])).
% 1.72/0.61  fof(f826,plain,(
% 1.72/0.61    ( ! [X0] : (~m1_pre_topc(sK2,sK2) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK2) | ~v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) | ~v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | v2_struct_0(sK2) | ~m1_pre_topc(X0,sK3) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK3,X0,k2_tmap_1(sK2,sK1,sK5,sK3)),k2_tmap_1(sK2,sK1,sK5,X0))) )),
% 1.72/0.61    inference(subsumption_resolution,[],[f825,f32])).
% 1.72/0.61  fof(f825,plain,(
% 1.72/0.61    ( ! [X0] : (~m1_pre_topc(sK2,sK2) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK2) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) | ~v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | v2_struct_0(sK2) | ~m1_pre_topc(X0,sK3) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK3,X0,k2_tmap_1(sK2,sK1,sK5,sK3)),k2_tmap_1(sK2,sK1,sK5,X0))) )),
% 1.72/0.61    inference(subsumption_resolution,[],[f824,f31])).
% 1.72/0.61  fof(f824,plain,(
% 1.72/0.61    ( ! [X0] : (~m1_pre_topc(sK2,sK2) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK2) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) | ~v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | v2_struct_0(sK2) | ~m1_pre_topc(X0,sK3) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK3,X0,k2_tmap_1(sK2,sK1,sK5,sK3)),k2_tmap_1(sK2,sK1,sK5,X0))) )),
% 1.72/0.61    inference(subsumption_resolution,[],[f823,f30])).
% 1.72/0.61  fof(f823,plain,(
% 1.72/0.61    ( ! [X0] : (~m1_pre_topc(sK2,sK2) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK2) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) | ~v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | v2_struct_0(sK2) | ~m1_pre_topc(X0,sK3) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK3,X0,k2_tmap_1(sK2,sK1,sK5,sK3)),k2_tmap_1(sK2,sK1,sK5,X0))) )),
% 1.72/0.61    inference(subsumption_resolution,[],[f822,f36])).
% 1.72/0.61  fof(f822,plain,(
% 1.72/0.61    ( ! [X0] : (~m1_pre_topc(sK2,sK2) | ~m1_pre_topc(sK3,sK2) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK2) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) | ~v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | v2_struct_0(sK2) | ~m1_pre_topc(X0,sK3) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK3,X0,k2_tmap_1(sK2,sK1,sK5,sK3)),k2_tmap_1(sK2,sK1,sK5,X0))) )),
% 1.72/0.61    inference(subsumption_resolution,[],[f821,f38])).
% 1.72/0.61  fof(f821,plain,(
% 1.72/0.61    ( ! [X0] : (~m1_pre_topc(sK2,sK2) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK2) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK2) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) | ~v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | v2_struct_0(sK2) | ~m1_pre_topc(X0,sK3) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK3,X0,k2_tmap_1(sK2,sK1,sK5,sK3)),k2_tmap_1(sK2,sK1,sK5,X0))) )),
% 1.72/0.61    inference(subsumption_resolution,[],[f820,f44])).
% 1.72/0.61  fof(f820,plain,(
% 1.72/0.61    ( ! [X0] : (~m1_pre_topc(sK2,sK2) | ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK2) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK2) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) | ~v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | v2_struct_0(sK2) | ~m1_pre_topc(X0,sK3) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK3,X0,k2_tmap_1(sK2,sK1,sK5,sK3)),k2_tmap_1(sK2,sK1,sK5,X0))) )),
% 1.72/0.61    inference(subsumption_resolution,[],[f819,f43])).
% 1.72/0.61  fof(f819,plain,(
% 1.72/0.61    ( ! [X0] : (~m1_pre_topc(sK2,sK2) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK2) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK2) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) | ~v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | v2_struct_0(sK2) | ~m1_pre_topc(X0,sK3) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK3,X0,k2_tmap_1(sK2,sK1,sK5,sK3)),k2_tmap_1(sK2,sK1,sK5,X0))) )),
% 1.72/0.61    inference(subsumption_resolution,[],[f818,f42])).
% 1.72/0.61  fof(f818,plain,(
% 1.72/0.61    ( ! [X0] : (~m1_pre_topc(sK2,sK2) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK2) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK2) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) | ~v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | v2_struct_0(sK2) | ~m1_pre_topc(X0,sK3) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK3,X0,k2_tmap_1(sK2,sK1,sK5,sK3)),k2_tmap_1(sK2,sK1,sK5,X0))) )),
% 1.72/0.61    inference(subsumption_resolution,[],[f817,f66])).
% 1.72/0.61  fof(f817,plain,(
% 1.72/0.61    ( ! [X0] : (~m1_pre_topc(sK2,sK2) | ~l1_pre_topc(sK2) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK2) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK2) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) | ~v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | v2_struct_0(sK2) | ~m1_pre_topc(X0,sK3) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK3,X0,k2_tmap_1(sK2,sK1,sK5,sK3)),k2_tmap_1(sK2,sK1,sK5,X0))) )),
% 1.72/0.61    inference(subsumption_resolution,[],[f816,f77])).
% 1.72/0.61  fof(f816,plain,(
% 1.72/0.61    ( ! [X0] : (~m1_pre_topc(sK2,sK2) | ~v2_pre_topc(sK2) | ~l1_pre_topc(sK2) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK2) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK2) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) | ~v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | v2_struct_0(sK2) | ~m1_pre_topc(X0,sK3) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK3,X0,k2_tmap_1(sK2,sK1,sK5,sK3)),k2_tmap_1(sK2,sK1,sK5,X0))) )),
% 1.72/0.61    inference(resolution,[],[f799,f51])).
% 1.72/0.61  fof(f51,plain,(
% 1.72/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | v2_struct_0(X0) | ~m1_pre_topc(X3,X2) | r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3))) )),
% 1.72/0.61    inference(cnf_transformation,[],[f19])).
% 1.72/0.61  fof(f19,plain,(
% 1.72/0.61    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3)) | ~m1_pre_topc(X3,X2) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.72/0.61    inference(flattening,[],[f18])).
% 1.72/0.61  fof(f18,plain,(
% 1.72/0.61    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3)) | (~m1_pre_topc(X3,X2) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2)))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.72/0.61    inference(ennf_transformation,[],[f8])).
% 1.72/0.61  fof(f8,axiom,(
% 1.72/0.61    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => ((m1_pre_topc(X3,X2) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2))) => r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3)))))))))),
% 1.72/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tmap_1)).
% 1.72/0.61  fof(f799,plain,(
% 1.72/0.61    r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),k2_tmap_1(sK2,sK1,sK5,sK3)) | ~m1_pre_topc(sK2,sK2)),
% 1.72/0.61    inference(subsumption_resolution,[],[f798,f36])).
% 1.72/0.61  fof(f798,plain,(
% 1.72/0.61    r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),k2_tmap_1(sK2,sK1,sK5,sK3)) | ~m1_pre_topc(sK3,sK2) | ~m1_pre_topc(sK2,sK2)),
% 1.72/0.61    inference(subsumption_resolution,[],[f784,f38])).
% 1.72/0.61  fof(f784,plain,(
% 1.72/0.61    r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),k2_tmap_1(sK2,sK1,sK5,sK3)) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK2) | ~m1_pre_topc(sK2,sK2)),
% 1.72/0.61    inference(superposition,[],[f763,f341])).
% 1.72/0.61  fof(f341,plain,(
% 1.72/0.61    k2_tmap_1(sK2,sK1,sK5,sK3) = k3_tmap_1(sK2,sK1,sK2,sK3,sK5)),
% 1.72/0.61    inference(forward_demodulation,[],[f337,f125])).
% 1.72/0.61  fof(f337,plain,(
% 1.72/0.61    k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK3)) = k3_tmap_1(sK2,sK1,sK2,sK3,sK5)),
% 1.72/0.61    inference(resolution,[],[f158,f36])).
% 1.72/0.61  fof(f158,plain,(
% 1.72/0.61    ( ! [X1] : (~m1_pre_topc(X1,sK2) | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X1)) = k3_tmap_1(sK2,sK1,sK2,X1,sK5)) )),
% 1.72/0.61    inference(subsumption_resolution,[],[f157,f40])).
% 1.72/0.61  fof(f157,plain,(
% 1.72/0.61    ( ! [X1] : (v2_struct_0(sK2) | ~m1_pre_topc(X1,sK2) | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X1)) = k3_tmap_1(sK2,sK1,sK2,X1,sK5)) )),
% 1.72/0.61    inference(subsumption_resolution,[],[f156,f77])).
% 1.72/0.61  fof(f156,plain,(
% 1.72/0.61    ( ! [X1] : (~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~m1_pre_topc(X1,sK2) | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X1)) = k3_tmap_1(sK2,sK1,sK2,X1,sK5)) )),
% 1.72/0.61    inference(subsumption_resolution,[],[f152,f66])).
% 1.72/0.61  fof(f152,plain,(
% 1.72/0.61    ( ! [X1] : (~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~m1_pre_topc(X1,sK2) | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X1)) = k3_tmap_1(sK2,sK1,sK2,X1,sK5)) )),
% 1.72/0.61    inference(duplicate_literal_removal,[],[f151])).
% 1.72/0.61  fof(f151,plain,(
% 1.72/0.61    ( ! [X1] : (~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~m1_pre_topc(X1,sK2) | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X1)) = k3_tmap_1(sK2,sK1,sK2,X1,sK5) | ~l1_pre_topc(sK2)) )),
% 1.72/0.61    inference(resolution,[],[f146,f48])).
% 1.72/0.61  fof(f763,plain,(
% 1.72/0.61    ( ! [X0] : (r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK2,X0,sK5),k2_tmap_1(sK2,sK1,sK5,X0)) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK2) | ~m1_pre_topc(sK2,sK2)) )),
% 1.72/0.61    inference(subsumption_resolution,[],[f762,f32])).
% 1.72/0.61  fof(f762,plain,(
% 1.72/0.61    ( ! [X0] : (~m1_pre_topc(sK2,sK2) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK2) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK2,X0,sK5),k2_tmap_1(sK2,sK1,sK5,X0))) )),
% 1.72/0.61    inference(subsumption_resolution,[],[f761,f31])).
% 1.72/0.61  fof(f761,plain,(
% 1.72/0.61    ( ! [X0] : (~m1_pre_topc(sK2,sK2) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK2) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK2,X0,sK5),k2_tmap_1(sK2,sK1,sK5,X0))) )),
% 1.72/0.61    inference(subsumption_resolution,[],[f760,f30])).
% 1.72/0.61  fof(f760,plain,(
% 1.72/0.61    ( ! [X0] : (~m1_pre_topc(sK2,sK2) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK2) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK2,X0,sK5),k2_tmap_1(sK2,sK1,sK5,X0))) )),
% 1.72/0.61    inference(subsumption_resolution,[],[f759,f40])).
% 1.72/0.61  fof(f759,plain,(
% 1.72/0.61    ( ! [X0] : (v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK2) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK2) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK2,X0,sK5),k2_tmap_1(sK2,sK1,sK5,X0))) )),
% 1.72/0.61    inference(subsumption_resolution,[],[f758,f44])).
% 1.72/0.61  fof(f758,plain,(
% 1.72/0.61    ( ! [X0] : (~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK2) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK2) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK2,X0,sK5),k2_tmap_1(sK2,sK1,sK5,X0))) )),
% 1.72/0.61    inference(subsumption_resolution,[],[f757,f43])).
% 1.72/0.61  fof(f757,plain,(
% 1.72/0.61    ( ! [X0] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK2) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK2) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK2,X0,sK5),k2_tmap_1(sK2,sK1,sK5,X0))) )),
% 1.72/0.61    inference(subsumption_resolution,[],[f756,f42])).
% 1.72/0.61  fof(f756,plain,(
% 1.72/0.61    ( ! [X0] : (v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK2) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK2) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK2,X0,sK5),k2_tmap_1(sK2,sK1,sK5,X0))) )),
% 1.72/0.61    inference(subsumption_resolution,[],[f755,f66])).
% 1.72/0.61  fof(f755,plain,(
% 1.72/0.61    ( ! [X0] : (~l1_pre_topc(sK2) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK2) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK2) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK2,X0,sK5),k2_tmap_1(sK2,sK1,sK5,X0))) )),
% 1.72/0.61    inference(subsumption_resolution,[],[f754,f77])).
% 1.72/0.61  fof(f754,plain,(
% 1.72/0.61    ( ! [X0] : (~v2_pre_topc(sK2) | ~l1_pre_topc(sK2) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK2) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK2) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK2,X0,sK5),k2_tmap_1(sK2,sK1,sK5,X0))) )),
% 1.72/0.61    inference(duplicate_literal_removal,[],[f749])).
% 1.72/0.61  fof(f749,plain,(
% 1.72/0.61    ( ! [X0] : (~v2_pre_topc(sK2) | ~l1_pre_topc(sK2) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK2) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK2) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | v2_struct_0(sK2) | ~m1_pre_topc(X0,sK2) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK2,X0,sK5),k2_tmap_1(sK2,sK1,sK5,X0))) )),
% 1.72/0.61    inference(resolution,[],[f51,f189])).
% 1.72/0.61  fof(f189,plain,(
% 1.72/0.61    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,k2_tmap_1(sK2,sK1,sK5,sK2))),
% 1.72/0.61    inference(subsumption_resolution,[],[f188,f45])).
% 1.72/0.61  fof(f188,plain,(
% 1.72/0.61    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,k2_tmap_1(sK2,sK1,sK5,sK2)) | v2_struct_0(sK0)),
% 1.72/0.61    inference(subsumption_resolution,[],[f187,f32])).
% 1.72/0.61  fof(f187,plain,(
% 1.72/0.61    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,k2_tmap_1(sK2,sK1,sK5,sK2)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | v2_struct_0(sK0)),
% 1.72/0.61    inference(subsumption_resolution,[],[f186,f31])).
% 1.72/0.61  fof(f186,plain,(
% 1.72/0.61    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,k2_tmap_1(sK2,sK1,sK5,sK2)) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | v2_struct_0(sK0)),
% 1.72/0.61    inference(subsumption_resolution,[],[f185,f30])).
% 1.72/0.61  fof(f185,plain,(
% 1.72/0.61    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,k2_tmap_1(sK2,sK1,sK5,sK2)) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | v2_struct_0(sK0)),
% 1.72/0.61    inference(subsumption_resolution,[],[f184,f41])).
% 1.72/0.61  fof(f184,plain,(
% 1.72/0.61    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,k2_tmap_1(sK2,sK1,sK5,sK2)) | ~m1_pre_topc(sK2,sK0) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | v2_struct_0(sK0)),
% 1.72/0.61    inference(subsumption_resolution,[],[f183,f40])).
% 1.72/0.61  fof(f183,plain,(
% 1.72/0.61    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,k2_tmap_1(sK2,sK1,sK5,sK2)) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | v2_struct_0(sK0)),
% 1.72/0.61    inference(subsumption_resolution,[],[f182,f44])).
% 1.72/0.61  fof(f182,plain,(
% 1.72/0.61    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,k2_tmap_1(sK2,sK1,sK5,sK2)) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | v2_struct_0(sK0)),
% 1.72/0.61    inference(subsumption_resolution,[],[f181,f43])).
% 1.72/0.61  fof(f181,plain,(
% 1.72/0.61    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,k2_tmap_1(sK2,sK1,sK5,sK2)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | v2_struct_0(sK0)),
% 1.72/0.61    inference(subsumption_resolution,[],[f180,f42])).
% 1.72/0.61  fof(f180,plain,(
% 1.72/0.61    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,k2_tmap_1(sK2,sK1,sK5,sK2)) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | v2_struct_0(sK0)),
% 1.72/0.61    inference(subsumption_resolution,[],[f179,f47])).
% 1.72/0.61  fof(f179,plain,(
% 1.72/0.61    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,k2_tmap_1(sK2,sK1,sK5,sK2)) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | v2_struct_0(sK0)),
% 1.72/0.61    inference(subsumption_resolution,[],[f169,f46])).
% 1.72/0.61  fof(f169,plain,(
% 1.72/0.61    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,k2_tmap_1(sK2,sK1,sK5,sK2)) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | v2_struct_0(sK0)),
% 1.72/0.61    inference(superposition,[],[f52,f163])).
% 1.72/0.61  fof(f163,plain,(
% 1.72/0.61    k2_tmap_1(sK2,sK1,sK5,sK2) = k3_tmap_1(sK0,sK1,sK2,sK2,sK5)),
% 1.72/0.61    inference(forward_demodulation,[],[f162,f127])).
% 1.72/0.61  fof(f127,plain,(
% 1.72/0.61    k2_tmap_1(sK2,sK1,sK5,sK2) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK2))),
% 1.72/0.61    inference(subsumption_resolution,[],[f124,f66])).
% 1.72/0.61  fof(f124,plain,(
% 1.72/0.61    k2_tmap_1(sK2,sK1,sK5,sK2) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK2)) | ~l1_pre_topc(sK2)),
% 1.72/0.61    inference(resolution,[],[f123,f48])).
% 1.72/0.61  fof(f162,plain,(
% 1.72/0.61    k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK2)) = k3_tmap_1(sK0,sK1,sK2,sK2,sK5)),
% 1.72/0.61    inference(subsumption_resolution,[],[f159,f66])).
% 1.72/0.61  fof(f159,plain,(
% 1.72/0.61    k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK2)) = k3_tmap_1(sK0,sK1,sK2,sK2,sK5) | ~l1_pre_topc(sK2)),
% 1.72/0.61    inference(resolution,[],[f155,f48])).
% 1.72/0.61  fof(f52,plain,(
% 1.72/0.61    ( ! [X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | v2_struct_0(X0)) )),
% 1.72/0.61    inference(cnf_transformation,[],[f21])).
% 1.72/0.61  fof(f21,plain,(
% 1.72/0.61    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.72/0.61    inference(flattening,[],[f20])).
% 1.72/0.61  fof(f20,plain,(
% 1.72/0.61    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.72/0.61    inference(ennf_transformation,[],[f7])).
% 1.72/0.61  fof(f7,axiom,(
% 1.72/0.61    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))))))),
% 1.72/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tmap_1)).
% 1.72/0.61  % SZS output end Proof for theBenchmark
% 1.72/0.61  % (6358)------------------------------
% 1.72/0.61  % (6358)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.72/0.61  % (6358)Termination reason: Refutation
% 1.72/0.61  
% 1.72/0.61  % (6358)Memory used [KB]: 6652
% 1.72/0.61  % (6358)Time elapsed: 0.193 s
% 1.72/0.61  % (6358)------------------------------
% 1.72/0.61  % (6358)------------------------------
% 1.72/0.61  % (6344)Success in time 0.251 s
%------------------------------------------------------------------------------
