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
% DateTime   : Thu Dec  3 13:18:36 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 878 expanded)
%              Number of leaves         :    6 ( 151 expanded)
%              Depth                    :   23
%              Number of atoms          :  836 (12523 expanded)
%              Number of equality atoms :   56 ( 640 expanded)
%              Maximal formula depth    :   22 (   8 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f214,plain,(
    $false ),
    inference(subsumption_resolution,[],[f213,f202])).

fof(f202,plain,(
    ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,sK2),sK5) ),
    inference(backward_demodulation,[],[f23,f201])).

fof(f201,plain,(
    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_tmap_1(sK3,sK1,sK4,sK2) ),
    inference(forward_demodulation,[],[f200,f143])).

fof(f143,plain,(
    k2_tmap_1(sK3,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) ),
    inference(resolution,[],[f111,f27])).

fof(f27,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
                          & ! [X6] :
                              ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6)
                              | ~ r2_hidden(X6,u1_struct_0(X2))
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
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
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
                          & ! [X6] :
                              ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6)
                              | ~ r2_hidden(X6,u1_struct_0(X2))
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
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
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
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
                              ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                                & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                                & v1_funct_1(X5) )
                             => ( ! [X6] :
                                    ( m1_subset_1(X6,u1_struct_0(X3))
                                   => ( r2_hidden(X6,u1_struct_0(X2))
                                     => k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6) ) )
                               => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
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
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                              & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                              & v1_funct_1(X5) )
                           => ( ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X3))
                                 => ( r2_hidden(X6,u1_struct_0(X2))
                                   => k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6) ) )
                             => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_tmap_1)).

fof(f111,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | k2_tmap_1(sK3,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f110,f26])).

fof(f26,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f9])).

fof(f110,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X0,sK3)
      | k2_tmap_1(sK3,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f109,f28])).

fof(f28,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f9])).

fof(f109,plain,(
    ! [X0] :
      ( v2_struct_0(sK3)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X0,sK3)
      | k2_tmap_1(sK3,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f108,f24])).

fof(f24,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f9])).

fof(f108,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK4)
      | v2_struct_0(sK3)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X0,sK3)
      | k2_tmap_1(sK3,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f107,f34])).

fof(f34,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f107,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK4)
      | v2_struct_0(sK3)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X0,sK3)
      | k2_tmap_1(sK3,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f106,f33])).

fof(f33,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f106,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK4)
      | v2_struct_0(sK3)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X0,sK3)
      | k2_tmap_1(sK3,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f105,f32])).

fof(f32,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f105,plain,(
    ! [X0] :
      ( v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK4)
      | v2_struct_0(sK3)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X0,sK3)
      | k2_tmap_1(sK3,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f104,f49])).

fof(f49,plain,(
    l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f47,f37])).

fof(f37,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f47,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK3) ),
    inference(resolution,[],[f29,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f29,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f104,plain,(
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
    inference(subsumption_resolution,[],[f99,f51])).

fof(f51,plain,(
    v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f50,f36])).

fof(f36,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f50,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f48,f37])).

fof(f48,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK3) ),
    inference(resolution,[],[f29,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
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

fof(f99,plain,(
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
    inference(resolution,[],[f25,f42])).

fof(f42,plain,(
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
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f25,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f200,plain,(
    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f199,f31])).

fof(f31,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f199,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) ),
    inference(resolution,[],[f155,f27])).

fof(f155,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | ~ m1_pre_topc(X0,sK0)
      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK4) ) ),
    inference(subsumption_resolution,[],[f154,f35])).

fof(f35,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f154,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(sK0)
      | ~ m1_pre_topc(X0,sK3)
      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK4) ) ),
    inference(subsumption_resolution,[],[f153,f36])).

fof(f153,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(sK0)
      | ~ m1_pre_topc(X0,sK3)
      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK4) ) ),
    inference(subsumption_resolution,[],[f152,f37])).

fof(f152,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(sK0)
      | ~ m1_pre_topc(X0,sK3)
      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK4) ) ),
    inference(resolution,[],[f116,f29])).

fof(f116,plain,(
    ! [X2,X1] :
      ( ~ m1_pre_topc(sK3,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X2,sK3)
      | k3_tmap_1(X1,sK1,sK3,X2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X2)) ) ),
    inference(subsumption_resolution,[],[f115,f26])).

fof(f115,plain,(
    ! [X2,X1] :
      ( ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(sK3,X1)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X2,sK3)
      | k3_tmap_1(X1,sK1,sK3,X2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X2)) ) ),
    inference(subsumption_resolution,[],[f114,f24])).

fof(f114,plain,(
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
    inference(subsumption_resolution,[],[f113,f34])).

fof(f113,plain,(
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
    inference(subsumption_resolution,[],[f112,f33])).

fof(f112,plain,(
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
    inference(subsumption_resolution,[],[f100,f32])).

fof(f100,plain,(
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
    inference(resolution,[],[f25,f41])).

fof(f41,plain,(
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
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).

fof(f23,plain,(
    ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(cnf_transformation,[],[f9])).

fof(f213,plain,(
    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,sK2),sK5) ),
    inference(subsumption_resolution,[],[f212,f206])).

fof(f206,plain,(
    k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(sK1,sK3,sK2,sK4,sK5)) = k1_funct_1(sK5,sK6(sK1,sK3,sK2,sK4,sK5)) ),
    inference(subsumption_resolution,[],[f205,f204])).

fof(f204,plain,(
    m1_subset_1(sK6(sK1,sK3,sK2,sK4,sK5),u1_struct_0(sK3)) ),
    inference(resolution,[],[f202,f178])).

fof(f178,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,sK2),sK5)
    | m1_subset_1(sK6(sK1,sK3,sK2,sK4,sK5),u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f177,f22])).

fof(f22,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f9])).

fof(f177,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | m1_subset_1(sK6(sK1,sK3,sK2,sK4,sK5),u1_struct_0(sK3))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,sK2),sK5) ),
    inference(subsumption_resolution,[],[f176,f30])).

fof(f30,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f176,plain,
    ( v2_struct_0(sK2)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | m1_subset_1(sK6(sK1,sK3,sK2,sK4,sK5),u1_struct_0(sK3))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,sK2),sK5) ),
    inference(subsumption_resolution,[],[f175,f20])).

fof(f20,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f9])).

fof(f175,plain,
    ( ~ v1_funct_1(sK5)
    | v2_struct_0(sK2)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | m1_subset_1(sK6(sK1,sK3,sK2,sK4,sK5),u1_struct_0(sK3))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,sK2),sK5) ),
    inference(subsumption_resolution,[],[f173,f27])).

fof(f173,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ v1_funct_1(sK5)
    | v2_struct_0(sK2)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | m1_subset_1(sK6(sK1,sK3,sK2,sK4,sK5),u1_struct_0(sK3))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,sK2),sK5) ),
    inference(resolution,[],[f124,f21])).

fof(f21,plain,(
    v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f124,plain,(
    ! [X4,X3] :
      ( ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
      | ~ m1_pre_topc(X3,sK3)
      | ~ v1_funct_1(X4)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
      | m1_subset_1(sK6(sK1,sK3,X3,sK4,X4),u1_struct_0(sK3))
      | r2_funct_2(u1_struct_0(X3),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,X3),X4) ) ),
    inference(subsumption_resolution,[],[f123,f26])).

fof(f123,plain,(
    ! [X4,X3] :
      ( v2_struct_0(X3)
      | ~ m1_pre_topc(X3,sK3)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
      | m1_subset_1(sK6(sK1,sK3,X3,sK4,X4),u1_struct_0(sK3))
      | r2_funct_2(u1_struct_0(X3),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,X3),X4) ) ),
    inference(subsumption_resolution,[],[f122,f32])).

fof(f122,plain,(
    ! [X4,X3] :
      ( v2_struct_0(X3)
      | ~ m1_pre_topc(X3,sK3)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
      | m1_subset_1(sK6(sK1,sK3,X3,sK4,X4),u1_struct_0(sK3))
      | r2_funct_2(u1_struct_0(X3),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,X3),X4) ) ),
    inference(subsumption_resolution,[],[f121,f24])).

fof(f121,plain,(
    ! [X4,X3] :
      ( v2_struct_0(X3)
      | ~ m1_pre_topc(X3,sK3)
      | ~ v1_funct_1(sK4)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
      | m1_subset_1(sK6(sK1,sK3,X3,sK4,X4),u1_struct_0(sK3))
      | r2_funct_2(u1_struct_0(X3),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,X3),X4) ) ),
    inference(subsumption_resolution,[],[f120,f49])).

fof(f120,plain,(
    ! [X4,X3] :
      ( ~ l1_pre_topc(sK3)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,sK3)
      | ~ v1_funct_1(sK4)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
      | m1_subset_1(sK6(sK1,sK3,X3,sK4,X4),u1_struct_0(sK3))
      | r2_funct_2(u1_struct_0(X3),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,X3),X4) ) ),
    inference(subsumption_resolution,[],[f119,f51])).

fof(f119,plain,(
    ! [X4,X3] :
      ( ~ v2_pre_topc(sK3)
      | ~ l1_pre_topc(sK3)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,sK3)
      | ~ v1_funct_1(sK4)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
      | m1_subset_1(sK6(sK1,sK3,X3,sK4,X4),u1_struct_0(sK3))
      | r2_funct_2(u1_struct_0(X3),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,X3),X4) ) ),
    inference(subsumption_resolution,[],[f118,f28])).

fof(f118,plain,(
    ! [X4,X3] :
      ( v2_struct_0(sK3)
      | ~ v2_pre_topc(sK3)
      | ~ l1_pre_topc(sK3)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,sK3)
      | ~ v1_funct_1(sK4)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
      | m1_subset_1(sK6(sK1,sK3,X3,sK4,X4),u1_struct_0(sK3))
      | r2_funct_2(u1_struct_0(X3),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,X3),X4) ) ),
    inference(subsumption_resolution,[],[f117,f34])).

fof(f117,plain,(
    ! [X4,X3] :
      ( ~ l1_pre_topc(sK1)
      | v2_struct_0(sK3)
      | ~ v2_pre_topc(sK3)
      | ~ l1_pre_topc(sK3)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,sK3)
      | ~ v1_funct_1(sK4)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
      | m1_subset_1(sK6(sK1,sK3,X3,sK4,X4),u1_struct_0(sK3))
      | r2_funct_2(u1_struct_0(X3),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,X3),X4) ) ),
    inference(subsumption_resolution,[],[f101,f33])).

fof(f101,plain,(
    ! [X4,X3] :
      ( ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK3)
      | ~ v2_pre_topc(sK3)
      | ~ l1_pre_topc(sK3)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,sK3)
      | ~ v1_funct_1(sK4)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
      | m1_subset_1(sK6(sK1,sK3,X3,sK4,X4),u1_struct_0(sK3))
      | r2_funct_2(u1_struct_0(X3),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,X3),X4) ) ),
    inference(resolution,[],[f25,f38])).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X1)
      | ~ v1_funct_1(X3)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
      | m1_subset_1(sK6(X0,X1,X2,X3,X4),u1_struct_0(X1))
      | r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      | ? [X5] :
                          ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5)
                          & r2_hidden(X5,u1_struct_0(X2))
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  | ~ v1_funct_1(X3) )
              | ~ m1_pre_topc(X2,X1)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      | ? [X5] :
                          ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5)
                          & r2_hidden(X5,u1_struct_0(X2))
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  | ~ v1_funct_1(X3) )
              | ~ m1_pre_topc(X2,X1)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                     => ( ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => ( r2_hidden(X5,u1_struct_0(X2))
                             => k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5) ) )
                       => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_tmap_1)).

fof(f205,plain,
    ( ~ m1_subset_1(sK6(sK1,sK3,sK2,sK4,sK5),u1_struct_0(sK3))
    | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(sK1,sK3,sK2,sK4,sK5)) = k1_funct_1(sK5,sK6(sK1,sK3,sK2,sK4,sK5)) ),
    inference(resolution,[],[f203,f19])).

fof(f19,plain,(
    ! [X6] :
      ( ~ r2_hidden(X6,u1_struct_0(sK2))
      | ~ m1_subset_1(X6,u1_struct_0(sK3))
      | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X6) = k1_funct_1(sK5,X6) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f203,plain,(
    r2_hidden(sK6(sK1,sK3,sK2,sK4,sK5),u1_struct_0(sK2)) ),
    inference(resolution,[],[f202,f187])).

fof(f187,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,sK2),sK5)
    | r2_hidden(sK6(sK1,sK3,sK2,sK4,sK5),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f186,f22])).

fof(f186,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | r2_hidden(sK6(sK1,sK3,sK2,sK4,sK5),u1_struct_0(sK2))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,sK2),sK5) ),
    inference(subsumption_resolution,[],[f185,f30])).

fof(f185,plain,
    ( v2_struct_0(sK2)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | r2_hidden(sK6(sK1,sK3,sK2,sK4,sK5),u1_struct_0(sK2))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,sK2),sK5) ),
    inference(subsumption_resolution,[],[f184,f20])).

fof(f184,plain,
    ( ~ v1_funct_1(sK5)
    | v2_struct_0(sK2)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | r2_hidden(sK6(sK1,sK3,sK2,sK4,sK5),u1_struct_0(sK2))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,sK2),sK5) ),
    inference(subsumption_resolution,[],[f182,f27])).

fof(f182,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ v1_funct_1(sK5)
    | v2_struct_0(sK2)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | r2_hidden(sK6(sK1,sK3,sK2,sK4,sK5),u1_struct_0(sK2))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,sK2),sK5) ),
    inference(resolution,[],[f132,f21])).

fof(f132,plain,(
    ! [X6,X5] :
      ( ~ v1_funct_2(X6,u1_struct_0(X5),u1_struct_0(sK1))
      | ~ m1_pre_topc(X5,sK3)
      | ~ v1_funct_1(X6)
      | v2_struct_0(X5)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1))))
      | r2_hidden(sK6(sK1,sK3,X5,sK4,X6),u1_struct_0(X5))
      | r2_funct_2(u1_struct_0(X5),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,X5),X6) ) ),
    inference(subsumption_resolution,[],[f131,f26])).

fof(f131,plain,(
    ! [X6,X5] :
      ( v2_struct_0(X5)
      | ~ m1_pre_topc(X5,sK3)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,u1_struct_0(X5),u1_struct_0(sK1))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1))))
      | r2_hidden(sK6(sK1,sK3,X5,sK4,X6),u1_struct_0(X5))
      | r2_funct_2(u1_struct_0(X5),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,X5),X6) ) ),
    inference(subsumption_resolution,[],[f130,f32])).

fof(f130,plain,(
    ! [X6,X5] :
      ( v2_struct_0(X5)
      | ~ m1_pre_topc(X5,sK3)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,u1_struct_0(X5),u1_struct_0(sK1))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1))))
      | r2_hidden(sK6(sK1,sK3,X5,sK4,X6),u1_struct_0(X5))
      | r2_funct_2(u1_struct_0(X5),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,X5),X6) ) ),
    inference(subsumption_resolution,[],[f129,f24])).

fof(f129,plain,(
    ! [X6,X5] :
      ( v2_struct_0(X5)
      | ~ m1_pre_topc(X5,sK3)
      | ~ v1_funct_1(sK4)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,u1_struct_0(X5),u1_struct_0(sK1))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1))))
      | r2_hidden(sK6(sK1,sK3,X5,sK4,X6),u1_struct_0(X5))
      | r2_funct_2(u1_struct_0(X5),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,X5),X6) ) ),
    inference(subsumption_resolution,[],[f128,f49])).

fof(f128,plain,(
    ! [X6,X5] :
      ( ~ l1_pre_topc(sK3)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X5,sK3)
      | ~ v1_funct_1(sK4)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,u1_struct_0(X5),u1_struct_0(sK1))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1))))
      | r2_hidden(sK6(sK1,sK3,X5,sK4,X6),u1_struct_0(X5))
      | r2_funct_2(u1_struct_0(X5),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,X5),X6) ) ),
    inference(subsumption_resolution,[],[f127,f51])).

fof(f127,plain,(
    ! [X6,X5] :
      ( ~ v2_pre_topc(sK3)
      | ~ l1_pre_topc(sK3)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X5,sK3)
      | ~ v1_funct_1(sK4)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,u1_struct_0(X5),u1_struct_0(sK1))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1))))
      | r2_hidden(sK6(sK1,sK3,X5,sK4,X6),u1_struct_0(X5))
      | r2_funct_2(u1_struct_0(X5),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,X5),X6) ) ),
    inference(subsumption_resolution,[],[f126,f28])).

fof(f126,plain,(
    ! [X6,X5] :
      ( v2_struct_0(sK3)
      | ~ v2_pre_topc(sK3)
      | ~ l1_pre_topc(sK3)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X5,sK3)
      | ~ v1_funct_1(sK4)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,u1_struct_0(X5),u1_struct_0(sK1))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1))))
      | r2_hidden(sK6(sK1,sK3,X5,sK4,X6),u1_struct_0(X5))
      | r2_funct_2(u1_struct_0(X5),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,X5),X6) ) ),
    inference(subsumption_resolution,[],[f125,f34])).

fof(f125,plain,(
    ! [X6,X5] :
      ( ~ l1_pre_topc(sK1)
      | v2_struct_0(sK3)
      | ~ v2_pre_topc(sK3)
      | ~ l1_pre_topc(sK3)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X5,sK3)
      | ~ v1_funct_1(sK4)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,u1_struct_0(X5),u1_struct_0(sK1))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1))))
      | r2_hidden(sK6(sK1,sK3,X5,sK4,X6),u1_struct_0(X5))
      | r2_funct_2(u1_struct_0(X5),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,X5),X6) ) ),
    inference(subsumption_resolution,[],[f102,f33])).

fof(f102,plain,(
    ! [X6,X5] :
      ( ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK3)
      | ~ v2_pre_topc(sK3)
      | ~ l1_pre_topc(sK3)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X5,sK3)
      | ~ v1_funct_1(sK4)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,u1_struct_0(X5),u1_struct_0(sK1))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1))))
      | r2_hidden(sK6(sK1,sK3,X5,sK4,X6),u1_struct_0(X5))
      | r2_funct_2(u1_struct_0(X5),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,X5),X6) ) ),
    inference(resolution,[],[f25,f39])).

fof(f39,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X1)
      | ~ v1_funct_1(X3)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
      | r2_hidden(sK6(X0,X1,X2,X3,X4),u1_struct_0(X2))
      | r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f212,plain,
    ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(sK1,sK3,sK2,sK4,sK5)) != k1_funct_1(sK5,sK6(sK1,sK3,sK2,sK4,sK5))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,sK2),sK5) ),
    inference(subsumption_resolution,[],[f211,f22])).

fof(f211,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(sK1,sK3,sK2,sK4,sK5)) != k1_funct_1(sK5,sK6(sK1,sK3,sK2,sK4,sK5))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,sK2),sK5) ),
    inference(subsumption_resolution,[],[f210,f30])).

fof(f210,plain,
    ( v2_struct_0(sK2)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(sK1,sK3,sK2,sK4,sK5)) != k1_funct_1(sK5,sK6(sK1,sK3,sK2,sK4,sK5))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,sK2),sK5) ),
    inference(subsumption_resolution,[],[f209,f20])).

fof(f209,plain,
    ( ~ v1_funct_1(sK5)
    | v2_struct_0(sK2)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(sK1,sK3,sK2,sK4,sK5)) != k1_funct_1(sK5,sK6(sK1,sK3,sK2,sK4,sK5))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,sK2),sK5) ),
    inference(subsumption_resolution,[],[f207,f27])).

fof(f207,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ v1_funct_1(sK5)
    | v2_struct_0(sK2)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(sK1,sK3,sK2,sK4,sK5)) != k1_funct_1(sK5,sK6(sK1,sK3,sK2,sK4,sK5))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,sK2),sK5) ),
    inference(resolution,[],[f140,f21])).

fof(f140,plain,(
    ! [X8,X7] :
      ( ~ v1_funct_2(X8,u1_struct_0(X7),u1_struct_0(sK1))
      | ~ m1_pre_topc(X7,sK3)
      | ~ v1_funct_1(X8)
      | v2_struct_0(X7)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1))))
      | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(sK1,sK3,X7,sK4,X8)) != k1_funct_1(X8,sK6(sK1,sK3,X7,sK4,X8))
      | r2_funct_2(u1_struct_0(X7),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,X7),X8) ) ),
    inference(subsumption_resolution,[],[f139,f26])).

fof(f139,plain,(
    ! [X8,X7] :
      ( v2_struct_0(X7)
      | ~ m1_pre_topc(X7,sK3)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_1(X8)
      | ~ v1_funct_2(X8,u1_struct_0(X7),u1_struct_0(sK1))
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1))))
      | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(sK1,sK3,X7,sK4,X8)) != k1_funct_1(X8,sK6(sK1,sK3,X7,sK4,X8))
      | r2_funct_2(u1_struct_0(X7),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,X7),X8) ) ),
    inference(subsumption_resolution,[],[f138,f32])).

fof(f138,plain,(
    ! [X8,X7] :
      ( v2_struct_0(X7)
      | ~ m1_pre_topc(X7,sK3)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_1(X8)
      | ~ v1_funct_2(X8,u1_struct_0(X7),u1_struct_0(sK1))
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1))))
      | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(sK1,sK3,X7,sK4,X8)) != k1_funct_1(X8,sK6(sK1,sK3,X7,sK4,X8))
      | r2_funct_2(u1_struct_0(X7),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,X7),X8) ) ),
    inference(subsumption_resolution,[],[f137,f24])).

fof(f137,plain,(
    ! [X8,X7] :
      ( v2_struct_0(X7)
      | ~ m1_pre_topc(X7,sK3)
      | ~ v1_funct_1(sK4)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_1(X8)
      | ~ v1_funct_2(X8,u1_struct_0(X7),u1_struct_0(sK1))
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1))))
      | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(sK1,sK3,X7,sK4,X8)) != k1_funct_1(X8,sK6(sK1,sK3,X7,sK4,X8))
      | r2_funct_2(u1_struct_0(X7),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,X7),X8) ) ),
    inference(subsumption_resolution,[],[f136,f49])).

fof(f136,plain,(
    ! [X8,X7] :
      ( ~ l1_pre_topc(sK3)
      | v2_struct_0(X7)
      | ~ m1_pre_topc(X7,sK3)
      | ~ v1_funct_1(sK4)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_1(X8)
      | ~ v1_funct_2(X8,u1_struct_0(X7),u1_struct_0(sK1))
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1))))
      | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(sK1,sK3,X7,sK4,X8)) != k1_funct_1(X8,sK6(sK1,sK3,X7,sK4,X8))
      | r2_funct_2(u1_struct_0(X7),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,X7),X8) ) ),
    inference(subsumption_resolution,[],[f135,f51])).

fof(f135,plain,(
    ! [X8,X7] :
      ( ~ v2_pre_topc(sK3)
      | ~ l1_pre_topc(sK3)
      | v2_struct_0(X7)
      | ~ m1_pre_topc(X7,sK3)
      | ~ v1_funct_1(sK4)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_1(X8)
      | ~ v1_funct_2(X8,u1_struct_0(X7),u1_struct_0(sK1))
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1))))
      | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(sK1,sK3,X7,sK4,X8)) != k1_funct_1(X8,sK6(sK1,sK3,X7,sK4,X8))
      | r2_funct_2(u1_struct_0(X7),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,X7),X8) ) ),
    inference(subsumption_resolution,[],[f134,f28])).

fof(f134,plain,(
    ! [X8,X7] :
      ( v2_struct_0(sK3)
      | ~ v2_pre_topc(sK3)
      | ~ l1_pre_topc(sK3)
      | v2_struct_0(X7)
      | ~ m1_pre_topc(X7,sK3)
      | ~ v1_funct_1(sK4)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_1(X8)
      | ~ v1_funct_2(X8,u1_struct_0(X7),u1_struct_0(sK1))
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1))))
      | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(sK1,sK3,X7,sK4,X8)) != k1_funct_1(X8,sK6(sK1,sK3,X7,sK4,X8))
      | r2_funct_2(u1_struct_0(X7),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,X7),X8) ) ),
    inference(subsumption_resolution,[],[f133,f34])).

fof(f133,plain,(
    ! [X8,X7] :
      ( ~ l1_pre_topc(sK1)
      | v2_struct_0(sK3)
      | ~ v2_pre_topc(sK3)
      | ~ l1_pre_topc(sK3)
      | v2_struct_0(X7)
      | ~ m1_pre_topc(X7,sK3)
      | ~ v1_funct_1(sK4)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_1(X8)
      | ~ v1_funct_2(X8,u1_struct_0(X7),u1_struct_0(sK1))
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1))))
      | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(sK1,sK3,X7,sK4,X8)) != k1_funct_1(X8,sK6(sK1,sK3,X7,sK4,X8))
      | r2_funct_2(u1_struct_0(X7),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,X7),X8) ) ),
    inference(subsumption_resolution,[],[f103,f33])).

fof(f103,plain,(
    ! [X8,X7] :
      ( ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK3)
      | ~ v2_pre_topc(sK3)
      | ~ l1_pre_topc(sK3)
      | v2_struct_0(X7)
      | ~ m1_pre_topc(X7,sK3)
      | ~ v1_funct_1(sK4)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_1(X8)
      | ~ v1_funct_2(X8,u1_struct_0(X7),u1_struct_0(sK1))
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1))))
      | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(sK1,sK3,X7,sK4,X8)) != k1_funct_1(X8,sK6(sK1,sK3,X7,sK4,X8))
      | r2_funct_2(u1_struct_0(X7),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,X7),X8) ) ),
    inference(resolution,[],[f25,f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X1)
      | ~ v1_funct_1(X3)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
      | k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK6(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK6(X0,X1,X2,X3,X4))
      | r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) ) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:21:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (11399)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.46  % (11407)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.20/0.47  % (11407)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % (11387)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f214,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(subsumption_resolution,[],[f213,f202])).
% 0.20/0.47  fof(f202,plain,(
% 0.20/0.47    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,sK2),sK5)),
% 0.20/0.47    inference(backward_demodulation,[],[f23,f201])).
% 0.20/0.47  fof(f201,plain,(
% 0.20/0.47    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_tmap_1(sK3,sK1,sK4,sK2)),
% 0.20/0.47    inference(forward_demodulation,[],[f200,f143])).
% 0.20/0.47  fof(f143,plain,(
% 0.20/0.47    k2_tmap_1(sK3,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2))),
% 0.20/0.47    inference(resolution,[],[f111,f27])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    m1_pre_topc(sK2,sK3)),
% 0.20/0.47    inference(cnf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & ! [X6] : (k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6) | ~r2_hidden(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f8])).
% 0.20/0.47  fof(f8,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & ! [X6] : ((k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6) | ~r2_hidden(X6,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3)))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5))) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,negated_conjecture,(
% 0.20/0.47    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => (! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => (r2_hidden(X6,u1_struct_0(X2)) => k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6))) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)))))))))),
% 0.20/0.47    inference(negated_conjecture,[],[f6])).
% 0.20/0.47  fof(f6,conjecture,(
% 0.20/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => (! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => (r2_hidden(X6,u1_struct_0(X2)) => k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6))) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)))))))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_tmap_1)).
% 0.20/0.47  fof(f111,plain,(
% 0.20/0.47    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0))) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f110,f26])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.20/0.47    inference(cnf_transformation,[],[f9])).
% 0.20/0.47  fof(f110,plain,(
% 0.20/0.47    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0))) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f109,f28])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ~v2_struct_0(sK3)),
% 0.20/0.47    inference(cnf_transformation,[],[f9])).
% 0.20/0.47  fof(f109,plain,(
% 0.20/0.47    ( ! [X0] : (v2_struct_0(sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0))) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f108,f24])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    v1_funct_1(sK4)),
% 0.20/0.47    inference(cnf_transformation,[],[f9])).
% 0.20/0.47  fof(f108,plain,(
% 0.20/0.47    ( ! [X0] : (~v1_funct_1(sK4) | v2_struct_0(sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0))) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f107,f34])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    l1_pre_topc(sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f9])).
% 0.20/0.47  fof(f107,plain,(
% 0.20/0.47    ( ! [X0] : (~l1_pre_topc(sK1) | ~v1_funct_1(sK4) | v2_struct_0(sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0))) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f106,f33])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    v2_pre_topc(sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f9])).
% 0.20/0.47  fof(f106,plain,(
% 0.20/0.47    ( ! [X0] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK4) | v2_struct_0(sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0))) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f105,f32])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ~v2_struct_0(sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f9])).
% 0.20/0.47  fof(f105,plain,(
% 0.20/0.47    ( ! [X0] : (v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK4) | v2_struct_0(sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0))) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f104,f49])).
% 0.20/0.47  fof(f49,plain,(
% 0.20/0.47    l1_pre_topc(sK3)),
% 0.20/0.47    inference(subsumption_resolution,[],[f47,f37])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    l1_pre_topc(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f9])).
% 0.20/0.47  fof(f47,plain,(
% 0.20/0.47    ~l1_pre_topc(sK0) | l1_pre_topc(sK3)),
% 0.20/0.47    inference(resolution,[],[f29,f44])).
% 0.20/0.47  fof(f44,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    m1_pre_topc(sK3,sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f9])).
% 0.20/0.47  fof(f104,plain,(
% 0.20/0.47    ( ! [X0] : (~l1_pre_topc(sK3) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK4) | v2_struct_0(sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0))) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f99,f51])).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    v2_pre_topc(sK3)),
% 0.20/0.47    inference(subsumption_resolution,[],[f50,f36])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    v2_pre_topc(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f9])).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    ~v2_pre_topc(sK0) | v2_pre_topc(sK3)),
% 0.20/0.47    inference(subsumption_resolution,[],[f48,f37])).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_pre_topc(sK3)),
% 0.20/0.47    inference(resolution,[],[f29,f43])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_pre_topc(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.47    inference(flattening,[],[f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.20/0.47  fof(f99,plain,(
% 0.20/0.47    ( ! [X0] : (~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK4) | v2_struct_0(sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0))) )),
% 0.20/0.47    inference(resolution,[],[f25,f42])).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | v2_struct_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.20/0.47    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f200,plain,(
% 0.20/0.48    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2))),
% 0.20/0.48    inference(subsumption_resolution,[],[f199,f31])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    m1_pre_topc(sK2,sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f199,plain,(
% 0.20/0.48    ~m1_pre_topc(sK2,sK0) | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2))),
% 0.20/0.48    inference(resolution,[],[f155,f27])).
% 0.20/0.48  fof(f155,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_pre_topc(X0,sK3) | ~m1_pre_topc(X0,sK0) | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK4)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f154,f35])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    ~v2_struct_0(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f154,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v2_struct_0(sK0) | ~m1_pre_topc(X0,sK3) | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK4)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f153,f36])).
% 0.20/0.48  fof(f153,plain,(
% 0.20/0.48    ( ! [X0] : (~v2_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(sK0) | ~m1_pre_topc(X0,sK3) | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK4)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f152,f37])).
% 0.20/0.48  fof(f152,plain,(
% 0.20/0.48    ( ! [X0] : (~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(sK0) | ~m1_pre_topc(X0,sK3) | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK4)) )),
% 0.20/0.48    inference(resolution,[],[f116,f29])).
% 0.20/0.48  fof(f116,plain,(
% 0.20/0.48    ( ! [X2,X1] : (~m1_pre_topc(sK3,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~m1_pre_topc(X2,X1) | v2_struct_0(X1) | ~m1_pre_topc(X2,sK3) | k3_tmap_1(X1,sK1,sK3,X2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X2))) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f115,f26])).
% 0.20/0.48  fof(f115,plain,(
% 0.20/0.48    ( ! [X2,X1] : (~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(sK3,X1) | ~m1_pre_topc(X2,X1) | v2_struct_0(X1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(X2,sK3) | k3_tmap_1(X1,sK1,sK3,X2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X2))) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f114,f24])).
% 0.20/0.48  fof(f114,plain,(
% 0.20/0.48    ( ! [X2,X1] : (~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(sK3,X1) | ~m1_pre_topc(X2,X1) | ~v1_funct_1(sK4) | v2_struct_0(X1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(X2,sK3) | k3_tmap_1(X1,sK1,sK3,X2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X2))) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f113,f34])).
% 0.20/0.48  fof(f113,plain,(
% 0.20/0.48    ( ! [X2,X1] : (~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(sK1) | ~m1_pre_topc(sK3,X1) | ~m1_pre_topc(X2,X1) | ~v1_funct_1(sK4) | v2_struct_0(X1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(X2,sK3) | k3_tmap_1(X1,sK1,sK3,X2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X2))) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f112,f33])).
% 0.20/0.48  fof(f112,plain,(
% 0.20/0.48    ( ! [X2,X1] : (~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_pre_topc(sK3,X1) | ~m1_pre_topc(X2,X1) | ~v1_funct_1(sK4) | v2_struct_0(X1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(X2,sK3) | k3_tmap_1(X1,sK1,sK3,X2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X2))) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f100,f32])).
% 0.20/0.48  fof(f100,plain,(
% 0.20/0.48    ( ! [X2,X1] : (~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_pre_topc(sK3,X1) | ~m1_pre_topc(X2,X1) | ~v1_funct_1(sK4) | v2_struct_0(X1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(X2,sK3) | k3_tmap_1(X1,sK1,sK3,X2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X2))) )),
% 0.20/0.48    inference(resolution,[],[f25,f41])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | v2_struct_0(X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f213,plain,(
% 0.20/0.48    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,sK2),sK5)),
% 0.20/0.48    inference(subsumption_resolution,[],[f212,f206])).
% 0.20/0.48  fof(f206,plain,(
% 0.20/0.48    k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(sK1,sK3,sK2,sK4,sK5)) = k1_funct_1(sK5,sK6(sK1,sK3,sK2,sK4,sK5))),
% 0.20/0.48    inference(subsumption_resolution,[],[f205,f204])).
% 0.20/0.48  fof(f204,plain,(
% 0.20/0.48    m1_subset_1(sK6(sK1,sK3,sK2,sK4,sK5),u1_struct_0(sK3))),
% 0.20/0.48    inference(resolution,[],[f202,f178])).
% 0.20/0.48  fof(f178,plain,(
% 0.20/0.48    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,sK2),sK5) | m1_subset_1(sK6(sK1,sK3,sK2,sK4,sK5),u1_struct_0(sK3))),
% 0.20/0.48    inference(subsumption_resolution,[],[f177,f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f177,plain,(
% 0.20/0.48    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | m1_subset_1(sK6(sK1,sK3,sK2,sK4,sK5),u1_struct_0(sK3)) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,sK2),sK5)),
% 0.20/0.48    inference(subsumption_resolution,[],[f176,f30])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ~v2_struct_0(sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f176,plain,(
% 0.20/0.48    v2_struct_0(sK2) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | m1_subset_1(sK6(sK1,sK3,sK2,sK4,sK5),u1_struct_0(sK3)) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,sK2),sK5)),
% 0.20/0.48    inference(subsumption_resolution,[],[f175,f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    v1_funct_1(sK5)),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f175,plain,(
% 0.20/0.48    ~v1_funct_1(sK5) | v2_struct_0(sK2) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | m1_subset_1(sK6(sK1,sK3,sK2,sK4,sK5),u1_struct_0(sK3)) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,sK2),sK5)),
% 0.20/0.48    inference(subsumption_resolution,[],[f173,f27])).
% 0.20/0.48  fof(f173,plain,(
% 0.20/0.48    ~m1_pre_topc(sK2,sK3) | ~v1_funct_1(sK5) | v2_struct_0(sK2) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | m1_subset_1(sK6(sK1,sK3,sK2,sK4,sK5),u1_struct_0(sK3)) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,sK2),sK5)),
% 0.20/0.48    inference(resolution,[],[f124,f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f124,plain,(
% 0.20/0.48    ( ! [X4,X3] : (~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) | ~m1_pre_topc(X3,sK3) | ~v1_funct_1(X4) | v2_struct_0(X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) | m1_subset_1(sK6(sK1,sK3,X3,sK4,X4),u1_struct_0(sK3)) | r2_funct_2(u1_struct_0(X3),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,X3),X4)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f123,f26])).
% 0.20/0.48  fof(f123,plain,(
% 0.20/0.48    ( ! [X4,X3] : (v2_struct_0(X3) | ~m1_pre_topc(X3,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) | m1_subset_1(sK6(sK1,sK3,X3,sK4,X4),u1_struct_0(sK3)) | r2_funct_2(u1_struct_0(X3),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,X3),X4)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f122,f32])).
% 0.20/0.48  fof(f122,plain,(
% 0.20/0.48    ( ! [X4,X3] : (v2_struct_0(X3) | ~m1_pre_topc(X3,sK3) | v2_struct_0(sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) | m1_subset_1(sK6(sK1,sK3,X3,sK4,X4),u1_struct_0(sK3)) | r2_funct_2(u1_struct_0(X3),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,X3),X4)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f121,f24])).
% 0.20/0.48  fof(f121,plain,(
% 0.20/0.48    ( ! [X4,X3] : (v2_struct_0(X3) | ~m1_pre_topc(X3,sK3) | ~v1_funct_1(sK4) | v2_struct_0(sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) | m1_subset_1(sK6(sK1,sK3,X3,sK4,X4),u1_struct_0(sK3)) | r2_funct_2(u1_struct_0(X3),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,X3),X4)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f120,f49])).
% 0.20/0.48  fof(f120,plain,(
% 0.20/0.48    ( ! [X4,X3] : (~l1_pre_topc(sK3) | v2_struct_0(X3) | ~m1_pre_topc(X3,sK3) | ~v1_funct_1(sK4) | v2_struct_0(sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) | m1_subset_1(sK6(sK1,sK3,X3,sK4,X4),u1_struct_0(sK3)) | r2_funct_2(u1_struct_0(X3),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,X3),X4)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f119,f51])).
% 0.20/0.48  fof(f119,plain,(
% 0.20/0.48    ( ! [X4,X3] : (~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | v2_struct_0(X3) | ~m1_pre_topc(X3,sK3) | ~v1_funct_1(sK4) | v2_struct_0(sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) | m1_subset_1(sK6(sK1,sK3,X3,sK4,X4),u1_struct_0(sK3)) | r2_funct_2(u1_struct_0(X3),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,X3),X4)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f118,f28])).
% 0.20/0.48  fof(f118,plain,(
% 0.20/0.48    ( ! [X4,X3] : (v2_struct_0(sK3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | v2_struct_0(X3) | ~m1_pre_topc(X3,sK3) | ~v1_funct_1(sK4) | v2_struct_0(sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) | m1_subset_1(sK6(sK1,sK3,X3,sK4,X4),u1_struct_0(sK3)) | r2_funct_2(u1_struct_0(X3),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,X3),X4)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f117,f34])).
% 0.20/0.48  fof(f117,plain,(
% 0.20/0.48    ( ! [X4,X3] : (~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | v2_struct_0(X3) | ~m1_pre_topc(X3,sK3) | ~v1_funct_1(sK4) | v2_struct_0(sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) | m1_subset_1(sK6(sK1,sK3,X3,sK4,X4),u1_struct_0(sK3)) | r2_funct_2(u1_struct_0(X3),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,X3),X4)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f101,f33])).
% 0.20/0.48  fof(f101,plain,(
% 0.20/0.48    ( ! [X4,X3] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | v2_struct_0(X3) | ~m1_pre_topc(X3,sK3) | ~v1_funct_1(sK4) | v2_struct_0(sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) | m1_subset_1(sK6(sK1,sK3,X3,sK4,X4),u1_struct_0(sK3)) | r2_funct_2(u1_struct_0(X3),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,X3),X4)) )),
% 0.20/0.48    inference(resolution,[],[f25,f38])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X1) | ~v1_funct_1(X3) | v2_struct_0(X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | m1_subset_1(sK6(X0,X1,X2,X3,X4),u1_struct_0(X1)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | ? [X5] : (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f10])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | ? [X5] : ((k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X1)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3))) | (~m1_pre_topc(X2,X1) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) => (! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => (r2_hidden(X5,u1_struct_0(X2)) => k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5))) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)))))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_tmap_1)).
% 0.20/0.48  fof(f205,plain,(
% 0.20/0.48    ~m1_subset_1(sK6(sK1,sK3,sK2,sK4,sK5),u1_struct_0(sK3)) | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(sK1,sK3,sK2,sK4,sK5)) = k1_funct_1(sK5,sK6(sK1,sK3,sK2,sK4,sK5))),
% 0.20/0.48    inference(resolution,[],[f203,f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ( ! [X6] : (~r2_hidden(X6,u1_struct_0(sK2)) | ~m1_subset_1(X6,u1_struct_0(sK3)) | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X6) = k1_funct_1(sK5,X6)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f203,plain,(
% 0.20/0.48    r2_hidden(sK6(sK1,sK3,sK2,sK4,sK5),u1_struct_0(sK2))),
% 0.20/0.48    inference(resolution,[],[f202,f187])).
% 0.20/0.48  fof(f187,plain,(
% 0.20/0.48    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,sK2),sK5) | r2_hidden(sK6(sK1,sK3,sK2,sK4,sK5),u1_struct_0(sK2))),
% 0.20/0.48    inference(subsumption_resolution,[],[f186,f22])).
% 0.20/0.48  fof(f186,plain,(
% 0.20/0.48    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | r2_hidden(sK6(sK1,sK3,sK2,sK4,sK5),u1_struct_0(sK2)) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,sK2),sK5)),
% 0.20/0.48    inference(subsumption_resolution,[],[f185,f30])).
% 0.20/0.48  fof(f185,plain,(
% 0.20/0.48    v2_struct_0(sK2) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | r2_hidden(sK6(sK1,sK3,sK2,sK4,sK5),u1_struct_0(sK2)) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,sK2),sK5)),
% 0.20/0.48    inference(subsumption_resolution,[],[f184,f20])).
% 0.20/0.48  fof(f184,plain,(
% 0.20/0.48    ~v1_funct_1(sK5) | v2_struct_0(sK2) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | r2_hidden(sK6(sK1,sK3,sK2,sK4,sK5),u1_struct_0(sK2)) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,sK2),sK5)),
% 0.20/0.48    inference(subsumption_resolution,[],[f182,f27])).
% 0.20/0.48  fof(f182,plain,(
% 0.20/0.48    ~m1_pre_topc(sK2,sK3) | ~v1_funct_1(sK5) | v2_struct_0(sK2) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | r2_hidden(sK6(sK1,sK3,sK2,sK4,sK5),u1_struct_0(sK2)) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,sK2),sK5)),
% 0.20/0.48    inference(resolution,[],[f132,f21])).
% 0.20/0.48  fof(f132,plain,(
% 0.20/0.48    ( ! [X6,X5] : (~v1_funct_2(X6,u1_struct_0(X5),u1_struct_0(sK1)) | ~m1_pre_topc(X5,sK3) | ~v1_funct_1(X6) | v2_struct_0(X5) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1)))) | r2_hidden(sK6(sK1,sK3,X5,sK4,X6),u1_struct_0(X5)) | r2_funct_2(u1_struct_0(X5),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,X5),X6)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f131,f26])).
% 0.20/0.48  fof(f131,plain,(
% 0.20/0.48    ( ! [X6,X5] : (v2_struct_0(X5) | ~m1_pre_topc(X5,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(X6) | ~v1_funct_2(X6,u1_struct_0(X5),u1_struct_0(sK1)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1)))) | r2_hidden(sK6(sK1,sK3,X5,sK4,X6),u1_struct_0(X5)) | r2_funct_2(u1_struct_0(X5),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,X5),X6)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f130,f32])).
% 0.20/0.48  fof(f130,plain,(
% 0.20/0.48    ( ! [X6,X5] : (v2_struct_0(X5) | ~m1_pre_topc(X5,sK3) | v2_struct_0(sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(X6) | ~v1_funct_2(X6,u1_struct_0(X5),u1_struct_0(sK1)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1)))) | r2_hidden(sK6(sK1,sK3,X5,sK4,X6),u1_struct_0(X5)) | r2_funct_2(u1_struct_0(X5),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,X5),X6)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f129,f24])).
% 0.20/0.48  fof(f129,plain,(
% 0.20/0.48    ( ! [X6,X5] : (v2_struct_0(X5) | ~m1_pre_topc(X5,sK3) | ~v1_funct_1(sK4) | v2_struct_0(sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(X6) | ~v1_funct_2(X6,u1_struct_0(X5),u1_struct_0(sK1)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1)))) | r2_hidden(sK6(sK1,sK3,X5,sK4,X6),u1_struct_0(X5)) | r2_funct_2(u1_struct_0(X5),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,X5),X6)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f128,f49])).
% 0.20/0.48  fof(f128,plain,(
% 0.20/0.48    ( ! [X6,X5] : (~l1_pre_topc(sK3) | v2_struct_0(X5) | ~m1_pre_topc(X5,sK3) | ~v1_funct_1(sK4) | v2_struct_0(sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(X6) | ~v1_funct_2(X6,u1_struct_0(X5),u1_struct_0(sK1)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1)))) | r2_hidden(sK6(sK1,sK3,X5,sK4,X6),u1_struct_0(X5)) | r2_funct_2(u1_struct_0(X5),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,X5),X6)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f127,f51])).
% 0.20/0.48  fof(f127,plain,(
% 0.20/0.48    ( ! [X6,X5] : (~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | v2_struct_0(X5) | ~m1_pre_topc(X5,sK3) | ~v1_funct_1(sK4) | v2_struct_0(sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(X6) | ~v1_funct_2(X6,u1_struct_0(X5),u1_struct_0(sK1)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1)))) | r2_hidden(sK6(sK1,sK3,X5,sK4,X6),u1_struct_0(X5)) | r2_funct_2(u1_struct_0(X5),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,X5),X6)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f126,f28])).
% 0.20/0.48  fof(f126,plain,(
% 0.20/0.48    ( ! [X6,X5] : (v2_struct_0(sK3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | v2_struct_0(X5) | ~m1_pre_topc(X5,sK3) | ~v1_funct_1(sK4) | v2_struct_0(sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(X6) | ~v1_funct_2(X6,u1_struct_0(X5),u1_struct_0(sK1)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1)))) | r2_hidden(sK6(sK1,sK3,X5,sK4,X6),u1_struct_0(X5)) | r2_funct_2(u1_struct_0(X5),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,X5),X6)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f125,f34])).
% 0.20/0.48  fof(f125,plain,(
% 0.20/0.48    ( ! [X6,X5] : (~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | v2_struct_0(X5) | ~m1_pre_topc(X5,sK3) | ~v1_funct_1(sK4) | v2_struct_0(sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(X6) | ~v1_funct_2(X6,u1_struct_0(X5),u1_struct_0(sK1)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1)))) | r2_hidden(sK6(sK1,sK3,X5,sK4,X6),u1_struct_0(X5)) | r2_funct_2(u1_struct_0(X5),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,X5),X6)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f102,f33])).
% 0.20/0.48  fof(f102,plain,(
% 0.20/0.48    ( ! [X6,X5] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | v2_struct_0(X5) | ~m1_pre_topc(X5,sK3) | ~v1_funct_1(sK4) | v2_struct_0(sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(X6) | ~v1_funct_2(X6,u1_struct_0(X5),u1_struct_0(sK1)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1)))) | r2_hidden(sK6(sK1,sK3,X5,sK4,X6),u1_struct_0(X5)) | r2_funct_2(u1_struct_0(X5),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,X5),X6)) )),
% 0.20/0.48    inference(resolution,[],[f25,f39])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X1) | ~v1_funct_1(X3) | v2_struct_0(X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | r2_hidden(sK6(X0,X1,X2,X3,X4),u1_struct_0(X2)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f212,plain,(
% 0.20/0.48    k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(sK1,sK3,sK2,sK4,sK5)) != k1_funct_1(sK5,sK6(sK1,sK3,sK2,sK4,sK5)) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,sK2),sK5)),
% 0.20/0.48    inference(subsumption_resolution,[],[f211,f22])).
% 0.20/0.48  fof(f211,plain,(
% 0.20/0.48    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(sK1,sK3,sK2,sK4,sK5)) != k1_funct_1(sK5,sK6(sK1,sK3,sK2,sK4,sK5)) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,sK2),sK5)),
% 0.20/0.48    inference(subsumption_resolution,[],[f210,f30])).
% 0.20/0.48  fof(f210,plain,(
% 0.20/0.48    v2_struct_0(sK2) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(sK1,sK3,sK2,sK4,sK5)) != k1_funct_1(sK5,sK6(sK1,sK3,sK2,sK4,sK5)) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,sK2),sK5)),
% 0.20/0.48    inference(subsumption_resolution,[],[f209,f20])).
% 0.20/0.48  fof(f209,plain,(
% 0.20/0.48    ~v1_funct_1(sK5) | v2_struct_0(sK2) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(sK1,sK3,sK2,sK4,sK5)) != k1_funct_1(sK5,sK6(sK1,sK3,sK2,sK4,sK5)) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,sK2),sK5)),
% 0.20/0.48    inference(subsumption_resolution,[],[f207,f27])).
% 0.20/0.48  fof(f207,plain,(
% 0.20/0.48    ~m1_pre_topc(sK2,sK3) | ~v1_funct_1(sK5) | v2_struct_0(sK2) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(sK1,sK3,sK2,sK4,sK5)) != k1_funct_1(sK5,sK6(sK1,sK3,sK2,sK4,sK5)) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,sK2),sK5)),
% 0.20/0.48    inference(resolution,[],[f140,f21])).
% 0.20/0.48  fof(f140,plain,(
% 0.20/0.48    ( ! [X8,X7] : (~v1_funct_2(X8,u1_struct_0(X7),u1_struct_0(sK1)) | ~m1_pre_topc(X7,sK3) | ~v1_funct_1(X8) | v2_struct_0(X7) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1)))) | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(sK1,sK3,X7,sK4,X8)) != k1_funct_1(X8,sK6(sK1,sK3,X7,sK4,X8)) | r2_funct_2(u1_struct_0(X7),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,X7),X8)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f139,f26])).
% 0.20/0.48  fof(f139,plain,(
% 0.20/0.48    ( ! [X8,X7] : (v2_struct_0(X7) | ~m1_pre_topc(X7,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(X8) | ~v1_funct_2(X8,u1_struct_0(X7),u1_struct_0(sK1)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1)))) | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(sK1,sK3,X7,sK4,X8)) != k1_funct_1(X8,sK6(sK1,sK3,X7,sK4,X8)) | r2_funct_2(u1_struct_0(X7),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,X7),X8)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f138,f32])).
% 0.20/0.48  fof(f138,plain,(
% 0.20/0.48    ( ! [X8,X7] : (v2_struct_0(X7) | ~m1_pre_topc(X7,sK3) | v2_struct_0(sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(X8) | ~v1_funct_2(X8,u1_struct_0(X7),u1_struct_0(sK1)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1)))) | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(sK1,sK3,X7,sK4,X8)) != k1_funct_1(X8,sK6(sK1,sK3,X7,sK4,X8)) | r2_funct_2(u1_struct_0(X7),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,X7),X8)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f137,f24])).
% 0.20/0.48  fof(f137,plain,(
% 0.20/0.48    ( ! [X8,X7] : (v2_struct_0(X7) | ~m1_pre_topc(X7,sK3) | ~v1_funct_1(sK4) | v2_struct_0(sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(X8) | ~v1_funct_2(X8,u1_struct_0(X7),u1_struct_0(sK1)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1)))) | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(sK1,sK3,X7,sK4,X8)) != k1_funct_1(X8,sK6(sK1,sK3,X7,sK4,X8)) | r2_funct_2(u1_struct_0(X7),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,X7),X8)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f136,f49])).
% 0.20/0.48  fof(f136,plain,(
% 0.20/0.48    ( ! [X8,X7] : (~l1_pre_topc(sK3) | v2_struct_0(X7) | ~m1_pre_topc(X7,sK3) | ~v1_funct_1(sK4) | v2_struct_0(sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(X8) | ~v1_funct_2(X8,u1_struct_0(X7),u1_struct_0(sK1)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1)))) | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(sK1,sK3,X7,sK4,X8)) != k1_funct_1(X8,sK6(sK1,sK3,X7,sK4,X8)) | r2_funct_2(u1_struct_0(X7),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,X7),X8)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f135,f51])).
% 0.20/0.48  fof(f135,plain,(
% 0.20/0.48    ( ! [X8,X7] : (~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | v2_struct_0(X7) | ~m1_pre_topc(X7,sK3) | ~v1_funct_1(sK4) | v2_struct_0(sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(X8) | ~v1_funct_2(X8,u1_struct_0(X7),u1_struct_0(sK1)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1)))) | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(sK1,sK3,X7,sK4,X8)) != k1_funct_1(X8,sK6(sK1,sK3,X7,sK4,X8)) | r2_funct_2(u1_struct_0(X7),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,X7),X8)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f134,f28])).
% 0.20/0.48  fof(f134,plain,(
% 0.20/0.48    ( ! [X8,X7] : (v2_struct_0(sK3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | v2_struct_0(X7) | ~m1_pre_topc(X7,sK3) | ~v1_funct_1(sK4) | v2_struct_0(sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(X8) | ~v1_funct_2(X8,u1_struct_0(X7),u1_struct_0(sK1)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1)))) | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(sK1,sK3,X7,sK4,X8)) != k1_funct_1(X8,sK6(sK1,sK3,X7,sK4,X8)) | r2_funct_2(u1_struct_0(X7),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,X7),X8)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f133,f34])).
% 0.20/0.48  fof(f133,plain,(
% 0.20/0.48    ( ! [X8,X7] : (~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | v2_struct_0(X7) | ~m1_pre_topc(X7,sK3) | ~v1_funct_1(sK4) | v2_struct_0(sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(X8) | ~v1_funct_2(X8,u1_struct_0(X7),u1_struct_0(sK1)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1)))) | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(sK1,sK3,X7,sK4,X8)) != k1_funct_1(X8,sK6(sK1,sK3,X7,sK4,X8)) | r2_funct_2(u1_struct_0(X7),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,X7),X8)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f103,f33])).
% 0.20/0.48  fof(f103,plain,(
% 0.20/0.48    ( ! [X8,X7] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | v2_struct_0(X7) | ~m1_pre_topc(X7,sK3) | ~v1_funct_1(sK4) | v2_struct_0(sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(X8) | ~v1_funct_2(X8,u1_struct_0(X7),u1_struct_0(sK1)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1)))) | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(sK1,sK3,X7,sK4,X8)) != k1_funct_1(X8,sK6(sK1,sK3,X7,sK4,X8)) | r2_funct_2(u1_struct_0(X7),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,X7),X8)) )),
% 0.20/0.48    inference(resolution,[],[f25,f40])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X1) | ~v1_funct_1(X3) | v2_struct_0(X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK6(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK6(X0,X1,X2,X3,X4)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (11407)------------------------------
% 0.20/0.48  % (11407)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (11407)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (11407)Memory used [KB]: 6268
% 0.20/0.48  % (11407)Time elapsed: 0.073 s
% 0.20/0.48  % (11407)------------------------------
% 0.20/0.48  % (11407)------------------------------
% 0.20/0.48  % (11386)Success in time 0.125 s
%------------------------------------------------------------------------------
