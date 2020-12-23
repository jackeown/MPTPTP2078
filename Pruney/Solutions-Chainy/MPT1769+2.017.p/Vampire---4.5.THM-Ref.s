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
% DateTime   : Thu Dec  3 13:18:46 EST 2020

% Result     : Theorem 1.38s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 579 expanded)
%              Number of leaves         :   10 ( 100 expanded)
%              Depth                    :   29
%              Number of atoms          :  558 (8361 expanded)
%              Number of equality atoms :   64 ( 448 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f171,plain,(
    $false ),
    inference(subsumption_resolution,[],[f169,f170])).

fof(f170,plain,(
    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
    inference(duplicate_literal_removal,[],[f167])).

fof(f167,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
    inference(backward_demodulation,[],[f125,f166])).

fof(f166,plain,(
    k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4) ),
    inference(forward_demodulation,[],[f163,f139])).

fof(f139,plain,(
    k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) ),
    inference(resolution,[],[f138,f47])).

fof(f47,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)
                              <~> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) )
                              & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                              & X0 = X3
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X6) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
                              ( ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)
                              <~> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) )
                              & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                              & X0 = X3
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X6) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
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
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                              & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                              & v1_funct_1(X5) )
                           => ! [X6] :
                                ( ( m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                                  & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                                  & v1_funct_1(X6) )
                               => ( ( r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                                    & X0 = X3 )
                                 => ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)
                                  <=> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
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
                         => ! [X6] :
                              ( ( m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                                & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                                & v1_funct_1(X6) )
                             => ( ( r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                                  & X0 = X3 )
                               => ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)
                                <=> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_tmap_1)).

fof(f138,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | k2_tmap_1(sK0,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f137,f43])).

fof(f43,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f16])).

fof(f137,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X0,sK0)
      | k2_tmap_1(sK0,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f136,f52])).

fof(f52,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f136,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X0,sK0)
      | k2_tmap_1(sK0,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f135,f51])).

fof(f51,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f135,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X0,sK0)
      | k2_tmap_1(sK0,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f134,f50])).

fof(f50,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f134,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK1)
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X0,sK0)
      | k2_tmap_1(sK0,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f133,f49])).

fof(f49,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f133,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X0,sK0)
      | k2_tmap_1(sK0,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f132,f48])).

fof(f48,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f132,plain,(
    ! [X0] :
      ( v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X0,sK0)
      | k2_tmap_1(sK0,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f131,f53])).

fof(f53,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f131,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X0,sK0)
      | k2_tmap_1(sK0,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) ) ),
    inference(resolution,[],[f129,f42])).

fof(f42,plain,(
    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_pre_topc(X2,X0)
      | k2_tmap_1(X0,X1,sK4,X2) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) ) ),
    inference(resolution,[],[f58,f41])).

fof(f41,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f16])).

fof(f58,plain,(
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
    inference(cnf_transformation,[],[f22])).

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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f163,plain,(
    k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) ),
    inference(resolution,[],[f162,f47])).

fof(f162,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK0,X0,sK4) ) ),
    inference(subsumption_resolution,[],[f161,f52])).

fof(f161,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK0,X0,sK4) ) ),
    inference(subsumption_resolution,[],[f160,f51])).

fof(f160,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK0,X0,sK4) ) ),
    inference(subsumption_resolution,[],[f157,f53])).

fof(f157,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK0,X0,sK4) ) ),
    inference(resolution,[],[f156,f71])).

fof(f71,plain,(
    m1_pre_topc(sK0,sK0) ),
    inference(backward_demodulation,[],[f45,f36])).

fof(f36,plain,(
    sK0 = sK3 ),
    inference(cnf_transformation,[],[f16])).

fof(f45,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f156,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(sK0,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,sK0)
      | k3_tmap_1(X0,sK1,sK0,X1,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f155,f43])).

fof(f155,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK0,X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X1,sK0)
      | k3_tmap_1(X0,sK1,sK0,X1,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f154,f50])).

fof(f154,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(sK1)
      | ~ m1_pre_topc(sK0,X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X1,sK0)
      | k3_tmap_1(X0,sK1,sK0,X1,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f153,f49])).

fof(f153,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ m1_pre_topc(sK0,X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X1,sK0)
      | k3_tmap_1(X0,sK1,sK0,X1,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f152,f48])).

fof(f152,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ m1_pre_topc(sK0,X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X1,sK0)
      | k3_tmap_1(X0,sK1,sK0,X1,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X1)) ) ),
    inference(resolution,[],[f144,f42])).

fof(f144,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(sK4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X2)
      | k3_tmap_1(X0,X1,X2,X3,sK4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),sK4,u1_struct_0(X3)) ) ),
    inference(subsumption_resolution,[],[f142,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X1)
      | m1_pre_topc(X2,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
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
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f142,plain,(
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
    inference(resolution,[],[f57,f41])).

fof(f57,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).

fof(f125,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
    inference(backward_demodulation,[],[f75,f119])).

fof(f119,plain,(
    sK4 = sK6 ),
    inference(subsumption_resolution,[],[f118,f48])).

fof(f118,plain,
    ( v2_struct_0(sK1)
    | sK4 = sK6 ),
    inference(subsumption_resolution,[],[f117,f50])).

fof(f117,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | sK4 = sK6 ),
    inference(subsumption_resolution,[],[f116,f49])).

fof(f116,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | sK4 = sK6 ),
    inference(subsumption_resolution,[],[f110,f54])).

fof(f54,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f110,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | sK4 = sK6 ),
    inference(superposition,[],[f60,f106])).

fof(f106,plain,
    ( k1_xboole_0 = sK7(sK1)
    | sK4 = sK6 ),
    inference(resolution,[],[f105,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f105,plain,(
    ! [X0] :
      ( r1_tarski(sK7(sK1),X0)
      | sK4 = sK6 ) ),
    inference(resolution,[],[f104,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK8(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f104,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK7(sK1))
      | sK4 = sK6 ) ),
    inference(subsumption_resolution,[],[f103,f48])).

fof(f103,plain,(
    ! [X0] :
      ( sK4 = sK6
      | ~ r2_hidden(X0,sK7(sK1))
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f102,f50])).

fof(f102,plain,(
    ! [X0] :
      ( sK4 = sK6
      | ~ r2_hidden(X0,sK7(sK1))
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f101,f49])).

fof(f101,plain,(
    ! [X0] :
      ( sK4 = sK6
      | ~ r2_hidden(X0,sK7(sK1))
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f100,f59])).

fof(f59,plain,(
    ! [X0] :
      ( m1_subset_1(sK7(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v4_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc7_pre_topc)).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | sK4 = sK6
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f99,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f99,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | sK4 = sK6 ),
    inference(subsumption_resolution,[],[f98,f72])).

fof(f72,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(forward_demodulation,[],[f35,f36])).

fof(f35,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f16])).

fof(f98,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | sK4 = sK6 ),
    inference(subsumption_resolution,[],[f97,f73])).

fof(f73,plain,(
    v1_funct_2(sK6,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f34,f36])).

fof(f34,plain,(
    v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f97,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_funct_2(sK6,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | sK4 = sK6 ),
    inference(subsumption_resolution,[],[f96,f33])).

fof(f33,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f16])).

fof(f96,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_funct_1(sK6)
    | ~ v1_funct_2(sK6,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | sK4 = sK6 ),
    inference(subsumption_resolution,[],[f95,f43])).

fof(f95,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK6)
    | ~ v1_funct_2(sK6,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | sK4 = sK6 ),
    inference(subsumption_resolution,[],[f94,f42])).

fof(f94,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK6)
    | ~ v1_funct_2(sK6,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | sK4 = sK6 ),
    inference(subsumption_resolution,[],[f93,f41])).

fof(f93,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK6)
    | ~ v1_funct_2(sK6,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | sK4 = sK6 ),
    inference(duplicate_literal_removal,[],[f90])).

fof(f90,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK6)
    | ~ v1_funct_2(sK6,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | sK4 = sK6
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(resolution,[],[f66,f69])).

fof(f69,plain,(
    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6) ),
    inference(backward_demodulation,[],[f37,f36])).

fof(f37,plain,(
    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6) ),
    inference(cnf_transformation,[],[f16])).

fof(f66,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
      | v1_xboole_0(X3)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X0,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | X4 = X5
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_2(X5,X2,X3)
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4)
        & ~ v1_xboole_0(X3)
        & ~ v1_xboole_0(X1) )
     => ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK7(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f75,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK6),sK5)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
    inference(forward_demodulation,[],[f31,f36])).

fof(f31,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5) ),
    inference(cnf_transformation,[],[f16])).

fof(f169,plain,(
    ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
    inference(duplicate_literal_removal,[],[f168])).

fof(f168,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
    inference(backward_demodulation,[],[f124,f166])).

fof(f124,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
    inference(backward_demodulation,[],[f74,f119])).

fof(f74,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK6),sK5)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
    inference(forward_demodulation,[],[f32,f36])).

fof(f32,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:21:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.53  % (28970)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.38/0.55  % (28970)Refutation found. Thanks to Tanya!
% 1.38/0.55  % SZS status Theorem for theBenchmark
% 1.38/0.56  % (28986)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.38/0.56  % SZS output start Proof for theBenchmark
% 1.38/0.56  fof(f171,plain,(
% 1.38/0.56    $false),
% 1.38/0.56    inference(subsumption_resolution,[],[f169,f170])).
% 1.38/0.56  fof(f170,plain,(
% 1.38/0.56    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)),
% 1.38/0.56    inference(duplicate_literal_removal,[],[f167])).
% 1.38/0.56  fof(f167,plain,(
% 1.38/0.56    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)),
% 1.38/0.56    inference(backward_demodulation,[],[f125,f166])).
% 1.38/0.56  fof(f166,plain,(
% 1.38/0.56    k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4)),
% 1.38/0.56    inference(forward_demodulation,[],[f163,f139])).
% 1.38/0.56  fof(f139,plain,(
% 1.38/0.56    k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2))),
% 1.38/0.56    inference(resolution,[],[f138,f47])).
% 1.38/0.56  fof(f47,plain,(
% 1.38/0.56    m1_pre_topc(sK2,sK0)),
% 1.38/0.56    inference(cnf_transformation,[],[f16])).
% 1.38/0.56  fof(f16,plain,(
% 1.38/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <~> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.38/0.56    inference(flattening,[],[f15])).
% 1.38/0.56  fof(f15,plain,(
% 1.38/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <~> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)) & (r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3)) & (m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.38/0.56    inference(ennf_transformation,[],[f12])).
% 1.38/0.56  fof(f12,negated_conjecture,(
% 1.38/0.56    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) => ((r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3) => (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <=> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5))))))))))),
% 1.38/0.56    inference(negated_conjecture,[],[f11])).
% 1.38/0.56  fof(f11,conjecture,(
% 1.38/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) => ((r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3) => (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <=> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5))))))))))),
% 1.38/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_tmap_1)).
% 1.38/0.56  fof(f138,plain,(
% 1.38/0.56    ( ! [X0] : (~m1_pre_topc(X0,sK0) | k2_tmap_1(sK0,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0))) )),
% 1.38/0.56    inference(subsumption_resolution,[],[f137,f43])).
% 1.38/0.56  fof(f43,plain,(
% 1.38/0.56    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.38/0.56    inference(cnf_transformation,[],[f16])).
% 1.38/0.56  fof(f137,plain,(
% 1.38/0.56    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_pre_topc(X0,sK0) | k2_tmap_1(sK0,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0))) )),
% 1.38/0.56    inference(subsumption_resolution,[],[f136,f52])).
% 1.38/0.56  fof(f52,plain,(
% 1.38/0.56    v2_pre_topc(sK0)),
% 1.38/0.56    inference(cnf_transformation,[],[f16])).
% 1.38/0.56  fof(f136,plain,(
% 1.38/0.56    ( ! [X0] : (~v2_pre_topc(sK0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_pre_topc(X0,sK0) | k2_tmap_1(sK0,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0))) )),
% 1.38/0.56    inference(subsumption_resolution,[],[f135,f51])).
% 1.38/0.56  fof(f51,plain,(
% 1.38/0.56    ~v2_struct_0(sK0)),
% 1.38/0.56    inference(cnf_transformation,[],[f16])).
% 1.38/0.56  fof(f135,plain,(
% 1.38/0.56    ( ! [X0] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_pre_topc(X0,sK0) | k2_tmap_1(sK0,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0))) )),
% 1.38/0.56    inference(subsumption_resolution,[],[f134,f50])).
% 1.38/0.56  fof(f50,plain,(
% 1.38/0.56    l1_pre_topc(sK1)),
% 1.38/0.56    inference(cnf_transformation,[],[f16])).
% 1.38/0.56  fof(f134,plain,(
% 1.38/0.56    ( ! [X0] : (~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_pre_topc(X0,sK0) | k2_tmap_1(sK0,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0))) )),
% 1.38/0.56    inference(subsumption_resolution,[],[f133,f49])).
% 1.38/0.56  fof(f49,plain,(
% 1.38/0.56    v2_pre_topc(sK1)),
% 1.38/0.56    inference(cnf_transformation,[],[f16])).
% 1.38/0.56  fof(f133,plain,(
% 1.38/0.56    ( ! [X0] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_pre_topc(X0,sK0) | k2_tmap_1(sK0,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0))) )),
% 1.38/0.56    inference(subsumption_resolution,[],[f132,f48])).
% 1.38/0.56  fof(f48,plain,(
% 1.38/0.56    ~v2_struct_0(sK1)),
% 1.38/0.56    inference(cnf_transformation,[],[f16])).
% 1.38/0.56  fof(f132,plain,(
% 1.38/0.56    ( ! [X0] : (v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_pre_topc(X0,sK0) | k2_tmap_1(sK0,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0))) )),
% 1.38/0.56    inference(subsumption_resolution,[],[f131,f53])).
% 1.38/0.56  fof(f53,plain,(
% 1.38/0.56    l1_pre_topc(sK0)),
% 1.38/0.56    inference(cnf_transformation,[],[f16])).
% 1.38/0.56  fof(f131,plain,(
% 1.38/0.56    ( ! [X0] : (~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_pre_topc(X0,sK0) | k2_tmap_1(sK0,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0))) )),
% 1.38/0.56    inference(resolution,[],[f129,f42])).
% 1.38/0.56  fof(f42,plain,(
% 1.38/0.56    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.38/0.56    inference(cnf_transformation,[],[f16])).
% 1.38/0.56  fof(f129,plain,(
% 1.38/0.56    ( ! [X2,X0,X1] : (~v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_pre_topc(X2,X0) | k2_tmap_1(X0,X1,sK4,X2) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2))) )),
% 1.38/0.56    inference(resolution,[],[f58,f41])).
% 1.38/0.56  fof(f41,plain,(
% 1.38/0.56    v1_funct_1(sK4)),
% 1.38/0.56    inference(cnf_transformation,[],[f16])).
% 1.38/0.56  fof(f58,plain,(
% 1.38/0.56    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))) )),
% 1.38/0.56    inference(cnf_transformation,[],[f22])).
% 1.38/0.56  fof(f22,plain,(
% 1.38/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.38/0.56    inference(flattening,[],[f21])).
% 1.38/0.56  fof(f21,plain,(
% 1.38/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.38/0.56    inference(ennf_transformation,[],[f7])).
% 1.38/0.56  fof(f7,axiom,(
% 1.38/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 1.38/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).
% 1.38/0.56  fof(f163,plain,(
% 1.38/0.56    k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2))),
% 1.38/0.56    inference(resolution,[],[f162,f47])).
% 1.38/0.56  fof(f162,plain,(
% 1.38/0.56    ( ! [X0] : (~m1_pre_topc(X0,sK0) | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK0,X0,sK4)) )),
% 1.38/0.56    inference(subsumption_resolution,[],[f161,f52])).
% 1.38/0.56  fof(f161,plain,(
% 1.38/0.56    ( ! [X0] : (~v2_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK0,X0,sK4)) )),
% 1.38/0.56    inference(subsumption_resolution,[],[f160,f51])).
% 1.38/0.56  fof(f160,plain,(
% 1.38/0.56    ( ! [X0] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK0,X0,sK4)) )),
% 1.38/0.56    inference(subsumption_resolution,[],[f157,f53])).
% 1.38/0.56  fof(f157,plain,(
% 1.38/0.56    ( ! [X0] : (~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK0,X0,sK4)) )),
% 1.38/0.56    inference(resolution,[],[f156,f71])).
% 1.38/0.56  fof(f71,plain,(
% 1.38/0.56    m1_pre_topc(sK0,sK0)),
% 1.38/0.56    inference(backward_demodulation,[],[f45,f36])).
% 1.38/0.56  fof(f36,plain,(
% 1.38/0.56    sK0 = sK3),
% 1.38/0.56    inference(cnf_transformation,[],[f16])).
% 1.38/0.56  fof(f45,plain,(
% 1.38/0.56    m1_pre_topc(sK3,sK0)),
% 1.38/0.56    inference(cnf_transformation,[],[f16])).
% 1.38/0.56  fof(f156,plain,(
% 1.38/0.56    ( ! [X0,X1] : (~m1_pre_topc(sK0,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X1,sK0) | k3_tmap_1(X0,sK1,sK0,X1,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X1))) )),
% 1.38/0.56    inference(subsumption_resolution,[],[f155,f43])).
% 1.38/0.56  fof(f155,plain,(
% 1.38/0.56    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(sK0,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_pre_topc(X1,sK0) | k3_tmap_1(X0,sK1,sK0,X1,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X1))) )),
% 1.38/0.56    inference(subsumption_resolution,[],[f154,f50])).
% 1.38/0.56  fof(f154,plain,(
% 1.38/0.56    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~l1_pre_topc(sK1) | ~m1_pre_topc(sK0,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_pre_topc(X1,sK0) | k3_tmap_1(X0,sK1,sK0,X1,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X1))) )),
% 1.38/0.56    inference(subsumption_resolution,[],[f153,f49])).
% 1.38/0.56  fof(f153,plain,(
% 1.38/0.56    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_pre_topc(sK0,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_pre_topc(X1,sK0) | k3_tmap_1(X0,sK1,sK0,X1,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X1))) )),
% 1.38/0.56    inference(subsumption_resolution,[],[f152,f48])).
% 1.38/0.56  fof(f152,plain,(
% 1.38/0.56    ( ! [X0,X1] : (~l1_pre_topc(X0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_pre_topc(sK0,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_pre_topc(X1,sK0) | k3_tmap_1(X0,sK1,sK0,X1,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X1))) )),
% 1.38/0.56    inference(resolution,[],[f144,f42])).
% 1.38/0.56  fof(f144,plain,(
% 1.38/0.56    ( ! [X2,X0,X3,X1] : (~v1_funct_2(sK4,u1_struct_0(X2),u1_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,sK4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),sK4,u1_struct_0(X3))) )),
% 1.38/0.56    inference(subsumption_resolution,[],[f142,f61])).
% 1.38/0.56  fof(f61,plain,(
% 1.38/0.56    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X1) | m1_pre_topc(X2,X0)) )),
% 1.38/0.56    inference(cnf_transformation,[],[f26])).
% 1.38/0.56  fof(f26,plain,(
% 1.38/0.56    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.38/0.56    inference(flattening,[],[f25])).
% 1.38/0.56  fof(f25,plain,(
% 1.38/0.56    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.38/0.56    inference(ennf_transformation,[],[f10])).
% 1.38/0.56  fof(f10,axiom,(
% 1.38/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 1.38/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).
% 1.38/0.56  fof(f142,plain,(
% 1.38/0.56    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X3,X0) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,sK4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),sK4,u1_struct_0(X3))) )),
% 1.38/0.56    inference(resolution,[],[f57,f41])).
% 1.38/0.56  fof(f57,plain,(
% 1.38/0.56    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X4) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X3,X0) | v2_struct_0(X0) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))) )),
% 1.38/0.56    inference(cnf_transformation,[],[f20])).
% 1.38/0.56  fof(f20,plain,(
% 1.38/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.38/0.56    inference(flattening,[],[f19])).
% 1.38/0.56  fof(f19,plain,(
% 1.38/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.38/0.56    inference(ennf_transformation,[],[f8])).
% 1.38/0.56  fof(f8,axiom,(
% 1.38/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 1.38/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).
% 1.38/0.56  fof(f125,plain,(
% 1.38/0.56    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)),
% 1.38/0.56    inference(backward_demodulation,[],[f75,f119])).
% 1.38/0.56  fof(f119,plain,(
% 1.38/0.56    sK4 = sK6),
% 1.38/0.56    inference(subsumption_resolution,[],[f118,f48])).
% 1.38/0.56  fof(f118,plain,(
% 1.38/0.56    v2_struct_0(sK1) | sK4 = sK6),
% 1.38/0.56    inference(subsumption_resolution,[],[f117,f50])).
% 1.38/0.56  fof(f117,plain,(
% 1.38/0.56    ~l1_pre_topc(sK1) | v2_struct_0(sK1) | sK4 = sK6),
% 1.38/0.56    inference(subsumption_resolution,[],[f116,f49])).
% 1.38/0.56  fof(f116,plain,(
% 1.38/0.56    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | sK4 = sK6),
% 1.38/0.56    inference(subsumption_resolution,[],[f110,f54])).
% 1.38/0.56  fof(f54,plain,(
% 1.38/0.56    v1_xboole_0(k1_xboole_0)),
% 1.38/0.56    inference(cnf_transformation,[],[f2])).
% 1.38/0.56  fof(f2,axiom,(
% 1.38/0.56    v1_xboole_0(k1_xboole_0)),
% 1.38/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.38/0.56  fof(f110,plain,(
% 1.38/0.56    ~v1_xboole_0(k1_xboole_0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | sK4 = sK6),
% 1.38/0.56    inference(superposition,[],[f60,f106])).
% 1.38/0.56  fof(f106,plain,(
% 1.38/0.56    k1_xboole_0 = sK7(sK1) | sK4 = sK6),
% 1.38/0.56    inference(resolution,[],[f105,f56])).
% 1.38/0.56  fof(f56,plain,(
% 1.38/0.56    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.38/0.56    inference(cnf_transformation,[],[f18])).
% 1.38/0.56  fof(f18,plain,(
% 1.38/0.56    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 1.38/0.56    inference(ennf_transformation,[],[f3])).
% 1.38/0.56  fof(f3,axiom,(
% 1.38/0.56    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 1.38/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 1.38/0.56  fof(f105,plain,(
% 1.38/0.56    ( ! [X0] : (r1_tarski(sK7(sK1),X0) | sK4 = sK6) )),
% 1.38/0.56    inference(resolution,[],[f104,f62])).
% 1.38/0.56  fof(f62,plain,(
% 1.38/0.56    ( ! [X0,X1] : (r2_hidden(sK8(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.38/0.56    inference(cnf_transformation,[],[f27])).
% 1.38/0.56  fof(f27,plain,(
% 1.38/0.56    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 1.38/0.56    inference(ennf_transformation,[],[f13])).
% 1.38/0.56  fof(f13,plain,(
% 1.38/0.56    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 1.38/0.56    inference(unused_predicate_definition_removal,[],[f1])).
% 1.38/0.56  fof(f1,axiom,(
% 1.38/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.38/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.38/0.56  fof(f104,plain,(
% 1.38/0.56    ( ! [X0] : (~r2_hidden(X0,sK7(sK1)) | sK4 = sK6) )),
% 1.38/0.56    inference(subsumption_resolution,[],[f103,f48])).
% 1.38/0.56  fof(f103,plain,(
% 1.38/0.56    ( ! [X0] : (sK4 = sK6 | ~r2_hidden(X0,sK7(sK1)) | v2_struct_0(sK1)) )),
% 1.38/0.56    inference(subsumption_resolution,[],[f102,f50])).
% 1.38/0.56  fof(f102,plain,(
% 1.38/0.56    ( ! [X0] : (sK4 = sK6 | ~r2_hidden(X0,sK7(sK1)) | ~l1_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 1.38/0.56    inference(subsumption_resolution,[],[f101,f49])).
% 1.38/0.56  fof(f101,plain,(
% 1.38/0.56    ( ! [X0] : (sK4 = sK6 | ~r2_hidden(X0,sK7(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 1.38/0.56    inference(resolution,[],[f100,f59])).
% 1.38/0.56  fof(f59,plain,(
% 1.38/0.56    ( ! [X0] : (m1_subset_1(sK7(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.38/0.56    inference(cnf_transformation,[],[f24])).
% 1.38/0.56  fof(f24,plain,(
% 1.38/0.56    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.38/0.56    inference(flattening,[],[f23])).
% 1.38/0.56  fof(f23,plain,(
% 1.38/0.56    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.38/0.56    inference(ennf_transformation,[],[f14])).
% 1.38/0.56  fof(f14,plain,(
% 1.38/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.38/0.56    inference(pure_predicate_removal,[],[f5])).
% 1.38/0.56  fof(f5,axiom,(
% 1.38/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v4_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.38/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc7_pre_topc)).
% 1.38/0.56  fof(f100,plain,(
% 1.38/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | sK4 = sK6 | ~r2_hidden(X1,X0)) )),
% 1.38/0.56    inference(resolution,[],[f99,f64])).
% 1.38/0.56  fof(f64,plain,(
% 1.38/0.56    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.38/0.56    inference(cnf_transformation,[],[f28])).
% 1.38/0.56  fof(f28,plain,(
% 1.38/0.56    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.38/0.56    inference(ennf_transformation,[],[f4])).
% 1.38/0.56  fof(f4,axiom,(
% 1.38/0.56    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.38/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 1.38/0.56  fof(f99,plain,(
% 1.38/0.56    v1_xboole_0(u1_struct_0(sK1)) | sK4 = sK6),
% 1.38/0.56    inference(subsumption_resolution,[],[f98,f72])).
% 1.38/0.56  fof(f72,plain,(
% 1.38/0.56    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.38/0.56    inference(forward_demodulation,[],[f35,f36])).
% 1.38/0.56  fof(f35,plain,(
% 1.38/0.56    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 1.38/0.56    inference(cnf_transformation,[],[f16])).
% 1.38/0.56  fof(f98,plain,(
% 1.38/0.56    v1_xboole_0(u1_struct_0(sK1)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | sK4 = sK6),
% 1.38/0.56    inference(subsumption_resolution,[],[f97,f73])).
% 1.38/0.56  fof(f73,plain,(
% 1.38/0.56    v1_funct_2(sK6,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.38/0.56    inference(forward_demodulation,[],[f34,f36])).
% 1.38/0.56  fof(f34,plain,(
% 1.38/0.56    v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1))),
% 1.38/0.56    inference(cnf_transformation,[],[f16])).
% 1.38/0.56  fof(f97,plain,(
% 1.38/0.56    v1_xboole_0(u1_struct_0(sK1)) | ~v1_funct_2(sK6,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | sK4 = sK6),
% 1.38/0.56    inference(subsumption_resolution,[],[f96,f33])).
% 1.38/0.56  fof(f33,plain,(
% 1.38/0.56    v1_funct_1(sK6)),
% 1.38/0.56    inference(cnf_transformation,[],[f16])).
% 1.38/0.56  fof(f96,plain,(
% 1.38/0.56    v1_xboole_0(u1_struct_0(sK1)) | ~v1_funct_1(sK6) | ~v1_funct_2(sK6,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | sK4 = sK6),
% 1.38/0.56    inference(subsumption_resolution,[],[f95,f43])).
% 1.38/0.56  fof(f95,plain,(
% 1.38/0.56    v1_xboole_0(u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_1(sK6) | ~v1_funct_2(sK6,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | sK4 = sK6),
% 1.38/0.56    inference(subsumption_resolution,[],[f94,f42])).
% 1.38/0.56  fof(f94,plain,(
% 1.38/0.56    v1_xboole_0(u1_struct_0(sK1)) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_1(sK6) | ~v1_funct_2(sK6,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | sK4 = sK6),
% 1.38/0.56    inference(subsumption_resolution,[],[f93,f41])).
% 1.38/0.56  fof(f93,plain,(
% 1.38/0.56    v1_xboole_0(u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_1(sK6) | ~v1_funct_2(sK6,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | sK4 = sK6),
% 1.38/0.56    inference(duplicate_literal_removal,[],[f90])).
% 1.38/0.56  fof(f90,plain,(
% 1.38/0.56    v1_xboole_0(u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_1(sK6) | ~v1_funct_2(sK6,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | sK4 = sK6 | v1_xboole_0(u1_struct_0(sK1))),
% 1.38/0.56    inference(resolution,[],[f66,f69])).
% 1.38/0.56  fof(f69,plain,(
% 1.38/0.56    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)),
% 1.38/0.56    inference(backward_demodulation,[],[f37,f36])).
% 1.38/0.56  fof(f37,plain,(
% 1.38/0.56    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6)),
% 1.38/0.56    inference(cnf_transformation,[],[f16])).
% 1.38/0.56  fof(f66,plain,(
% 1.38/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (~r1_funct_2(X0,X1,X2,X3,X4,X5) | v1_xboole_0(X3) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X0,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X2,X3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | X4 = X5 | v1_xboole_0(X1)) )),
% 1.38/0.56    inference(cnf_transformation,[],[f30])).
% 1.38/0.56  fof(f30,plain,(
% 1.38/0.56    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 1.38/0.56    inference(flattening,[],[f29])).
% 1.38/0.56  fof(f29,plain,(
% 1.38/0.56    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 1.38/0.56    inference(ennf_transformation,[],[f6])).
% 1.38/0.56  fof(f6,axiom,(
% 1.38/0.56    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 1.38/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_funct_2)).
% 1.38/0.56  fof(f60,plain,(
% 1.38/0.56    ( ! [X0] : (~v1_xboole_0(sK7(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.38/0.56    inference(cnf_transformation,[],[f24])).
% 1.38/0.56  fof(f75,plain,(
% 1.38/0.56    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK6),sK5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)),
% 1.38/0.56    inference(forward_demodulation,[],[f31,f36])).
% 1.38/0.56  fof(f31,plain,(
% 1.38/0.56    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)),
% 1.38/0.56    inference(cnf_transformation,[],[f16])).
% 1.38/0.56  fof(f169,plain,(
% 1.38/0.56    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)),
% 1.38/0.56    inference(duplicate_literal_removal,[],[f168])).
% 1.38/0.56  fof(f168,plain,(
% 1.38/0.56    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)),
% 1.38/0.56    inference(backward_demodulation,[],[f124,f166])).
% 1.38/0.56  fof(f124,plain,(
% 1.38/0.56    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)),
% 1.38/0.56    inference(backward_demodulation,[],[f74,f119])).
% 1.38/0.56  fof(f74,plain,(
% 1.38/0.56    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK6),sK5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)),
% 1.38/0.56    inference(forward_demodulation,[],[f32,f36])).
% 1.38/0.56  fof(f32,plain,(
% 1.38/0.56    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)),
% 1.38/0.56    inference(cnf_transformation,[],[f16])).
% 1.38/0.56  % SZS output end Proof for theBenchmark
% 1.38/0.56  % (28970)------------------------------
% 1.38/0.56  % (28970)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.56  % (28970)Termination reason: Refutation
% 1.38/0.56  
% 1.38/0.56  % (28970)Memory used [KB]: 6396
% 1.38/0.56  % (28970)Time elapsed: 0.118 s
% 1.38/0.56  % (28970)------------------------------
% 1.38/0.56  % (28970)------------------------------
% 1.38/0.57  % (28963)Success in time 0.197 s
%------------------------------------------------------------------------------
