%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 753 expanded)
%              Number of leaves         :    9 ( 127 expanded)
%              Depth                    :   42
%              Number of atoms          : 1012 (11584 expanded)
%              Number of equality atoms :   32 (1398 expanded)
%              Maximal formula depth    :   30 (   9 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f191,plain,(
    $false ),
    inference(subsumption_resolution,[],[f190,f161])).

fof(f161,plain,(
    ~ r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(subsumption_resolution,[],[f156,f160])).

fof(f160,plain,(
    r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK5) ),
    inference(subsumption_resolution,[],[f159,f72])).

fof(f72,plain,
    ( r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK5)
    | r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(forward_demodulation,[],[f30,f33])).

fof(f33,plain,(
    sK5 = sK7 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( r1_tmap_1(X0,X1,X2,X5)
                                  <~> ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                      & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) ) )
                                  & X5 = X7
                                  & X5 = X6
                                  & m1_subset_1(X7,u1_struct_0(X4)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,u1_struct_0(X0)) )
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
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
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( r1_tmap_1(X0,X1,X2,X5)
                                  <~> ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                      & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) ) )
                                  & X5 = X7
                                  & X5 = X6
                                  & m1_subset_1(X7,u1_struct_0(X4)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,u1_struct_0(X0)) )
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
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
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_pre_topc(X4,X0)
                          & ~ v2_struct_0(X4) )
                       => ( k1_tsep_1(X0,X3,X4) = X0
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X0))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X3))
                                 => ! [X7] :
                                      ( m1_subset_1(X7,u1_struct_0(X4))
                                     => ( ( X5 = X7
                                          & X5 = X6 )
                                       => ( r1_tmap_1(X0,X1,X2,X5)
                                        <=> ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                            & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) ) ) ) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
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
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ( k1_tsep_1(X0,X3,X4) = X0
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X0))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X3))
                               => ! [X7] :
                                    ( m1_subset_1(X7,u1_struct_0(X4))
                                   => ( ( X5 = X7
                                        & X5 = X6 )
                                     => ( r1_tmap_1(X0,X1,X2,X5)
                                      <=> ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                          & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) ) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_tmap_1)).

fof(f30,plain,
    ( r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7)
    | r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(cnf_transformation,[],[f13])).

fof(f159,plain,
    ( ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK5) ),
    inference(subsumption_resolution,[],[f158,f36])).

fof(f36,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f13])).

fof(f158,plain,
    ( v2_struct_0(sK4)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK5) ),
    inference(subsumption_resolution,[],[f157,f35])).

fof(f35,plain,(
    m1_subset_1(sK5,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f157,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | v2_struct_0(sK4)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK5) ),
    inference(subsumption_resolution,[],[f148,f37])).

fof(f37,plain,(
    m1_pre_topc(sK4,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f148,plain,
    ( ~ m1_pre_topc(sK4,sK0)
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | v2_struct_0(sK4)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK5) ),
    inference(resolution,[],[f110,f71])).

fof(f71,plain,(
    m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(forward_demodulation,[],[f31,f33])).

fof(f31,plain,(
    m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f13])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | v2_struct_0(X0)
      | ~ r1_tmap_1(sK0,sK1,sK2,X1)
      | r1_tmap_1(X0,sK1,k2_tmap_1(sK0,sK1,sK2,X0),X1) ) ),
    inference(subsumption_resolution,[],[f109,f44])).

fof(f44,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f109,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r1_tmap_1(sK0,sK1,sK2,X1)
      | r1_tmap_1(X0,sK1,k2_tmap_1(sK0,sK1,sK2,X0),X1) ) ),
    inference(subsumption_resolution,[],[f108,f42])).

fof(f42,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | v2_struct_0(sK1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r1_tmap_1(sK0,sK1,sK2,X1)
      | r1_tmap_1(X0,sK1,k2_tmap_1(sK0,sK1,sK2,X0),X1) ) ),
    inference(subsumption_resolution,[],[f107,f41])).

fof(f41,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | v2_struct_0(sK1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r1_tmap_1(sK0,sK1,sK2,X1)
      | r1_tmap_1(X0,sK1,k2_tmap_1(sK0,sK1,sK2,X0),X1) ) ),
    inference(subsumption_resolution,[],[f106,f49])).

fof(f49,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(sK0)
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | v2_struct_0(sK1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r1_tmap_1(sK0,sK1,sK2,X1)
      | r1_tmap_1(X0,sK1,k2_tmap_1(sK0,sK1,sK2,X0),X1) ) ),
    inference(subsumption_resolution,[],[f105,f48])).

fof(f48,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | v2_struct_0(sK1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r1_tmap_1(sK0,sK1,sK2,X1)
      | r1_tmap_1(X0,sK1,k2_tmap_1(sK0,sK1,sK2,X0),X1) ) ),
    inference(subsumption_resolution,[],[f104,f47])).

fof(f47,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f104,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | v2_struct_0(sK1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r1_tmap_1(sK0,sK1,sK2,X1)
      | r1_tmap_1(X0,sK1,k2_tmap_1(sK0,sK1,sK2,X0),X1) ) ),
    inference(subsumption_resolution,[],[f103,f46])).

fof(f46,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(sK1)
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | v2_struct_0(sK1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r1_tmap_1(sK0,sK1,sK2,X1)
      | r1_tmap_1(X0,sK1,k2_tmap_1(sK0,sK1,sK2,X0),X1) ) ),
    inference(subsumption_resolution,[],[f102,f45])).

fof(f45,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | v2_struct_0(sK1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r1_tmap_1(sK0,sK1,sK2,X1)
      | r1_tmap_1(X0,sK1,k2_tmap_1(sK0,sK1,sK2,X0),X1) ) ),
    inference(resolution,[],[f61,f43])).

fof(f43,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f13])).

fof(f61,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | v2_struct_0(X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ r1_tmap_1(X1,X0,X2,X5)
      | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
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
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tmap_1)).

fof(f156,plain,
    ( ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK5)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(subsumption_resolution,[],[f75,f155])).

fof(f155,plain,(
    r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) ),
    inference(subsumption_resolution,[],[f154,f73])).

fof(f73,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)
    | r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(forward_demodulation,[],[f29,f32])).

fof(f32,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f13])).

fof(f29,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
    | r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(cnf_transformation,[],[f13])).

fof(f154,plain,
    ( ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) ),
    inference(subsumption_resolution,[],[f153,f39])).

fof(f39,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f13])).

fof(f153,plain,
    ( v2_struct_0(sK3)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) ),
    inference(subsumption_resolution,[],[f152,f35])).

fof(f152,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | v2_struct_0(sK3)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) ),
    inference(subsumption_resolution,[],[f147,f40])).

fof(f40,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f147,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | v2_struct_0(sK3)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) ),
    inference(resolution,[],[f110,f70])).

fof(f70,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(backward_demodulation,[],[f34,f32])).

fof(f34,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f13])).

fof(f75,plain,
    ( ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK5)
    | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(forward_demodulation,[],[f74,f33])).

fof(f74,plain,
    ( ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(forward_demodulation,[],[f28,f32])).

fof(f28,plain,
    ( ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(cnf_transformation,[],[f13])).

fof(f190,plain,(
    r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(subsumption_resolution,[],[f189,f45])).

fof(f189,plain,
    ( ~ v2_pre_topc(sK1)
    | r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(subsumption_resolution,[],[f188,f86])).

fof(f86,plain,(
    m1_connsp_2(sK8(sK0,sK5),sK0,sK5) ),
    inference(subsumption_resolution,[],[f85,f47])).

fof(f85,plain,
    ( v2_struct_0(sK0)
    | m1_connsp_2(sK8(sK0,sK5),sK0,sK5) ),
    inference(subsumption_resolution,[],[f84,f49])).

fof(f84,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | m1_connsp_2(sK8(sK0,sK5),sK0,sK5) ),
    inference(subsumption_resolution,[],[f81,f48])).

fof(f81,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | m1_connsp_2(sK8(sK0,sK5),sK0,sK5) ),
    inference(resolution,[],[f59,f35])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | m1_connsp_2(sK8(X0,X1),X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X2] : m1_connsp_2(X2,X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_connsp_2)).

fof(f188,plain,
    ( ~ m1_connsp_2(sK8(sK0,sK5),sK0,sK5)
    | ~ v2_pre_topc(sK1)
    | r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(subsumption_resolution,[],[f187,f44])).

fof(f187,plain,
    ( v2_struct_0(sK1)
    | ~ m1_connsp_2(sK8(sK0,sK5),sK0,sK5)
    | ~ v2_pre_topc(sK1)
    | r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(subsumption_resolution,[],[f186,f35])).

fof(f186,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | v2_struct_0(sK1)
    | ~ m1_connsp_2(sK8(sK0,sK5),sK0,sK5)
    | ~ v2_pre_topc(sK1)
    | r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(subsumption_resolution,[],[f185,f79])).

fof(f79,plain,(
    m1_pre_topc(sK0,sK0) ),
    inference(resolution,[],[f50,f49])).

fof(f50,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X0) ) ),
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

fof(f185,plain,
    ( ~ m1_pre_topc(sK0,sK0)
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | v2_struct_0(sK1)
    | ~ m1_connsp_2(sK8(sK0,sK5),sK0,sK5)
    | ~ v2_pre_topc(sK1)
    | r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(subsumption_resolution,[],[f184,f43])).

fof(f184,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | v2_struct_0(sK1)
    | ~ m1_connsp_2(sK8(sK0,sK5),sK0,sK5)
    | ~ v2_pre_topc(sK1)
    | r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(subsumption_resolution,[],[f183,f42])).

fof(f183,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | v2_struct_0(sK1)
    | ~ m1_connsp_2(sK8(sK0,sK5),sK0,sK5)
    | ~ v2_pre_topc(sK1)
    | r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(subsumption_resolution,[],[f182,f41])).

fof(f182,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | v2_struct_0(sK1)
    | ~ m1_connsp_2(sK8(sK0,sK5),sK0,sK5)
    | ~ v2_pre_topc(sK1)
    | r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(subsumption_resolution,[],[f181,f49])).

fof(f181,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | v2_struct_0(sK1)
    | ~ m1_connsp_2(sK8(sK0,sK5),sK0,sK5)
    | ~ v2_pre_topc(sK1)
    | r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(subsumption_resolution,[],[f180,f48])).

fof(f180,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | v2_struct_0(sK1)
    | ~ m1_connsp_2(sK8(sK0,sK5),sK0,sK5)
    | ~ v2_pre_topc(sK1)
    | r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(subsumption_resolution,[],[f179,f47])).

fof(f179,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | v2_struct_0(sK1)
    | ~ m1_connsp_2(sK8(sK0,sK5),sK0,sK5)
    | ~ v2_pre_topc(sK1)
    | r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(subsumption_resolution,[],[f178,f46])).

fof(f178,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | v2_struct_0(sK1)
    | ~ m1_connsp_2(sK8(sK0,sK5),sK0,sK5)
    | ~ v2_pre_topc(sK1)
    | r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(resolution,[],[f165,f175])).

fof(f175,plain,(
    r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5) ),
    inference(subsumption_resolution,[],[f174,f44])).

fof(f174,plain,
    ( v2_struct_0(sK1)
    | r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5) ),
    inference(subsumption_resolution,[],[f173,f155])).

fof(f173,plain,
    ( ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)
    | v2_struct_0(sK1)
    | r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5) ),
    inference(subsumption_resolution,[],[f172,f71])).

fof(f172,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)
    | v2_struct_0(sK1)
    | r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5) ),
    inference(subsumption_resolution,[],[f171,f70])).

fof(f171,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)
    | v2_struct_0(sK1)
    | r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5) ),
    inference(subsumption_resolution,[],[f170,f43])).

fof(f170,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)
    | v2_struct_0(sK1)
    | r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5) ),
    inference(subsumption_resolution,[],[f169,f42])).

fof(f169,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)
    | v2_struct_0(sK1)
    | r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5) ),
    inference(subsumption_resolution,[],[f168,f41])).

fof(f168,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)
    | v2_struct_0(sK1)
    | r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5) ),
    inference(subsumption_resolution,[],[f167,f46])).

fof(f167,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)
    | v2_struct_0(sK1)
    | r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5) ),
    inference(subsumption_resolution,[],[f166,f45])).

fof(f166,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)
    | v2_struct_0(sK1)
    | r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5) ),
    inference(resolution,[],[f160,f137])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tmap_1(sK4,X1,k2_tmap_1(sK0,X1,X2,sK4),X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,u1_struct_0(sK4))
      | ~ r1_tmap_1(sK3,X1,k2_tmap_1(sK0,X1,X2,sK3),X0)
      | v2_struct_0(X1)
      | r1_tmap_1(sK0,X1,k2_tmap_1(sK0,X1,X2,sK0),X0) ) ),
    inference(subsumption_resolution,[],[f136,f98])).

fof(f98,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK3))
      | m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f97,f47])).

fof(f97,plain,(
    ! [X1] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK3))
      | m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f96,f39])).

fof(f96,plain,(
    ! [X1] :
      ( v2_struct_0(sK3)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK3))
      | m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f90,f49])).

fof(f90,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(sK3)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK3))
      | m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f57,f40])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,u1_struct_0(sK4))
      | ~ r1_tmap_1(sK3,X1,k2_tmap_1(sK0,X1,X2,sK3),X0)
      | ~ r1_tmap_1(sK4,X1,k2_tmap_1(sK0,X1,X2,sK4),X0)
      | r1_tmap_1(sK0,X1,k2_tmap_1(sK0,X1,X2,sK0),X0) ) ),
    inference(subsumption_resolution,[],[f135,f47])).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,u1_struct_0(sK4))
      | ~ r1_tmap_1(sK3,X1,k2_tmap_1(sK0,X1,X2,sK3),X0)
      | ~ r1_tmap_1(sK4,X1,k2_tmap_1(sK0,X1,X2,sK4),X0)
      | r1_tmap_1(sK0,X1,k2_tmap_1(sK0,X1,X2,sK0),X0) ) ),
    inference(subsumption_resolution,[],[f134,f37])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | ~ m1_pre_topc(sK4,sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,u1_struct_0(sK4))
      | ~ r1_tmap_1(sK3,X1,k2_tmap_1(sK0,X1,X2,sK3),X0)
      | ~ r1_tmap_1(sK4,X1,k2_tmap_1(sK0,X1,X2,sK4),X0)
      | r1_tmap_1(sK0,X1,k2_tmap_1(sK0,X1,X2,sK0),X0) ) ),
    inference(subsumption_resolution,[],[f133,f36])).

fof(f133,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,u1_struct_0(sK4))
      | ~ r1_tmap_1(sK3,X1,k2_tmap_1(sK0,X1,X2,sK3),X0)
      | ~ r1_tmap_1(sK4,X1,k2_tmap_1(sK0,X1,X2,sK4),X0)
      | r1_tmap_1(sK0,X1,k2_tmap_1(sK0,X1,X2,sK0),X0) ) ),
    inference(subsumption_resolution,[],[f132,f40])).

fof(f132,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,u1_struct_0(sK4))
      | ~ r1_tmap_1(sK3,X1,k2_tmap_1(sK0,X1,X2,sK3),X0)
      | ~ r1_tmap_1(sK4,X1,k2_tmap_1(sK0,X1,X2,sK4),X0)
      | r1_tmap_1(sK0,X1,k2_tmap_1(sK0,X1,X2,sK0),X0) ) ),
    inference(subsumption_resolution,[],[f131,f39])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,u1_struct_0(sK4))
      | ~ r1_tmap_1(sK3,X1,k2_tmap_1(sK0,X1,X2,sK3),X0)
      | ~ r1_tmap_1(sK4,X1,k2_tmap_1(sK0,X1,X2,sK4),X0)
      | r1_tmap_1(sK0,X1,k2_tmap_1(sK0,X1,X2,sK0),X0) ) ),
    inference(subsumption_resolution,[],[f130,f49])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,u1_struct_0(sK4))
      | ~ r1_tmap_1(sK3,X1,k2_tmap_1(sK0,X1,X2,sK3),X0)
      | ~ r1_tmap_1(sK4,X1,k2_tmap_1(sK0,X1,X2,sK4),X0)
      | r1_tmap_1(sK0,X1,k2_tmap_1(sK0,X1,X2,sK0),X0) ) ),
    inference(subsumption_resolution,[],[f129,f48])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,u1_struct_0(sK4))
      | ~ r1_tmap_1(sK3,X1,k2_tmap_1(sK0,X1,X2,sK3),X0)
      | ~ r1_tmap_1(sK4,X1,k2_tmap_1(sK0,X1,X2,sK4),X0)
      | r1_tmap_1(sK0,X1,k2_tmap_1(sK0,X1,X2,sK0),X0) ) ),
    inference(superposition,[],[f65,f38])).

fof(f38,plain,(
    sK0 = k1_tsep_1(sK0,sK3,sK4) ),
    inference(cnf_transformation,[],[f13])).

fof(f65,plain,(
    ! [X4,X2,X0,X7,X3,X1] :
      ( ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X7)
      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
      | r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X6,X4,X2,X0,X7,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X4,X0)
      | ~ m1_subset_1(X6,u1_struct_0(k1_tsep_1(X0,X3,X4)))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | X6 != X7
      | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)
      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
      | r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X6) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X4,X0)
      | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4)))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | X5 != X6
      | X5 != X7
      | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)
      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
      | r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5)
                                  <=> ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                      & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) ) )
                                  | X5 != X7
                                  | X5 != X6
                                  | ~ m1_subset_1(X7,u1_struct_0(X4)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4))) )
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
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
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5)
                                  <=> ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                      & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) ) )
                                  | X5 != X7
                                  | X5 != X6
                                  | ~ m1_subset_1(X7,u1_struct_0(X4)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4))) )
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4)))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X3))
                             => ! [X7] :
                                  ( m1_subset_1(X7,u1_struct_0(X4))
                                 => ( ( X5 = X7
                                      & X5 = X6 )
                                   => ( r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5)
                                    <=> ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                        & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_tmap_1)).

fof(f165,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tmap_1(sK0,X0,k2_tmap_1(X1,X0,X2,sK0),X3)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ m1_pre_topc(sK0,X1)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | v2_struct_0(X0)
      | ~ m1_connsp_2(sK8(sK0,sK5),X1,X3)
      | ~ v2_pre_topc(X0)
      | r1_tmap_1(X1,X0,X2,X3) ) ),
    inference(subsumption_resolution,[],[f164,f47])).

fof(f164,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | v2_struct_0(sK0)
      | ~ m1_pre_topc(sK0,X1)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | v2_struct_0(X0)
      | ~ m1_connsp_2(sK8(sK0,sK5),X1,X3)
      | ~ r1_tmap_1(sK0,X0,k2_tmap_1(X1,X0,X2,sK0),X3)
      | r1_tmap_1(X1,X0,X2,X3) ) ),
    inference(resolution,[],[f144,f77])).

fof(f77,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( ~ r1_tarski(X4,u1_struct_0(X3))
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
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | v2_struct_0(X0)
      | ~ m1_connsp_2(X4,X1,X6)
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | r1_tmap_1(X1,X0,X2,X6) ) ),
    inference(subsumption_resolution,[],[f76,f57])).

fof(f76,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
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
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ m1_connsp_2(X4,X1,X6)
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | r1_tmap_1(X1,X0,X2,X6) ) ),
    inference(subsumption_resolution,[],[f63,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X2,X0,X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(f63,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
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
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ m1_connsp_2(X4,X1,X6)
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | r1_tmap_1(X1,X0,X2,X6) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
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
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ m1_connsp_2(X4,X1,X5)
      | X5 != X6
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | r1_tmap_1(X1,X0,X2,X5) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X1,X0,X2,X5)
                              <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                              | X5 != X6
                              | ~ m1_connsp_2(X4,X1,X5)
                              | ~ r1_tarski(X4,u1_struct_0(X3))
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X1,X0,X2,X5)
                              <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                              | X5 != X6
                              | ~ m1_connsp_2(X4,X1,X5)
                              | ~ r1_tarski(X4,u1_struct_0(X3))
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X3))
                             => ( ( X5 = X6
                                  & m1_connsp_2(X4,X1,X5)
                                  & r1_tarski(X4,u1_struct_0(X3)) )
                               => ( r1_tmap_1(X1,X0,X2,X5)
                                <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tmap_1)).

fof(f144,plain,(
    r1_tarski(sK8(sK0,sK5),u1_struct_0(sK0)) ),
    inference(resolution,[],[f142,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f142,plain,(
    m1_subset_1(sK8(sK0,sK5),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f141,f47])).

fof(f141,plain,
    ( v2_struct_0(sK0)
    | m1_subset_1(sK8(sK0,sK5),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f140,f35])).

fof(f140,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | m1_subset_1(sK8(sK0,sK5),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f139,f49])).

fof(f139,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | m1_subset_1(sK8(sK0,sK5),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f138,f48])).

fof(f138,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | m1_subset_1(sK8(sK0,sK5),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f86,f58])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:46:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.44  % (25517)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.44  % (25517)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f191,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(subsumption_resolution,[],[f190,f161])).
% 0.21/0.44  fof(f161,plain,(
% 0.21/0.44    ~r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.44    inference(subsumption_resolution,[],[f156,f160])).
% 0.21/0.44  fof(f160,plain,(
% 0.21/0.44    r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK5)),
% 0.21/0.44    inference(subsumption_resolution,[],[f159,f72])).
% 0.21/0.44  fof(f72,plain,(
% 0.21/0.44    r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK5) | r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.44    inference(forward_demodulation,[],[f30,f33])).
% 0.21/0.44  fof(f33,plain,(
% 0.21/0.44    sK5 = sK7),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((r1_tmap_1(X0,X1,X2,X5) <~> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6))) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.44    inference(flattening,[],[f12])).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (? [X7] : (((r1_tmap_1(X0,X1,X2,X5) <~> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6))) & (X5 = X7 & X5 = X6)) & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0) & (m1_pre_topc(X4,X0) & ~v2_struct_0(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f10])).
% 0.21/0.44  fof(f10,negated_conjecture,(
% 0.21/0.44    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => (k1_tsep_1(X0,X3,X4) = X0 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X0)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X4)) => ((X5 = X7 & X5 = X6) => (r1_tmap_1(X0,X1,X2,X5) <=> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)))))))))))))),
% 0.21/0.44    inference(negated_conjecture,[],[f9])).
% 0.21/0.44  fof(f9,conjecture,(
% 0.21/0.44    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => (k1_tsep_1(X0,X3,X4) = X0 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X0)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X4)) => ((X5 = X7 & X5 = X6) => (r1_tmap_1(X0,X1,X2,X5) <=> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)))))))))))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_tmap_1)).
% 0.21/0.44  fof(f30,plain,(
% 0.21/0.44    r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) | r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f159,plain,(
% 0.21/0.44    ~r1_tmap_1(sK0,sK1,sK2,sK5) | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK5)),
% 0.21/0.44    inference(subsumption_resolution,[],[f158,f36])).
% 0.21/0.44  fof(f36,plain,(
% 0.21/0.44    ~v2_struct_0(sK4)),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f158,plain,(
% 0.21/0.44    v2_struct_0(sK4) | ~r1_tmap_1(sK0,sK1,sK2,sK5) | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK5)),
% 0.21/0.44    inference(subsumption_resolution,[],[f157,f35])).
% 0.21/0.44  fof(f35,plain,(
% 0.21/0.44    m1_subset_1(sK5,u1_struct_0(sK0))),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f157,plain,(
% 0.21/0.44    ~m1_subset_1(sK5,u1_struct_0(sK0)) | v2_struct_0(sK4) | ~r1_tmap_1(sK0,sK1,sK2,sK5) | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK5)),
% 0.21/0.44    inference(subsumption_resolution,[],[f148,f37])).
% 0.21/0.44  fof(f37,plain,(
% 0.21/0.44    m1_pre_topc(sK4,sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f148,plain,(
% 0.21/0.44    ~m1_pre_topc(sK4,sK0) | ~m1_subset_1(sK5,u1_struct_0(sK0)) | v2_struct_0(sK4) | ~r1_tmap_1(sK0,sK1,sK2,sK5) | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK5)),
% 0.21/0.44    inference(resolution,[],[f110,f71])).
% 0.21/0.44  fof(f71,plain,(
% 0.21/0.44    m1_subset_1(sK5,u1_struct_0(sK4))),
% 0.21/0.44    inference(forward_demodulation,[],[f31,f33])).
% 0.21/0.44  fof(f31,plain,(
% 0.21/0.44    m1_subset_1(sK7,u1_struct_0(sK4))),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f110,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | v2_struct_0(X0) | ~r1_tmap_1(sK0,sK1,sK2,X1) | r1_tmap_1(X0,sK1,k2_tmap_1(sK0,sK1,sK2,X0),X1)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f109,f44])).
% 0.21/0.44  fof(f44,plain,(
% 0.21/0.44    ~v2_struct_0(sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f109,plain,(
% 0.21/0.44    ( ! [X0,X1] : (v2_struct_0(sK1) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_tmap_1(sK0,sK1,sK2,X1) | r1_tmap_1(X0,sK1,k2_tmap_1(sK0,sK1,sK2,X0),X1)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f108,f42])).
% 0.21/0.44  fof(f42,plain,(
% 0.21/0.44    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f108,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | v2_struct_0(sK1) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_tmap_1(sK0,sK1,sK2,X1) | r1_tmap_1(X0,sK1,k2_tmap_1(sK0,sK1,sK2,X0),X1)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f107,f41])).
% 0.21/0.44  fof(f41,plain,(
% 0.21/0.44    v1_funct_1(sK2)),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f107,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | v2_struct_0(sK1) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_tmap_1(sK0,sK1,sK2,X1) | r1_tmap_1(X0,sK1,k2_tmap_1(sK0,sK1,sK2,X0),X1)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f106,f49])).
% 0.21/0.44  fof(f49,plain,(
% 0.21/0.44    l1_pre_topc(sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f106,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~l1_pre_topc(sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | v2_struct_0(sK1) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_tmap_1(sK0,sK1,sK2,X1) | r1_tmap_1(X0,sK1,k2_tmap_1(sK0,sK1,sK2,X0),X1)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f105,f48])).
% 0.21/0.44  fof(f48,plain,(
% 0.21/0.44    v2_pre_topc(sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f105,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | v2_struct_0(sK1) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_tmap_1(sK0,sK1,sK2,X1) | r1_tmap_1(X0,sK1,k2_tmap_1(sK0,sK1,sK2,X0),X1)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f104,f47])).
% 0.21/0.44  fof(f47,plain,(
% 0.21/0.44    ~v2_struct_0(sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f104,plain,(
% 0.21/0.44    ( ! [X0,X1] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | v2_struct_0(sK1) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_tmap_1(sK0,sK1,sK2,X1) | r1_tmap_1(X0,sK1,k2_tmap_1(sK0,sK1,sK2,X0),X1)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f103,f46])).
% 0.21/0.44  fof(f46,plain,(
% 0.21/0.44    l1_pre_topc(sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f103,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | v2_struct_0(sK1) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_tmap_1(sK0,sK1,sK2,X1) | r1_tmap_1(X0,sK1,k2_tmap_1(sK0,sK1,sK2,X0),X1)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f102,f45])).
% 0.21/0.44  fof(f45,plain,(
% 0.21/0.44    v2_pre_topc(sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f102,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | v2_struct_0(sK1) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_tmap_1(sK0,sK1,sK2,X1) | r1_tmap_1(X0,sK1,k2_tmap_1(sK0,sK1,sK2,X0),X1)) )),
% 0.21/0.44    inference(resolution,[],[f61,f43])).
% 0.21/0.44  fof(f43,plain,(
% 0.21/0.44    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f61,plain,(
% 0.21/0.44    ( ! [X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | v2_struct_0(X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~r1_tmap_1(X1,X0,X2,X5) | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) )),
% 0.21/0.44    inference(equality_resolution,[],[f51])).
% 0.21/0.44  fof(f51,plain,(
% 0.21/0.44    ( ! [X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X3)) | X4 != X5 | ~r1_tmap_1(X1,X0,X2,X4) | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f16])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.44    inference(flattening,[],[f15])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f7])).
% 0.21/0.44  fof(f7,axiom,(
% 0.21/0.44    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tmap_1)).
% 0.21/0.44  fof(f156,plain,(
% 0.21/0.44    ~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK5) | ~r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.44    inference(subsumption_resolution,[],[f75,f155])).
% 0.21/0.44  fof(f155,plain,(
% 0.21/0.44    r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)),
% 0.21/0.44    inference(subsumption_resolution,[],[f154,f73])).
% 0.21/0.44  fof(f73,plain,(
% 0.21/0.44    r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) | r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.44    inference(forward_demodulation,[],[f29,f32])).
% 0.21/0.44  fof(f32,plain,(
% 0.21/0.44    sK5 = sK6),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f29,plain,(
% 0.21/0.44    r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) | r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f154,plain,(
% 0.21/0.44    ~r1_tmap_1(sK0,sK1,sK2,sK5) | r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)),
% 0.21/0.44    inference(subsumption_resolution,[],[f153,f39])).
% 0.21/0.44  fof(f39,plain,(
% 0.21/0.44    ~v2_struct_0(sK3)),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f153,plain,(
% 0.21/0.44    v2_struct_0(sK3) | ~r1_tmap_1(sK0,sK1,sK2,sK5) | r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)),
% 0.21/0.44    inference(subsumption_resolution,[],[f152,f35])).
% 0.21/0.44  fof(f152,plain,(
% 0.21/0.44    ~m1_subset_1(sK5,u1_struct_0(sK0)) | v2_struct_0(sK3) | ~r1_tmap_1(sK0,sK1,sK2,sK5) | r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)),
% 0.21/0.44    inference(subsumption_resolution,[],[f147,f40])).
% 0.21/0.44  fof(f40,plain,(
% 0.21/0.44    m1_pre_topc(sK3,sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f147,plain,(
% 0.21/0.44    ~m1_pre_topc(sK3,sK0) | ~m1_subset_1(sK5,u1_struct_0(sK0)) | v2_struct_0(sK3) | ~r1_tmap_1(sK0,sK1,sK2,sK5) | r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)),
% 0.21/0.44    inference(resolution,[],[f110,f70])).
% 0.21/0.44  fof(f70,plain,(
% 0.21/0.44    m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.21/0.44    inference(backward_demodulation,[],[f34,f32])).
% 0.21/0.44  fof(f34,plain,(
% 0.21/0.44    m1_subset_1(sK6,u1_struct_0(sK3))),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f75,plain,(
% 0.21/0.44    ~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK5) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) | ~r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.44    inference(forward_demodulation,[],[f74,f33])).
% 0.21/0.44  fof(f74,plain,(
% 0.21/0.44    ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) | ~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) | ~r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.44    inference(forward_demodulation,[],[f28,f32])).
% 0.21/0.44  fof(f28,plain,(
% 0.21/0.44    ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) | ~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) | ~r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f190,plain,(
% 0.21/0.44    r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.44    inference(subsumption_resolution,[],[f189,f45])).
% 0.21/0.44  fof(f189,plain,(
% 0.21/0.44    ~v2_pre_topc(sK1) | r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.44    inference(subsumption_resolution,[],[f188,f86])).
% 0.21/0.44  fof(f86,plain,(
% 0.21/0.44    m1_connsp_2(sK8(sK0,sK5),sK0,sK5)),
% 0.21/0.44    inference(subsumption_resolution,[],[f85,f47])).
% 0.21/0.44  fof(f85,plain,(
% 0.21/0.44    v2_struct_0(sK0) | m1_connsp_2(sK8(sK0,sK5),sK0,sK5)),
% 0.21/0.44    inference(subsumption_resolution,[],[f84,f49])).
% 0.21/0.44  fof(f84,plain,(
% 0.21/0.44    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | m1_connsp_2(sK8(sK0,sK5),sK0,sK5)),
% 0.21/0.44    inference(subsumption_resolution,[],[f81,f48])).
% 0.21/0.44  fof(f81,plain,(
% 0.21/0.44    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | m1_connsp_2(sK8(sK0,sK5),sK0,sK5)),
% 0.21/0.44    inference(resolution,[],[f59,f35])).
% 0.21/0.44  fof(f59,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | m1_connsp_2(sK8(X0,X1),X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f26])).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.44    inference(flattening,[],[f25])).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X2] : m1_connsp_2(X2,X0,X1))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_connsp_2)).
% 0.21/0.44  fof(f188,plain,(
% 0.21/0.44    ~m1_connsp_2(sK8(sK0,sK5),sK0,sK5) | ~v2_pre_topc(sK1) | r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.44    inference(subsumption_resolution,[],[f187,f44])).
% 0.21/0.44  fof(f187,plain,(
% 0.21/0.44    v2_struct_0(sK1) | ~m1_connsp_2(sK8(sK0,sK5),sK0,sK5) | ~v2_pre_topc(sK1) | r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.44    inference(subsumption_resolution,[],[f186,f35])).
% 0.21/0.44  fof(f186,plain,(
% 0.21/0.44    ~m1_subset_1(sK5,u1_struct_0(sK0)) | v2_struct_0(sK1) | ~m1_connsp_2(sK8(sK0,sK5),sK0,sK5) | ~v2_pre_topc(sK1) | r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.44    inference(subsumption_resolution,[],[f185,f79])).
% 0.21/0.44  fof(f79,plain,(
% 0.21/0.44    m1_pre_topc(sK0,sK0)),
% 0.21/0.44    inference(resolution,[],[f50,f49])).
% 0.21/0.44  fof(f50,plain,(
% 0.21/0.44    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f14])).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f6])).
% 0.21/0.44  fof(f6,axiom,(
% 0.21/0.44    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.21/0.44  fof(f185,plain,(
% 0.21/0.44    ~m1_pre_topc(sK0,sK0) | ~m1_subset_1(sK5,u1_struct_0(sK0)) | v2_struct_0(sK1) | ~m1_connsp_2(sK8(sK0,sK5),sK0,sK5) | ~v2_pre_topc(sK1) | r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.44    inference(subsumption_resolution,[],[f184,f43])).
% 0.21/0.44  fof(f184,plain,(
% 0.21/0.44    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_pre_topc(sK0,sK0) | ~m1_subset_1(sK5,u1_struct_0(sK0)) | v2_struct_0(sK1) | ~m1_connsp_2(sK8(sK0,sK5),sK0,sK5) | ~v2_pre_topc(sK1) | r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.44    inference(subsumption_resolution,[],[f183,f42])).
% 0.21/0.44  fof(f183,plain,(
% 0.21/0.44    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_pre_topc(sK0,sK0) | ~m1_subset_1(sK5,u1_struct_0(sK0)) | v2_struct_0(sK1) | ~m1_connsp_2(sK8(sK0,sK5),sK0,sK5) | ~v2_pre_topc(sK1) | r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.44    inference(subsumption_resolution,[],[f182,f41])).
% 0.21/0.44  fof(f182,plain,(
% 0.21/0.44    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_pre_topc(sK0,sK0) | ~m1_subset_1(sK5,u1_struct_0(sK0)) | v2_struct_0(sK1) | ~m1_connsp_2(sK8(sK0,sK5),sK0,sK5) | ~v2_pre_topc(sK1) | r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.44    inference(subsumption_resolution,[],[f181,f49])).
% 0.21/0.44  fof(f181,plain,(
% 0.21/0.44    ~l1_pre_topc(sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_pre_topc(sK0,sK0) | ~m1_subset_1(sK5,u1_struct_0(sK0)) | v2_struct_0(sK1) | ~m1_connsp_2(sK8(sK0,sK5),sK0,sK5) | ~v2_pre_topc(sK1) | r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.44    inference(subsumption_resolution,[],[f180,f48])).
% 0.21/0.44  fof(f180,plain,(
% 0.21/0.44    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_pre_topc(sK0,sK0) | ~m1_subset_1(sK5,u1_struct_0(sK0)) | v2_struct_0(sK1) | ~m1_connsp_2(sK8(sK0,sK5),sK0,sK5) | ~v2_pre_topc(sK1) | r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.44    inference(subsumption_resolution,[],[f179,f47])).
% 0.21/0.44  fof(f179,plain,(
% 0.21/0.44    v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_pre_topc(sK0,sK0) | ~m1_subset_1(sK5,u1_struct_0(sK0)) | v2_struct_0(sK1) | ~m1_connsp_2(sK8(sK0,sK5),sK0,sK5) | ~v2_pre_topc(sK1) | r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.44    inference(subsumption_resolution,[],[f178,f46])).
% 0.21/0.44  fof(f178,plain,(
% 0.21/0.44    ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_pre_topc(sK0,sK0) | ~m1_subset_1(sK5,u1_struct_0(sK0)) | v2_struct_0(sK1) | ~m1_connsp_2(sK8(sK0,sK5),sK0,sK5) | ~v2_pre_topc(sK1) | r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.44    inference(resolution,[],[f165,f175])).
% 0.21/0.44  fof(f175,plain,(
% 0.21/0.44    r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5)),
% 0.21/0.44    inference(subsumption_resolution,[],[f174,f44])).
% 0.21/0.44  fof(f174,plain,(
% 0.21/0.44    v2_struct_0(sK1) | r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5)),
% 0.21/0.44    inference(subsumption_resolution,[],[f173,f155])).
% 0.21/0.44  fof(f173,plain,(
% 0.21/0.44    ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) | v2_struct_0(sK1) | r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5)),
% 0.21/0.44    inference(subsumption_resolution,[],[f172,f71])).
% 0.21/0.44  fof(f172,plain,(
% 0.21/0.44    ~m1_subset_1(sK5,u1_struct_0(sK4)) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) | v2_struct_0(sK1) | r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5)),
% 0.21/0.44    inference(subsumption_resolution,[],[f171,f70])).
% 0.21/0.44  fof(f171,plain,(
% 0.21/0.44    ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK4)) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) | v2_struct_0(sK1) | r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5)),
% 0.21/0.44    inference(subsumption_resolution,[],[f170,f43])).
% 0.21/0.44  fof(f170,plain,(
% 0.21/0.44    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK4)) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) | v2_struct_0(sK1) | r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5)),
% 0.21/0.44    inference(subsumption_resolution,[],[f169,f42])).
% 0.21/0.44  fof(f169,plain,(
% 0.21/0.44    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK4)) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) | v2_struct_0(sK1) | r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5)),
% 0.21/0.44    inference(subsumption_resolution,[],[f168,f41])).
% 0.21/0.44  fof(f168,plain,(
% 0.21/0.44    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK4)) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) | v2_struct_0(sK1) | r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5)),
% 0.21/0.44    inference(subsumption_resolution,[],[f167,f46])).
% 0.21/0.44  fof(f167,plain,(
% 0.21/0.44    ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK4)) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) | v2_struct_0(sK1) | r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5)),
% 0.21/0.44    inference(subsumption_resolution,[],[f166,f45])).
% 0.21/0.44  fof(f166,plain,(
% 0.21/0.44    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK4)) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) | v2_struct_0(sK1) | r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5)),
% 0.21/0.44    inference(resolution,[],[f160,f137])).
% 0.21/0.44  fof(f137,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~r1_tmap_1(sK4,X1,k2_tmap_1(sK0,X1,X2,sK4),X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK4)) | ~r1_tmap_1(sK3,X1,k2_tmap_1(sK0,X1,X2,sK3),X0) | v2_struct_0(X1) | r1_tmap_1(sK0,X1,k2_tmap_1(sK0,X1,X2,sK0),X0)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f136,f98])).
% 0.21/0.44  fof(f98,plain,(
% 0.21/0.44    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK3)) | m1_subset_1(X1,u1_struct_0(sK0))) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f97,f47])).
% 0.21/0.44  fof(f97,plain,(
% 0.21/0.44    ( ! [X1] : (v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK3)) | m1_subset_1(X1,u1_struct_0(sK0))) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f96,f39])).
% 0.21/0.44  fof(f96,plain,(
% 0.21/0.44    ( ! [X1] : (v2_struct_0(sK3) | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK3)) | m1_subset_1(X1,u1_struct_0(sK0))) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f90,f49])).
% 0.21/0.44  fof(f90,plain,(
% 0.21/0.44    ( ! [X1] : (~l1_pre_topc(sK0) | v2_struct_0(sK3) | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK3)) | m1_subset_1(X1,u1_struct_0(sK0))) )),
% 0.21/0.44    inference(resolution,[],[f57,f40])).
% 0.21/0.44  fof(f57,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | m1_subset_1(X2,u1_struct_0(X0))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f22])).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.44    inference(flattening,[],[f21])).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).
% 0.21/0.44  fof(f136,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK4)) | ~r1_tmap_1(sK3,X1,k2_tmap_1(sK0,X1,X2,sK3),X0) | ~r1_tmap_1(sK4,X1,k2_tmap_1(sK0,X1,X2,sK4),X0) | r1_tmap_1(sK0,X1,k2_tmap_1(sK0,X1,X2,sK0),X0)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f135,f47])).
% 0.21/0.44  fof(f135,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK4)) | ~r1_tmap_1(sK3,X1,k2_tmap_1(sK0,X1,X2,sK3),X0) | ~r1_tmap_1(sK4,X1,k2_tmap_1(sK0,X1,X2,sK4),X0) | r1_tmap_1(sK0,X1,k2_tmap_1(sK0,X1,X2,sK0),X0)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f134,f37])).
% 0.21/0.44  fof(f134,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK4)) | ~r1_tmap_1(sK3,X1,k2_tmap_1(sK0,X1,X2,sK3),X0) | ~r1_tmap_1(sK4,X1,k2_tmap_1(sK0,X1,X2,sK4),X0) | r1_tmap_1(sK0,X1,k2_tmap_1(sK0,X1,X2,sK0),X0)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f133,f36])).
% 0.21/0.44  fof(f133,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK4)) | ~r1_tmap_1(sK3,X1,k2_tmap_1(sK0,X1,X2,sK3),X0) | ~r1_tmap_1(sK4,X1,k2_tmap_1(sK0,X1,X2,sK4),X0) | r1_tmap_1(sK0,X1,k2_tmap_1(sK0,X1,X2,sK0),X0)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f132,f40])).
% 0.21/0.44  fof(f132,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK4)) | ~r1_tmap_1(sK3,X1,k2_tmap_1(sK0,X1,X2,sK3),X0) | ~r1_tmap_1(sK4,X1,k2_tmap_1(sK0,X1,X2,sK4),X0) | r1_tmap_1(sK0,X1,k2_tmap_1(sK0,X1,X2,sK0),X0)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f131,f39])).
% 0.21/0.44  fof(f131,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK4)) | ~r1_tmap_1(sK3,X1,k2_tmap_1(sK0,X1,X2,sK3),X0) | ~r1_tmap_1(sK4,X1,k2_tmap_1(sK0,X1,X2,sK4),X0) | r1_tmap_1(sK0,X1,k2_tmap_1(sK0,X1,X2,sK0),X0)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f130,f49])).
% 0.21/0.44  fof(f130,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK4)) | ~r1_tmap_1(sK3,X1,k2_tmap_1(sK0,X1,X2,sK3),X0) | ~r1_tmap_1(sK4,X1,k2_tmap_1(sK0,X1,X2,sK4),X0) | r1_tmap_1(sK0,X1,k2_tmap_1(sK0,X1,X2,sK0),X0)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f129,f48])).
% 0.21/0.44  fof(f129,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK4)) | ~r1_tmap_1(sK3,X1,k2_tmap_1(sK0,X1,X2,sK3),X0) | ~r1_tmap_1(sK4,X1,k2_tmap_1(sK0,X1,X2,sK4),X0) | r1_tmap_1(sK0,X1,k2_tmap_1(sK0,X1,X2,sK0),X0)) )),
% 0.21/0.44    inference(superposition,[],[f65,f38])).
% 0.21/0.44  fof(f38,plain,(
% 0.21/0.44    sK0 = k1_tsep_1(sK0,sK3,sK4)),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f65,plain,(
% 0.21/0.44    ( ! [X4,X2,X0,X7,X3,X1] : (~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X4) | ~m1_pre_topc(X4,X0) | v2_struct_0(X0) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(X4)) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X7) | ~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7)) )),
% 0.21/0.44    inference(equality_resolution,[],[f64])).
% 0.21/0.44  fof(f64,plain,(
% 0.21/0.44    ( ! [X6,X4,X2,X0,X7,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X4) | ~m1_pre_topc(X4,X0) | ~m1_subset_1(X6,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(X4)) | X6 != X7 | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X6)) )),
% 0.21/0.44    inference(equality_resolution,[],[f56])).
% 0.21/0.44  fof(f56,plain,(
% 0.21/0.44    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X4) | ~m1_pre_topc(X4,X0) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(X4)) | X5 != X6 | X5 != X7 | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f20])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) <=> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6))) | X5 != X7 | X5 != X6 | ~m1_subset_1(X7,u1_struct_0(X4))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4)))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.44    inference(flattening,[],[f19])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) <=> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6))) | (X5 != X7 | X5 != X6)) | ~m1_subset_1(X7,u1_struct_0(X4))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4)))) | (~m1_pre_topc(X4,X0) | v2_struct_0(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,axiom,(
% 0.21/0.44    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X4)) => ((X5 = X7 & X5 = X6) => (r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) <=> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6))))))))))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_tmap_1)).
% 0.21/0.44  fof(f165,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (~r1_tmap_1(sK0,X0,k2_tmap_1(X1,X0,X2,sK0),X3) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~m1_pre_topc(sK0,X1) | ~m1_subset_1(X3,u1_struct_0(sK0)) | v2_struct_0(X0) | ~m1_connsp_2(sK8(sK0,sK5),X1,X3) | ~v2_pre_topc(X0) | r1_tmap_1(X1,X0,X2,X3)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f164,f47])).
% 0.21/0.44  fof(f164,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(sK0) | ~m1_pre_topc(sK0,X1) | ~m1_subset_1(X3,u1_struct_0(sK0)) | v2_struct_0(X0) | ~m1_connsp_2(sK8(sK0,sK5),X1,X3) | ~r1_tmap_1(sK0,X0,k2_tmap_1(X1,X0,X2,sK0),X3) | r1_tmap_1(X1,X0,X2,X3)) )),
% 0.21/0.44    inference(resolution,[],[f144,f77])).
% 0.21/0.44  fof(f77,plain,(
% 0.21/0.44    ( ! [X6,X4,X2,X0,X3,X1] : (~r1_tarski(X4,u1_struct_0(X3)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X6,u1_struct_0(X3)) | v2_struct_0(X0) | ~m1_connsp_2(X4,X1,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X6)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f76,f57])).
% 0.21/0.44  fof(f76,plain,(
% 0.21/0.44    ( ! [X6,X4,X2,X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_connsp_2(X4,X1,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X6)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f63,f58])).
% 0.21/0.44  fof(f58,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~m1_connsp_2(X2,X0,X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f24])).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.44    inference(flattening,[],[f23])).
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).
% 0.21/0.44  fof(f63,plain,(
% 0.21/0.44    ( ! [X6,X4,X2,X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_connsp_2(X4,X1,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X6)) )),
% 0.21/0.44    inference(equality_resolution,[],[f52])).
% 0.21/0.44  fof(f52,plain,(
% 0.21/0.44    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_connsp_2(X4,X1,X5) | X5 != X6 | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f18])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.44    inference(flattening,[],[f17])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f8])).
% 0.21/0.44  fof(f8,axiom,(
% 0.21/0.44    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & m1_connsp_2(X4,X1,X5) & r1_tarski(X4,u1_struct_0(X3))) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tmap_1)).
% 0.21/0.44  fof(f144,plain,(
% 0.21/0.44    r1_tarski(sK8(sK0,sK5),u1_struct_0(sK0))),
% 0.21/0.44    inference(resolution,[],[f142,f60])).
% 0.21/0.44  fof(f60,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f27])).
% 0.21/0.44  fof(f27,plain,(
% 0.21/0.44    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.21/0.44    inference(ennf_transformation,[],[f11])).
% 0.21/0.45  fof(f11,plain,(
% 0.21/0.45    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 0.21/0.45    inference(unused_predicate_definition_removal,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.45  fof(f142,plain,(
% 0.21/0.45    m1_subset_1(sK8(sK0,sK5),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.45    inference(subsumption_resolution,[],[f141,f47])).
% 0.21/0.45  fof(f141,plain,(
% 0.21/0.45    v2_struct_0(sK0) | m1_subset_1(sK8(sK0,sK5),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.45    inference(subsumption_resolution,[],[f140,f35])).
% 0.21/0.45  fof(f140,plain,(
% 0.21/0.45    ~m1_subset_1(sK5,u1_struct_0(sK0)) | v2_struct_0(sK0) | m1_subset_1(sK8(sK0,sK5),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.45    inference(subsumption_resolution,[],[f139,f49])).
% 0.21/0.45  fof(f139,plain,(
% 0.21/0.45    ~l1_pre_topc(sK0) | ~m1_subset_1(sK5,u1_struct_0(sK0)) | v2_struct_0(sK0) | m1_subset_1(sK8(sK0,sK5),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.45    inference(subsumption_resolution,[],[f138,f48])).
% 0.21/0.45  fof(f138,plain,(
% 0.21/0.45    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK5,u1_struct_0(sK0)) | v2_struct_0(sK0) | m1_subset_1(sK8(sK0,sK5),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.45    inference(resolution,[],[f86,f58])).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (25517)------------------------------
% 0.21/0.45  % (25517)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (25517)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (25517)Memory used [KB]: 1791
% 0.21/0.45  % (25517)Time elapsed: 0.044 s
% 0.21/0.45  % (25517)------------------------------
% 0.21/0.45  % (25517)------------------------------
% 0.21/0.45  % (25499)Success in time 0.09 s
%------------------------------------------------------------------------------
