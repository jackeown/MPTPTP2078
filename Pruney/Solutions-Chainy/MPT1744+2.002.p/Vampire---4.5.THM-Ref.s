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
% DateTime   : Thu Dec  3 13:18:11 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 314 expanded)
%              Number of leaves         :   11 (  55 expanded)
%              Depth                    :   33
%              Number of atoms          :  673 (4241 expanded)
%              Number of equality atoms :   34 (  34 expanded)
%              Maximal formula depth    :   29 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f196,plain,(
    $false ),
    inference(subsumption_resolution,[],[f195,f32])).

fof(f32,plain,(
    ~ r1_tmap_1(sK2,sK0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4),sK6) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6)
                              & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5)))
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & r1_tmap_1(X1,X0,X4,X5)
                          & v5_pre_topc(X3,X2,X1)
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & l1_pre_topc(X2)
              & v2_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6)
                              & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5)))
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & r1_tmap_1(X1,X0,X4,X5)
                          & v5_pre_topc(X3,X2,X1)
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & l1_pre_topc(X2)
              & v2_pre_topc(X2)
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
                ( ( l1_pre_topc(X2)
                  & v2_pre_topc(X2)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                          & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0))
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => ( ( r1_tmap_1(X1,X0,X4,X5)
                                & v5_pre_topc(X3,X2,X1) )
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X2))
                                 => ( r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5)))
                                   => r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6) ) ) ) ) ) ) ) ) ) ),
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
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ( ( r1_tmap_1(X1,X0,X4,X5)
                              & v5_pre_topc(X3,X2,X1) )
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5)))
                                 => r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_tmap_1)).

fof(f195,plain,(
    r1_tmap_1(sK2,sK0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4),sK6) ),
    inference(subsumption_resolution,[],[f194,f48])).

fof(f48,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f194,plain,
    ( v2_struct_0(sK0)
    | r1_tmap_1(sK2,sK0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4),sK6) ),
    inference(subsumption_resolution,[],[f193,f38])).

fof(f38,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f14])).

fof(f193,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK0)
    | r1_tmap_1(sK2,sK0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4),sK6) ),
    inference(subsumption_resolution,[],[f192,f37])).

fof(f37,plain,(
    v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f192,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK0)
    | r1_tmap_1(sK2,sK0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4),sK6) ),
    inference(subsumption_resolution,[],[f191,f36])).

fof(f36,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f14])).

fof(f191,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK0)
    | r1_tmap_1(sK2,sK0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4),sK6) ),
    inference(subsumption_resolution,[],[f190,f50])).

fof(f50,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f190,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK0)
    | r1_tmap_1(sK2,sK0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4),sK6) ),
    inference(subsumption_resolution,[],[f189,f49])).

fof(f49,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f189,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK0)
    | r1_tmap_1(sK2,sK0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4),sK6) ),
    inference(resolution,[],[f175,f35])).

fof(f35,plain,(
    r1_tmap_1(sK1,sK0,sK4,sK5) ),
    inference(cnf_transformation,[],[f14])).

fof(f175,plain,(
    ! [X0,X1] :
      ( ~ r1_tmap_1(sK1,X0,X1,sK5)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
      | v2_struct_0(X0)
      | r1_tmap_1(sK2,X0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X0),sK3,X1),sK6) ) ),
    inference(subsumption_resolution,[],[f174,f135])).

fof(f135,plain,(
    r1_tmap_1(sK2,sK1,sK3,sK6) ),
    inference(resolution,[],[f100,f30])).

fof(f30,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f100,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | r1_tmap_1(sK2,sK1,sK3,X0) ) ),
    inference(subsumption_resolution,[],[f99,f45])).

fof(f45,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f99,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | r1_tmap_1(sK2,sK1,sK3,X0)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f98,f41])).

fof(f41,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f14])).

fof(f98,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | r1_tmap_1(sK2,sK1,sK3,X0)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f97,f40])).

fof(f40,plain,(
    v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f97,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | r1_tmap_1(sK2,sK1,sK3,X0)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f96,f39])).

fof(f39,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f14])).

fof(f96,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK3)
      | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | r1_tmap_1(sK2,sK1,sK3,X0)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f95,f44])).

fof(f44,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f95,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK2)
      | ~ v1_funct_1(sK3)
      | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | r1_tmap_1(sK2,sK1,sK3,X0)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f94,f43])).

fof(f43,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f94,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK2)
      | ~ l1_pre_topc(sK2)
      | ~ v1_funct_1(sK3)
      | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | r1_tmap_1(sK2,sK1,sK3,X0)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f93,f42])).

fof(f42,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f93,plain,(
    ! [X0] :
      ( v2_struct_0(sK2)
      | ~ v2_pre_topc(sK2)
      | ~ l1_pre_topc(sK2)
      | ~ v1_funct_1(sK3)
      | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | r1_tmap_1(sK2,sK1,sK3,X0)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f92,f47])).

fof(f47,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f92,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK1)
      | v2_struct_0(sK2)
      | ~ v2_pre_topc(sK2)
      | ~ l1_pre_topc(sK2)
      | ~ v1_funct_1(sK3)
      | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | r1_tmap_1(sK2,sK1,sK3,X0)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f91,f46])).

fof(f46,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f91,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK2)
      | ~ v2_pre_topc(sK2)
      | ~ l1_pre_topc(sK2)
      | ~ v1_funct_1(sK3)
      | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | r1_tmap_1(sK2,sK1,sK3,X0)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f34,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_pre_topc(X2,X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | r1_tmap_1(X1,X0,X2,X3)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( r1_tmap_1(X1,X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
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
              ( ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( r1_tmap_1(X1,X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => r1_tmap_1(X1,X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tmap_1)).

fof(f34,plain,(
    v5_pre_topc(sK3,sK2,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f174,plain,(
    ! [X0,X1] :
      ( ~ r1_tmap_1(sK1,X0,X1,sK5)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
      | ~ r1_tmap_1(sK2,sK1,sK3,sK6)
      | v2_struct_0(X0)
      | r1_tmap_1(sK2,X0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X0),sK3,X1),sK6) ) ),
    inference(subsumption_resolution,[],[f173,f33])).

fof(f33,plain,(
    m1_subset_1(sK5,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f173,plain,(
    ! [X0,X1] :
      ( ~ r1_tmap_1(sK1,X0,X1,sK5)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
      | ~ m1_subset_1(sK5,u1_struct_0(sK1))
      | ~ r1_tmap_1(sK2,sK1,sK3,sK6)
      | v2_struct_0(X0)
      | r1_tmap_1(sK2,X0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X0),sK3,X1),sK6) ) ),
    inference(subsumption_resolution,[],[f172,f30])).

fof(f172,plain,(
    ! [X0,X1] :
      ( ~ r1_tmap_1(sK1,X0,X1,sK5)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
      | ~ m1_subset_1(sK5,u1_struct_0(sK1))
      | ~ r1_tmap_1(sK2,sK1,sK3,sK6)
      | v2_struct_0(X0)
      | r1_tmap_1(sK2,X0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X0),sK3,X1),sK6) ) ),
    inference(subsumption_resolution,[],[f171,f41])).

fof(f171,plain,(
    ! [X0,X1] :
      ( ~ r1_tmap_1(sK1,X0,X1,sK5)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
      | ~ m1_subset_1(sK5,u1_struct_0(sK1))
      | ~ r1_tmap_1(sK2,sK1,sK3,sK6)
      | v2_struct_0(X0)
      | r1_tmap_1(sK2,X0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X0),sK3,X1),sK6) ) ),
    inference(subsumption_resolution,[],[f170,f40])).

fof(f170,plain,(
    ! [X0,X1] :
      ( ~ r1_tmap_1(sK1,X0,X1,sK5)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
      | ~ m1_subset_1(sK5,u1_struct_0(sK1))
      | ~ r1_tmap_1(sK2,sK1,sK3,sK6)
      | v2_struct_0(X0)
      | r1_tmap_1(sK2,X0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X0),sK3,X1),sK6) ) ),
    inference(subsumption_resolution,[],[f169,f39])).

fof(f169,plain,(
    ! [X0,X1] :
      ( ~ r1_tmap_1(sK1,X0,X1,sK5)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_funct_1(sK3)
      | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
      | ~ m1_subset_1(sK5,u1_struct_0(sK1))
      | ~ r1_tmap_1(sK2,sK1,sK3,sK6)
      | v2_struct_0(X0)
      | r1_tmap_1(sK2,X0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X0),sK3,X1),sK6) ) ),
    inference(subsumption_resolution,[],[f168,f47])).

fof(f168,plain,(
    ! [X0,X1] :
      ( ~ r1_tmap_1(sK1,X0,X1,sK5)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK3)
      | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
      | ~ m1_subset_1(sK5,u1_struct_0(sK1))
      | ~ r1_tmap_1(sK2,sK1,sK3,sK6)
      | v2_struct_0(X0)
      | r1_tmap_1(sK2,X0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X0),sK3,X1),sK6) ) ),
    inference(subsumption_resolution,[],[f167,f46])).

fof(f167,plain,(
    ! [X0,X1] :
      ( ~ r1_tmap_1(sK1,X0,X1,sK5)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK3)
      | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
      | ~ m1_subset_1(sK5,u1_struct_0(sK1))
      | ~ r1_tmap_1(sK2,sK1,sK3,sK6)
      | v2_struct_0(X0)
      | r1_tmap_1(sK2,X0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X0),sK3,X1),sK6) ) ),
    inference(subsumption_resolution,[],[f166,f45])).

fof(f166,plain,(
    ! [X0,X1] :
      ( ~ r1_tmap_1(sK1,X0,X1,sK5)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK3)
      | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
      | ~ m1_subset_1(sK5,u1_struct_0(sK1))
      | ~ r1_tmap_1(sK2,sK1,sK3,sK6)
      | v2_struct_0(X0)
      | r1_tmap_1(sK2,X0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X0),sK3,X1),sK6) ) ),
    inference(subsumption_resolution,[],[f165,f44])).

% (320)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
fof(f165,plain,(
    ! [X0,X1] :
      ( ~ r1_tmap_1(sK1,X0,X1,sK5)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(sK2)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK3)
      | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
      | ~ m1_subset_1(sK5,u1_struct_0(sK1))
      | ~ r1_tmap_1(sK2,sK1,sK3,sK6)
      | v2_struct_0(X0)
      | r1_tmap_1(sK2,X0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X0),sK3,X1),sK6) ) ),
    inference(subsumption_resolution,[],[f164,f43])).

fof(f164,plain,(
    ! [X0,X1] :
      ( ~ r1_tmap_1(sK1,X0,X1,sK5)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(sK2)
      | ~ l1_pre_topc(sK2)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK3)
      | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
      | ~ m1_subset_1(sK5,u1_struct_0(sK1))
      | ~ r1_tmap_1(sK2,sK1,sK3,sK6)
      | v2_struct_0(X0)
      | r1_tmap_1(sK2,X0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X0),sK3,X1),sK6) ) ),
    inference(subsumption_resolution,[],[f163,f42])).

fof(f163,plain,(
    ! [X0,X1] :
      ( ~ r1_tmap_1(sK1,X0,X1,sK5)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(sK2)
      | ~ v2_pre_topc(sK2)
      | ~ l1_pre_topc(sK2)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK3)
      | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
      | ~ m1_subset_1(sK5,u1_struct_0(sK1))
      | ~ r1_tmap_1(sK2,sK1,sK3,sK6)
      | v2_struct_0(X0)
      | r1_tmap_1(sK2,X0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X0),sK3,X1),sK6) ) ),
    inference(superposition,[],[f71,f162])).

fof(f162,plain,(
    sK5 = k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6) ),
    inference(forward_demodulation,[],[f161,f153])).

fof(f153,plain,(
    sK5 = k1_funct_1(sK3,sK6) ),
    inference(resolution,[],[f138,f72])).

fof(f72,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f138,plain,(
    r2_hidden(k1_funct_1(sK3,sK6),k1_tarski(sK5)) ),
    inference(backward_demodulation,[],[f133,f137])).

fof(f137,plain,(
    k6_domain_1(u1_struct_0(sK1),sK5) = k1_tarski(sK5) ),
    inference(resolution,[],[f88,f90])).

fof(f90,plain,(
    ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f89,f45])).

fof(f89,plain,
    ( v2_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(resolution,[],[f83,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f83,plain,(
    l1_struct_0(sK1) ),
    inference(resolution,[],[f47,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f88,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | k6_domain_1(u1_struct_0(sK1),sK5) = k1_tarski(sK5) ),
    inference(resolution,[],[f33,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f133,plain,(
    r2_hidden(k1_funct_1(sK3,sK6),k6_domain_1(u1_struct_0(sK1),sK5)) ),
    inference(subsumption_resolution,[],[f132,f124])).

fof(f124,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f41,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f132,plain,
    ( r2_hidden(k1_funct_1(sK3,sK6),k6_domain_1(u1_struct_0(sK1),sK5))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f129,f39])).

fof(f129,plain,
    ( ~ v1_funct_1(sK3)
    | r2_hidden(k1_funct_1(sK3,sK6),k6_domain_1(u1_struct_0(sK1),sK5))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f127,f76])).

fof(f76,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k10_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | r2_hidden(k1_funct_1(X0,X3),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(k1_funct_1(X0,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_funct_1)).

fof(f127,plain,(
    r2_hidden(sK6,k10_relat_1(sK3,k6_domain_1(u1_struct_0(sK1),sK5))) ),
    inference(backward_demodulation,[],[f31,f125])).

fof(f125,plain,(
    ! [X0] : k10_relat_1(sK3,X0) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0) ),
    inference(resolution,[],[f41,f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f31,plain,(
    r2_hidden(sK6,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k6_domain_1(u1_struct_0(sK1),sK5))) ),
    inference(cnf_transformation,[],[f14])).

fof(f161,plain,(
    k1_funct_1(sK3,sK6) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6) ),
    inference(resolution,[],[f120,f30])).

fof(f120,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0) = k1_funct_1(sK3,X0) ) ),
    inference(subsumption_resolution,[],[f119,f41])).

fof(f119,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0) = k1_funct_1(sK3,X0) ) ),
    inference(subsumption_resolution,[],[f118,f87])).

fof(f87,plain,(
    ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f86,f42])).

fof(f86,plain,
    ( v2_struct_0(sK2)
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(resolution,[],[f82,f62])).

fof(f82,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f44,f63])).

fof(f118,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0) = k1_funct_1(sK3,X0) ) ),
    inference(subsumption_resolution,[],[f117,f39])).

fof(f117,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK3)
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0) = k1_funct_1(sK3,X0) ) ),
    inference(resolution,[],[f40,f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,X0)
      | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r1_tmap_1(X2,X0,X4,k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5),u1_struct_0(X2))
      | ~ r1_tmap_1(X1,X2,X3,X5)
      | v2_struct_0(X0)
      | r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) != X6
      | ~ r1_tmap_1(X1,X2,X3,X5)
      | ~ r1_tmap_1(X2,X0,X4,X6)
      | r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5)
                              | ~ r1_tmap_1(X2,X0,X4,X6)
                              | ~ r1_tmap_1(X1,X2,X3,X5)
                              | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                  | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  | ~ v1_funct_1(X3) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | v2_struct_0(X2) )
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
                          ( ! [X6] :
                              ( r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5)
                              | ~ r1_tmap_1(X2,X0,X4,X6)
                              | ~ r1_tmap_1(X1,X2,X3,X5)
                              | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                  | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  | ~ v1_funct_1(X3) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | v2_struct_0(X2) )
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
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                    & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                    & v1_funct_1(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X2))
                             => ( ( r1_tmap_1(X2,X0,X4,X6)
                                  & r1_tmap_1(X1,X2,X3,X5)
                                  & k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) = X6 )
                               => r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_tmap_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.20/0.35  % CPULimit   : 60
% 0.20/0.35  % WCLimit    : 600
% 0.20/0.35  % DateTime   : Tue Dec  1 17:25:51 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.21/0.50  % (306)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (303)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (302)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (322)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.52  % (321)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.52  % (309)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.52  % (301)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.52  % (315)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.52  % (306)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (312)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.53  % (301)Refutation not found, incomplete strategy% (301)------------------------------
% 0.21/0.53  % (301)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (301)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (301)Memory used [KB]: 10746
% 0.21/0.53  % (301)Time elapsed: 0.099 s
% 0.21/0.53  % (301)------------------------------
% 0.21/0.53  % (301)------------------------------
% 0.21/0.53  % (305)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.53  % (313)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.53  % (324)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f196,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(subsumption_resolution,[],[f195,f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ~r1_tmap_1(sK2,sK0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4),sK6)),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5))) & m1_subset_1(X6,u1_struct_0(X2))) & r1_tmap_1(X1,X0,X4,X5) & v5_pre_topc(X3,X2,X1) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((? [X6] : ((~r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5)))) & m1_subset_1(X6,u1_struct_0(X2))) & (r1_tmap_1(X1,X0,X4,X5) & v5_pre_topc(X3,X2,X1))) & m1_subset_1(X5,u1_struct_0(X1))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3))) & (l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,negated_conjecture,(
% 0.21/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ((r1_tmap_1(X1,X0,X4,X5) & v5_pre_topc(X3,X2,X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5))) => r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6))))))))))),
% 0.21/0.53    inference(negated_conjecture,[],[f11])).
% 0.21/0.53  fof(f11,conjecture,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ((r1_tmap_1(X1,X0,X4,X5) & v5_pre_topc(X3,X2,X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5))) => r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6))))))))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_tmap_1)).
% 0.21/0.53  fof(f195,plain,(
% 0.21/0.53    r1_tmap_1(sK2,sK0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4),sK6)),
% 0.21/0.53    inference(subsumption_resolution,[],[f194,f48])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ~v2_struct_0(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f194,plain,(
% 0.21/0.53    v2_struct_0(sK0) | r1_tmap_1(sK2,sK0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4),sK6)),
% 0.21/0.53    inference(subsumption_resolution,[],[f193,f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f193,plain,(
% 0.21/0.53    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK0) | r1_tmap_1(sK2,sK0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4),sK6)),
% 0.21/0.53    inference(subsumption_resolution,[],[f192,f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f192,plain,(
% 0.21/0.53    ~v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK0) | r1_tmap_1(sK2,sK0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4),sK6)),
% 0.21/0.53    inference(subsumption_resolution,[],[f191,f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    v1_funct_1(sK4)),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f191,plain,(
% 0.21/0.53    ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK0) | r1_tmap_1(sK2,sK0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4),sK6)),
% 0.21/0.53    inference(subsumption_resolution,[],[f190,f50])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    l1_pre_topc(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f190,plain,(
% 0.21/0.53    ~l1_pre_topc(sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK0) | r1_tmap_1(sK2,sK0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4),sK6)),
% 0.21/0.53    inference(subsumption_resolution,[],[f189,f49])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    v2_pre_topc(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f189,plain,(
% 0.21/0.53    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK0) | r1_tmap_1(sK2,sK0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4),sK6)),
% 0.21/0.53    inference(resolution,[],[f175,f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    r1_tmap_1(sK1,sK0,sK4,sK5)),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f175,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tmap_1(sK1,X0,X1,sK5) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) | v2_struct_0(X0) | r1_tmap_1(sK2,X0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X0),sK3,X1),sK6)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f174,f135])).
% 0.21/0.53  fof(f135,plain,(
% 0.21/0.53    r1_tmap_1(sK2,sK1,sK3,sK6)),
% 0.21/0.53    inference(resolution,[],[f100,f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    m1_subset_1(sK6,u1_struct_0(sK2))),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f100,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK2)) | r1_tmap_1(sK2,sK1,sK3,X0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f99,f45])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ~v2_struct_0(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f99,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK2)) | r1_tmap_1(sK2,sK1,sK3,X0) | v2_struct_0(sK1)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f98,f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f98,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_subset_1(X0,u1_struct_0(sK2)) | r1_tmap_1(sK2,sK1,sK3,X0) | v2_struct_0(sK1)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f97,f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f97,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_subset_1(X0,u1_struct_0(sK2)) | r1_tmap_1(sK2,sK1,sK3,X0) | v2_struct_0(sK1)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f96,f39])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    v1_funct_1(sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f96,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_funct_1(sK3) | ~v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_subset_1(X0,u1_struct_0(sK2)) | r1_tmap_1(sK2,sK1,sK3,X0) | v2_struct_0(sK1)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f95,f44])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    l1_pre_topc(sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f95,plain,(
% 0.21/0.53    ( ! [X0] : (~l1_pre_topc(sK2) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_subset_1(X0,u1_struct_0(sK2)) | r1_tmap_1(sK2,sK1,sK3,X0) | v2_struct_0(sK1)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f94,f43])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    v2_pre_topc(sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f94,plain,(
% 0.21/0.53    ( ! [X0] : (~v2_pre_topc(sK2) | ~l1_pre_topc(sK2) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_subset_1(X0,u1_struct_0(sK2)) | r1_tmap_1(sK2,sK1,sK3,X0) | v2_struct_0(sK1)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f93,f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ~v2_struct_0(sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f93,plain,(
% 0.21/0.53    ( ! [X0] : (v2_struct_0(sK2) | ~v2_pre_topc(sK2) | ~l1_pre_topc(sK2) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_subset_1(X0,u1_struct_0(sK2)) | r1_tmap_1(sK2,sK1,sK3,X0) | v2_struct_0(sK1)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f92,f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    l1_pre_topc(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f92,plain,(
% 0.21/0.53    ( ! [X0] : (~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~v2_pre_topc(sK2) | ~l1_pre_topc(sK2) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_subset_1(X0,u1_struct_0(sK2)) | r1_tmap_1(sK2,sK1,sK3,X0) | v2_struct_0(sK1)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f91,f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    v2_pre_topc(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f91,plain,(
% 0.21/0.53    ( ! [X0] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~v2_pre_topc(sK2) | ~l1_pre_topc(sK2) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_subset_1(X0,u1_struct_0(sK2)) | r1_tmap_1(sK2,sK1,sK3,X0) | v2_struct_0(sK1)) )),
% 0.21/0.53    inference(resolution,[],[f34,f58])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~v5_pre_topc(X2,X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~m1_subset_1(X3,u1_struct_0(X1)) | r1_tmap_1(X1,X0,X2,X3) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X1,X0) <=> ! [X3] : (r1_tmap_1(X1,X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X1,X0) <=> ! [X3] : (r1_tmap_1(X1,X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X1,X0) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => r1_tmap_1(X1,X0,X2,X3))))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tmap_1)).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    v5_pre_topc(sK3,sK2,sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f174,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tmap_1(sK1,X0,X1,sK5) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) | ~r1_tmap_1(sK2,sK1,sK3,sK6) | v2_struct_0(X0) | r1_tmap_1(sK2,X0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X0),sK3,X1),sK6)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f173,f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    m1_subset_1(sK5,u1_struct_0(sK1))),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f173,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tmap_1(sK1,X0,X1,sK5) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~r1_tmap_1(sK2,sK1,sK3,sK6) | v2_struct_0(X0) | r1_tmap_1(sK2,X0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X0),sK3,X1),sK6)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f172,f30])).
% 0.21/0.53  fof(f172,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tmap_1(sK1,X0,X1,sK5) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~r1_tmap_1(sK2,sK1,sK3,sK6) | v2_struct_0(X0) | r1_tmap_1(sK2,X0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X0),sK3,X1),sK6)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f171,f41])).
% 0.21/0.53  fof(f171,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tmap_1(sK1,X0,X1,sK5) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~r1_tmap_1(sK2,sK1,sK3,sK6) | v2_struct_0(X0) | r1_tmap_1(sK2,X0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X0),sK3,X1),sK6)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f170,f40])).
% 0.21/0.53  fof(f170,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tmap_1(sK1,X0,X1,sK5) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~r1_tmap_1(sK2,sK1,sK3,sK6) | v2_struct_0(X0) | r1_tmap_1(sK2,X0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X0),sK3,X1),sK6)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f169,f39])).
% 0.21/0.53  fof(f169,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tmap_1(sK1,X0,X1,sK5) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~r1_tmap_1(sK2,sK1,sK3,sK6) | v2_struct_0(X0) | r1_tmap_1(sK2,X0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X0),sK3,X1),sK6)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f168,f47])).
% 0.21/0.53  fof(f168,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tmap_1(sK1,X0,X1,sK5) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~r1_tmap_1(sK2,sK1,sK3,sK6) | v2_struct_0(X0) | r1_tmap_1(sK2,X0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X0),sK3,X1),sK6)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f167,f46])).
% 0.21/0.53  fof(f167,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tmap_1(sK1,X0,X1,sK5) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~r1_tmap_1(sK2,sK1,sK3,sK6) | v2_struct_0(X0) | r1_tmap_1(sK2,X0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X0),sK3,X1),sK6)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f166,f45])).
% 0.21/0.53  fof(f166,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tmap_1(sK1,X0,X1,sK5) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~r1_tmap_1(sK2,sK1,sK3,sK6) | v2_struct_0(X0) | r1_tmap_1(sK2,X0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X0),sK3,X1),sK6)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f165,f44])).
% 0.21/0.53  % (320)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.53  fof(f165,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tmap_1(sK1,X0,X1,sK5) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~l1_pre_topc(sK2) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~r1_tmap_1(sK2,sK1,sK3,sK6) | v2_struct_0(X0) | r1_tmap_1(sK2,X0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X0),sK3,X1),sK6)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f164,f43])).
% 0.21/0.53  fof(f164,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tmap_1(sK1,X0,X1,sK5) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(sK2) | ~l1_pre_topc(sK2) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~r1_tmap_1(sK2,sK1,sK3,sK6) | v2_struct_0(X0) | r1_tmap_1(sK2,X0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X0),sK3,X1),sK6)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f163,f42])).
% 0.21/0.53  fof(f163,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tmap_1(sK1,X0,X1,sK5) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK2) | ~v2_pre_topc(sK2) | ~l1_pre_topc(sK2) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~r1_tmap_1(sK2,sK1,sK3,sK6) | v2_struct_0(X0) | r1_tmap_1(sK2,X0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X0),sK3,X1),sK6)) )),
% 0.21/0.53    inference(superposition,[],[f71,f162])).
% 0.21/0.53  fof(f162,plain,(
% 0.21/0.53    sK5 = k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6)),
% 0.21/0.53    inference(forward_demodulation,[],[f161,f153])).
% 0.21/0.53  fof(f153,plain,(
% 0.21/0.53    sK5 = k1_funct_1(sK3,sK6)),
% 0.21/0.53    inference(resolution,[],[f138,f72])).
% 0.21/0.53  fof(f72,plain,(
% 0.21/0.53    ( ! [X2,X0] : (~r2_hidden(X2,k1_tarski(X0)) | X0 = X2) )),
% 0.21/0.53    inference(equality_resolution,[],[f53])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.21/0.53  fof(f138,plain,(
% 0.21/0.53    r2_hidden(k1_funct_1(sK3,sK6),k1_tarski(sK5))),
% 0.21/0.53    inference(backward_demodulation,[],[f133,f137])).
% 0.21/0.53  fof(f137,plain,(
% 0.21/0.53    k6_domain_1(u1_struct_0(sK1),sK5) = k1_tarski(sK5)),
% 0.21/0.53    inference(resolution,[],[f88,f90])).
% 0.21/0.53  fof(f90,plain,(
% 0.21/0.53    ~v1_xboole_0(u1_struct_0(sK1))),
% 0.21/0.53    inference(subsumption_resolution,[],[f89,f45])).
% 0.21/0.53  fof(f89,plain,(
% 0.21/0.53    v2_struct_0(sK1) | ~v1_xboole_0(u1_struct_0(sK1))),
% 0.21/0.53    inference(resolution,[],[f83,f62])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    ( ! [X0] : (~l1_struct_0(X0) | v2_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.53  fof(f83,plain,(
% 0.21/0.53    l1_struct_0(sK1)),
% 0.21/0.53    inference(resolution,[],[f47,f63])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.53  fof(f88,plain,(
% 0.21/0.53    v1_xboole_0(u1_struct_0(sK1)) | k6_domain_1(u1_struct_0(sK1),sK5) = k1_tarski(sK5)),
% 0.21/0.53    inference(resolution,[],[f33,f57])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.53    inference(flattening,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.21/0.53  fof(f133,plain,(
% 0.21/0.53    r2_hidden(k1_funct_1(sK3,sK6),k6_domain_1(u1_struct_0(sK1),sK5))),
% 0.21/0.53    inference(subsumption_resolution,[],[f132,f124])).
% 0.21/0.53  fof(f124,plain,(
% 0.21/0.53    v1_relat_1(sK3)),
% 0.21/0.53    inference(resolution,[],[f41,f70])).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.53  fof(f132,plain,(
% 0.21/0.53    r2_hidden(k1_funct_1(sK3,sK6),k6_domain_1(u1_struct_0(sK1),sK5)) | ~v1_relat_1(sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f129,f39])).
% 0.21/0.53  fof(f129,plain,(
% 0.21/0.53    ~v1_funct_1(sK3) | r2_hidden(k1_funct_1(sK3,sK6),k6_domain_1(u1_struct_0(sK1),sK5)) | ~v1_relat_1(sK3)),
% 0.21/0.53    inference(resolution,[],[f127,f76])).
% 0.21/0.53  fof(f76,plain,(
% 0.21/0.53    ( ! [X0,X3,X1] : (~r2_hidden(X3,k10_relat_1(X0,X1)) | ~v1_funct_1(X0) | r2_hidden(k1_funct_1(X0,X3),X1) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(equality_resolution,[],[f68])).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,X2) | k10_relat_1(X0,X1) != X2) )),
% 0.21/0.53    inference(cnf_transformation,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(flattening,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_funct_1)).
% 0.21/0.53  fof(f127,plain,(
% 0.21/0.53    r2_hidden(sK6,k10_relat_1(sK3,k6_domain_1(u1_struct_0(sK1),sK5)))),
% 0.21/0.53    inference(backward_demodulation,[],[f31,f125])).
% 0.21/0.53  fof(f125,plain,(
% 0.21/0.53    ( ! [X0] : (k10_relat_1(sK3,X0) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0)) )),
% 0.21/0.53    inference(resolution,[],[f41,f56])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    r2_hidden(sK6,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k6_domain_1(u1_struct_0(sK1),sK5)))),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f161,plain,(
% 0.21/0.53    k1_funct_1(sK3,sK6) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6)),
% 0.21/0.53    inference(resolution,[],[f120,f30])).
% 0.21/0.53  fof(f120,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK2)) | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0) = k1_funct_1(sK3,X0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f119,f41])).
% 0.21/0.53  fof(f119,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_subset_1(X0,u1_struct_0(sK2)) | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0) = k1_funct_1(sK3,X0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f118,f87])).
% 0.21/0.53  fof(f87,plain,(
% 0.21/0.53    ~v1_xboole_0(u1_struct_0(sK2))),
% 0.21/0.53    inference(subsumption_resolution,[],[f86,f42])).
% 0.21/0.53  fof(f86,plain,(
% 0.21/0.53    v2_struct_0(sK2) | ~v1_xboole_0(u1_struct_0(sK2))),
% 0.21/0.53    inference(resolution,[],[f82,f62])).
% 0.21/0.53  fof(f82,plain,(
% 0.21/0.53    l1_struct_0(sK2)),
% 0.21/0.53    inference(resolution,[],[f44,f63])).
% 0.21/0.53  fof(f118,plain,(
% 0.21/0.53    ( ! [X0] : (v1_xboole_0(u1_struct_0(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_subset_1(X0,u1_struct_0(sK2)) | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0) = k1_funct_1(sK3,X0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f117,f39])).
% 0.21/0.53  fof(f117,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_funct_1(sK3) | v1_xboole_0(u1_struct_0(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_subset_1(X0,u1_struct_0(sK2)) | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0) = k1_funct_1(sK3,X0)) )),
% 0.21/0.53    inference(resolution,[],[f40,f61])).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,X0) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.21/0.53    inference(flattening,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 0.21/0.53  fof(f71,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (~r1_tmap_1(X2,X0,X4,k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5),u1_struct_0(X2)) | ~r1_tmap_1(X1,X2,X3,X5) | v2_struct_0(X0) | r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5)) )),
% 0.21/0.53    inference(equality_resolution,[],[f51])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X6,u1_struct_0(X2)) | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) != X6 | ~r1_tmap_1(X1,X2,X3,X5) | ~r1_tmap_1(X2,X0,X4,X6) | r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5) | ~r1_tmap_1(X2,X0,X4,X6) | ~r1_tmap_1(X1,X2,X3,X5) | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X3)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5) | (~r1_tmap_1(X2,X0,X4,X6) | ~r1_tmap_1(X1,X2,X3,X5) | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) != X6)) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X1))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X3))) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X0,X4,X6) & r1_tmap_1(X1,X2,X3,X5) & k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) = X6) => r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5)))))))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_tmap_1)).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (306)------------------------------
% 0.21/0.53  % (306)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (306)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (306)Memory used [KB]: 6268
% 0.21/0.53  % (306)Time elapsed: 0.104 s
% 0.21/0.53  % (306)------------------------------
% 0.21/0.53  % (306)------------------------------
% 0.21/0.53  % (316)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.53  % (300)Success in time 0.166 s
%------------------------------------------------------------------------------
